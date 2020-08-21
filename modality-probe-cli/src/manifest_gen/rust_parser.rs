use crate::manifest_gen::{
    event_metadata::EventMetadata,
    parser::{
        self, event_name_valid, probe_name_valid, remove_double_quotes, tags_or_desc_valid,
        trimmed_string, trimmed_string_w_space, Parser, ParserConfig, Span,
    },
    probe_metadata::ProbeMetadata,
    source_location::SourceLocation,
    type_hint::TypeHint,
};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take, take_till1, take_until},
    character::complete::{char, line_ending, multispace0},
    combinator::{iterator, opt, peek, rest},
    error::ParseError,
    sequence::{delimited, preceded},
};
use nom_locate::position;
use std::fmt;
use std::str::FromStr;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct RustParser<'a> {
    pub config: ParserConfig<'a>,
}

impl<'a> Default for RustParser<'a> {
    fn default() -> Self {
        RustParser {
            config: ParserConfig {
                prefix: "ModalityProbe",
            },
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    Syntax(SourceLocation),
    MissingSemicolon(SourceLocation),
    UnrecognizedTypeHint(SourceLocation),
    EmptyTags(SourceLocation),
}

impl Error {
    pub fn location(&self) -> &SourceLocation {
        match self {
            Error::Syntax(l) => l,
            Error::MissingSemicolon(l) => l,
            Error::UnrecognizedTypeHint(l) => l,
            Error::EmptyTags(l) => l,
        }
    }
}

impl<'a> Parser for RustParser<'a> {
    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, parser::Error> {
        let md = self.parse_event_md(input)?;
        Ok(md)
    }

    fn parse_probes(&self, input: &str) -> Result<Vec<ProbeMetadata>, parser::Error> {
        let md = self.parse_probe_md(input)?;
        Ok(md)
    }
}

impl<'a> RustParser<'a> {
    pub fn new(config: ParserConfig<'a>) -> Self {
        RustParser { config }
    }

    pub fn parse_event_md(&self, input: &str) -> Result<Vec<EventMetadata>, Error> {
        parse_input(&self.config, input, parse_record_event_call_exp)
    }

    pub fn parse_probe_md(&self, input: &str) -> Result<Vec<ProbeMetadata>, Error> {
        parse_input(&self.config, input, parse_init_call_exp)
    }
}

fn parse_input<T>(
    config: &ParserConfig,
    input: &str,
    parse_fn: fn(Span) -> ParserResult<Span, T>,
) -> Result<Vec<T>, Error> {
    let mut md = vec![];
    let mut input = Span::new_extra(input, Some(config));
    while !input.fragment().is_empty() {
        match parse_fn(input) {
            Ok((rem, metadata)) => {
                md.push(metadata);
                input = rem;
            }
            Err(e) => match e {
                nom::Err::Incomplete(_) => {
                    break;
                }
                nom::Err::Error(int_err) => {
                    let res: nom::IResult<Span, _> = take(1usize)(int_err.into_inner());
                    if let Ok((rem, _)) = res {
                        input = rem;
                    } else {
                        break;
                    }
                }
                nom::Err::Failure(e) => match e.kind {
                    InternalErrorKind::Nom(_, _) => break,
                    InternalErrorKind::Error(_, err) => return Err(err),
                },
            },
        }
    }
    Ok(md)
}

fn parse_record_event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, _) = imports(input)?;
    let (input, found_try) = peek(opt(alt((
        tag("try_record"),
        tag("try_record_w_"),
        tag("try_expect"),
    ))))(input)?;
    if found_try.is_some() {
        let (input, found_expect) = peek(opt(tag("try_expect")))(input)?;
        if found_expect.is_some() {
            let (input, metadata) = expect_try_call_exp(input)?;
            Ok((input, metadata))
        } else {
            let (input, found_with_payload) = peek(opt(tag("try_record_w_")))(input)?;
            let (input, metadata) = match found_with_payload {
                None => event_try_call_exp(input)?,
                Some(_) => event_try_with_payload_call_exp(input)?,
            };
            Ok((input, metadata))
        }
    } else {
        let (input, found_expect) = peek(opt(tag("expect")))(input)?;
        if found_expect.is_some() {
            let (input, metadata) = expect_call_exp(input)?;
            Ok((input, metadata))
        } else {
            let (input, found_with_payload) = peek(opt(tag("record_w_")))(input)?;
            let (input, metadata) = match found_with_payload {
                None => event_call_exp(input)?,
                Some(_) => event_with_payload_call_exp(input)?,
            };
            Ok((input, metadata))
        }
    }
}

fn expect_try_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("try_expect!")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(";")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            arg_vec.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    match arg_vec.len() {
        1..=3 => (), // At least an expression, maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    let expr = arg_vec.remove(0).trim().to_string();
    if expr.is_empty() {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc = arg_vec;
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let mut tags = tags_pos
        .map(|index| tags_and_desc.remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &mut tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
        if !t.contains("EXPECTATION") {
            t.insert_str(0, "EXPECTATION;");
        }
    } else {
        tags = Some(String::from("EXPECTATION"));
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: Some((TypeHint::U32, expr).into()),
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn expect_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("expect!(")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, full_name) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg = Span::new_extra(&full_name, input.extra);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg)
        .map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            arg_vec.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    let arg = arg_vec.remove(0);
    let arg = Span::new_extra(&arg, input.extra);
    let (_, expr) =
        rest_literal(arg).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if expr.is_empty() {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = arg_vec
        .iter()
        .filter(|s| !s.is_empty())
        .map(|s| (*s).to_string())
        .collect();
    match tags_and_desc.len() {
        0..=2 => (), // Maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let mut tags = tags_pos
        .map(|index| tags_and_desc.swap_remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &mut tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
        if !t.contains("EXPECTATION") {
            t.insert_str(0, "EXPECTATION;");
        }
    } else {
        tags = Some(String::from("EXPECTATION"));
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: Some((TypeHint::U32, expr).into()),
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn event_try_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("try_record!")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(";")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) = variable_call_exp_arg(args)?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, name) = if expect_tags_or_desc {
        variable_call_exp_arg(args)?
    } else {
        let (args, remain) = rest(args)?;
        let (remain, arg) = opt(take_until(")"))(remain)?;
        let (remain, _) = opt(tag(")"))(remain)?;
        if let Some(arg) = arg {
            (args, (*arg.fragment()).trim().to_string())
        } else {
            (args, (*remain.fragment()).trim().to_string())
        }
    };
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            tags_and_desc.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    if tags_and_desc.len() > 2 {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let tags = tags_pos
        .map(|index| tags_and_desc.remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: None,
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("record!(")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, full_name) = if expect_tags_or_desc {
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    } else {
        let (args, name_token) =
            take_until(")")(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        let (_args, _) = tag(")")(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        rest_string(name_token).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    };
    let arg = Span::new_extra(&full_name, input.extra);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg)
        .map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            arg_vec.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    let mut tags_and_desc: Vec<String> = arg_vec
        .iter()
        .filter(|s| !s.is_empty())
        .map(|s| (*s).to_string())
        .collect();
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let tags = tags_pos
        .map(|index| tags_and_desc.swap_remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: None,
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn event_try_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("try_record_w_")(input)?;
    let (input, type_hint) = take_until("!")(input)?;
    let (input, _) = tag("!")(input)?;
    let type_hint = TypeHint::from_str(type_hint.fragment())
        .map_err(|_| make_failure(input, Error::UnrecognizedTypeHint(pos.into())))?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(";")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            arg_vec.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    match arg_vec.len() {
        1..=3 => (), // At least a payload, maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    let payload = arg_vec.remove(0).trim().to_string();
    let mut tags_and_desc = arg_vec;
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let tags = tags_pos
        .map(|index| tags_and_desc.remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: Some((type_hint, payload).into()),
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn event_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("record_w_")(input)?;
    let (input, type_hint) = take_until("!")(input)?;
    let (input, _) = tag("!")(input)?;
    let type_hint = TypeHint::from_str(type_hint.fragment())
        .map_err(|_| make_failure(input, Error::UnrecognizedTypeHint(pos.into())))?;
    let (input, _) = tag("(")(input).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, probe_instance) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, full_name) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg = Span::new_extra(&full_name, input.extra);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg)
        .map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| arg_vec.push(s));
    let (_args, _) = iter.finish()?;
    let arg = arg_vec.remove(0);
    let arg = Span::new_extra(&arg, input.extra);
    let (_, payload) =
        rest_literal(arg).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if payload.is_empty() {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = arg_vec
        .iter()
        .filter(|s| !s.is_empty())
        .map(|s| (*s).to_string())
        .collect();
    match tags_and_desc.len() {
        0..=2 => (), // Maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let tags = tags_pos
        .map(|index| tags_and_desc.swap_remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            probe_instance,
            payload: Some((type_hint, payload).into()),
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn reduced_event_id_exp_alt_a(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, id) = take_until(".")(input)?;
    if !id
        .fragment()
        .chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == ':')
    {
        return Err(make_error(input, Error::Syntax(pos.into())));
    }
    Ok((input, trimmed_string(id.fragment())))
}

fn reduced_event_id_exp_alt_b(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = take_until("(")(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, id) = take_until(")")(input)?;
    if !id
        .fragment()
        .chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == ':')
    {
        return Err(make_error(input, Error::Syntax(pos.into())));
    }
    Ok((input, trimmed_string(id.fragment())))
}

fn variable_call_exp_arg(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, arg) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    Ok((input, trimmed_string(arg.fragment())))
}

fn multi_variable_call_exp_arg_literal(input: Span) -> ParserResult<Span, String> {
    if input.fragment().is_empty() {
        return Err(nom::Err::Error(
            (input, nom::error::ErrorKind::ParseTo).into(),
        ));
    }
    let (input, _) = comments_and_spacing(input)?;
    let (input, expect_tags) = peek(opt(tag("tags!")))(input)?;
    let expect_another = peek(variable_call_exp_arg_literal)(input).is_ok();
    let (input, arg) = if expect_tags.is_some() {
        modality_tags(input)?
    } else if expect_another {
        variable_call_exp_arg_literal(input)?
    } else {
        let (input, _) = comments_and_spacing(input)?;
        let (input, remain) = rest(input)?;
        let (remain, arg) = opt(take_until(")"))(remain)?;
        let (remain, _) = opt(tag(")"))(remain)?;
        if let Some(arg) = arg {
            (input, (*arg.fragment()).to_string())
        } else {
            (input, (*remain.fragment()).to_string())
        }
    };
    let (input, maybe_terminal) = opt(terminal_tokens)(input)?;
    let input = if maybe_terminal.is_some() {
        let (input, _) = opt(alt((take_until("?"), take_until(")"))))(input)?;
        let (input, _) = opt(alt((tag("?"), tag(")"))))(input)?;
        input
    } else {
        input
    };
    Ok((input, arg))
}

fn terminal_tokens(input: Span) -> ParserResult<Span, ()> {
    let (input, _) = tag(")")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = comment(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = comment(input)?;
    let (input, _) = opt(alt((tag("."), tag("?"))))(input)?;
    Ok((input, ()))
}

fn variable_call_exp_arg_literal(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, arg) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    Ok((input, (*arg.fragment()).to_string()))
}

fn parse_init_call_exp(input: Span) -> ParserResult<Span, ProbeMetadata> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, _) = imports(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = alt((
        tag("try_initialize_at!"),
        tag("initialize_at!"),
        tag("new_with_storage!"),
    ))(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(";")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, _storage) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, full_name) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, _next_seq_id_provider) = if expect_tags_or_desc {
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    } else {
        let (args, token) =
            take_until(")")(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        let (_args, _) = tag(")")(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        rest_string(token).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    };
    let name =
        reduce_namespace(&full_name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !probe_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| {
        if !s.is_empty() {
            tags_and_desc.push(s)
        }
    });
    let (_args, _) = iter.finish()?;
    if tags_and_desc.len() > 2 {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    for s in tags_and_desc.iter_mut() {
        *s = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    }
    let tags_pos = tags_and_desc.iter().position(|s| s.contains("tags="));
    let tags = tags_pos
        .map(|index| tags_and_desc.remove(index))
        .map(|s| s.replace("tags=", ""));
    if let Some(t) = &tags {
        if t.is_empty() {
            return Err(make_failure(input, Error::EmptyTags(pos.into())));
        }
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        ProbeMetadata {
            name,
            location: pos.into(),
            tags,
            description,
        },
    ))
}

fn modality_tags(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = tag("tags!")(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)
        .map_err(|e| convert_error(e, Error::EmptyTags(pos.into())))?;
    let (input, _) = opt(tag(","))(input)?;
    let split: Vec<&str> = args.fragment().split(',').collect();
    if split.is_empty() {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags = String::from("tags=");
    for (idx, s) in split.iter().enumerate() {
        let t = truncate_and_trim(s).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
        tags.push_str(&t);
        if (split.len() > 1) && (idx < (split.len() - 1)) {
            tags.push(';');
        }
    }
    let tags = format!("\"{}\"", tags);
    Ok((input, tags))
}

fn comments_and_spacing(input: Span) -> ParserResult<Span, ()> {
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = comment(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = comment(input)?;
    Ok((input, ()))
}

fn comment(input: Span) -> ParserResult<Span, ()> {
    let (input, maybe_comment) = opt(alt((tag("///"), tag("//"))))(input)?;
    let input = if maybe_comment.is_some() {
        let (input, _) = take_till1(|c| c == '\n')(input)?;
        input
    } else {
        input
    };

    let (input, maybe_comment) = opt(tag("/*"))(input)?;
    let input = if maybe_comment.is_some() {
        let (input, _) = take_until("*/")(input)?;
        let (input, _) = tag("*/")(input)?;
        input
    } else {
        input
    };

    Ok((input, ()))
}

fn imports(input: Span) -> ParserResult<Span, ()> {
    let (input, _) = opt(preceded(tag("use "), take_until(";")))(input)?;
    Ok((input, ()))
}

fn rest_string(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, rst) = rest(input)?;
    Ok((input, trimmed_string(rst.fragment())))
}

fn rest_literal(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, rst) = rest(input)?;
    Ok((input, (*rst.fragment()).to_string()))
}

fn truncate_and_trim(s: &str) -> Result<String, ()> {
    let arg = Span::new_extra(s, None);
    let (arg, _) = comments_and_spacing(arg).map_err(|_| ())?;
    let tail_index = arg.fragment().rfind('"').ok_or(())?;
    if tail_index == 0 {
        return Err(());
    }
    let mut s = (*arg.fragment()).to_string();
    s.truncate(tail_index + 1);
    s = trimmed_string_w_space(&s);
    if !tags_or_desc_valid(&s) {
        return Err(());
    }
    s = remove_double_quotes(&s);
    Ok(s)
}

fn reduce_namespace(s: &str) -> Result<String, ()> {
    if s.contains("::") {
        let split: Vec<&str> = s.split("::").collect();
        match split.last() {
            None => Err(()),
            Some(last) => {
                if *last == "" {
                    Err(())
                } else {
                    Ok((*last).to_string())
                }
            }
        }
    } else {
        Ok(s.to_string())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Syntax(_) => write!(
                f,
                "Enountered a syntax error while parsing a record event call-site",
            ),
            Error::MissingSemicolon(_) => {
                write!(f, "Record event call-site is missing a semicolon",)
            }
            Error::UnrecognizedTypeHint(_) => write!(
                f,
                "Record event with payload call-site has an unrecognized payload type hint",
            ),
            Error::EmptyTags(_) => write!(
                f,
                "Enountered an empty tags statement while parsing a record event call-site",
            ),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum InternalErrorKind<I> {
    Nom(I, nom::error::ErrorKind),
    Error(I, Error),
}

type ParserResult<I, O> = nom::IResult<I, O, InternalError<I>>;

impl<I> ParseError<I> for InternalError<I> {
    fn from_error_kind(input: I, kind: nom::error::ErrorKind) -> Self {
        Self {
            kind: InternalErrorKind::Nom(input, kind),
            backtrace: Vec::new(),
        }
    }

    fn append(input: I, kind: nom::error::ErrorKind, mut other: Self) -> Self {
        other.backtrace.push(InternalErrorKind::Nom(input, kind));
        other
    }
}

fn convert_error<I>(nom_err: nom::Err<InternalError<I>>, err: Error) -> nom::Err<InternalError<I>> {
    match nom_err {
        nom::Err::Failure(i) | nom::Err::Error(i) => {
            nom::Err::Failure((i.into_inner(), err).into())
        }
        nom::Err::Incomplete(i) => nom::Err::Incomplete(i),
    }
}

fn make_failure<I>(input: I, err: Error) -> nom::Err<InternalError<I>> {
    nom::Err::Failure((input, err).into())
}

fn make_error<I>(input: I, err: Error) -> nom::Err<InternalError<I>> {
    nom::Err::Error((input, err).into())
}

impl<I> From<(I, nom::error::ErrorKind)> for InternalErrorKind<I> {
    fn from(e: (I, nom::error::ErrorKind)) -> Self {
        InternalErrorKind::Nom(e.0, e.1)
    }
}

impl<I> From<(I, Error)> for InternalErrorKind<I> {
    fn from(e: (I, Error)) -> Self {
        InternalErrorKind::Error(e.0, e.1)
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct InternalError<I> {
    kind: InternalErrorKind<I>,
    backtrace: Vec<InternalErrorKind<I>>,
}

impl<I> InternalError<I> {
    fn into_inner(self) -> I {
        match self.kind {
            InternalErrorKind::Nom(i, _) => i,
            InternalErrorKind::Error(i, _) => i,
        }
    }
}

impl<I> From<(I, nom::error::ErrorKind)> for InternalError<I> {
    fn from(e: (I, nom::error::ErrorKind)) -> Self {
        Self {
            kind: (e.0, e.1).into(),
            backtrace: Vec::new(),
        }
    }
}

impl<I> From<(I, Error)> for InternalError<I> {
    fn from(e: (I, Error)) -> Self {
        Self {
            kind: (e.0, e.1).into(),
            backtrace: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    const MIXED_PROBE_ID_INPUT: &'static str = r#"
    /// Docs ModalityProbe::try_initialize_at(a, b, c)
    let probe = try_initialize_at!(&mut storage, PROBE_ID_A, RestartCounterProvider::NoRestartTracking)
        .expect("Could not initialize ModalityProbe");

    let probe_foo = try_initialize_at!(&mut storage_bytes, PROBE_ID_B, &mut my_tracker, "desc")?;

    // A comment
    let bar = modality_probe::initialize_at!(
        &mut storage_bytes, // docs
        my_ids::PROBE_ID_C, // docs
        RestartCounterProvider::NoRestartTracking)?; // docs

    let probe_foo = try_initialize_at!(&mut storage_bytes,
    my::nested::mod::PROBE_ID_D, &mut next_id, tags!("my tag", "more-tags"))?; // docs

    /* More comments
     * on more lines modality_probe::new_with_storage!(a, b, c)
     */
    let probe = modality_probe::new_with_storage!(storage, PROBE_ID_E, my_next_seq_id).unwrap();

    let bar = modality_probe::initialize_at!(
        &mut storage_bytes, /* comments */
        my_ids::PROBE_ID_F, // comments
        RestartCounterProvider::NoRestartTracking, // comments
        " desc ", /* Order of tags and docs doesn't matter */
        tags!("thing1", "thing2", "my::namespace", "tag with spaces"))?; //docs
"#;

    const MIXED_EVENT_RECORDING_INPUT: &'static str = r#"
    /* Comments */
    try_record!(probe, EVENT_A, "my text").expect("Could not record event");

    try_record!(
        probe, // docs
        EVENT_B, /* docs */
        "my text") /// docs
    .expect("Could not record event");

    /// More docs
    try_record!(probe, EVENT_C).expect("Could not record event");

    record!(
        probe, // docs
        EventId::try_from(EVENT_D).unwrap(), /* docs */
        "my text" //docs
    ); // docs

    record!(probe, EVENT_E.try_into()?);
    record!(probe, EVENT_EAGAIN1.try_into()?,
    );
    record!(probe, EventId::try_from(EVENT_EAGAIN2).unwrap(),
    );
    record!(probe, EVENT_F.try_into().unwrap(), tags!("my tag", "tag 2"));
    record!(probe, EventId::try_from(EVENT_G).expect("abc"), "docs");

    try_record_w_u32!(probe, EVENT_H, 1_u32)
        .expect("Could not record event");

    /*
     * docs
     * record!(probe, EventId::try_from(EVENT_NONE).unwrap());
     */
    try_record_w_f32!(probe, EVENT_I, 1.234_f32, "desc", tags!("tag 1")) // docs
        .expect("Could not record event");

    record_w_i8!(
        probe,
        EventId::try_from(EVENT_J).unwrap(),
        -2_i8,
        tags!("thing1", "thing2", "my::namespace", "tag with spaces"), //docs
        "desc" //docs
    );

    expect!(
        probe,
        EventId::try_from(EVENT_K).unwrap(),
        14 == (10 + 4),
        tags!("SEVERITY_1", "another tag"),
        "Some description",
    );

    try_expect!(probe, EVENT_K, foo != bar, tags!("EXPECTATION", "SEVERITY_2", "network")).unwrap();

    /* Special "EXPECTATION" tag is inserted" */
    modality_probe::expect!(probe, EVENT_K.try_into()?, foo != bar);

    try_record!(
        probe,
        TOP_OF_THE_LOOP,
        "At the top of the loop",
        tags!("example", "my-tag")
    )
    .expect("Could not record event");

    try_expect!(
        probe,
        MOD10_CONDITION_EVENT,
        loop_counter % 10 == 0,
        "Loop counter % 10 event",
        tags!("example")
    )
    .expect("Could not record event");
"#;

    #[test]
    fn probe_metadata_in_mixed_input() {
        let parser = RustParser::default();
        let tokens = parser.parse_probes(MIXED_PROBE_ID_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                ProbeMetadata {
                    name: "PROBE_ID_A".to_string(),
                    location: (72, 3, 17).into(),
                    tags: None,
                    description: None,
                },
                ProbeMetadata {
                    name: "PROBE_ID_B".to_string(),
                    location: (236, 6, 21).into(),
                    tags: None,
                    description: Some("desc".to_string()),
                },
                ProbeMetadata {
                    name: "PROBE_ID_C".to_string(),
                    location: (362, 9, 31).into(),
                    tags: None,
                    description: None,
                },
                ProbeMetadata {
                    name: "PROBE_ID_D".to_string(),
                    location: (532, 14, 21).into(),
                    tags: Some("my tag;more-tags".to_string()),
                    description: None,
                },
                ProbeMetadata {
                    name: "PROBE_ID_E".to_string(),
                    location: (784, 20, 33).into(),
                    tags: None,
                    description: None,
                },
                ProbeMetadata {
                    name: "PROBE_ID_F".to_string(),
                    location: (880, 22, 31).into(),
                    tags: Some("thing1;thing2;my::namespace;tag with spaces".to_string()),
                    description: Some("desc".to_string()),
                },
            ])
        );
    }

    #[test]
    fn event_metadata_in_mixed_input() {
        let parser = RustParser::default();
        let tokens = parser.parse_event_md(MIXED_EVENT_RECORDING_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (24, 3, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (102, 5, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (256, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (323, 14, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_E".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (456, 20, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN1".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (497, 21, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN2".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (550, 23, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_F".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: None,
                    tags: Some("my tag;tag 2".to_string()),
                    location: (619, 25, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_G".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("docs".to_string()),
                    tags: None,
                    location: (694, 26, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_H".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "1_u32").into()),
                    description: None,
                    tags: None,
                    location: (765, 28, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_I".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::F32, "1.234_f32").into()),
                    description: Some("desc".to_string()),
                    tags: Some("tag 1".to_string()),
                    location: (944, 35, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_J".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::I8, "-2_i8").into()),
                    description: Some("desc".to_string()),
                    tags: Some("thing1;thing2;my::namespace;tag with spaces".to_string()),
                    location: (1069, 38, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_K".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "14 == (10 + 4)").into()),
                    description: Some("Some description".to_string()),
                    tags: Some("EXPECTATION;SEVERITY_1;another tag".to_string()),
                    location: (1270, 46, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_K".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "foo != bar").into()),
                    description: None,
                    tags: Some("EXPECTATION;SEVERITY_2;network".to_string()),
                    location: (1447, 54, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_K".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "foo != bar").into()),
                    description: None,
                    tags: Some("EXPECTATION".to_string()),
                    location: (1614, 57, 21).into(),
                },
                EventMetadata {
                    name: "TOP_OF_THE_LOOP".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("At the top of the loop".to_string()),
                    tags: Some("example;my-tag".to_string()),
                    location: (1668, 59, 5).into(),
                },
                EventMetadata {
                    name: "MOD10_CONDITION_EVENT".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "loop_counter % 10 == 0").into()),
                    description: Some("Loop counter % 10 event".to_string()),
                    tags: Some("EXPECTATION;example".to_string()),
                    location: (1840, 67, 5).into(),
                },
            ])
        );
    }

    #[test]
    fn probe_id_namespace_error() {
        let parser = RustParser::default();
        let input =
            "modality_probe::try_initialize_at!(&mut storage_bytes,my::nested::mod::, next_id);";
        let tokens = parser.parse_probe_md(input);
        assert_eq!(tokens, Err(Error::Syntax((16, 1, 17).into())));
    }

    #[test]
    fn missing_semicolon_errors() {
        let parser = RustParser::default();
        let input = r#"
record!(probe, EVENT_F.try_into().unwrap())
let a = b;
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((1, 2, 1).into())));
        let input = r#"
record_w_i8!(
        probe,
        EventId::try_from(EVENT_J).unwrap(),
        -2_i8,
        "desc"
    )
let a = b;
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((1, 2, 1).into())));
    }

    #[test]
    fn event_syntax_errors() {
        let parser = RustParser::default();
        let input = r#"
record!(probe, abc, EVENT_F.try_into().unwrap());
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record!(probe, EVENT_F.try_into().unwrap(), abc, abc);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record_w_f32!(
            probe,
            EventId::try_from(EVENT_J).unwrap(),
            1.234_f32,
            "desc",
            abc
        );
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record_w_i32!(
            probe,
            EventId::try_from(EVENT_J).unwrap(),
        );
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record!(probe, EventId::try_from::<>EVENT_E);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
try_record!(

record!(probe, EventId::try_from(EVENT_D).unwrap(), "my text");
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
    }

    #[test]
    fn event_payload_type_hint_errors() {
        let parser = RustParser::default();
        let input = "record_w_i12!(t, EVENT, 1);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
        let input = "record_w_f64!(t, EVENT, 1, asdf);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
    }

    #[test]
    fn ignores_include_statements() {
        let parser = RustParser::default();
        let input = r#"
use crate::tracing_ids::*;
use modality_probe::{try_record, record, try_record_w_u32, record_w_i8, ModalityProbe, Probe};
use std::net::UdpSocket;
use std::{thread, time};

another_macro!(mything);
"#;
        let tokens = parser.parse_probe_md(input);
        assert_eq!(tokens, Ok(vec![]));
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Ok(vec![]));
    }

    #[test]
    fn events_with_namespace() {
        let parser = RustParser::default();
        let input = r#"
try_record!(probe, events::EVENT_A, "desc").unwrap();

record!(probe, EventId::try_from(events::more_events::EVENT_B).unwrap(), "my text");

try_record_w_u32!(probe, events::EVENT_C, 1_u32).expect("Could not record event");

record_w_i8!(probe, EventId::try_from(events::more::EVENT_D).unwrap(), 1_i8, "desc");
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Ok(vec![
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("desc".to_string()),
                    tags: None,
                    location: (1, 2, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (56, 4, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::U32, "1_u32").into()),
                    description: None,
                    tags: None,
                    location: (142, 6, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    probe_instance: "probe".to_string(),
                    payload: Some((TypeHint::I8, "1_i8").into()),
                    description: Some("desc".to_string()),
                    tags: None,
                    location: (226, 8, 1).into(),
                },
            ])
        );
    }

    #[test]
    fn empty_event_tags_errors() {
        let parser = RustParser::default();
        let input = r#"try_record!(probe, events::EVENT_A, "desc", "tags=").unwrap();"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((0, 1, 1).into())));
        let input = r#"
        record!(probe, EventId::try_from(events::more_events::EVENT_B).unwrap(), "tags=", "my text");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
        let input = r#"
        try_record_w_u32!(probe, events::EVENT_C, 1_u32, "tags=").expect("failed here");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
        let input = r#"
        record_w_i8!(probe, EventId::try_from(events::more::EVENT_D).unwrap(), 1_i8, "tags=", "desc");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
    }
}
