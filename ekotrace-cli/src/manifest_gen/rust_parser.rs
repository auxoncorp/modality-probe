use crate::manifest_gen::{
    event_metadata::EventMetadata,
    parser::{
        self, event_name_valid, remove_double_quotes, tags_or_desc_valid, tracer_name_valid,
        trimmed_string, trimmed_string_w_space, Parser, ParserConfig, Span,
    },
    source_location::SourceLocation,
    tracer_metadata::TracerMetadata,
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
            config: ParserConfig { prefix: "Ekotrace" },
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

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, parser::Error> {
        let md = self.parse_tracer_md(input)?;
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

    pub fn parse_tracer_md(&self, input: &str) -> Result<Vec<TracerMetadata>, Error> {
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
    let (input, found_try) = peek(opt(tag("try_record")))(input)?;
    let (input, metadata) = match found_try {
        None => {
            let (input, found_with_payload) = peek(opt(tag("record_w_")))(input)?;
            match found_with_payload {
                None => event_call_exp(input)?,
                Some(_) => event_with_payload_call_exp(input)?,
            }
        }
        Some(_) => {
            let (input, found_with_payload) = peek(opt(tag("try_record_w_")))(input)?;
            match found_with_payload {
                None => event_try_call_exp(input)?,
                Some(_) => event_try_with_payload_call_exp(input)?,
            }
        }
    };
    Ok((input, metadata))
}

fn event_try_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("try_record!")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (args, agent_instance) = variable_call_exp_arg(args)?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, name) = if expect_tags_or_desc {
        variable_call_exp_arg(args)?
    } else {
        rest_string(args)?
    };
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| tags_and_desc.push(s));
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
            agent_instance,
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
    let mut arg_vec: Vec<&str> = args
        .fragment()
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    match arg_vec.len() {
        2..=4 => (), // Tracer and event name required, maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    let arg0 = Span::new_extra(arg_vec.remove(0), input.extra);
    let (_, agent_instance) =
        rest_string(arg0).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg1 = Span::new_extra(arg_vec.remove(0), input.extra);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg1)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = arg_vec.iter().map(|s| (*s).to_string()).collect();
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
            agent_instance,
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
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (args, agent_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| arg_vec.push(s));
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
            agent_instance,
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
    let mut arg_vec: Vec<&str> = args
        .fragment()
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    match arg_vec.len() {
        3..=5 => (), // Tracer, event name and payload required, maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    let arg = Span::new_extra(arg_vec.remove(0), input.extra);
    let (_, agent_instance) =
        rest_string(arg).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg = Span::new_extra(arg_vec.remove(0), input.extra);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let name =
        reduce_namespace(&name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let arg = Span::new_extra(arg_vec.remove(0), input.extra);
    let (_, payload) =
        rest_literal(arg).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let mut tags_and_desc: Vec<String> = arg_vec.iter().map(|s| (*s).to_string()).collect();
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
            agent_instance,
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
    let expect_another = peek(variable_call_exp_arg_literal)(input).is_ok();
    let (input, arg) = if expect_another {
        variable_call_exp_arg_literal(input)?
    } else {
        rest_literal(input)?
    };
    Ok((input, arg))
}

fn variable_call_exp_arg_literal(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, arg) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    Ok((input, (*arg.fragment()).to_string()))
}

fn parse_init_call_exp(input: Span) -> ParserResult<Span, TracerMetadata> {
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
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, _storage) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, full_name) = if expect_tags_or_desc {
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    } else {
        rest_string(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    };
    let name =
        reduce_namespace(&full_name).map_err(|_| make_failure(input, Error::Syntax(pos.into())))?;
    if !tracer_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| tags_and_desc.push(s));
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
        TracerMetadata {
            name,
            location: pos.into(),
            tags,
            description,
        },
    ))
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

    const MIXED_TRACER_ID_INPUT: &'static str = r#"
    /// Docs Ekotrace::try_initialize_at(a, b, c)
    let tracer = try_initialize_at!(&mut storage, LOCATION_ID_A)
        .expect("Could not initialize Ekotrace");

    let ekotrace_foo = try_initialize_at!(&mut storage_bytes, LOCATION_ID_B, "desc")?;

    // A comment
    let bar = ekotrace::initialize_at!(
        &mut storage_bytes, // docs
        my_ids::LOCATION_ID_C)?; // docs

    let ekotrace_foo = try_initialize_at!(&mut storage_bytes,
    my::nested::mod::LOCATION_ID_D, "tags=my tag;more-tags")?; // docs

    /* More comments
     * on more lines ekotrace::new_with_storage!(a, b)
     */
    let tracer = ekotrace::new_with_storage!(storage, LOCATION_ID_E).unwrap();

    let bar = ekotrace::initialize_at!(
        &mut storage_bytes, /* comments */
        my_ids::LOCATION_ID_F, // comments
        " desc ", /* Order of tags and docs doesn't matter */
        "tags=thing1;thing2;my::namespace;tag with spaces")?; //docs

"#;

    const MIXED_EVENT_RECORDING_INPUT: &'static str = r#"
    /* Comments */
    try_record!(tracer, EVENT_A, "my text").expect("Could not record event");

    try_record!(
        tracer, // docs
        EVENT_B, /* docs */
        "my text") /// docs
    .expect("Could not record event");

    /// More docs
    try_record!(tracer, EVENT_C).expect("Could not record event");

    record!(
        tracer, // docs
        EventId::try_from(EVENT_D).unwrap(), /* docs */
        "my text" //docs
    ); // docs

    record!(tracer, EVENT_E.try_into()?);
    record!(tracer, EVENT_EAGAIN1.try_into()?,
    );
    record!(tracer, EventId::try_from(EVENT_EAGAIN2).unwrap(),
    );
    record!(tracer, EVENT_F.try_into().unwrap());
    record!(tracer, EventId::try_from(EVENT_G).expect("abc"), "docs");

    try_record_w_u32!(tracer, EVENT_H, 1_u32)
        .expect("Could not record event");

    /*
     * docs
     * record!(tracer, EventId::try_from(EVENT_NONE).unwrap());
     */
    try_record_w_f32!(tracer, EVENT_I, 1.234_f32, "desc") // docs
        .expect("Could not record event");

    record_w_i8!(
        tracer,
        EventId::try_from(EVENT_J).unwrap(),
        -2_i8,
        "tags=thing1;thing2;my::namespace;tag with spaces", //docs
        "desc" //docs
    );
"#;

    #[test]
    fn tracer_metadata_in_mixed_input() {
        let parser = RustParser::default();
        let tokens = parser.parse_tracers(MIXED_TRACER_ID_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                TracerMetadata {
                    name: "LOCATION_ID_A".to_string(),
                    location: (68, 3, 18).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_B".to_string(),
                    location: (190, 6, 24).into(),
                    tags: None,
                    description: Some("desc".to_string()),
                },
                TracerMetadata {
                    name: "LOCATION_ID_C".to_string(),
                    location: (296, 9, 25).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_D".to_string(),
                    location: (413, 13, 24).into(),
                    tags: Some("my tag;more-tags".to_string()),
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_E".to_string(),
                    location: (635, 19, 28).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_F".to_string(),
                    location: (712, 21, 25).into(),
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
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (24, 3, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (103, 5, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (258, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (326, 14, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_E".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (460, 20, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN1".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (502, 21, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN2".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (556, 23, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_F".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (626, 25, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_G".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("docs".to_string()),
                    tags: None,
                    location: (676, 26, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_H".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::U32, "1_u32").into()),
                    description: None,
                    tags: None,
                    location: (748, 28, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_I".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::F32, "1.234_f32").into()),
                    description: Some("desc".to_string()),
                    tags: None,
                    location: (929, 35, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_J".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::I8, "-2_i8").into()),
                    description: Some("desc".to_string()),
                    tags: Some("thing1;thing2;my::namespace;tag with spaces".to_string()),
                    location: (1039, 38, 5).into(),
                },
            ])
        );
    }

    #[test]
    fn tracer_id_namespace_error() {
        let parser = RustParser::default();
        let input = "ekotrace::try_initialize_at!(&mut storage_bytes,my::nested::mod::)";
        let tokens = parser.parse_tracer_md(input);
        assert_eq!(tokens, Err(Error::Syntax((10, 1, 11).into())));
    }

    #[test]
    fn missing_semicolon_errors() {
        let parser = RustParser::default();
        let input = r#"
record!(tracer, EVENT_F.try_into().unwrap())
let a = b;
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((1, 2, 1).into())));
        let input = r#"
record_w_i8!(
        tracer,
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
record!(tracer, abc, EVENT_F.try_into().unwrap());
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record!(tracer, EVENT_F.try_into().unwrap(), abc, abc);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record_w_f32!(
            tracer,
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
            tracer,
            EventId::try_from(EVENT_J).unwrap(),
        );
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
record!(tracer, EventId::try_from::<>EVENT_E);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
try_record!(

record!(tracer, EventId::try_from(EVENT_D).unwrap(), "my text");
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
use ekotrace::{try_record, record, try_record_w_u32, record_w_i8, Ekotrace, Tracer};
use std::net::UdpSocket;
use std::{thread, time};

another_macro!(mything);
"#;
        let tokens = parser.parse_tracer_md(input);
        assert_eq!(tokens, Ok(vec![]));
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Ok(vec![]));
    }

    #[test]
    fn events_with_namespace() {
        let parser = RustParser::default();
        let input = r#"
try_record!(tracer, events::EVENT_A, "desc").unwrap();

record!(tracer, EventId::try_from(events::more_events::EVENT_B).unwrap(), "my text");

try_record_w_u32!(tracer, events::EVENT_C, 1_u32).expect("Could not record event");

record_w_i8!(tracer, EventId::try_from(events::more::EVENT_D).unwrap(), 1_i8, "desc");
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Ok(vec![
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("desc".to_string()),
                    tags: None,
                    location: (1, 2, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    tags: None,
                    location: (57, 4, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::U32, "1_u32").into()),
                    description: None,
                    tags: None,
                    location: (144, 6, 1).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::I8, "1_i8").into()),
                    description: Some("desc".to_string()),
                    tags: None,
                    location: (229, 8, 1).into(),
                },
            ])
        );
    }

    #[test]
    fn empty_event_tags_errors() {
        let parser = RustParser::default();
        let input = r#"try_record!(tracer, events::EVENT_A, "desc", "tags=").unwrap();"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((0, 1, 1).into())));
        let input = r#"
        record!(tracer, EventId::try_from(events::more_events::EVENT_B).unwrap(), "tags=", "my text");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
        let input = r#"
        try_record_w_u32!(tracer, events::EVENT_C, 1_u32, "tags=").expect("failed here");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
        let input = r#"
        record_w_i8!(tracer, EventId::try_from(events::more::EVENT_D).unwrap(), 1_i8, "tags=", "desc");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((9, 2, 9).into())));
    }
}
