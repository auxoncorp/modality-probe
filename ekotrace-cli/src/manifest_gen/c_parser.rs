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
    sequence::delimited,
};
use nom_locate::position;
use std::fmt;
use std::str::FromStr;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct CParser<'a> {
    pub config: ParserConfig<'a>,
}

impl<'a> Default for CParser<'a> {
    fn default() -> Self {
        CParser {
            config: ParserConfig { prefix: "EKOTRACE" },
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    Syntax(SourceLocation),
    MissingSemicolon(SourceLocation),
    UnrecognizedTypeHint(SourceLocation),
    TypeHintNameNotUpperCase(SourceLocation),
    PayloadArgumentSpansManyLines(SourceLocation),
    EmptyTags(SourceLocation),
}

impl Error {
    pub fn location(&self) -> &SourceLocation {
        match self {
            Error::Syntax(l) => l,
            Error::MissingSemicolon(l) => l,
            Error::UnrecognizedTypeHint(l) => l,
            Error::TypeHintNameNotUpperCase(l) => l,
            Error::PayloadArgumentSpansManyLines(l) => l,
            Error::EmptyTags(l) => l,
        }
    }
}

impl<'a> Parser for CParser<'a> {
    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, parser::Error> {
        let md = self.parse_event_md(input)?;
        Ok(md)
    }

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, parser::Error> {
        let md = self.parse_tracer_md(input)?;
        Ok(md)
    }
}

impl<'a> CParser<'a> {
    pub fn new(config: ParserConfig<'a>) -> Self {
        CParser { config }
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
    let prefix = input.extra.as_ref().unwrap().prefix;
    let (input, _) = comments_and_spacing(input)?;
    let tag_string = format!("{}_EXPECT", prefix);
    let (input, found_expect) = peek(opt(tag(tag_string.as_str())))(input)?;
    if found_expect.is_some() {
        let (input, metadata) = expect_call_exp(input)?;
        Ok((input, metadata))
    } else {
        let tag_string = format!("{}_RECORD_W_", prefix);
        let (input, found_with_payload) = peek(opt(tag(tag_string.as_str())))(input)?;
        let (input, metadata) = match found_with_payload {
            None => event_call_exp(input)?,
            Some(_) => event_with_payload_call_exp(input)?,
        };
        Ok((input, metadata))
    }
}

fn expect_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let prefix = input.extra.as_ref().unwrap().prefix;
    let tag_string = format!("{}_EXPECT", prefix);
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = tag(tag_string.as_str())(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, agent_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    if !event_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut arg_vec: Vec<String> = Vec::new();
    let mut iter = iterator(args, multi_variable_call_exp_arg_literal);
    iter.for_each(|s| arg_vec.push(s));
    let (_args, _) = iter.finish()?;
    match arg_vec.len() {
        1..=3 => (), // At least an expression, maybe tags and description
        _ => return Err(make_failure(input, Error::Syntax(pos.into()))),
    }
    let expr = arg_vec.remove(0).trim().to_string();
    let mut tags_and_desc = arg_vec;
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
        if !t.contains("expectation") {
            t.insert_str(0, "expectation;");
        }
    } else {
        tags = Some(String::from("expectation"));
    }
    let description = tags_and_desc.pop();
    Ok((
        input,
        EventMetadata {
            name,
            agent_instance,
            payload: Some((TypeHint::U32, expr).into()),
            description,
            tags,
            location: pos.into(),
        },
    ))
}

fn event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let prefix = input.extra.as_ref().unwrap().prefix;
    let tag_string = format!("{}_RECORD", prefix);
    let (input, pos) = position(input)?;
    let (input, _) = tag(tag_string.as_str())(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, agent_instance) = variable_call_exp_arg(args)?;
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, name) = if expect_tags_or_desc {
        variable_call_exp_arg(args)?
    } else {
        rest_string(args)?
    };
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

fn event_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let prefix = input.extra.as_ref().unwrap().prefix;
    let tag_string = format!("{}_RECORD_W_", prefix);
    let (input, pos) = position(input)?;
    let (input, _) = tag(tag_string.as_str())(input)?;
    let (input, type_hint) = take_until("(")(input)?;
    if &type_hint.fragment().to_uppercase().as_str() != type_hint.fragment() {
        return Err(make_failure(
            input,
            Error::TypeHintNameNotUpperCase(pos.into()),
        ));
    }
    let type_hint = TypeHint::from_str(type_hint.fragment())
        .map_err(|_| make_failure(input, Error::UnrecognizedTypeHint(pos.into())))?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, agent_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
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
    // We have a constraint that the payload argument doesn't span
    // multiple lines, trim off leading and trailing space
    let payload = arg_vec.remove(0).trim().to_string();
    for c in payload.chars() {
        if c == '\n' {
            return Err(make_failure(
                input,
                Error::PayloadArgumentSpansManyLines(pos.into()),
            ));
        }
    }
    // Check for equal open/close parentheses
    let open = payload.chars().filter(|&c| c == '(').count();
    let close = payload.chars().filter(|&c| c == ')').count();
    if open != close {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let mut tags_and_desc = arg_vec;
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
    let prefix = input.extra.as_ref().unwrap().prefix;
    let tag_string = format!("{}_INITIALIZE", prefix);
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = tag(tag_string.as_str())(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, _storage) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, _storage_size) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let (args, name) =
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    if !tracer_name_valid(&name) {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let expect_tags_or_desc = peek(variable_call_exp_arg)(args).is_ok();
    let (args, _agent_instance) = if expect_tags_or_desc {
        variable_call_exp_arg(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    } else {
        rest_string(args).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?
    };
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

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::MissingSemicolon(_) => write!(
                f,
                "Record event call-site is missing a semicolon",
            ),
            Error::UnrecognizedTypeHint(_) => write!(
                f,
                "Record event with payload call-site has an unrecognized payload type hint",
            ),
            Error::TypeHintNameNotUpperCase(_) => write!(
                f,
                "Record event with payload call-site has a payload type hint that needs to be upper case",
            ),
            Error::PayloadArgumentSpansManyLines(_) => write!(
                f,
                "Record event with payload call-site has a payload argument that spans many lines",
            ),
            Error::Syntax(_) => write!(
                f,
                "Enountered a syntax error while parsing a record event call-site",
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
    /* C/C++ style */
    ekotrace_result result = EKOTRACE_INITIALIZE(
        destination,
        DEFAULT_TRACER_SIZE,
        DEFAULT_TRACER_ID,
        &t);

    // One line
    EKOTRACE_INITIALIZE(dest,TRACER_SIZE,MY_TRACER_ID,&t);

    const size_t err = EKOTRACE_INITIALIZE(     dest,  TRACER_SIZE,
    LOCATION_ID_FOO,      &t);

    const size_t err =
        EKOTRACE_INITIALIZE(
        // stuff
        dest, // more stuff
        TRACER_SIZE, /* comment */
    LOCATION_ID_BAR,   /* things */   &t);

    EKOTRACE_INITIALIZE(
        dest, /* more docs */ TRACER_SIZE , /* docs */ MY_OTHER_TRACER_ID, /* docs */ &t, "desc");

    /* things in comments
     * are
     * ignored
     *
     * EKOTRACE_INITIALIZE(dest,TRACER_SIZE,ANOTHER_ID,&t);
     *
     */
    size_t err = EKOTRACE_INITIALIZE(
            &g_agent_storage[0],
            STORAGE_SIZE,
            LOCATION_ID_FOO,
            &g_agent,
            "tags=my-tags;more tags",
            "Description");
    assert(err == EKOTRACE_RESULT_OK);

    EKOTRACE_INITIALIZE(storage, size, ID_BAR, t, "tags=my tag");
"#;

    const MIXED_EVENT_RECORDING_INPUT: &'static str = r#"
    /* The user writes this line: */
    const size_t err = EKOTRACE_RECORD(g_ekotrace, EVENT_READ1);

    assert(err == EKOTRACE_RESULT_OK);

    /* The tooling replaces it with this (assumes it picked ID 1): */
    const size_t err = EKOTRACE_RECORD(g_ekotrace, EVENT_READ2, "my docs");

    assert(err == EKOTRACE_RESULT_OK);

    EKOTRACE_RECORD(
            ekt, /* comments */
            EVENT_WRITE1,
            "tags=network"); // more comments

    EKOTRACE_RECORD(  ekt, /* comments */ EVENT_WRITE2, "tags=network;file-system", "docs"); // more comments

    uint8_t status;
    const size_t err = EKOTRACE_RECORD_W_U8(ekt, EVENT_A, status);

    const size_t err = EKOTRACE_RECORD_W_U8(
        ekt, // stuff
        EVENT_B, /* here */
        status,
        "desc text here"); // The end

    /* stuff
     * EKOTRACE_RECORD_W_U8(ekt, SOME_EVENT, status);
     */
    const size_t err = EKOTRACE_RECORD_W_I16(ekt, EVENT_C, (int16_t) data);

    const size_t err = EKOTRACE_RECORD_W_I16(ekt, EVENT_D, (int16_t) data, "docs");

    const size_t err = EKOTRACE_RECORD_W_I8(ekt, EVENT_E,
    (int8_t) *((uint8_t*) &mydata));

    const size_t err = EKOTRACE_RECORD_W_U16(
        ekt,
        EVENT_F,
    (uint16_t) *((uint16_t*) &mydata),
    "tags=my tag"
    );

    const size_t err = EKOTRACE_RECORD_W_U16(
        ekt,
        EVENT_G,
    (uint16_t) *((uint16_t*) &mydata),
    " docs ", /* Order of tags and docs doesn't matter */
    "tags=thing1;thing2;my::namespace;tag with spaces" //docs
    );

    err = EKOTRACE_EXPECT(
            tracer,
            EVENT_H,
            1 == 0, /* Arbitrary expression, evaluates to 0 (failure) or 1 (success) */
            "tags=severity.1;another tag",
            "Some description");
    assert(err == EKOTRACE_RESULT_OK);

    EKOTRACE_EXPECT(ekt, EVENT_I, *foo != (1 + bar), "tags=expectation;severity.2;network");

    /* Special "expectation" tag is inserted"
    EKOTRACE_EXPECT(ekt, EVENT_J, 0 == 0);
"#;

    #[test]
    fn tracer_metadata_in_mixed_input() {
        let parser = CParser::default();
        let tokens = parser.parse_tracers(MIXED_TRACER_ID_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                TracerMetadata {
                    name: "DEFAULT_TRACER_ID".to_string(),
                    location: (52, 3, 30).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "MY_TRACER_ID".to_string(),
                    location: (184, 10, 5).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_FOO".to_string(),
                    location: (263, 12, 24).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "LOCATION_ID_BAR".to_string(),
                    location: (371, 16, 9).into(),
                    tags: None,
                    description: None,
                },
                TracerMetadata {
                    name: "MY_OTHER_TRACER_ID".to_string(),
                    location: (520, 22, 5).into(),
                    tags: None,
                    description: Some("desc".to_string()),
                },
                TracerMetadata {
                    name: "LOCATION_ID_FOO".to_string(),
                    location: (792, 32, 18).into(),
                    tags: Some("my-tags;more tags".to_string()),
                    description: Some("Description".to_string()),
                },
                TracerMetadata {
                    name: "ID_BAR".to_string(),
                    location: (1033, 41, 5).into(),
                    tags: Some("my tag".to_string()),
                    description: None,
                },
            ])
        );
    }

    #[test]
    fn event_metadata_in_mixed_input() {
        let parser = CParser::default();
        let tokens = parser.parse_event_md(MIXED_EVENT_RECORDING_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                EventMetadata {
                    name: "EVENT_READ1".to_string(),
                    agent_instance: "g_ekotrace".to_string(),
                    payload: None,
                    description: None,
                    tags: None,
                    location: (61, 3, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_READ2".to_string(),
                    agent_instance: "g_ekotrace".to_string(),
                    payload: None,
                    description: Some("my docs".to_string()),
                    tags: None,
                    location: (237, 8, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE1".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: None,
                    description: None,
                    tags: Some("network".to_string()),
                    location: (335, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE2".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: None,
                    description: Some("docs".to_string()),
                    tags: Some("network;file-system".to_string()),
                    location: (461, 17, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    description: None,
                    tags: None,
                    location: (611, 20, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    description: Some("desc text here".to_string()),
                    tags: None,
                    location: (679, 22, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    description: None,
                    tags: None,
                    location: (904, 31, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    description: Some("docs".to_string()),
                    tags: None,
                    location: (981, 33, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_E".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I8, "(int8_t) *((uint8_t*) &mydata)").into()),
                    description: None,
                    tags: None,
                    location: (1066, 35, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_F".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U16, "(uint16_t) *((uint16_t*) &mydata)").into()),
                    description: None,
                    tags: Some("my tag".to_string()),
                    location: (1162, 38, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_G".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U16, "(uint16_t) *((uint16_t*) &mydata)").into()),
                    description: Some("docs".to_string()),
                    tags: Some("thing1;thing2;my::namespace;tag with spaces".to_string()),
                    location: (1303, 45, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_H".to_string(),
                    agent_instance: "tracer".to_string(),
                    payload: Some((TypeHint::U32, "1 == 0").into()),
                    description: Some("Some description".to_string()),
                    tags: Some("expectation;severity.1;another tag".to_string()),
                    location: (1533, 53, 11).into(),
                },
                EventMetadata {
                    name: "EVENT_I".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U32, "*foo != (1 + bar)").into()),
                    description: None,
                    tags: Some("expectation;severity.2;network".to_string()),
                    location: (1799, 61, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_J".to_string(),
                    agent_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U32, "0 == 0").into()),
                    description: None,
                    tags: Some("expectation".to_string()),
                    location: (1939, 64, 5).into(),
                },
            ])
        );
    }

    #[test]
    fn missing_semicolon_errors() {
        let parser = CParser::default();
        let input = r#"
const size_t err = EKOTRACE_RECORD(g_ekotrace, EVENT_READ)
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((20, 2, 20).into())));
        let input = "const size_t err = EKOTRACE_RECORD(g_ekotrace, EVENT_READ)";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((19, 1, 20).into())));
        let input = "EKOTRACE_RECORD_W_I16(ekt, E0, data)";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((0, 1, 1).into())));
        let input = "EKOTRACE_INITIALIZE(storage, size, ID_BAR, t)";
        let tokens = parser.parse_tracer_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((0, 1, 1).into())));
    }

    #[test]
    fn syntax_errors() {
        let parser = CParser::default();
        let input = r#"
const size_t err = EKOTRACE_RECORD_W_U8(g_ekotrace, EVENT_READ, (uint8_t) (( ))))status);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((20, 2, 20).into())));
        let input = r#"
const size_t err = EKOTRACE_RECORD_W_U8(g_ekotrace, EVENT_READ, (uint8_t) status)
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Err(Error::PayloadArgumentSpansManyLines((20, 2, 20).into()))
        );
        let input = r#"
err = EKOTRACE_RECORD_W_U8(
        g_ekotrace,
        EVENT_READ_STATUS2,
        (uint8_t) status,
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((7, 2, 7).into())));
        let input = r#"
err = EKOTRACE_RECORD(
        g_ekotrace,
        EVENT_READ_STATUS2,
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((7, 2, 7).into())));
    }

    #[test]
    fn event_payload_type_hint_errors() {
        let parser = CParser::default();
        let input = "EKOTRACE_RECORD_W_I12(ekt, E0, data);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
    }

    #[test]
    fn event_payload_casing_errors() {
        let parser = CParser::default();
        let input = "EKOTRACE_RECORD_W_i8(ekt, EVENT_A, status);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Err(Error::TypeHintNameNotUpperCase((0, 1, 1).into()))
        );
    }

    #[test]
    fn empty_event_tags_errors() {
        let parser = CParser::default();
        let input = r#"EKOTRACE_RECORD(ekt, EVENT_A, "tags=", "desc");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((0, 1, 1).into())));
        let input = r#"EKOTRACE_RECORD(ekt, EVENT_A, "tags=");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((0, 1, 1).into())));
        let input = r#"EKOTRACE_RECORD_W_U32(ekt, EVENT_A, 123, "desc", "tags=");"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::EmptyTags((0, 1, 1).into())));
    }
}
