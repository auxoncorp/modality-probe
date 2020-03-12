use crate::manifest_gen::{
    event_metadata::EventMetadata,
    parser::{self, Parser, Span},
    source_location::SourceLocation,
    tracer_metadata::TracerMetadata,
    type_hint::TypeHint,
};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take, take_till1, take_until},
    character::complete::{char, line_ending, multispace0},
    combinator::{map, opt, peek, rest},
    error::ParseError,
    sequence::delimited,
};
use nom_locate::position;
use std::fmt;
use std::str::FromStr;

#[derive(Default)]
pub struct CParser {}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    Syntax(SourceLocation),
    MissingSemicolon(SourceLocation),
    UnrecognizedTypeHint(SourceLocation),
    TypeHintNameNotUpperCase(SourceLocation),
    PayloadArgumentSpansManyLines(SourceLocation),
}

impl Error {
    pub fn location(&self) -> &SourceLocation {
        match self {
            Error::Syntax(l) => l,
            Error::MissingSemicolon(l) => l,
            Error::UnrecognizedTypeHint(l) => l,
            Error::TypeHintNameNotUpperCase(l) => l,
            Error::PayloadArgumentSpansManyLines(l) => l,
        }
    }
}

impl Parser for CParser {
    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, parser::Error> {
        let md = self.parse_event_md(input)?;
        Ok(md)
    }

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, parser::Error> {
        let md = self.parse_tracer_md(input)?;
        Ok(md)
    }
}

impl CParser {
    fn parse_event_md(&self, input: &str) -> Result<Vec<EventMetadata>, Error> {
        let mut md = vec![];
        let mut input = Span::new(input);
        while !input.fragment().is_empty() {
            match parse_record_event_call_exp(input) {
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

    fn parse_tracer_md(&self, input: &str) -> Result<Vec<TracerMetadata>, Error> {
        let mut md = vec![];
        let mut input = Span::new(input);
        while !input.fragment().is_empty() {
            match parse_init_call_exp(input) {
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
}

fn parse_record_event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, found_with_payload) = peek(opt(tag("EKT_RECORD_W_")))(input)?;
    let (input, metadata) = match found_with_payload {
        None => event_call_exp(input)?,
        Some(_) => event_with_payload_call_exp(input)?,
    };
    Ok((input, metadata))
}

fn event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("EKT_RECORD")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (input, _) =
        tag(";")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;
    let mut expect_arg3 = false;
    let (args, name) = match peek(variable_call_exp_arg)(args) {
        Ok(_) => {
            expect_arg3 = true;
            variable_call_exp_arg(args)?
        }
        Err(_) => rest_string(args)?,
    };
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    let (_args, description) = if expect_arg3 {
        let (args, desc) = map(rest_literal, |id: String| {
            Some(id.replace("\n", "").replace("\t", "").trim().to_string())
        })(args)?;
        if let Some(d) = &desc {
            if d.chars().filter(|&c| c == '"').count() != 2 {
                return Err(make_failure(input, Error::Syntax(pos.into())));
            }
        }
        let desc = desc.map(|d| d.replace("\"", "").trim().to_string());
        (args, desc)
    } else {
        (args, None)
    };
    Ok((
        input,
        EventMetadata {
            name,
            ekotrace_instance,
            payload: None,
            description,
            location: pos.into(),
        },
    ))
}

fn event_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("EKT_RECORD_W_")(input)?;
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
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }

    // Payload token stored in literal form
    let mut expect_arg4 = false;
    let (args, payload) = match peek(variable_call_exp_arg_literal)(args) {
        Ok(_) => {
            expect_arg4 = true;
            variable_call_exp_arg_literal(args)?
        }
        Err(_) => rest_literal(args)?,
    };

    // We have a constraint that the payload argument doesn't span
    // multiple lines, trim off leading and trailing space
    let payload = payload.trim().to_string();
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

    let (_args, description) = if expect_arg4 {
        let (args, desc) = map(rest_literal, |id: String| {
            Some(id.replace("\n", "").replace("\t", "").trim().to_string())
        })(args)?;
        if let Some(d) = &desc {
            if d.chars().filter(|&c| c == '"').count() != 2 {
                return Err(make_failure(input, Error::Syntax(pos.into())));
            }
        }
        let desc = desc.map(|d| d.replace("\"", "").trim().to_string());
        (args, desc)
    } else {
        (args, None)
    };
    Ok((
        input,
        EventMetadata {
            name,
            ekotrace_instance,
            payload: Some((type_hint, payload).into()),
            description,
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

fn variable_call_exp_arg_literal(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, arg) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    Ok((input, (*arg.fragment()).to_string()))
}

fn parse_init_call_exp(input: Span) -> ParserResult<Span, TracerMetadata> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = tag("ekotrace_initialize")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (_args, name) = init_call_exp_tracer_arg(args)?;
    Ok((
        input,
        TracerMetadata {
            name,
            location: pos.into(),
        },
    ))
}

fn init_call_exp_tracer_arg(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, _arg0) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    let (input, _) = comments_and_spacing(input)?;
    let (input, _arg1) = take_until(",")(input)?;
    let (input, _) = tag(",")(input)?;
    let (input, _) = comments_and_spacing(input)?;
    let (input, name) = take_until(",")(input)?;
    Ok((input, trimmed_string(name.fragment())))
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

fn trimmed_string(s: &str) -> String {
    s.trim()
        .to_string()
        .replace("\n", "")
        .replace("\t", "")
        .replace(" ", "")
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::MissingSemicolon(_) => write!(
                f,
                "Ekotrace record event call-site is missing a semicolon",
            ),
            Error::UnrecognizedTypeHint(_) => write!(
                f,
                "Ekotrace record event with payload call-site has an unrecognized payload type hint",
            ),
            Error::TypeHintNameNotUpperCase(_) => write!(
                f,
                "Ekotrace record event with payload call-site has a payload type hint that needs to be upper case",
            ),
            Error::PayloadArgumentSpansManyLines(_) => write!(
                f,
                "Ekotrace record event with payload call-site has a payload argument that spans many lines",
            ),
            Error::Syntax(_) => write!(
                f,
                "Enountered a syntax error while parsing an Ekotrace record event call-site",
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
    ekotrace_result result = ekotrace_initialize(
        destination,
        DEFAULT_TRACER_SIZE,
        DEFAULT_TRACER_ID,
        &t);

    // One line
    ekotrace_initialize(dest,TRACER_SIZE,MY_TRACER_ID,&t);

    const size_t err = ekotrace_initialize(     dest,  TRACER_SIZE,
    LOCATION_ID_FOO,      &t);

    const size_t err =
        ekotrace_initialize(
        // stuff
        dest, // more stuff
        TRACER_SIZE, /* comment */
    LOCATION_ID_BAR,   /* things */   &t);

    ekotrace_initialize(
        dest, /* more docs */ TRACER_SIZE , /* docs */ MY_OTHER_TRACER_ID, /* docs */ &t);

    /* things in comments
     * are
     * ignored
     *
     * ekotrace_initialize(dest,TRACER_SIZE,ANOTHER_ID,&t);
     *
     */
"#;

    const MIXED_EVENT_RECORDING_INPUT: &'static str = r#"
    /* The user writes this line: */
    const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ1);

    assert(err == EKOTRACE_RESULT_OK);

    /* The tooling replaces it with this (assumes it picked ID 1): */
    const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ2, "my docs");

    assert(err == EKOTRACE_RESULT_OK);

    EKT_RECORD(
            ekt, /* comments */
            EVENT_WRITE1); // more comments

    EKT_RECORD(  ekt, /* comments */ EVENT_WRITE2, "docs"); // more comments

    uint8_t status;
    const size_t err = EKT_RECORD_W_U8(ekt, EVENT_A, status);

    const size_t err = EKT_RECORD_W_U8(
        ekt, // stuff
        EVENT_B, /* here */
        status,
        "desc text here"); // The end

    /* stuff
     * EKT_RECORD_W_U8(ekt, SOME_EVENT, status);
     */
    const size_t err = EKT_RECORD_W_I16(ekt, EVENT_C, (int16_t) data);

    const size_t err = EKT_RECORD_W_I16(ekt, EVENT_D, (int16_t) data, "docs");

    const size_t err = EKT_RECORD_W_I8(ekt, EVENT_E,
    (int8_t) *((uint8_t*) &mydata));

    const size_t err = EKT_RECORD_W_U16(
        ekt,
        EVENT_F,
    (uint16_t) *((uint16_t*) &mydata)
    );

    const size_t err = EKT_RECORD_W_U16(
        ekt,
        EVENT_G,
    (uint16_t) *((uint16_t*) &mydata),
    " docs "
    );
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
                },
                TracerMetadata {
                    name: "MY_TRACER_ID".to_string(),
                    location: (184, 10, 5).into(),
                },
                TracerMetadata {
                    name: "LOCATION_ID_FOO".to_string(),
                    location: (263, 12, 24).into(),
                },
                TracerMetadata {
                    name: "LOCATION_ID_BAR".to_string(),
                    location: (371, 16, 9).into(),
                },
                TracerMetadata {
                    name: "MY_OTHER_TRACER_ID".to_string(),
                    location: (520, 22, 5).into(),
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
                    ekotrace_instance: "g_ekotrace".to_string(),
                    payload: None,
                    description: None,
                    location: (61, 3, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_READ2".to_string(),
                    ekotrace_instance: "g_ekotrace".to_string(),
                    payload: None,
                    description: Some("my docs".to_string()),
                    location: (232, 8, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE1".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: None,
                    description: None,
                    location: (325, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE2".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: None,
                    description: Some("docs".to_string()),
                    location: (418, 16, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    description: None,
                    location: (535, 19, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    description: Some("desc text here".to_string()),
                    location: (598, 21, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    description: None,
                    location: (813, 30, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    description: Some("docs".to_string()),
                    location: (885, 32, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_E".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I8, "(int8_t) *((uint8_t*) &mydata)").into()),
                    description: None,
                    location: (965, 34, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_F".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U16, "(uint16_t) *((uint16_t*) &mydata)").into()),
                    description: None,
                    location: (1056, 37, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_G".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U16, "(uint16_t) *((uint16_t*) &mydata)").into()),
                    description: Some("docs".to_string()),
                    location: (1173, 43, 24).into(),
                },
            ])
        );
    }

    #[test]
    fn missing_semicolon_errors() {
        let parser = CParser::default();
        let input = r#"
const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ)
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((20, 2, 20).into())));
        let input = "const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ)";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((19, 1, 20).into())));
        let input = "EKT_RECORD_W_I16(ekt, E0, data)";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((0, 1, 1).into())));
    }

    #[test]
    fn syntax_errors() {
        let parser = CParser::default();
        let input = r#"
const size_t err = EKT_RECORD_W_U8(g_ekotrace, EVENT_READ, (uint8_t) (( ))))status);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((20, 2, 20).into())));
        let input = r#"
const size_t err = EKT_RECORD_W_U8(g_ekotrace, EVENT_READ, (uint8_t) status)
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Err(Error::PayloadArgumentSpansManyLines((20, 2, 20).into()))
        );
        let input = r#"
err = EKT_RECORD_W_U8(
        g_ekotrace,
        EVENT_READ_STATUS2,
        (uint8_t) status,
assert(err == EKOTRACE_RESULT_OK);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((7, 2, 7).into())));
        let input = r#"
err = EKT_RECORD(
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
        let input = "EKT_RECORD_W_I12(ekt, E0, data);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
    }

    #[test]
    fn event_payload_casing_errors() {
        let parser = CParser::default();
        let input = "EKT_RECORD_W_i8(ekt, EVENT_A, status);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(
            tokens,
            Err(Error::TypeHintNameNotUpperCase((0, 1, 1).into()))
        );
    }
}
