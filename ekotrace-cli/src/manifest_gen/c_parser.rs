use crate::manifest_gen::event_metadata::EventMetadata;
use crate::manifest_gen::parser::Parser;
use crate::manifest_gen::source_location::SourceLocation;
use crate::manifest_gen::tracer_metadata::TracerMetadata;
use crate::manifest_gen::type_hint::TypeHint;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take, take_till1, take_until},
    character::complete::{char, line_ending, multispace0},
    combinator::{map, opt, peek, rest},
    error::ParseError,
    sequence::delimited,
};
use nom_locate::{position, LocatedSpan};
use std::fmt;
use std::str::FromStr;

#[derive(Default)]
pub struct CParser {}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    MissingSemicolon(SourceLocation),
    UnrecognizedTypeHint(SourceLocation),
    AssignedEventIdParseIntError(SourceLocation),
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

fn make_error<I>(input: I, err: Error) -> nom::Err<InternalError<I>> {
    nom::Err::Failure((input, err).into())
}

type Span<'a> = LocatedSpan<&'a str>;

impl<'a> From<Span<'a>> for SourceLocation {
    fn from(span: Span<'a>) -> SourceLocation {
        SourceLocation {
            offset: span.location_offset(),
            line: span.location_line() as usize,
            column: span.get_column(),
        }
    }
}

impl Parser for CParser {
    type Error = Error;

    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, Error> {
        let mut tracers = vec![];
        let mut input = Span::new(input);
        while input.fragment().len() != 0 {
            match parse_record_event_call_exp(input) {
                Ok((rem, metadata)) => {
                    tracers.push(metadata);
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
        Ok(tracers)
    }

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, Error> {
        let mut tracers = vec![];
        let mut input = Span::new(input);
        while input.fragment().len() != 0 {
            match parse_init_call_exp(input) {
                Ok((rem, metadata)) => {
                    tracers.push(metadata);
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
        Ok(tracers)
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
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) = tag(");")(input)?;
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;

    let mut expect_arg3 = false;
    let (args, name) = match peek(variable_call_exp_arg)(args) {
        Ok(_) => {
            expect_arg3 = true;
            variable_call_exp_arg(args)?
        }
        Err(_) => rest_string(args)?,
    };

    let (_args, assigned_id_str) = match expect_arg3 {
        false => (args, None),
        true => map(rest_string, |id: String| Some(id))(args)?,
    };

    let assigned_id = match assigned_id_str {
        None => None,
        Some(id) => Some(
            id.parse::<u32>()
                .map_err(|_| make_error(input, Error::AssignedEventIdParseIntError(pos.into())))?,
        ),
    };

    Ok((
        input,
        EventMetadata {
            name,
            ekotrace_instance,
            payload: None,
            assigned_id,
            location: pos.into(),
        },
    ))
}

fn event_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("EKT_RECORD_W_")(input)?;
    let (input, type_hint) = take_until("(")(input)?;
    let type_hint = TypeHint::from_str(type_hint.fragment())
        .map_err(|_| make_error(input, Error::UnrecognizedTypeHint(pos.into())))?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) = tag(");")(input)?;
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;

    // Payload token stored in literal form
    let mut expect_arg4 = false;
    let (args, payload) = match peek(variable_call_exp_arg_literal)(args) {
        Ok(_) => {
            expect_arg4 = true;
            variable_call_exp_arg_literal(args)?
        }
        Err(_) => rest_literal(args)?,
    };

    let (_args, assigned_id_str) = match expect_arg4 {
        false => (args, None),
        true => map(rest_string, |id: String| Some(id))(args)?,
    };

    let assigned_id = match assigned_id_str {
        None => None,
        Some(id) => Some(
            id.parse::<u32>()
                .map_err(|_| make_error(input, Error::AssignedEventIdParseIntError(pos.into())))?,
        ),
    };

    Ok((
        input,
        EventMetadata {
            name,
            ekotrace_instance,
            payload: Some((type_hint, payload).into()),
            assigned_id,
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
    Ok((input, arg.fragment().to_string()))
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
    Ok((input, rst.fragment().to_string()))
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
        match *self {
            Error::MissingSemicolon(loc) => write!(
                f,
                "An Ekotrace record event invocation is missing a semicolon, expected near\n{}",
                loc
            ),
            Error::UnrecognizedTypeHint(loc) => write!(
                f,
                "An Ekotrace record event with payload invocation has an unrecognized payload type hint near\n{}",
                loc
            ),
            Error::AssignedEventIdParseIntError(loc) => write!(
                f,
                "Can't parse an Ekotrace record event invocation assigned identifier as u32 near \n{}",
                loc
            ),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum InternalErrorKind<I> {
    Nom(I, nom::error::ErrorKind),
    Error(I, Error),
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
    const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ);

    assert(err == EKOTRACE_RESULT_OK);

    /* The tooling replaces it with this (assumes it picked ID 1): */
    const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ, 1);

    assert(err == EKOTRACE_RESULT_OK);

    EKT_RECORD(
            ekt, /* comments */
            EVENT_WRITE); // more comments

    EKT_RECORD(  ekt, /* comments */ EVENT_WRITE, 2); // more comments

    uint8_t status;
    const size_t err = EKT_RECORD_W_U8(ekt, EVENT_A, status);

    const size_t err = EKT_RECORD_W_U8(
        ekt, // stuff
        EVENT_A, /* here */
        status,
        3); // The end

    const size_t err = EKT_RECORD_W_I16(ekt, EVENT_B, (int16_t) data);

    const size_t err = EKT_RECORD_W_I16(ekt, EVENT_B, (int16_t) data, 4);

    const size_t err = EKT_RECORD_W_i8(ekt, EVENT_C,
    (int8_t) *((uint8_t*) &mydata));
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
        let tokens = parser.parse_events(MIXED_EVENT_RECORDING_INPUT);
        assert_eq!(
            tokens,
            Ok(vec![
                EventMetadata {
                    name: "EVENT_READ".to_string(),
                    ekotrace_instance: "g_ekotrace".to_string(),
                    payload: None,
                    assigned_id: None,
                    location: (61, 3, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_READ".to_string(),
                    ekotrace_instance: "g_ekotrace".to_string(),
                    payload: None,
                    assigned_id: Some(1),
                    location: (231, 8, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: None,
                    assigned_id: None,
                    location: (315, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_WRITE".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: None,
                    assigned_id: Some(2),
                    location: (407, 16, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    assigned_id: None,
                    location: (518, 19, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_A".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::U8, "status").into()),
                    assigned_id: Some(3),
                    location: (581, 21, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    assigned_id: None,
                    location: (711, 27, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I16, "(int16_t) data").into()),
                    assigned_id: Some(4),
                    location: (783, 29, 24).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    ekotrace_instance: "ekt".to_string(),
                    payload: Some((TypeHint::I8, "(int8_t) *((uint8_t*) &mydata)").into()),
                    assigned_id: None,
                    location: (858, 31, 24).into(),
                },
            ])
        );
    }

    #[test]
    fn missing_semicolon() {
        let parser = CParser::default();
        let input = "const size_t err = EKT_RECORD(g_ekotrace, EVENT_READ)";
        let tokens = parser.parse_events(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((19, 1, 20).into())));
        let input = "EKT_RECORD_W_I16(ekt, E0, data)";
        let tokens = parser.parse_events(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((0, 1, 1).into())));
    }

    #[test]
    fn event_payload_type_hint_errors() {
        let parser = CParser::default();
        let input = "EKT_RECORD_W_I12(ekt, E0, data);";
        let tokens = parser.parse_events(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
    }
}
