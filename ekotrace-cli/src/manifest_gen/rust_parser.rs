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
    sequence::{delimited, preceded},
};
use nom_locate::position;
use std::fmt;
use std::str::FromStr;

#[derive(Default)]
pub struct RustParser {}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    Syntax(SourceLocation),
    MissingSemicolon(SourceLocation),
    UnrecognizedTypeHint(SourceLocation),
}

impl Parser for RustParser {
    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, parser::Error> {
        let md = self.parse_event_md(input)?;
        Ok(md)
    }

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, parser::Error> {
        let md = self.parse_tracer_md(input)?;
        Ok(md)
    }
}

impl RustParser {
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
    let (input, _) = imports(input)?;
    let (input, found_try) = peek(opt(tag("ekt_try_record")))(input)?;
    let (input, metadata) = match found_try {
        None => {
            let (input, found_with_payload) = peek(opt(tag("ekt_record_w_")))(input)?;
            match found_with_payload {
                None => event_call_exp(input)?,
                Some(_) => event_with_payload_call_exp(input)?,
            }
        }
        Some(_) => {
            let (input, found_with_payload) = peek(opt(tag("ekt_try_record_w_")))(input)?;
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
    let (input, _) = tag("ekt_try_record!")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;
    let mut expect_desc = false;
    let (args, name) = match peek(variable_call_exp_arg)(args) {
        Ok(_) => {
            expect_desc = true;
            variable_call_exp_arg(args)?
        }
        Err(_) => rest_string(args)?,
    };
    let (_args, description) = if expect_desc {
        map(rest_literal, |desc: String| {
            Some(
                desc.replace("\n", "")
                    .replace("\t", "")
                    .replace("\"", "")
                    .trim()
                    .to_string(),
            )
        })(args)?
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

fn event_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("ekt_record!(")(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = take_until(");")(input)
        .map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let (input, _) =
        tag(");")(input).map_err(|e| convert_error(e, Error::MissingSemicolon(pos.into())))?;
    let split: Vec<&str> = args
        .fragment()
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    if split.len() != 2 && split.len() != 3 {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    // Use convert_error to preserve the original pos lost after the split
    let arg0 = Span::new(split[0]);
    let (_, ekotrace_instance) =
        rest_string(arg0).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg1 = Span::new(split[1]);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg1)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let description = if split.len() == 3 {
        let arg2 = Span::new(split[2]);
        let (arg2, _) =
            comments_and_spacing(arg2).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        let (_, desc) = delimited(char('"'), is_not("\""), char('"'))(arg2)
            .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        Some(
            desc.fragment()
                .replace("\n", "")
                .replace("\t", "")
                .replace("\"", "")
                .trim()
                .to_string(),
        )
    } else {
        None
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

fn event_try_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("ekt_try_record_w_")(input)?;
    let (input, type_hint) = take_until("!")(input)?;
    let (input, _) = tag("!")(input)?;
    let type_hint = TypeHint::from_str(type_hint.fragment())
        .map_err(|_| make_failure(input, Error::UnrecognizedTypeHint(pos.into())))?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;
    let (input, args) = delimited(char('('), is_not(")"), char(')'))(input)?;
    let (args, ekotrace_instance) = variable_call_exp_arg(args)?;
    let (args, name) = variable_call_exp_arg(args)?;
    let mut expect_arg4 = false;
    let (args, payload) = match peek(variable_call_exp_arg_literal)(args) {
        Ok(_) => {
            expect_arg4 = true;
            variable_call_exp_arg_literal(args)?
        }
        Err(_) => rest_literal(args)?,
    };
    let (_args, description) = if expect_arg4 {
        map(rest_literal, |desc: String| {
            Some(
                desc.replace("\n", "")
                    .replace("\t", "")
                    .replace("\"", "")
                    .trim()
                    .to_string(),
            )
        })(args)?
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

fn event_with_payload_call_exp(input: Span) -> ParserResult<Span, EventMetadata> {
    let (input, pos) = position(input)?;
    let (input, _) = tag("ekt_record_w_")(input)?;
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
    let split: Vec<&str> = args
        .fragment()
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();
    if split.len() != 3 && split.len() != 4 {
        return Err(make_failure(input, Error::Syntax(pos.into())));
    }
    // Use convert_error to preserve the original pos lost after the split
    let arg = Span::new(split[0]);
    let (_, ekotrace_instance) =
        rest_string(arg).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg = Span::new(split[1]);
    let (_, name) = alt((reduced_event_id_exp_alt_a, reduced_event_id_exp_alt_b))(arg)
        .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let arg = Span::new(split[2]);
    let (_, payload) =
        rest_literal(arg).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
    let description = if split.len() == 4 {
        let arg = Span::new(split[3]);
        let (arg, _) =
            comments_and_spacing(arg).map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        let (_, desc) = delimited(char('"'), is_not("\""), char('"'))(arg)
            .map_err(|e| convert_error(e, Error::Syntax(pos.into())))?;
        Some(
            desc.fragment()
                .replace("\n", "")
                .replace("\t", "")
                .replace("\"", "")
                .trim()
                .to_string(),
        )
    } else {
        None
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

fn reduced_event_id_exp_alt_a(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, pos) = position(input)?;
    let (input, id) = take_until(".")(input)?;
    if !id
        .fragment()
        .chars()
        .all(|c| c.is_alphanumeric() || c == '_')
    {
        return Err(make_error(input, Error::Syntax(pos.into())));
    }
    Ok((input, trimmed_string(id.fragment())))
}

fn reduced_event_id_exp_alt_b(input: Span) -> ParserResult<Span, String> {
    let (input, _) = comments_and_spacing(input)?;
    let (input, _) = take_until("(")(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, id) = take_until(")")(input)?;
    Ok((input, trimmed_string(id.fragment())))
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
    let (input, _) = imports(input)?;
    let (input, pos) = position(input)?;
    let (input, _) = alt((
        tag("Ekotrace::try_initialize_at"),
        tag("Ekotrace::initialize_at"),
        tag("Ekotrace::new_with_storage"),
    ))(input)?;
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
    let (input, pos) = position(input)?;
    let (input, name) = rest_string(input)?;
    let name = if name.contains("::") {
        let split: Vec<&str> = name.split("::").collect();
        match split.last() {
            None => return Err(make_failure(input, Error::Syntax(pos.into()))),
            Some(last) => {
                if *last == "" {
                    return Err(make_failure(input, Error::Syntax(pos.into())));
                }
                (*last).to_string()
            }
        }
    } else {
        name
    };
    Ok((input, name))
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
            Error::Syntax(loc) => write!(
                f,
                "Enountered a syntax error while parsing an Ekotrace record event invocation near\n{}",
                loc
            ),
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
    let tracer = Ekotrace::try_initialize_at(&mut storage, LOCATION_ID_A)
        .expect("Could not initialize Ekotrace");

    let ekotrace_foo = Ekotrace::try_initialize_at(&mut storage_bytes, LOCATION_ID_B)?;

    // A comment
    let bar = Ekotrace::initialize_at(
        &mut storage_bytes, // docs
        my_ids::LOCATION_ID_C)?; // docs

    let ekotrace_foo = Ekotrace::try_initialize_at(&mut storage_bytes,
    my::nested::mod::LOCATION_ID_D)?; // docs

    /* More comments
     * on more lines Ekotrace::new_with_storage(a, b)
     */
    let tracer = Ekotrace::new_with_storage(storage, LOCATION_ID_E).unwrap();
"#;

    const MIXED_EVENT_RECORDING_INPUT: &'static str = r#"
    /* Comments */
    ekt_try_record!(tracer, EVENT_A, "my text").expect("Could not record event");

    ekt_try_record!(
        tracer, // docs
        EVENT_B, /* docs */
        "my text") /// docs
    .expect("Could not record event");

    /// More docs
    ekt_try_record!(tracer, EVENT_C).expect("Could not record event");

    ekt_record!(
        tracer, // docs
        EventId::try_from(EVENT_D).unwrap(), /* docs */
        "my text" //docs
    ); // docs

    ekt_record!(tracer, EVENT_E.try_into()?);
    ekt_record!(tracer, EVENT_EAGAIN1.try_into()?,
    );
    ekt_record!(tracer, EventId::try_from(EVENT_EAGAIN2).unwrap(),
    );
    ekt_record!(tracer, EVENT_F.try_into().unwrap());
    ekt_record!(tracer, EventId::try_from(EVENT_G).expect("abc"), "docs");

    ekt_try_record_w_u32!(tracer, EVENT_H, 1_u32)
        .expect("Could not record event");

    /*
     * docs
     * ekt_record!(tracer, EventId::try_from(EVENT_NONE).unwrap());
     */
    ekt_try_record_w_f32!(tracer, EVENT_I, 1.234_f32, "desc") // docs
        .expect("Could not record event");

    ekt_record_w_i8!(
        tracer,
        EventId::try_from(EVENT_J).unwrap(),
        -2_i8,
        "desc"
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
                },
                TracerMetadata {
                    name: "LOCATION_ID_B".to_string(),
                    location: (199, 6, 24).into(),
                },
                TracerMetadata {
                    name: "LOCATION_ID_C".to_string(),
                    location: (296, 9, 15).into(),
                },
                TracerMetadata {
                    name: "LOCATION_ID_D".to_string(),
                    location: (422, 13, 24).into(),
                },
                TracerMetadata {
                    name: "LOCATION_ID_E".to_string(),
                    location: (617, 19, 18).into(),
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
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    location: (24, 3, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_B".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    location: (107, 5, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_C".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    location: (266, 12, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_D".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("my text".to_string()),
                    location: (338, 14, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_E".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    location: (476, 20, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN1".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    location: (522, 21, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_EAGAIN2".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    location: (580, 23, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_F".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: None,
                    location: (654, 25, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_G".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: None,
                    description: Some("docs".to_string()),
                    location: (708, 26, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_H".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: Some((TypeHint::U32, "1_u32").into()),
                    description: None,
                    location: (784, 28, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_I".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: Some((TypeHint::F32, "1.234_f32").into()),
                    description: Some("desc".to_string()),
                    location: (973, 35, 5).into(),
                },
                EventMetadata {
                    name: "EVENT_J".to_string(),
                    ekotrace_instance: "tracer".to_string(),
                    payload: Some((TypeHint::I8, "-2_i8").into()),
                    description: Some("desc".to_string()),
                    location: (1087, 38, 5).into(),
                },
            ])
        );
    }

    #[test]
    fn tracer_id_namespace_error() {
        let parser = RustParser::default();
        let input = "Ekotrace::try_initialize_at(&mut storage_bytes,my::nested::mod::)";
        let tokens = parser.parse_tracer_md(input);
        assert_eq!(tokens, Err(Error::Syntax((47, 1, 48).into())));
    }

    #[test]
    fn missing_semicolon_errors() {
        let parser = RustParser::default();
        let input = r#"
ekt_record!(tracer, EVENT_F.try_into().unwrap())
let a = b;
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::MissingSemicolon((1, 2, 1).into())));
        let input = r#"
ekt_record_w_i8!(
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
ekt_record!(tracer, abc, EVENT_F.try_into().unwrap());
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
ekt_record!(tracer, EVENT_F.try_into().unwrap(), abc, abc);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
ekt_record_w_f32!(
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
ekt_record_w_i32!(
            tracer,
            EventId::try_from(EVENT_J).unwrap(),
        );
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
        let input = r#"
ekt_record!(tracer, EventId::try_from::<>EVENT_E);
"#;
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::Syntax((1, 2, 1).into())));
    }

    #[test]
    fn event_payload_type_hint_errors() {
        let parser = RustParser::default();
        let input = "ekt_record_w_i12!(t, EVENT, 1);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
        let input = "ekt_record_w_f64!(t, EVENT, 1, asdf);";
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Err(Error::UnrecognizedTypeHint((0, 1, 1).into())));
    }

    #[test]
    fn ignores_include_statements() {
        let parser = RustParser::default();
        let input = r#"
use crate::tracing_ids::*;
use ekotrace::{ekt_try_record, ekt_record, ekt_try_record_w_u32, ekt_record_w_i8, Ekotrace, Tracer};
use std::net::UdpSocket;
use std::{thread, time};

another_macro!(mything);
"#;
        let tokens = parser.parse_tracer_md(input);
        assert_eq!(tokens, Ok(vec![]));
        let tokens = parser.parse_event_md(input);
        assert_eq!(tokens, Ok(vec![]));
    }
}
