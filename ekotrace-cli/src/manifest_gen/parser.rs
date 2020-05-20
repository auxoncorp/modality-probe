use crate::manifest_gen::{
    c_parser, event_metadata::EventMetadata, rust_parser, source_location::SourceLocation,
    tracer_metadata::TracerMetadata,
};
use nom_locate::LocatedSpan;
use std::fmt;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    CParser(c_parser::Error),
    RustParser(rust_parser::Error),
}

impl Error {
    pub fn location(&self) -> &SourceLocation {
        match self {
            Error::CParser(inner) => inner.location(),
            Error::RustParser(inner) => inner.location(),
        }
    }
}

pub trait Parser {
    fn parse_events(&self, input: &str) -> Result<Vec<EventMetadata>, Error>;

    fn parse_tracers(&self, input: &str) -> Result<Vec<TracerMetadata>, Error>;
}

pub type Span<'a> = LocatedSpan<&'a str>;

impl<'a> From<Span<'a>> for SourceLocation {
    fn from(span: Span<'a>) -> SourceLocation {
        SourceLocation {
            offset: span.location_offset(),
            line: span.location_line() as usize,
            column: span.get_column(),
        }
    }
}

impl From<c_parser::Error> for Error {
    fn from(e: c_parser::Error) -> Self {
        Error::CParser(e)
    }
}

impl From<rust_parser::Error> for Error {
    fn from(e: rust_parser::Error) -> Self {
        Error::RustParser(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::CParser(t) => write!(f, "{}", t),
            Error::RustParser(t) => write!(f, "{}", t),
        }
    }
}

pub(crate) fn trimmed_string(s: &str) -> String {
    s.trim()
        .to_string()
        .replace("\n", "")
        .replace("\t", "")
        .replace(" ", "")
}

pub(crate) fn trimmed_string_w_space(s: &str) -> String {
    s.trim().to_string().replace("\n", "").replace("\t", "")
}

pub(crate) fn remove_double_quotes(s: &str) -> String {
    s.replace("\"", "").trim().to_string()
}

pub(crate) fn tags_or_desc_valid(s: &str) -> bool {
    s.chars().filter(|&c| c == '"').count() == 2
}

pub(crate) fn event_name_valid(s: &str) -> bool {
    s.chars().all(|c| c.is_alphanumeric() || c == '_')
}
