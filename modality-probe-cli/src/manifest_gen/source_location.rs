use std::fmt;

/// A location in a file/buffer
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct SourceLocation {
    pub offset: usize,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Offset: {}, line: {}, column: {}",
            self.offset, self.line, self.column
        )
    }
}

impl From<(usize, usize, usize)> for SourceLocation {
    fn from(triple: (usize, usize, usize)) -> SourceLocation {
        SourceLocation {
            offset: triple.0,
            line: triple.1,
            column: triple.2,
        }
    }
}
