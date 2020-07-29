use std::{
    convert::TryFrom,
    io::{Read, Write},
};

use super::{LogFileRow, ReadError, ReportLogEntry};

pub fn write_log_entries<'a, W: Write, E: IntoIterator<Item = &'a ReportLogEntry>>(
    w: &mut W,
    entries: E,
    include_header_row: bool,
) -> Result<(), csv::Error> {
    let mut csv = csv::WriterBuilder::new()
        .has_headers(include_header_row)
        .from_writer(w);

    for e in entries.into_iter() {
        let line: LogFileRow = e.into();
        csv.serialize(line)?;
    }

    csv.flush()?;
    Ok(())
}

impl From<csv::Error> for ReadError {
    fn from(e: csv::Error) -> ReadError {
        ReadError::Serialization(Box::new(e))
    }
}

pub fn read_log_entries<R: Read>(r: &mut R) -> Result<Vec<ReportLogEntry>, ReadError> {
    let mut csv = csv::Reader::from_reader(r);
    csv.deserialize()
        .map(|line| Ok(ReportLogEntry::try_from(&line?)?))
        .collect()
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn round_trip_serialization(
            entries in proptest::collection::vec(
                crate::test::arb_log_entry(),
                0..15
            )
        ) {
            let mut data = Vec::<u8>::new();
            prop_assert!(super::write_log_entries(&mut data, &entries, true).is_ok());

            let read_back = super::read_log_entries(&mut data.as_slice());

            match read_back {
                Err(e) => prop_assert!(false, "read_back error: {:?}", e),
                Ok(es) => prop_assert_eq!(entries, es),
            }
        }
    }
}
