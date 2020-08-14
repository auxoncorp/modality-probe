use std::io::{BufRead, BufReader, Read, Write};

use super::{Error, ReportLogEntry};

pub fn write_log_entries<'a, W: Write, E: IntoIterator<Item = &'a ReportLogEntry>>(
    w: &mut W,
    entries: E,
) -> Result<(), Error> {
    for e in entries.into_iter() {
        writeln!(w, "{}", serde_json::to_string(&e)?)?;
    }
    Ok(())
}

impl From<serde_json::error::Error> for Error {
    fn from(e: serde_json::error::Error) -> Error {
        Error::Serialization(format!("json failure: {}", e))
    }
}

impl From<&serde_json::error::Error> for Error {
    fn from(e: &serde_json::error::Error) -> Error {
        Error::Serialization(format!("json failure: {}", e))
    }
}

pub fn read_log_entries<R: Read>(r: &mut R) -> Result<Vec<ReportLogEntry>, Error> {
    let br = BufReader::new(r);
    let entries: Result<Vec<ReportLogEntry>, _> = br
        .lines()
        .into_iter()
        .map(|line| match line {
            Ok(l) => serde_json::from_str::<ReportLogEntry>(&l)
                .map_err(|e| Error::Serialization(format!("unable to deserialize log row: {}", e))),
            Err(e) => Err(Error::Serialization(format!("unable to read log: {}", e))),
        })
        .collect();
    Ok(entries?)
}

#[cfg(test)]
mod test {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn round_trip_json(
            entries in proptest::collection::vec(
                crate::test::arb_log_entry(),
                0..15
            )
        ) {
            let mut data = Vec::<u8>::new();
            prop_assert!(super::write_log_entries(&mut data, &entries).is_ok());

            let read_back = super::read_log_entries(&mut data.as_slice());

            match read_back {
                Err(e) => prop_assert!(false, "read_back error: {:?}", e),
                Ok(es) => prop_assert_eq!(entries, es),
            }
        }
    }
}
