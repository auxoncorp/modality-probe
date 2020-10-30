use dynfmt::{Argument, Format, SimpleCurlyFormat};

pub trait DescriptionFormat {
    fn contains_formatting(&self) -> bool;

    fn format_payload(&self, payload: Argument) -> Result<String, dynfmt::Error>;
}

impl<T: AsRef<str>> DescriptionFormat for T {
    fn contains_formatting(&self) -> bool {
        self.as_ref().contains("{}")
    }

    fn format_payload(&self, payload: Argument) -> Result<String, dynfmt::Error> {
        let cow = SimpleCurlyFormat.format(self.as_ref(), &[payload])?;
        Ok(cow.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    const DESC_STR: &'static str = "My event payload = {} other stuff";

    fn desc_string() -> String {
        DESC_STR.to_string()
    }

    #[test]
    fn does_not_contain_formatting() {
        assert_eq!("no formatting here".contains_formatting(), false);
        assert_eq!("this {   } stuff".contains_formatting(), false);
        assert_eq!("nothing {{{{".contains_formatting(), false);
        assert_eq!("}}}} here".contains_formatting(), false);
    }

    #[test]
    fn string_and_str() {
        let payload = -123_i16;
        let desc = desc_string();

        assert!(desc.contains_formatting());
        assert!(DESC_STR.contains_formatting());

        // Matches with format!()'s output
        let expected = format!("My event payload = {} other stuff", payload);
        assert_eq!(expected, desc.format_payload(&payload).unwrap());
        assert_eq!(expected, DESC_STR.format_payload(&payload).unwrap());
    }

    proptest! {
        #[test]
        fn format_i8(payload in proptest::num::i8::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_u8(payload in proptest::num::u8::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_i16(payload in proptest::num::i16::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_u16(payload in proptest::num::u16::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_i32(payload in proptest::num::i32::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_u32(payload in proptest::num::u32::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_bool(payload in proptest::bool::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_f32(payload in proptest::num::f32::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }

    proptest! {
        #[test]
        fn format_f64(payload in proptest::num::f64::ANY) {
            let desc = desc_string();
            assert!(desc.contains_formatting());
            let expected = format!("My event payload = {} other stuff", payload);
            assert_eq!(expected, desc.format_payload(&payload).unwrap());
        }
    }
}
