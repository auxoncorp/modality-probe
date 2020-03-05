use std::str::FromStr;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum TypeHint {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    Enum,
}

impl Default for TypeHint {
    /// The default payload is a u32
    fn default() -> TypeHint {
        TypeHint::U32
    }
}

impl FromStr for TypeHint {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.to_lowercase().as_str() {
            "i8" => TypeHint::I8,
            "i16" => TypeHint::I16,
            "i32" => TypeHint::I32,
            "i64" => TypeHint::I64,
            "u8" => TypeHint::U8,
            "u16" => TypeHint::U16,
            "u32" => TypeHint::U32,
            "u64" => TypeHint::U64,
            "f32" => TypeHint::F32,
            "f64" => TypeHint::F64,
            "boolean" | "bool" => TypeHint::Bool,
            "enum" | "enumeration" => TypeHint::Enum,
            _ => return Err("Unsupported type hint"),
        })
    }
}
