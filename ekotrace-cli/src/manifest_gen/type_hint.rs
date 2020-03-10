use std::str;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum TypeHint {
    I8,
    I16,
    I32,
    U8,
    U16,
    U32,
    F32,
    Bool,
}

impl Default for TypeHint {
    /// The default payload is a u32
    fn default() -> TypeHint {
        TypeHint::U32
    }
}

impl str::FromStr for TypeHint {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.to_lowercase().as_str() {
            "i8" => TypeHint::I8,
            "i16" => TypeHint::I16,
            "i32" => TypeHint::I32,
            "u8" => TypeHint::U8,
            "u16" => TypeHint::U16,
            "u32" => TypeHint::U32,
            "f32" => TypeHint::F32,
            "bool" => TypeHint::Bool,
            _ => return Err("Unsupported type hint"),
        })
    }
}

impl TypeHint {
    pub fn as_str(&self) -> &str {
        match *self {
            TypeHint::I8 => "i8",
            TypeHint::I16 => "i16",
            TypeHint::I32 => "i32",
            TypeHint::U8 => "u8",
            TypeHint::U16 => "u16",
            TypeHint::U32 => "u32",
            TypeHint::F32 => "f32",
            TypeHint::Bool => "bool",
        }
    }

    pub fn to_string(&self) -> String {
        self.as_str().to_string()
    }
}
