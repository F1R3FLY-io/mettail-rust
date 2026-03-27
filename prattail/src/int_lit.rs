use num_bigint::BigInt;
use num_traits::Num;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntLit {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    BigInt(BigInt),
}

impl From<i8> for IntLit {
    fn from(v: i8) -> Self {
        IntLit::I8(v)
    }
}
impl From<i16> for IntLit {
    fn from(v: i16) -> Self {
        IntLit::I16(v)
    }
}
impl From<i32> for IntLit {
    fn from(v: i32) -> Self {
        IntLit::I32(v)
    }
}
impl From<i64> for IntLit {
    fn from(v: i64) -> Self {
        IntLit::I64(v)
    }
}
impl From<i128> for IntLit {
    fn from(v: i128) -> Self {
        IntLit::I128(v)
    }
}
impl From<u8> for IntLit {
    fn from(v: u8) -> Self {
        IntLit::U8(v)
    }
}
impl From<u16> for IntLit {
    fn from(v: u16) -> Self {
        IntLit::U16(v)
    }
}
impl From<u32> for IntLit {
    fn from(v: u32) -> Self {
        IntLit::U32(v)
    }
}
impl From<u64> for IntLit {
    fn from(v: u64) -> Self {
        IntLit::U64(v)
    }
}
impl From<u128> for IntLit {
    fn from(v: u128) -> Self {
        IntLit::U128(v)
    }
}
impl From<BigInt> for IntLit {
    fn from(v: BigInt) -> Self {
        IntLit::BigInt(v)
    }
}

impl IntLit {
    pub fn to_i8(&self) -> Option<i8> {
        match self {
            IntLit::I8(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_i16(&self) -> Option<i16> {
        match self {
            IntLit::I16(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_i32(&self) -> Option<i32> {
        match self {
            IntLit::I32(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            IntLit::I64(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_i128(&self) -> Option<i128> {
        match self {
            IntLit::I128(v) => Some(*v),
            _ => None,
        }
    }

    pub fn to_u8(&self) -> Option<u8> {
        match self {
            IntLit::U8(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_u16(&self) -> Option<u16> {
        match self {
            IntLit::U16(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_u32(&self) -> Option<u32> {
        match self {
            IntLit::U32(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_u64(&self) -> Option<u64> {
        match self {
            IntLit::U64(v) => Some(*v),
            _ => None,
        }
    }
    pub fn to_u128(&self) -> Option<u128> {
        match self {
            IntLit::U128(v) => Some(*v),
            _ => None,
        }
    }

    pub fn to_bigint(&self) -> Option<BigInt> {
        match self {
            IntLit::BigInt(v) => Some(v.clone()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Suffix {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    BigInt,
}

fn split_suffix(s: &str) -> (&str, Option<Suffix>) {
    // Order matters: longest first.
    for (suffix, tag) in [
        ("i128", Suffix::I128),
        ("u128", Suffix::U128),
        ("isize", Suffix::Isize),
        ("usize", Suffix::Usize),
        ("i64", Suffix::I64),
        ("u64", Suffix::U64),
        ("i32", Suffix::I32),
        ("u32", Suffix::U32),
        ("i16", Suffix::I16),
        ("u16", Suffix::U16),
        ("i8", Suffix::I8),
        ("u8", Suffix::U8),
        ("n", Suffix::BigInt),
    ] {
        if let Some(body) = s.strip_suffix(suffix) {
            return (body, Some(tag));
        }
    }
    (s, None)
}

fn split_radix_prefix(s: &str) -> (u32, &str) {
    if let Some(h) = s.strip_prefix("0x") {
        (16, h)
    } else if let Some(o) = s.strip_prefix("0o") {
        (8, o)
    } else if let Some(b) = s.strip_prefix("0b") {
        (2, b)
    } else {
        (10, s)
    }
}

#[allow(clippy::result_unit_err)]
pub fn parse_int_lit(text: &str, default_suffix: Option<Suffix>) -> Result<IntLit, ()> {
    let cleaned = text.replace('_', "");
    let (body, suffix) = split_suffix(cleaned.as_str());
    let (radix, digits) = split_radix_prefix(body);

    match suffix.unwrap_or(default_suffix.unwrap_or(Suffix::I64)) {
        Suffix::I8 => i128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| i8::try_from(v).ok())
            .map(IntLit::I8)
            .ok_or(()),
        Suffix::I16 => i128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| i16::try_from(v).ok())
            .map(IntLit::I16)
            .ok_or(()),
        Suffix::I32 => i128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| i32::try_from(v).ok())
            .map(IntLit::I32)
            .ok_or(()),
        Suffix::I64 | Suffix::Isize => i128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| i64::try_from(v).ok())
            .map(IntLit::I64)
            .ok_or(()),
        Suffix::I128 => i128::from_str_radix(digits, radix)
            .map(IntLit::I128)
            .map_err(|_| ()),

        Suffix::U8 => u128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| u8::try_from(v).ok())
            .map(IntLit::U8)
            .ok_or(()),
        Suffix::U16 => u128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| u16::try_from(v).ok())
            .map(IntLit::U16)
            .ok_or(()),
        Suffix::U32 => u128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| u32::try_from(v).ok())
            .map(IntLit::U32)
            .ok_or(()),
        Suffix::U64 | Suffix::Usize => u128::from_str_radix(digits, radix)
            .ok()
            .and_then(|v| u64::try_from(v).ok())
            .map(IntLit::U64)
            .ok_or(()),
        Suffix::U128 => u128::from_str_radix(digits, radix)
            .map(IntLit::U128)
            .map_err(|_| ()),

        Suffix::BigInt => BigInt::from_str_radix(digits, radix)
            .map(IntLit::BigInt)
            .map_err(|_| ()),
    }
}
