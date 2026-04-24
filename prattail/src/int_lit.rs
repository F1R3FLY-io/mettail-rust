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

    /// Convert any signed/unsigned variant to i64, returning None on overflow.
    /// Used by the lexer to generate Token::Integer(i64) from suffixed literals.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            IntLit::I8(v) => Some(*v as i64),
            IntLit::I16(v) => Some(*v as i64),
            IntLit::I32(v) => Some(*v as i64),
            IntLit::I64(v) => Some(*v),
            IntLit::I128(v) => i64::try_from(*v).ok(),
            IntLit::U8(v) => Some(*v as i64),
            IntLit::U16(v) => Some(*v as i64),
            IntLit::U32(v) => Some(*v as i64),
            IntLit::U64(v) => i64::try_from(*v).ok(),
            IntLit::U128(v) => i64::try_from(*v).ok(),
            IntLit::BigInt(v) => {
                use num_traits::ToPrimitive;
                v.to_i64()
            },
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

/// Explicit-suffix tag carried on `Token::Integer` so the parser's native
/// literal arms can reject suffix/category mismatches. Bare digits (`42`)
/// produce `Unsuffixed`, which is compatible with every integer category
/// — preserving Ambiguous preservation on unsuffixed literals while
/// rejecting e.g. `1u32` in an Int-typed position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntSuffix {
    Unsuffixed,
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
}

impl IntSuffix {
    /// Detect the suffix from a lexed integer literal text (e.g. `"42u32"`,
    /// `"-3"`, `"0x1Ai64"`). `"n"` (BigInt) is never emitted as
    /// `Token::Integer`, so it's not a variant here.
    pub fn from_text(text: &str) -> Self {
        let cleaned: std::string::String = text.chars().filter(|&c| c != '_').collect();
        let s = cleaned.as_str();
        for (tag, suf) in [
            ("i128", IntSuffix::I128),
            ("u128", IntSuffix::U128),
            ("isize", IntSuffix::Isize),
            ("usize", IntSuffix::Usize),
            ("i64", IntSuffix::I64),
            ("u64", IntSuffix::U64),
            ("i32", IntSuffix::I32),
            ("u32", IntSuffix::U32),
            ("i16", IntSuffix::I16),
            ("u16", IntSuffix::U16),
            ("i8", IntSuffix::I8),
            ("u8", IntSuffix::U8),
        ] {
            if s.ends_with(tag) {
                return suf;
            }
        }
        IntSuffix::Unsuffixed
    }

    pub fn matches_i8(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::I8) }
    pub fn matches_i16(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::I16) }
    pub fn matches_i32(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::I32) }
    pub fn matches_i64(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::I64 | IntSuffix::Isize) }
    pub fn matches_i128(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::I128) }
    pub fn matches_isize(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::Isize | IntSuffix::I64) }
    pub fn matches_u8(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::U8) }
    pub fn matches_u16(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::U16) }
    pub fn matches_u32(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::U32) }
    pub fn matches_u64(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::U64 | IntSuffix::Usize) }
    pub fn matches_u128(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::U128) }
    pub fn matches_usize(&self) -> bool { matches!(self, IntSuffix::Unsuffixed | IntSuffix::Usize | IntSuffix::U64) }
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

/// Attempt to fit `big` into the variant indicated by `suffix`. Returns `None`
/// when the value is out of range for that variant.
fn try_fit_type(big: &BigInt, suffix: &Suffix) -> Option<IntLit> {
    use num_traits::ToPrimitive;
    match suffix {
        Suffix::I8 => big.to_i8().map(IntLit::I8),
        Suffix::I16 => big.to_i16().map(IntLit::I16),
        Suffix::I32 => big.to_i32().map(IntLit::I32),
        Suffix::I64 | Suffix::Isize => big.to_i64().map(IntLit::I64),
        Suffix::I128 => big.to_i128().map(IntLit::I128),
        Suffix::U8 => big.to_u8().map(IntLit::U8),
        Suffix::U16 => big.to_u16().map(IntLit::U16),
        Suffix::U32 => big.to_u32().map(IntLit::U32),
        Suffix::U64 | Suffix::Usize => big.to_u64().map(IntLit::U64),
        Suffix::U128 => big.to_u128().map(IntLit::U128),
        Suffix::BigInt => Some(IntLit::BigInt(big.clone())),
    }
}

/// Parse an integer literal with value-based bound tightening.
///
/// - An explicit suffix (e.g. `42u32`, `-3i32`, `10n`) is honored exactly;
///   if the value does not fit the requested width, `Err(())` is returned.
/// - `default_suffix`, when provided, is a strict requirement — the caller is
///   declaring the category's canonical type (e.g. `Int`'s `literals { }` block
///   passes `Some(Suffix::I32)`). Values that overflow that width return
///   `Err(())` so the caller's category can reject out-of-range literals.
/// - When `default_suffix` is `None`, the result is the NARROWEST type that
///   fits, via the cascade `i32 → u32 → i64 → u64 → i128 → u128 → BigInt`.
///   This is the "bound tightening" that lets callers without a fixed width
///   route to the tightest type by value: `34` → `i32`, `3_000_000_000` →
///   `u32`, huge numbers → `BigInt`.
#[allow(clippy::result_unit_err)]
pub fn parse_int_lit(text: &str, default_suffix: Option<Suffix>) -> Result<IntLit, ()> {
    let cleaned = text.replace('_', "");
    let (body, suffix) = split_suffix(cleaned.as_str());
    let (negative, unsigned_body) = match body.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, body),
    };
    let (radix, digits) = split_radix_prefix(unsigned_body);

    let magnitude = BigInt::from_str_radix(digits, radix).map_err(|_| ())?;
    let big = if negative { -magnitude } else { magnitude };

    if let Some(s) = suffix {
        return try_fit_type(&big, &s).ok_or(());
    }

    if let Some(ref hint) = default_suffix {
        return try_fit_type(&big, hint).ok_or(());
    }

    for candidate in [
        Suffix::I32,
        Suffix::U32,
        Suffix::I64,
        Suffix::U64,
        Suffix::I128,
        Suffix::U128,
    ] {
        if let Some(lit) = try_fit_type(&big, &candidate) {
            return Ok(lit);
        }
    }
    Ok(IntLit::BigInt(big))
}
