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

    /// Convert any integer variant to a `num_bigint::BigInt`. Always succeeds
    /// because every fixed-width integer fits in BigInt. Returns `Option` for
    /// API parity with sister methods like `as_i64`, but the `None` case is
    /// unreachable in practice — every variant produces `Some`. (B11 fix:
    /// previously this only handled `IntLit::BigInt(_)`, returning `None` for
    /// every other variant. That broke BigInt's category eval block when bare
    /// unsuffixed integers — which `parse_int_lit` returns as the narrowest
    /// fit, e.g. `IntLit::I32(0)` for "0" — were routed to BigInt's NumLit
    /// arm. The eval block called `parse_int_lit(text, None).to_bigint()`
    /// expecting it to always succeed, but it returned `None` for any
    /// non-BigInt variant, leaving the builder empty.)
    pub fn to_bigint(&self) -> Option<BigInt> {
        match self {
            IntLit::I8(v) => Some(BigInt::from(*v)),
            IntLit::I16(v) => Some(BigInt::from(*v)),
            IntLit::I32(v) => Some(BigInt::from(*v)),
            IntLit::I64(v) => Some(BigInt::from(*v)),
            IntLit::I128(v) => Some(BigInt::from(*v)),
            IntLit::U8(v) => Some(BigInt::from(*v)),
            IntLit::U16(v) => Some(BigInt::from(*v)),
            IntLit::U32(v) => Some(BigInt::from(*v)),
            IntLit::U64(v) => Some(BigInt::from(*v)),
            IntLit::U128(v) => Some(BigInt::from(*v)),
            IntLit::BigInt(v) => Some(v.clone()),
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

    /// Convert any variant to i128, returning None on overflow. Lossless across
    /// every variant that fits in i128 — e.g. `IntLit::I128(i128::MAX)`,
    /// `IntLit::U64(u64::MAX)`, `IntLit::U128(u128::MAX as i128)` all succeed.
    /// (B12 fix: emission previously routed Int128 conversions through
    /// `as_i64`, which silently failed for any value greater than `i64::MAX`,
    /// turning a valid `i128` literal into "WPDS produced no result".)
    pub fn as_i128(&self) -> Option<i128> {
        match self {
            IntLit::I8(v) => Some(*v as i128),
            IntLit::I16(v) => Some(*v as i128),
            IntLit::I32(v) => Some(*v as i128),
            IntLit::I64(v) => Some(*v as i128),
            IntLit::I128(v) => Some(*v),
            IntLit::U8(v) => Some(*v as i128),
            IntLit::U16(v) => Some(*v as i128),
            IntLit::U32(v) => Some(*v as i128),
            IntLit::U64(v) => Some(*v as i128),
            IntLit::U128(v) => i128::try_from(*v).ok(),
            IntLit::BigInt(v) => {
                use num_traits::ToPrimitive;
                v.to_i128()
            },
        }
    }

    /// Convert any variant to u64, returning None on overflow or negative
    /// values. Lossless for non-negative values up to u64::MAX. (B12 fix:
    /// previously routed through `as_i64`, which failed for `IntLit::U64(v)`
    /// where v > i64::MAX — silently rejecting valid u64 literals.)
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            IntLit::I8(v) => u64::try_from(*v).ok(),
            IntLit::I16(v) => u64::try_from(*v).ok(),
            IntLit::I32(v) => u64::try_from(*v).ok(),
            IntLit::I64(v) => u64::try_from(*v).ok(),
            IntLit::I128(v) => u64::try_from(*v).ok(),
            IntLit::U8(v) => Some(*v as u64),
            IntLit::U16(v) => Some(*v as u64),
            IntLit::U32(v) => Some(*v as u64),
            IntLit::U64(v) => Some(*v),
            IntLit::U128(v) => u64::try_from(*v).ok(),
            IntLit::BigInt(v) => {
                use num_traits::ToPrimitive;
                v.to_u64()
            },
        }
    }

    /// Convert any variant to u128, returning None on overflow or negative
    /// values. Lossless for non-negative values up to u128::MAX. (B12 fix:
    /// same reason as `as_u64`.)
    pub fn as_u128(&self) -> Option<u128> {
        match self {
            IntLit::I8(v) => u128::try_from(*v).ok(),
            IntLit::I16(v) => u128::try_from(*v).ok(),
            IntLit::I32(v) => u128::try_from(*v).ok(),
            IntLit::I64(v) => u128::try_from(*v).ok(),
            IntLit::I128(v) => u128::try_from(*v).ok(),
            IntLit::U8(v) => Some(*v as u128),
            IntLit::U16(v) => Some(*v as u128),
            IntLit::U32(v) => Some(*v as u128),
            IntLit::U64(v) => Some(*v as u128),
            IntLit::U128(v) => Some(*v),
            IntLit::BigInt(v) => {
                use num_traits::ToPrimitive;
                v.to_u128()
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

/// Explicit-suffix tag carried on `Token::Integer`, so a consumer can tell an
/// UNSUFFIXED numeral from a width-suffixed one. Bare digits (`42`) produce
/// `Unsuffixed`.
///
/// ⚠ This tag does NOT by itself decide which category a literal belongs to.
/// It once carried a `matches_i8` … `matches_usize` family that looked like it
/// did; that family had zero callers and was retired in 2026-07 (see the note in
/// the `impl` below). A category's literal domain is decided by that category's
/// own `eval`, which must accept exactly what its `pattern` declares.
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

    // ── ★ RETIRED 2026-07-25 (divergence I, Stage E) ────────────────────────────
    //
    // The `matches_i8` … `matches_usize` family lived here for two months with
    // **zero callers**. It was written as the guard that would keep a suffix out
    // of the wrong category ("rejecting e.g. `1u32` in an Int-typed position",
    // per this enum's own doc), and the only place that idea was ever wired in is
    // the doc comment at `macros/.../wpda_codegen/prefix.rs:381`, which describes
    // a trampoline arm the WPDA path does not emit.
    //
    // That is not a tidy-up: it is the reason divergence I was invisible. Reading
    // the code, a suffix/category guard APPEARED to exist, so `BigInt`'s eval —
    // `parse_int_lit(text, None)`, a universal acceptor contradicting its own
    // declared `…n` pattern — read as "the guard is elsewhere" rather than as the
    // hole it was. A documented-but-unread guard family is worse than no guard:
    // it is a false negative for every reviewer.
    //
    // The real guard is now where it can be neither bypassed nor overlooked — in
    // each category's own `eval`, which accepts EXACTLY the domain its `pattern`
    // declares (`languages/src/rholang.rs`, `languages/src/calculator.rs`).
    // `from_text` above is RETAINED: it is live (the lexer tags every
    // `Token::Integer` with it, and `BigInt`'s eval reads it to distinguish an
    // unsuffixed overflow from a width-suffixed one).
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
        // D1 fix (2026-05-13, refined): the `n` (BigInt) explicit suffix is
        // a "promote to arbitrary precision" annotation and always wins over
        // any fixed-width default (matches the pre-existing
        // `bigint_default_suffix_is_respected` contract).
        //
        // For FIXED-WIDTH explicit suffixes (i32/u32/i64/u64/i128/u128),
        // the suffix must match the fixed-width `default_suffix` hint
        // (or `default_suffix` must be None). This rejects `1u32` against
        // the Int category (which passes `Some(Suffix::I32)`) so the
        // user-facing `Int::parse("1u32").is_err()` test holds —
        // closes test_int_parse_rejects_u32_suffix and test_uint32_bitwise.
        // The BigInt-default path (`default_suffix == Some(BigInt)`) is
        // not constrained: BigInt is a "any-precision" type, and fixed-width
        // explicit suffixes naturally narrow to that fixed type.
        if !matches!(s, Suffix::BigInt) {
            if let Some(ref hint) = default_suffix {
                if !matches!(hint, Suffix::BigInt) && s != *hint {
                    return Err(());
                }
            }
        }
        return try_fit_type(&big, &s).ok_or(());
    }

    if let Some(ref hint) = default_suffix {
        return try_fit_type(&big, hint).ok_or(());
    }

    for candidate in
        [Suffix::I32, Suffix::U32, Suffix::I64, Suffix::U64, Suffix::I128, Suffix::U128]
    {
        if let Some(lit) = try_fit_type(&big, &candidate) {
            return Ok(lit);
        }
    }
    Ok(IntLit::BigInt(big))
}
