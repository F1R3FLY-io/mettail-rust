//! Original richer native-type vocabulary and exact classification helpers.
//!
//! Relocated from macro generation without changing its variants or policies.
//! This is distinct from NativeKind: collection wrappers and Other spellings
//! are needed by existing constructor-label and backend consumers.

/// Typed representation of a native Rust type mapped to a language category.
/// Eliminates string comparisons on type names throughout code generation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum NativeType {
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Isize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Usize,
    Float32,
    Float64,
    Bool,
    /// Rust `str` or `String` — string types
    Str,
    /// Arbitrary-precision integer wrapper (`mettail_runtime::CanonicalBigInt`,
    /// or any user wrapper whose last path segment ends in `BigInt`).
    CanonicalBigInt,
    /// Arbitrary-precision rational wrapper (`mettail_runtime::CanonicalBigRat`).
    CanonicalBigRat,
    /// Fixed-point decimal wrapper (`mettail_runtime::CanonicalFixedPoint`).
    CanonicalFixedPoint,
    /// Vector collection wrapper (`Vec<T>` — outer type `Vec`).
    VecCollection,
    /// Multiset collection wrapper (`HashBag<T>` — outer type `HashBag`).
    HashBagCollection,
    /// Set collection wrapper (`HashSet<T>` — outer type `HashSet`).
    HashSetCollection,
    /// Runtime map wrapper (`HashMapLit<K, V>` — outer type `HashMapLit`).
    HashMapLitCollection,
    /// Runtime HashMap wrapper shorthand (`HashMap<K, V>` in user-facing spec).
    /// Parsed to `HashMapLit` at the AST layer; surfaces here when code inspects
    /// native-type strings directly.
    HashMapCollection,
    /// Unknown or unsupported native type
    Other(String),
}

impl NativeType {
    /// Parse a native type string into a `NativeType` enum variant.
    pub fn from_type_str(s: &str) -> Self {
        match s {
            "i8" => Self::Int8,
            "i16" => Self::Int16,
            "i32" => Self::Int32,
            "i64" => Self::Int64,
            "i128" => Self::Int128,
            "isize" => Self::Isize,
            "u8" => Self::UInt8,
            "u16" => Self::UInt16,
            "u32" => Self::UInt32,
            "u64" => Self::UInt64,
            "u128" => Self::UInt128,
            "usize" => Self::Usize,
            "f32" => Self::Float32,
            "f64" => Self::Float64,
            "bool" => Self::Bool,
            "str" | "String" => Self::Str,
            "CanonicalBigRat" => Self::CanonicalBigRat,
            "CanonicalFixedPoint" => Self::CanonicalFixedPoint,
            "Vec" => Self::VecCollection,
            "HashBag" => Self::HashBagCollection,
            "HashSet" => Self::HashSetCollection,
            "HashMapLit" => Self::HashMapLitCollection,
            "HashMap" => Self::HashMapCollection,
            // Any user wrapper whose last path segment ends with "BigInt"
            // (e.g. `CanonicalBigInt`, `mettail_runtime::CanonicalBigInt`)
            // is treated as the arbitrary-precision integer category.
            other if other.ends_with("BigInt") => Self::CanonicalBigInt,
            other => Self::Other(other.to_string()),
        }
    }

    /// Whether this is an integer type (including `CanonicalBigInt`).
    #[inline]
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Self::Int8
                | Self::Int16
                | Self::Int32
                | Self::Int64
                | Self::Int128
                | Self::Isize
                | Self::UInt8
                | Self::UInt16
                | Self::UInt32
                | Self::UInt64
                | Self::UInt128
                | Self::Usize
                | Self::CanonicalBigInt
        )
    }

    /// Whether this is a floating-point type.
    #[inline]
    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float32 | Self::Float64)
    }

    /// Whether this is a string type (str or String).
    #[inline]
    pub fn is_string(&self) -> bool {
        matches!(self, Self::Str)
    }

    /// Whether this is a known collection wrapper type.
    #[inline]
    pub fn is_collection(&self) -> bool {
        matches!(
            self,
            Self::VecCollection
                | Self::HashBagCollection
                | Self::HashSetCollection
                | Self::HashMapLitCollection
                | Self::HashMapCollection
        )
    }
}
