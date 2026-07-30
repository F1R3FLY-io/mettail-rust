//! Native type support generation
//!
//! Generates code for handling native Rust types mapped to language types.
//! Currently provides `eval()` for evaluating expressions to native values.
//!
//! This module is designed for expansion as more native type features are added.

use mettail_ast::language::LanguageDef;
use syn::Ident;

pub mod eval;
pub mod lossless_coercion;
pub mod rust_code_rewrite;

/// Typed representation of a native Rust type mapped to a language category.
/// Eliminates string comparisons on type names throughout code generation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

    /// Parse from a `syn::Type`.
    pub fn from_syn_type(ty: &syn::Type) -> Self {
        Self::from_type_str(&native_type_to_string(ty))
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

/// Check if a category has a native type and return it
pub fn has_native_type<'a>(category: &Ident, language: &'a LanguageDef) -> Option<&'a syn::Type> {
    language
        .types
        .iter()
        .find(|t| t.name == *category)
        .and_then(|t| t.native_type.as_ref())
}

/// Get native type as string for comparison.
/// Prefer `NativeType::from_syn_type()` for typed comparisons.
///
/// Returns the **last segment** of the path (not the full path). Callers that
/// need a fully-qualified type expression for code emission should use
/// [`native_type_to_full_string`] instead.
pub fn native_type_to_string(native_type: &syn::Type) -> String {
    match native_type {
        syn::Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.last() {
                segment.ident.to_string()
            } else {
                "unknown".to_string()
            }
        },
        _ => "unknown".to_string(),
    }
}

/// Get the full path of a native type as a string (e.g., `mettail_runtime::CanonicalBigRat`).
/// Used when emitting Rust source code that needs the type to resolve at the emission site.
pub fn native_type_to_full_string(native_type: &syn::Type) -> String {
    use quote::ToTokens;
    let mut s = native_type.to_token_stream().to_string();
    // Collapse whitespace introduced by the token stream's display (e.g. `mettail_runtime :: CanonicalBigRat`)
    while s.contains(" :: ") {
        s = s.replace(" :: ", "::");
    }
    s
}

/// Is this native type the BYTE-SEQUENCE carrier `Vec<u8>`?
///
/// # Why this is a predicate on the `syn::Type` and not a [`NativeType`] variant
///
/// [`NativeType::from_type_str`] classifies by the type's LAST PATH SEGMENT alone, so it cannot
/// tell `Vec<u8>` from `Vec<Proc>` — both are the string `"Vec"`. The distinction is in the
/// generic ARGUMENT, which only the full `syn::Type` carries. Rather than widen
/// `from_type_str`'s contract (its callers pass bare names such as `"HashSetLit"`), the byte
/// question is asked here, of the type, by every site that needs it.
///
/// # Why the byte carrier is not a collection
///
/// A `Vec<Proc>` is a COLLECTION of terms: it is declared `as List`, it carries collection
/// delimiters, its elements are themselves renderable terms, and `DisplayTask::DisplayProc`
/// exists for them. A `Vec<u8>` is a SCALAR VALUE that happens to be backed by a vector: `u8`
/// is not a category, there is no `DisplayTask::Displayu8`, and its surface is one indivisible
/// literal (`b"deadbeef"`) rather than a delimited sequence of element surfaces. Treating it as
/// a collection is exactly what produced the measured defect — the byte carrier rendered with
/// EMPTY open/close delimiters, so `Bytes::…(vec![])` displayed as the empty string and no
/// byte value round-tripped at all.
///
/// Three sites share this one predicate, so the classification cannot drift between them:
///
/// 1. [`crate::gen::generate_literal_label`] — names the AST variant `BytesLit`, not `ListLit`.
/// 2. `crate::gen::syntax::display` — emits the `b"<hex>"` arm ahead of the collection arm.
/// 3. `crate::gen::runtime::wpda_codegen::prefix` — routes it to `LiteralFamily::Custom`.
pub fn is_byte_vector(native_type: &syn::Type) -> bool {
    let syn::Type::Path(type_path) = native_type else {
        return false;
    };
    let Some(segment) = type_path.path.segments.last() else {
        return false;
    };
    if segment.ident != "Vec" {
        return false;
    }
    let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
        return false;
    };
    if args.args.len() != 1 {
        return false;
    }
    match args.args.first() {
        Some(syn::GenericArgument::Type(syn::Type::Path(elem))) => {
            elem.path.segments.last().is_some_and(|s| s.ident == "u8")
        },
        _ => false,
    }
}

/// Extract the element type Ident from a collection native type (e.g. Vec<Proc> -> Proc, HashBag<Proc> -> Proc).
pub fn native_type_element_ident(native_type: &syn::Type) -> Option<Ident> {
    use syn::GenericArgument;
    let path = match native_type {
        syn::Type::Path(t) => &t.path,
        _ => return None,
    };
    let segment = path.segments.last()?;
    let args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(a) => &a.args,
        _ => return None,
    };
    let first = args.first()?;
    match first {
        GenericArgument::Type(syn::Type::Path(t)) => t
            .path
            .get_ident()
            .cloned()
            .or_else(|| t.path.segments.last().map(|s| s.ident.clone())),
        _ => None,
    }
}
