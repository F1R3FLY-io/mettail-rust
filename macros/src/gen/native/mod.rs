//! Native type support generation
//!
//! Generates code for handling native Rust types mapped to language types.
//! Currently provides `eval()` for evaluating expressions to native values.
//!
//! This module is designed for expansion as more native type features are added.

use mettail_ast::language::LanguageDef;
use syn::Ident;

pub mod eval;
pub mod rust_code_rewrite;

/// Typed representation of a native Rust type mapped to a language category.
/// Eliminates string comparisons on type names throughout code generation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NativeType {
    Int32,
    Int64,
    Isize,
    Usize,
    UInt32,
    UInt64,
    Float32,
    Float64,
    Bool,
    /// Rust `str` or `String` — string types
    Str,
    /// Unknown or unsupported native type
    Other(String),
}

impl NativeType {
    /// Parse a native type string into a `NativeType` enum variant.
    pub fn from_type_str(s: &str) -> Self {
        match s {
            "i32" => Self::Int32,
            "i64" => Self::Int64,
            "isize" => Self::Isize,
            "usize" => Self::Usize,
            "u32" => Self::UInt32,
            "u64" => Self::UInt64,
            "f32" => Self::Float32,
            "f64" => Self::Float64,
            "bool" => Self::Bool,
            "str" | "String" => Self::Str,
            other => Self::Other(other.to_string()),
        }
    }

    /// Parse from a `syn::Type`.
    pub fn from_syn_type(ty: &syn::Type) -> Self {
        Self::from_type_str(&native_type_to_string(ty))
    }

    /// Whether this is an integer type.
    #[inline]
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Int32 | Self::Int64 | Self::Isize | Self::Usize | Self::UInt32 | Self::UInt64)
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

    /// Whether this is a boolean type.
    #[inline]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Get the Rust type name as a string (for code generation).
    pub fn as_rust_str(&self) -> &str {
        match self {
            Self::Int32 => "i32",
            Self::Int64 => "i64",
            Self::Isize => "isize",
            Self::Usize => "usize",
            Self::UInt32 => "u32",
            Self::UInt64 => "u64",
            Self::Float32 => "f32",
            Self::Float64 => "f64",
            Self::Bool => "bool",
            Self::Str => "str",
            Self::Other(s) => s,
        }
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
