//! Native type support generation
//!
//! Generates code for handling native Rust types mapped to language types.
//! Currently provides `eval()` for evaluating expressions to native values.
//!
//! This module is designed for expansion as more native type features are added.

use crate::ast::language::LanguageDef;
use syn::Ident;

pub mod eval;

/// Check if a category has a native type and return it
pub fn has_native_type<'a>(category: &Ident, language: &'a LanguageDef) -> Option<&'a syn::Type> {
    language
        .types
        .iter()
        .find(|t| t.name == *category)
        .and_then(|t| t.native_type.as_ref())
}

/// Get native type as string for comparison
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
        GenericArgument::Type(syn::Type::Path(t)) => t.path.get_ident().cloned().or_else(|| t.path.segments.last().map(|s| s.ident.clone())),
        _ => None,
    }
}
