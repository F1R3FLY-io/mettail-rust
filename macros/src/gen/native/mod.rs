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

/// True if the native type is a collection (Vec or HashBag) that does not implement Display.
/// Used to emit Debug formatting (`{:?}`) instead of Display (`{}`) in generated code.
pub fn is_collection_native_type(native_type: &syn::Type) -> bool {
    match native_type {
        syn::Type::Path(type_path) => type_path
            .path
            .segments
            .first()
            .map(|s| {
                let name = s.ident.to_string();
                name == "Vec" || name == "HashBag"
            })
            .unwrap_or(false),
        _ => false,
    }
}

/// True if the native type is Vec<T> (used for List category traversal).
pub fn is_vec_native_type(native_type: &syn::Type) -> bool {
    match native_type {
        syn::Type::Path(type_path) => type_path
            .path
            .segments
            .first()
            .map(|s| s.ident.to_string() == "Vec")
            .unwrap_or(false),
        _ => false,
    }
}

/// For Vec<T>, return the Ident of the element type T (e.g. Proc for Vec<Proc>).
/// Used to generate substitution/normalize traversal over list elements.
pub fn vec_element_ident(native_type: &syn::Type) -> Option<syn::Ident> {
    use syn::GenericArgument;
    let type_path = match native_type {
        syn::Type::Path(t) => t,
        _ => return None,
    };
    let segment = type_path.path.segments.last()?;
    let args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(a) => &a.args,
        _ => return None,
    };
    let first_arg = args.first()?;
    let inner_type = match first_arg {
        GenericArgument::Type(t) => t,
        _ => return None,
    };
    if let syn::Type::Path(inner_path) = inner_type {
        inner_path.path.get_ident().cloned()
    } else {
        None
    }
}
