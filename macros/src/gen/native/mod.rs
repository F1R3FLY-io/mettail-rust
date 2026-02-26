//! Native type support generation
//!
//! Generates code for handling native Rust types mapped to language types.
//! Currently provides `eval()` for evaluating expressions to native values.
//!
//! This module is designed for expansion as more native type features are added.

use crate::ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::TypeExpr;
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

/// True if rule is list-literal style: single param of Vec-backed category with *sep(param, ...) in pattern.
/// Such rules use variant Cat::Label(Vec<elem>) so the parser can pass (elements) directly.
pub fn is_list_literal_rule(rule: &GrammarRule, language: &LanguageDef) -> bool {
    let context = match &rule.term_context {
        Some(c) if c.len() == 1 => c,
        _ => return false,
    };
    let TermParam::Simple { name: param_name, ty: TypeExpr::Base(cat) } = &context[0] else {
        return false;
    };
    if !language
        .types
        .iter()
        .find(|t| t.name == *cat)
        .and_then(|t| t.native_type.as_ref())
        .map_or(false, is_vec_native_type)
    {
        return false;
    }
    // Prefer pattern check: *sep(param, ...) with source None
    if let Some(pattern) = &rule.syntax_pattern {
        let param_str = param_name.to_string();
        if pattern.iter().any(|expr| {
            if let SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) = expr {
                collection.to_string() == param_str
            } else {
                false
            }
        }) {
            return true;
        }
    }
    // Fallback: single param of Vec-backed category that matches rule category (same-category list literal)
    if rule.category == *cat {
        return true;
    }
    false
}

/// For list literal rule, return the element category ident (e.g. Proc for List = Vec<Proc>).
pub fn list_literal_element_cat(rule: &GrammarRule, language: &LanguageDef) -> Option<Ident> {
    let context = rule.term_context.as_ref().filter(|c| c.len() == 1)?;
    let TermParam::Simple { ty: TypeExpr::Base(cat), .. } = &context[0] else {
        return None;
    };
    if !is_list_literal_rule(rule, language) {
        return None;
    }
    language
        .types
        .iter()
        .find(|t| t.name == *cat)
        .and_then(|t| t.native_type.as_ref())
        .and_then(vec_element_ident)
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
