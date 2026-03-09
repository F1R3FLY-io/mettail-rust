//! Term-depth measurement generation for MeTTaIL terms (A-RT05)
//!
//! Generates per-category `term_depth()` methods that recursively compute the
//! maximum nesting depth of a term. Used by the post-fixpoint convergence check
//! to detect unbounded term growth during Ascent evaluation.
//!
//! ## Depth semantics
//!
//! - Variables: depth 0
//! - Literals: depth 0
//! - Nullary constructors: depth 0
//! - Constructor application: 1 + max(field depths)
//! - Collections: 1 + max(element depths)
//! - Binders: 1 + max(pre-scope field depths, body depth)

use crate::ast::language::LanguageDef;
use crate::ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Generate `term_depth()` methods for all categories in the language.
///
/// Produces one `impl Cat { pub fn term_depth(&self) -> u32 { ... } }` block
/// per category. The match arms cover every variant (grammar rules + auto-generated
/// Var, Literal, Lambda, Apply variants).
pub fn generate_term_depth_methods(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let category = &lang_type.name;
            let variants = collect_category_variants(category, language);
            let match_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_depth_arm(category, v))
                .collect();
            quote! {
                impl #category {
                    /// Compute the maximum nesting depth of this term.
                    ///
                    /// - Leaves (variables, literals, nullary constructors): 0
                    /// - Constructors: 1 + max(child depths)
                    /// - Collections: 1 + max(element depths)
                    /// - Binders: 1 + max(pre-scope fields, body)
                    ///
                    /// Used by A-RT05 post-fixpoint convergence check.
                    pub fn term_depth(&self) -> u32 {
                        match self {
                            #(#match_arms),*
                        }
                    }
                }
            }
        })
        .collect();
    quote! { #(#impls)* }
}

/// Generate a single match arm for one variant of a category.
fn generate_depth_arm(category: &Ident, variant: &VariantKind) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            quote! { #category::#label(_) => 0 }
        }
        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => 0 }
        }
        VariantKind::Nullary { label } => {
            quote! { #category::#label => 0 }
        }
        VariantKind::Regular { label, fields } => generate_regular_depth_arm(category, label, fields),
        VariantKind::Collection { label, coll_type, .. } => {
            let max_elem = collection_max_depth(quote! { coll }, coll_type);
            quote! { #category::#label(coll) => 1 + #max_elem }
        }
        VariantKind::Binder {
            label,
            pre_scope_fields,
            ..
        } => generate_binder_depth_arm(category, label, pre_scope_fields),
        VariantKind::MultiBinder {
            label,
            pre_scope_fields,
            ..
        } => generate_binder_depth_arm(category, label, pre_scope_fields),
    }
}

/// Compute max depth across elements of a collection.
fn collection_max_depth(name: TokenStream, coll_type: &CollectionType) -> TokenStream {
    match coll_type {
        CollectionType::HashBag => {
            quote! { #name.iter().map(|(x, _count)| x.term_depth()).max().unwrap_or(0) }
        }
        CollectionType::Vec | CollectionType::HashSet => {
            quote! { #name.iter().map(|x| x.term_depth()).max().unwrap_or(0) }
        }
    }
}

/// Compute depth contribution of a single field.
fn field_depth_expr(field: &FieldInfo, name: &Ident) -> TokenStream {
    if field.is_collection {
        let coll_type = field
            .coll_type
            .as_ref()
            .unwrap_or(&CollectionType::HashBag);
        collection_max_depth(quote! { #name }, coll_type)
    } else {
        quote! { #name.term_depth() }
    }
}

/// Generate a match arm for a `Regular` variant (constructor with fields).
fn generate_regular_depth_arm(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    let depth_exprs: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_depth_expr(field, name))
        .collect();

    // max of all field depths, then + 1
    let body = if depth_exprs.is_empty() {
        quote! { 0 }
    } else if depth_exprs.len() == 1 {
        let d = &depth_exprs[0];
        quote! { 1 + #d }
    } else {
        // Chain of .max() calls
        let first = &depth_exprs[0];
        let rest = &depth_exprs[1..];
        let mut chain = quote! { #first };
        for d in rest {
            chain = quote! { (#chain).max(#d) };
        }
        quote! { 1 + #chain }
    };

    quote! {
        #category::#label(#(#field_names),*) => #body
    }
}

/// Generate a match arm for a `Binder` or `MultiBinder` variant.
fn generate_binder_depth_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();

    let field_depth_exprs: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_depth_expr(field, name))
        .collect();

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };

    let body_depth = quote! { scope.inner().unsafe_body.term_depth() };

    // Combine: 1 + max(all field depths, body depth)
    let mut all_exprs: Vec<&TokenStream> = field_depth_exprs.iter().collect();
    let body_depth_ref = &body_depth;
    all_exprs.push(body_depth_ref);

    let body = if all_exprs.len() == 1 {
        let d = all_exprs[0];
        quote! { 1 + #d }
    } else {
        let first = all_exprs[0];
        let rest = &all_exprs[1..];
        let mut chain = quote! { #first };
        for d in rest {
            chain = quote! { (#chain).max(#d) };
        }
        quote! { 1 + #chain }
    };

    quote! { #pattern => #body }
}
