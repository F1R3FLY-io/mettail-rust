//! Ground-term checking generation for MeTTaIL terms
//!
//! Generates per-category `is_ground()` methods that recursively check whether
//! a term contains any free variables. A ground term is fully concrete — all
//! leaf positions are literals or nullary constructors. Bound variables (inside
//! `Scope`) do not make a term non-ground.
//!
//! ## Motivation
//!
//! The previous `is_accepting()` implementation had two problems:
//! 1. **Wasteful**: For native types it called `try_eval()` which computes the
//!    full native value then discards it, only to be re-evaluated later.
//! 2. **Shallow**: For non-native types it only checked for bare variables at
//!    the top level, missing variables nested inside compound terms.
//!
//! `is_ground()` fixes both: zero arithmetic, deep recursive traversal.

use crate::ast::language::LanguageDef;
use crate::ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Ident;

use super::subst::{collect_category_variants, FieldInfo, VariantKind};

/// Generate `is_ground()` methods for all categories in the language.
///
/// Produces one `impl Cat { pub fn is_ground(&self) -> bool { ... } }` block
/// per category. The match arms cover every variant (grammar rules + auto-generated
/// Var, Literal, Lambda, Apply variants).
pub fn generate_is_ground_methods(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let category = &lang_type.name;
            let variants = collect_category_variants(category, language);
            let match_arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| generate_is_ground_arm(category, v))
                .collect();
            quote! {
                impl #category {
                    /// Returns `true` if this term contains no free variables.
                    ///
                    /// A ground term is fully concrete — all leaf positions are
                    /// literals or nullary constructors. Bound variables (inside
                    /// `Scope`) do not make a term non-ground.
                    pub fn is_ground(&self) -> bool {
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
fn generate_is_ground_arm(category: &Ident, variant: &VariantKind) -> TokenStream {
    match variant {
        VariantKind::Var { label } => {
            quote! { #category::#label(_) => false }
        },
        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => true }
        },
        VariantKind::Nullary { label } => {
            quote! { #category::#label => true }
        },
        VariantKind::Regular { label, fields } => generate_regular_arm(category, label, fields),
        VariantKind::Collection { label, coll_type, .. } => {
            let check = collection_all_ground(quote! { coll }, coll_type);
            quote! { #category::#label(ref coll) => #check }
        },
        VariantKind::Binder { label, pre_scope_fields, .. } => {
            generate_binder_arm(category, label, pre_scope_fields)
        },
        VariantKind::MultiBinder { label, pre_scope_fields, .. } => {
            generate_binder_arm(category, label, pre_scope_fields)
        },
    }
}

/// Generate the `all elements are ground` check for a collection, accounting
/// for the different iteration patterns of `HashBag` (yields `(&T, usize)`)
/// vs `Vec`/`HashSet` (yields `&T`).
fn collection_all_ground(name: TokenStream, coll_type: &CollectionType) -> TokenStream {
    match coll_type {
        CollectionType::HashBag => {
            quote! { #name.iter().all(|(x, _count)| x.is_ground()) }
        },
        CollectionType::Vec | CollectionType::HashSet => {
            quote! { #name.iter().all(|x| x.is_ground()) }
        },
    }
}

/// Generate the `is_ground` check for a single field, dispatching to
/// `collection_all_ground` for collection fields.
fn field_ground_check(field: &FieldInfo, name: &Ident) -> TokenStream {
    if field.is_collection {
        let coll_type = field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag);
        collection_all_ground(quote! { #name }, coll_type)
    } else {
        quote! { #name.is_ground() }
    }
}

/// Generate a match arm for a `Regular` variant (constructor with fields).
///
/// Pattern: `Cat::Label(f0, f1, ...)` where each field is checked recursively.
/// Collection fields use the appropriate iteration pattern for their type.
fn generate_regular_arm(category: &Ident, label: &Ident, fields: &[FieldInfo]) -> TokenStream {
    let field_names: Vec<Ident> = (0..fields.len()).map(|i| format_ident!("f{}", i)).collect();
    let field_patterns: Vec<TokenStream> = field_names
        .iter()
        .map(|n| quote! { ref #n })
        .collect();

    let checks: Vec<TokenStream> = fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_ground_check(field, name))
        .collect();

    // If there are no checks (shouldn't happen for Regular, but be safe), return true
    let body = if checks.is_empty() {
        quote! { true }
    } else {
        quote! { #(#checks)&&* }
    };

    quote! {
        #category::#label(#(#field_patterns),*) => #body
    }
}

/// Generate a match arm for a `Binder` or `MultiBinder` variant.
///
/// Pattern: `Cat::Label(f0, ..., scope)` where pre-scope fields are checked
/// recursively and the scope body is checked via `scope.inner().unsafe_body.is_ground()`.
fn generate_binder_arm(
    category: &Ident,
    label: &Ident,
    pre_scope_fields: &[FieldInfo],
) -> TokenStream {
    let field_names: Vec<Ident> = (0..pre_scope_fields.len())
        .map(|i| format_ident!("f{}", i))
        .collect();
    let field_patterns: Vec<TokenStream> = field_names
        .iter()
        .map(|n| quote! { ref #n })
        .collect();

    let field_checks: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_ground_check(field, name))
        .collect();

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(ref scope) }
    } else {
        quote! { #category::#label(#(#field_patterns,)* ref scope) }
    };

    let body_check = quote! { scope.inner().unsafe_body.is_ground() };

    let all_checks: Vec<&TokenStream> = field_checks
        .iter()
        .chain(std::iter::once(&body_check))
        .collect();

    quote! { #pattern => #(#all_checks)&&* }
}
