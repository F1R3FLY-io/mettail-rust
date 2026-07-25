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

use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
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
        // A SCALAR literal is ground by construction: its payload is a native value
        // (`i64`, `String`, `CanonicalBigRat`, …) with no term structure, so there is
        // nothing to descend into and no position a free variable could occupy.
        VariantKind::Literal { label } => {
            quote! { #category::#label(_) => true }
        },
        // ★ #29 (collection-literal Stage 2). A COLLECTION literal is NOT ground by
        // construction — its payload is a container OF TERMS, each of which may be a
        // free variable. This arm previously shared the scalar arm and answered `true`
        // unconditionally, so `[1, v]` reported ground with `v` free.
        //
        // That is a contract violation in the FAILURE direction, which is the dangerous
        // one: `is_ground` is consulted to decide whether a term may be treated as a
        // finished value, so a false `true` licenses downstream code to skip work that
        // was actually required, and it does so silently. A false `false` would merely
        // cost a redundant descent.
        //
        // The descent is the same `collection_all_ground` every non-literal collection
        // field already uses, so this arm now agrees with `VariantKind::Collection` and
        // with `field_ground_check`'s collection branch rather than contradicting them.
        VariantKind::CollectionLiteral { label, coll_type, .. } => {
            let check = collection_all_ground(quote! { coll }, coll_type);
            quote! { #category::#label(coll) => #check }
        },
        VariantKind::Nullary { label } => {
            quote! { #category::#label => true }
        },
        VariantKind::Regular { label, fields } => generate_regular_arm(category, label, fields),
        VariantKind::Collection { label, coll_type, .. } => {
            let check = collection_all_ground(quote! { coll }, coll_type);
            quote! { #category::#label(coll) => #check }
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
/// for the different iterator item shapes:
/// HashBag -> `(&T, usize)`, HashMapLit -> `(&K, &V)`,
/// Vec/HashSet -> `&T`.
fn collection_all_ground(name: TokenStream, coll_type: &CollectionType) -> TokenStream {
    match coll_type {
        CollectionType::HashBag => {
            quote! { #name.iter().all(|(x, _count)| x.is_ground()) }
        },
        CollectionType::Vec | CollectionType::HashSet => {
            quote! { #name.iter().all(|x| x.is_ground()) }
        },
        CollectionType::HashMap | CollectionType::PathMap => {
            quote! { #name.iter().all(|(k, v)| k.is_ground() && v.is_ground()) }
        },
    }
}

/// Generate the `is_ground` check for a single field, dispatching to
/// `collection_all_ground` for collection fields.
fn field_ground_check(field: &FieldInfo, name: &Ident) -> TokenStream {
    // Phase 3A-C1 (predicated types): a `BehavioralPred` field is
    // always trivially "ground" from the host-category perspective.
    // Variables inside a predicate (e.g., `halts(y)` referencing a
    // pattern-bound `y`) are bound by the parent's `MatchBindings`,
    // not by host-category `FreeVar<String>`s.
    let _ = name;
    // L9-3: a token-text capture (`String`) is a ground leaf — a token's text
    // contains no host-category free variables (mirrors the predicate leaf).
    if field.is_predicate || field.is_opaque_leaf() {
        return quote! { true };
    }
    let _ = name;
    if field.is_optional {
        // Phase 4 #3 (2026-05-12): Optional-Collection — None is
        // trivially ground; Some(c) is ground iff every element is.
        if field.is_collection {
            let coll_type = field.coll_type.as_ref().unwrap_or(&CollectionType::HashBag);
            let inner = collection_all_ground(quote! { __c }, coll_type);
            return quote! { #name.as_ref().map(|__c| #inner).unwrap_or(true) };
        }
        // Opt-Group: None is trivially ground (no variables); Some(b)
        // is ground iff inner is ground.
        return quote! { #name.as_ref().map(|__b| __b.is_ground()).unwrap_or(true) };
    }
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
    let suppress_unused = field_names.iter().map(|name| quote! { let _ = #name; });

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
        #category::#label(#(#field_names),*) => {
            #(#suppress_unused)*
            #body
        }
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
    let suppress_unused = field_names.iter().map(|name| quote! { let _ = #name; });

    let field_checks: Vec<TokenStream> = pre_scope_fields
        .iter()
        .zip(field_names.iter())
        .map(|(field, name)| field_ground_check(field, name))
        .collect();

    let pattern = if field_names.is_empty() {
        quote! { #category::#label(scope) }
    } else {
        quote! { #category::#label(#(#field_names,)* scope) }
    };

    let body_check = quote! { scope.inner().unsafe_body.is_ground() };

    let all_checks: Vec<&TokenStream> = field_checks
        .iter()
        .chain(std::iter::once(&body_check))
        .collect();

    quote! {
        #pattern => {
            #(#suppress_unused)*
            #(#all_checks)&&*
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collection_ground_hashmap_checks_keys_and_values() {
        let generated =
            collection_all_ground(quote! { coll }, &CollectionType::HashMap).to_string();
        assert!(
            generated.contains("k . is_ground") && generated.contains("v . is_ground"),
            "HashMap groundness must inspect both keys and values: {}",
            generated,
        );
    }

    #[test]
    fn collection_ground_hashbag_uses_counted_items() {
        let generated =
            collection_all_ground(quote! { coll }, &CollectionType::HashBag).to_string();
        assert!(
            generated.contains("_count") && generated.contains("x . is_ground"),
            "HashBag groundness must inspect counted items: {}",
            generated,
        );
    }
}
