//! Unification/matching rule generation.
//!
//! This module generates directional matching relations:
//! `unifies_<cat>(pattern, value)`.

use crate::ast::language::LanguageDef;
use crate::gen::generate_var_label;
use proc_macro2::TokenStream;
use quote::quote;

use super::common::{in_cat_filter, relation_names, CategoryFilter};

/// Generate unification rules for all categories in scope.
///
/// Current phase implements:
/// - eq-lifted matching: `eq_cat(p, v) => unifies_cat(p, v)`
/// - wildcard pattern variable: `Cat::VarLabel(_)` on pattern side matches any value
pub fn generate_unification_rules(
    language: &LanguageDef,
    cat_filter: CategoryFilter,
) -> TokenStream {
    let mut rules = Vec::new();

    for lang_type in &language.types {
        let category = &lang_type.name;
        if !in_cat_filter(category, cat_filter) {
            continue;
        }
        let rn = relation_names(category);
        let unifies_rel = quote::format_ident!("unifies_{}", rn.cat_lower);
        let cat = rn.cat;
        let cat_lower = rn.cat_lower;
        let var_label = generate_var_label(&cat);

        rules.push(quote! {
            #unifies_rel(pat_u.clone(), val_u.clone()) <--
                #cat_lower(pat_u),
                #cat_lower(val_u),
                if pat_u == val_u;
        });
        rules.push(quote! {
            #unifies_rel(pat_u.clone(), val_u.clone()) <--
                #cat_lower(pat_u),
                #cat_lower(val_u),
                if let #cat::#var_label(_) = pat_u.clone();
        });
        rules.push(quote! {
            #unifies_rel(pat_u.clone(), val_u.clone()) <--
                #cat_lower(pat_u),
                #cat_lower(val_u),
                if pat_u.pattern_matches(&val_u);
        });
    }

    quote! { #(#rules)* }
}
