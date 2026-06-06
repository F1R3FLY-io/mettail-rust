//! Category and rule-index static tables.
//!
//! These are emitted per-language by `generate_wpda_engine_module` and
//! establish the stable `(src_idx, rule_idx)` mapping used throughout the
//! WPDS engine's `LexicographicWeight` for tiebreak ordering.

use mettail_ast::grammar::GrammarRule;
use proc_macro2::TokenStream;
use quote::quote;

/// Emit the `WPDA_CATEGORIES: &[&str]` table entries (without the outer
/// `&[...]` brackets — caller wraps).
pub(crate) fn emit_category_table(categories: &[String]) -> TokenStream {
    let entries = categories.iter().map(|c| quote! { #c, });
    quote! { #(#entries)* }
}

/// Emit per-category rule tables from a combined user + synthetic list.
///
/// `per_cat[i]` is the full list of rules for category `i` in source-index
/// order. Each rule's index in its category's list becomes its `rule_idx`.
pub(crate) fn emit_rule_table_from_per_cat(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let cat_entries = per_cat.iter().map(|rules| {
        let pairs = rules.iter().enumerate().map(|(idx, rule)| {
            let label = rule.label.to_string();
            let idx_u16 = idx as u16;
            quote! { (#label, #idx_u16), }
        });
        quote! { &[ #(#pairs)* ], }
    });
    quote! { #(#cat_entries)* }
}
