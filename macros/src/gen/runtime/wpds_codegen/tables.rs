//! Category and rule-index static tables.
//!
//! These are emitted per-language by `generate_wpds_engine_module` and
//! establish the stable `(src_idx, rule_idx)` mapping used throughout the
//! WPDS engine's `LexicographicWeight` for tiebreak ordering.

use mettail_ast::grammar::GrammarRule;
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Emit the `WPDS_CATEGORIES: &[&str]` table entries (without the outer
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

/// Emit the per-category rule tables `&[&[(label, rule_idx)]]` entries
/// (without outer brackets).
///
/// Kept for backwards-compatibility with callers that haven't migrated to
/// `emit_rule_table_from_per_cat`. New code should use the per-cat variant
/// so synthetic literal rules appear in the table.
pub(crate) fn emit_rule_table(language: &LanguageDef, categories: &[String]) -> TokenStream {
    let mut per_cat: Vec<Vec<(String, u16)>> = vec![Vec::new(); categories.len()];
    let cat_idx: std::collections::HashMap<&str, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();
    for rule in &language.terms {
        let cat = rule.category.to_string();
        if let Some(&i) = cat_idx.get(cat.as_str()) {
            let next_idx = per_cat[i].len() as u16;
            per_cat[i].push((rule.label.to_string(), next_idx));
        }
    }
    let cat_entries = per_cat.into_iter().map(|rules| {
        let pairs = rules.into_iter().map(|(label, idx)| {
            quote! { (#label, #idx), }
        });
        quote! { &[ #(#pairs)* ], }
    });
    quote! { #(#cat_entries)* }
}
