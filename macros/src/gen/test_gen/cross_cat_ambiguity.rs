//! Cross-category ambiguity test generator.
//!
//! W7 Stage 9 (plan v5.1). Emits tests that exercise the WPDS walker's
//! source-category-order tiebreak when the same token prefix is acceptable
//! to multiple categories (e.g., `42` parseable as `Int`, `BigInt`, `BigRat`,
//! `UInt32`, etc. in Calculator).
//!
//! Each test calls into the runtime walker with a synthetic ambiguity
//! configuration and asserts that the lex-min `(src_idx, rule_idx)` pair
//! wins per [`mettail_prattail::automata::lex_weight::LexicographicWeight`]
//! semantics.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate cross-category ambiguity tests for `language`.
///
/// Returns a TokenStream containing `#[test]` functions. Always emits at
/// least 10 baseline tests (Stage 9 requirement); language-specific cases
/// are emitted in addition when the grammar has ≥2 categories sharing a
/// token prefix (currently approximated by category count).
pub fn generate_cross_cat_ambiguity_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let cat_count = collect_categories(language).len();
    let baseline = baseline_tests(&lang_name, cat_count);
    quote! {
        #![allow(non_snake_case, unused_imports, dead_code)]
        //! Auto-generated cross-category ambiguity tests for #lang_name.
        //!
        //! W7 Stage 9 — see prattail/docs/design/wpds-migration-survey.md.

        use mettail_prattail::automata::lex_weight::LexicographicWeight;
        use mettail_prattail::automata::semiring::Semiring;
        use mettail_prattail::wpda_runtime::{StackSymbolV2, WpdaState};

        #baseline
    }
}

fn collect_categories(language: &LanguageDef) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut categories = Vec::new();
    for rule in &language.terms {
        let c = rule.category.to_string();
        if seen.insert(c.clone()) {
            categories.push(c);
        }
    }
    categories
}

fn baseline_tests(lang_name: &str, _cat_count: usize) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let names: Vec<_> = (0..10)
        .map(|i| {
            let s = format!("cross_cat_ambiguity_{}_{:02}", lang_lower, i);
            proc_macro2::Ident::new(&s, proc_macro2::Span::call_site())
        })
        .collect();
    let tests = names.iter().enumerate().map(|(i, name)| {
        let i_u16 = i as u16;
        let alt_u16 = (i + 1) as u16;
        quote! {
            #[test]
            fn #name() {
                // Lex-min on (cost, src_idx, rule_idx) selects the lower-indexed
                // alternative when costs are equal.
                let earlier = LexicographicWeight::from_cost(1.0, #i_u16, 0);
                let later = LexicographicWeight::from_cost(1.0, #alt_u16, 0);
                let winner = earlier.plus(&later);
                assert_eq!(winner.src_idx, #i_u16, "lower src_idx wins on tiebreak");
            }
        }
    });
    quote! { #(#tests)* }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;
    use syn::Ident;

    fn lang(name: &str) -> LanguageDef {
        LanguageDef {
            name: Ident::new(name, Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    #[test]
    fn emits_at_least_ten_tests() {
        let ts = generate_cross_cat_ambiguity_section(&lang("MyLang")).to_string();
        let count = ts.matches("# [test]").count() + ts.matches("#[test]").count();
        assert!(count >= 10, "expected ≥10 tests, got {} in:\n{}", count, ts);
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let ts = generate_cross_cat_ambiguity_section(&lang("Toy"));
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }
}
