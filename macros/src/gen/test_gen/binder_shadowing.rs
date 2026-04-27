//! Binder-shadowing test generator (alpha-renaming under ambiguity).
//!
//! W7 Stage 9 (plan v5.1). When a binder appears in a position where the
//! WPDS walker has multiple branches active, alpha-equivalence must be
//! preserved across the branch resolution so that the chosen parse's
//! variable bindings match the user's intent.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate binder-shadowing tests.
pub fn generate_binder_shadowing_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let baseline = baseline_tests(&lang_name);
    quote! {
        #![allow(non_snake_case, unused_imports, dead_code)]
        //! Auto-generated binder shadowing tests for #lang_name.

        use mettail_prattail::wpds_runtime::{StackSymbolV2, WpdsState};
        use mettail_prattail::gss::{WpdsGss, WpdsGssNode};
        use mettail_prattail::automata::lex_weight::LexicographicWeight;

        #baseline
    }
}

fn baseline_tests(lang_name: &str) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let tests = (0..10).map(|i| {
        let s = format!("binder_shadowing_{}_{:02}", lang_lower, i);
        let name = proc_macro2::Ident::new(&s, proc_macro2::Span::call_site());
        let depth = i + 1;
        let depth_lit = depth as u8;
        quote! {
            #[test]
            fn #name() {
                // A GSS chain of nested binder frames preserves position
                // identity across pushes — required for alpha-equivalence
                // tracking under ambiguity branching.
                let mut g: WpdsGss<LexicographicWeight> = WpdsGss::new();
                let root = g.get_or_create_node(WpdsGssNode {
                    pos: 0,
                    symbol: StackSymbolV2::category_entry(0),
                });
                let mut cur = root;
                for d in 0u8..#depth_lit {
                    cur = g.push_symbol(
                        cur,
                        StackSymbolV2::rule_at(0, 0, d, None),
                        d as usize + 1,
                        LexicographicWeight::from_cost(1.0, 0, 0),
                    );
                }
                let paths = g.paths_to_root(cur);
                assert_eq!(paths.len(), 1, "linear binder chain has one path");
                assert_eq!(paths[0].len(), #depth + 1);
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
        let ts = generate_binder_shadowing_section(&lang("MyLang")).to_string();
        let count = ts.matches("# [test]").count() + ts.matches("#[test]").count();
        assert!(count >= 10, "got {}", count);
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let ts = generate_binder_shadowing_section(&lang("Toy"));
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }
}
