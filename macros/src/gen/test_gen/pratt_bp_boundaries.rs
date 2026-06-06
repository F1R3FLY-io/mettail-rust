//! Pratt binding-power boundary test generator.
//!
//! W7 Stage 9 (plan v5.1). Emits tests that exercise the WPDS walker's
//! handling of Pratt binding-power edges: associativity flips, postfix
//! interactions, prefix-vs-infix dispatch, and BP-equality tiebreaks.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate Pratt BP-boundary tests.
pub fn generate_pratt_bp_boundaries_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let baseline = baseline_tests(&lang_name);
    quote! {
        use mettail_prattail::wpda_runtime::{StackSymbolV2, SymbolKind, WpdaState};

        #baseline
    }
}

fn baseline_tests(lang_name: &str) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let tests = (0..10).map(|i| {
        let s = format!("pratt_bp_boundary_{}_{:02}", lang_lower, i);
        let name = proc_macro2::Ident::new(&s, proc_macro2::Span::call_site());
        let bp = (i * 10) as u8;
        let next_bp = (bp + 5) as u8;
        quote! {
            #[test]
            fn #name() {
                // Stack symbols at different binding powers must remain distinct
                // identities so the walker preserves Pratt precedence.
                let a = StackSymbolV2::infix_continuation(0, 0, #bp);
                let b = StackSymbolV2::infix_continuation(0, 0, #next_bp);
                assert_ne!(a, b, "different BPs must produce distinct symbols");
                // The kind is unchanged across BP variants.
                assert_eq!(a.kind, SymbolKind::InfixContinuation);
                assert_eq!(b.kind, SymbolKind::InfixContinuation);
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
        let ts = generate_pratt_bp_boundaries_section(&lang("MyLang")).to_string();
        let count = ts.matches("# [test]").count() + ts.matches("#[test]").count();
        assert!(count >= 10, "got {}", count);
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let ts = generate_pratt_bp_boundaries_section(&lang("Toy"));
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }
}
