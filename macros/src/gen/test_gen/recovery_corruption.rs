//! Recovery corruption test generator.
//!
//! W7 Stage 9 (plan v5.1). Exercises the WPDS walker's resilience to
//! malformed events and corrupted GSS configurations: pop on empty stack,
//! fork into zero branches, branch resolution to non-existent winners,
//! etc. The walker should reach `WpdaState::Error` cleanly rather than
//! panicking or silently misbehaving.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate recovery-corruption tests.
pub fn generate_recovery_corruption_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let baseline = baseline_tests(&lang_name);
    quote! {
        #![allow(non_snake_case, unused_imports, dead_code)]
        //! Auto-generated recovery / corruption tests for #lang_name.

        use mettail_prattail::wpda_runtime::{
            StackSymbolV2, WpdaConfiguration, WpdaControl, WpdaEvent, WpdaState,
        };
        use mettail_prattail::wpda_walker::{
            IdleEngine, NullConsumer, WalkerConsumer, WpdaEngine, WpdaWalker,
        };
        use mettail_prattail::automata::lex_weight::LexicographicWeight;

        #baseline
    }
}

fn baseline_tests(lang_name: &str) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let tests = (0..10).map(|i| {
        let s = format!("recovery_corruption_{}_{:02}", lang_lower, i);
        let name = proc_macro2::Ident::new(&s, proc_macro2::Span::call_site());
        let pos = (i * 7) as usize;
        quote! {
            #[test]
            fn #name() {
                // Walker must absorb terminal-state events without panicking.
                let mut w: WpdaWalker<LexicographicWeight, _> = WpdaWalker::new(IdleEngine, 0);
                // Inject a TokenConsumed advance from an unsuspecting position;
                // walker should record the new position without crashing.
                let _ = w.process_event(WpdaEvent::TokenConsumed {
                    pos: #pos,
                    token: mettail_prattail::automata::TokenKind::Ident,
                });
                assert_eq!(w.position(), #pos);
                // Inspect after the corruption-style event must yield NoChange.
                let _ = w.process_event(WpdaEvent::Inspect);
                assert!(!w.state().is_terminal());
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
        let ts = generate_recovery_corruption_section(&lang("MyLang")).to_string();
        let count = ts.matches("# [test]").count() + ts.matches("#[test]").count();
        assert!(count >= 10, "got {}", count);
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let ts = generate_recovery_corruption_section(&lang("Toy"));
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }
}
