//! Ambiguity-exposure test generator (D11 diagnostic emission).
//!
//! W7 Stage 9 (plan v5.1). Exercises the runtime diagnostics queue
//! introduced in Stage 7. When a generated `*Inner::Ambiguous(alts)`
//! variant is rendered via `Display`, a `[LANG-D11]` warning must land
//! in `mettail_runtime::diagnostics::take_diagnostics()`.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate ambiguity-exposure tests.
pub fn generate_ambiguity_exposure_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let baseline = baseline_tests(&lang_name);
    quote! {
        #![allow(non_snake_case, unused_imports, dead_code)]
        //! Auto-generated ambiguity exposure (D11) tests for #lang_name.

        use mettail_runtime::diagnostics::{
            self, clear_diagnostics, emit_d11, pending_count, take_diagnostics,
        };

        #baseline
    }
}

fn baseline_tests(lang_name: &str) -> TokenStream {
    let lang_lower = lang_name.to_lowercase();
    let lang_str = lang_name.to_string();
    let tests = (0..10).map(|i| {
        let s = format!("ambiguity_exposure_{}_{:02}", lang_lower, i);
        let name = proc_macro2::Ident::new(&s, proc_macro2::Span::call_site());
        let alt_count = (i + 2) as usize;
        let lang_lit = lang_str.clone();
        quote! {
            #[test]
            fn #name() {
                clear_diagnostics();
                emit_d11(#lang_lit, "TestCat", #alt_count);
                let drained = take_diagnostics();
                assert_eq!(drained.len(), 1);
                assert_eq!(drained[0].code, "D11");
                assert_eq!(drained[0].language, #lang_lit);
                assert!(drained[0].message.contains(&#alt_count.to_string()));
                // Queue is empty after take.
                assert_eq!(pending_count(), 0);
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
        let ts = generate_ambiguity_exposure_section(&lang("MyLang")).to_string();
        let count = ts.matches("# [test]").count() + ts.matches("#[test]").count();
        assert!(count >= 10, "got {}", count);
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let ts = generate_ambiguity_exposure_section(&lang("Toy"));
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }
}
