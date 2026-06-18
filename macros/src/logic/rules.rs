//! Freshness-function generation retained after the Ascent rule generator
//! was retired (P6).
//!
//! `generate_freshness_functions` emits the `is_fresh` helper used by the
//! Dovetail binder/congruence path; the former Ascent clause generators
//! (`generate_rule_clause` et al.) were removed.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

pub fn generate_freshness_functions(_language: &LanguageDef) -> TokenStream {
    quote! {
        pub fn is_fresh<T>(binder: &mettail_runtime::Binder<String>, term: &T) -> bool
        where
            T: mettail_runtime::BoundTerm<String>
        {
            use mettail_runtime::BoundTerm;

            let mut is_fresh = true;
            term.visit_vars(&mut |v| {
                if let mettail_runtime::Var::Free(fv) = v {
                    if fv == &binder.0 {
                        is_fresh = false;
                    }
                }
            });

            is_fresh
        }
    }
}
