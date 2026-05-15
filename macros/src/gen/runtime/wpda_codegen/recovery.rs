//! Stage 3.20 / L12 (Commit D, 2026-05-06): Walker-side recovery emission.
//!
//! Emits per-category `recovery_infra_<cat>()` accessors that build a
//! `mettail_prattail::recovery_dispatch::RecoveryInfra` lazily via
//! `LazyLock`. The engine's PrefixDispatch dead-end (formerly `_ => Idle`,
//! rewired in this commit) calls `recovery_infra_for(state_cat_src_idx)`
//! to retrieve the per-cat infra, then dispatches via
//! `recovery_dispatch::emit_recovery_fork` to construct lex-min Fork
//! branches.
//!
//! Replaces the wrapper-level skip-to-sync retry loop in `facade.rs`
//! (deleted in Commit E).

use mettail_ast::language::LanguageDef;
use mettail_ast::grammar::{GrammarItem, GrammarRule};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Emit Walker-side recovery infrastructure: per-category
/// `recovery_infra_<cat>()` accessors + a top-level `recovery_infra_for`
/// dispatch. Each accessor uses `LazyLock<RecoveryInfra>` so the
/// per-grammar RecoveryWfst is constructed once on first dispatch.
pub(crate) fn emit_recovery_module(
    language: &LanguageDef,
    categories: &[String],
) -> TokenStream {
    let mut per_cat_emissions: Vec<TokenStream> = Vec::new();
    let mut dispatch_arms: Vec<TokenStream> = Vec::new();

    for (cat_idx, cat_name) in categories.iter().enumerate() {
        let cat_idx_u16 = cat_idx as u16;
        let cat_lower = cat_name.to_lowercase();
        let infra_fn = format_ident!("recovery_infra_{}", cat_lower);
        let cat_lit = cat_name.as_str();

        // Collect grammar terminals for this category. Walk all rules
        // whose category matches and extract every literal text.
        let grammar_terminals = collect_terminals_for_category(language, cat_name);
        let term_lits: Vec<TokenStream> =
            grammar_terminals.iter().map(|s| quote! { #s }).collect();

        // FOLLOW set tokens: structural delimiters + grammar terminals.
        // Structural delimiters are the universal sync points: closing
        // delimiters `)`, `}`, `]`, statement terminator `;`, list
        // separator `,`. These are the same set the legacy wrapper
        // retry loop hardcoded as SYNC_TOKENS.
        let follow_lits: Vec<TokenStream> = ["", ")", "}", "]", ";", ",", "Eof"]
            .iter()
            .filter(|s| !s.is_empty())
            .map(|s| quote! { #s })
            .collect();

        // Conservative default: assume all categories may be recursive
        // (RecoveryWfst tightens recovery cost when recursive_category=true,
        // which is safe for non-recursive grammars too).
        let is_recursive = true;

        per_cat_emissions.push(quote! {
            /// Stage 3.20 / L12: per-category RecoveryInfra accessor.
            /// Built lazily once via LazyLock; the build path projects
            /// FOLLOW + grammar terminals into a TokenIdMap and constructs
            /// the RecoveryWfst.
            pub fn #infra_fn() -> &'static mettail_prattail::recovery_dispatch::RecoveryInfra {
                use mettail_prattail::recovery_dispatch::{
                    build_recovery_infra_for_category, RecoveryInfra,
                };
                use std::sync::LazyLock;
                static INFRA: LazyLock<RecoveryInfra> = LazyLock::new(|| {
                    let follow: &[&str] = &[ #( #follow_lits ),* ];
                    let terms: &[&str] = &[ #( #term_lits ),* ];
                    build_recovery_infra_for_category(
                        #cat_lit,
                        #cat_idx_u16,
                        follow,
                        terms,
                        #is_recursive,
                    )
                });
                &*INFRA
            }
        });

        dispatch_arms.push(quote! {
            #cat_idx_u16 => Some(#infra_fn()),
        });
    }

    quote! {
        // Stage 3.20 / L12 (Commit D, 2026-05-06): per-category recovery
        // infrastructure. Replaces the wrapper-level skip-to-sync loop in
        // facade.rs with intrinsic Walker recovery (see
        // prattail/src/recovery_dispatch.rs).
        #( #per_cat_emissions )*

        /// Top-level dispatch: given state_cat_src_idx, return the
        /// per-category RecoveryInfra. Used by engine_impl.rs's
        /// PrefixDispatch dead-end to dispatch into recovery_dispatch::emit_recovery_fork.
        pub fn recovery_infra_for(
            state_cat_src_idx: u16,
        ) -> Option<&'static mettail_prattail::recovery_dispatch::RecoveryInfra> {
            match state_cat_src_idx {
                #( #dispatch_arms )*
                _ => None,
            }
        }
    }
}

/// Collect literal terminals from rules in the given category. Walks all
/// `GrammarItem::Fixed` values (literal-text terminals) across the
/// category's rules and dedups. Unsorted by design — order matches
/// declaration order (deterministic).
fn collect_terminals_for_category(
    language: &LanguageDef,
    cat_name: &str,
) -> Vec<String> {
    let mut terminals: Vec<String> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        collect_terminals_in_rule(rule, &mut terminals, &mut seen);
    }
    terminals
}

fn collect_terminals_in_rule(
    rule: &GrammarRule,
    terminals: &mut Vec<String>,
    seen: &mut std::collections::BTreeSet<String>,
) {
    for item in &rule.items {
        if let GrammarItem::Terminal(text) = item {
            if seen.insert(text.clone()) {
                terminals.push(text.clone());
            }
        }
    }
}
