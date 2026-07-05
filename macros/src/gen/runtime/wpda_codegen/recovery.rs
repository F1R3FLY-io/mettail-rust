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

use mettail_ast::grammar::{GrammarItem, GrammarRule};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use super::prefix::{classify_atomic, AtomicShape};

/// Emit Walker-side recovery infrastructure: per-category
/// `recovery_infra_<cat>()` accessors + a top-level `recovery_infra_for`
/// dispatch. Each accessor uses `LazyLock<RecoveryInfra>` so the
/// per-grammar RecoveryWfst is constructed once on first dispatch.
pub(crate) fn emit_recovery_module(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut per_cat_emissions: Vec<TokenStream> = Vec::new();
    let mut dispatch_arms: Vec<TokenStream> = Vec::new();

    for (cat_idx, cat_name) in categories.iter().enumerate() {
        let cat_idx_u16 = cat_idx as u16;
        let cat_lower = cat_name.to_lowercase();
        let infra_fn = format_ident!("recovery_infra_{}", cat_lower);
        let cat_lit = cat_name.as_str();

        // Collect grammar terminals for this category from the same combined
        // user+synthetic rule surface used by prefix dispatch. Synthetic
        // literal rules matter here: suffixed BigRat/Fixed literals arrive as
        // `TokenKind::Custom("<category>")`, so recovery's token map must
        // include those category payload names.
        let rules = per_cat.get(cat_idx).map(Vec::as_slice).unwrap_or(&[]);
        let grammar_terminals = collect_terminals_for_category(language, rules);
        let term_lits: Vec<TokenStream> = grammar_terminals.iter().map(|s| quote! { #s }).collect();

        // FOLLOW set tokens: structural delimiters + sequence separators +
        // grammar terminals. GEN-1 GAP-2 extension (2026-06-28): these sync
        // points are now SPEC-DERIVED rather than the formerly-hardcoded
        // rhocalc bracket alphabet `) } ] ; ,` (a non-bracket grammar — e.g.
        // one using `« »` — needs ITS OWN closers/separators as sync points,
        // not rhocalc's). The closing delimiters come from
        // `collect_structural_delimiters` (the same source the dispatch
        // delimiter table uses) and the separators from
        // `collect_sequence_separators`; `"Eof"` is the universal end sync.
        // For rhocalc this is a SUPERSET of the former hardcode (adds the Set/
        // Pathmap closers `}# |}` and the `& |` separators), so recovery is at
        // least as effective and never regresses. Audit §GAP-2 (additional site
        // surfaced by the grammar-generality harness INV-6).
        let (_open_delims, close_delims) =
            super::collection::collect_structural_delimiters(language, per_cat);
        let seq_separators = super::kind_dispatch::collect_sequence_separators(language);
        let mut follow_set: std::collections::BTreeSet<String> = close_delims;
        follow_set.extend(seq_separators);
        follow_set.insert("Eof".to_string());
        let follow_lits: Vec<TokenStream> = follow_set.iter().map(|s| quote! { #s }).collect();

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

/// Collect token-map names from the combined rules for one category. Walks
/// literal-text terminals, collection separators/delimiters, and
/// literal-pattern category payload names. Unsorted by design: order follows
/// rule traversal and remains deterministic.
fn collect_terminals_for_category(language: &LanguageDef, rules: &[GrammarRule]) -> Vec<String> {
    let mut terminals: Vec<String> = Vec::new();
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for rule in rules {
        collect_terminals_in_rule(rule, &mut terminals, &mut seen);
        if let AtomicShape::LiteralPatterned { cat_name, .. } = classify_atomic(rule, language) {
            push_terminal(cat_name, &mut terminals, &mut seen);
        }
    }
    terminals
}

fn push_terminal(
    text: String,
    terminals: &mut Vec<String>,
    seen: &mut std::collections::BTreeSet<String>,
) {
    if seen.insert(text.clone()) {
        terminals.push(text);
    }
}

fn collect_terminals_in_rule(
    rule: &GrammarRule,
    terminals: &mut Vec<String>,
    seen: &mut std::collections::BTreeSet<String>,
) {
    for item in &rule.items {
        match item {
            GrammarItem::Terminal(text) => {
                push_terminal(text.clone(), terminals, seen);
            },
            GrammarItem::Collection { separator, delimiters, .. } => {
                push_terminal(separator.clone(), terminals, seen);
                if let Some((open, close)) = delimiters {
                    push_terminal(open.clone(), terminals, seen);
                    push_terminal(close.clone(), terminals, seen);
                }
            },
            GrammarItem::NonTerminal { .. } | GrammarItem::Binder { .. } => {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use quote::quote;
    use syn::{parse_quote, Ident};

    fn empty_language(name: &str) -> LanguageDef {
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
    fn recovery_terminals_include_synthetic_literal_payload_names() {
        let mut language = empty_language("LiteralRecovery");
        language.types.push(LangType {
            name: Ident::new("BigRat", Span::call_site()),
            native_type: Some(parse_quote! { mettail_runtime::CanonicalBigRat }),
            collection_kind: None,
        });
        language.token_defs.push(TokenDef {
            name: Ident::new("BigRat", Span::call_site()),
            pattern: "[0-9]+r".to_string(),
            category: Some(Ident::new("BigRat", Span::call_site())),
            rust_code: Some(quote! { parse_rational_lit(text) }),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });

        let categories = vec!["BigRat".to_string()];
        let per_cat = super::super::synthetic::build_per_category_rules(&language, &categories);
        let terminals = collect_terminals_for_category(&language, &per_cat[0]);

        assert!(
            terminals.iter().any(|terminal| terminal == "BigRat"),
            "recovery token map must include TokenKind::Custom(\"BigRat\") \
             payloads emitted by literal-patterned rules",
        );
    }

    #[test]
    fn recovery_terminals_include_collection_separators_and_delimiters() {
        let rule = GrammarRule {
            label: Ident::new("ListLit", Span::call_site()),
            category: Ident::new("List", Span::call_site()),
            items: vec![GrammarItem::Collection {
                coll_type: mettail_ast::types::CollectionType::Vec,
                element_type: Ident::new("Expr", Span::call_site()),
                separator: ",".to_string(),
                delimiters: Some(("[".to_string(), "]".to_string())),
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        };
        let language = empty_language("CollectionRecovery");
        let terminals = collect_terminals_for_category(&language, &[rule]);

        assert_eq!(terminals, vec![",".to_string(), "[".to_string(), "]".to_string()]);
    }
}
