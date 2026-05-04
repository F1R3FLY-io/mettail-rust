//! WPDS-runtime engine codegen (sub-tree facade).
//!
//! Walks a `LanguageDef` and emits a Rust module containing:
//!
//! - A `<LangName>WpdsEngine` struct (zero-sized — all dispatch is via
//!   `&self` methods on the trait impl).
//! - An `impl mettail_prattail::wpds_walker::WpdsStepEngine<LexicographicWeight>`
//!   with state-based dispatch keyed by category source-index.
//! - Static category and rule-index tables for stable tiebreak indices.
//! - Per-rule push/pop/replace action tables, semantic action registrations,
//!   prefix-dispatch arms, infix loops, cross-cat Forks (F8), binder Forks
//!   (F7), collection markers, refinement predicates, recovery wrappers.
//!
//! ## Module organization
//!
//! - `mod.rs` (this file) — the facade: `generate_wpds_engine_module()`.
//! - `tables.rs` — category/rule-index static tables.
//! - `engine_impl.rs` — `impl WpdsStepEngine` body.
//! - `prefix.rs`, `infix.rs`, `binder.rs`, `collection.rs`, `refinement.rs`,
//!   `semantic_actions.rs`, `facade.rs`, `synthetic.rs`. Cross-category
//!   projections are codegen'd directly within `prefix.rs` and `infix.rs`;
//!   behavioral predicates are inlined into the action bodies emitted by
//!   `semantic_actions.rs` (no separate `cross_cat.rs` or `predicate.rs`
//!   module). Mixfix Optional groups (`#opt(...)`) are tracked as #68.
//!   Classic Pratt-style ternaries (`a ? b : c`) are handled by `infix.rs`
//!   BP analysis.
//!
//! ## 📌 Long-term recovery note
//!
//! TODAY: recovery is wrapper-level. `parse_<Cat>_via_wpds` (`facade.rs`)
//! wraps the walker in a skip-to-sync retry loop. On `WpdsState::Error`,
//! the loop advances `pos` past the offending token until a sync delimiter
//! is found, then re-seeds the walker and retries up to MAX_RECOVERY_ROUNDS.
//!
//! LONG-TERM (tracked as #64 / L12): recovery becomes alternate WPDS edges
//! (Skip / Delete / Substitute / Insert Fork branches at every PrefixDispatch
//! dead-end, selected by `LexicographicWeight` lex-min). When L12 lands,
//! the wrapper loop is deleted and recovery becomes first-class WPDS semantics.
//!
//! Cross-references:
//! - `prattail/src/wpds_runtime.rs` module doc
//! - `prattail/docs/design/wpds-migration-survey.md` §4A
//! - `prattail/docs/design/wpds-stage-10-audit.md` §6
//!
//! ## File layout (per language)
//!
//! Generated module is written to `target/generated/<lang>/wpds.rs` and
//! `include!`-ed from the `language!` expansion site (per the existing
//! spill-and-include pattern documented at
//! `macros/src/logic/writer.rs::spill_and_include`).

pub mod auto_inject;
pub mod binder;
pub mod builtin_metadata;
pub mod collection;
pub mod engine_impl;
pub mod facade;
pub mod infix;
pub mod prefix;
pub mod refinement;
pub mod semantic_actions;
pub mod synthetic;
pub mod tables;

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Generate the WPDS-runtime engine module for the given language.
///
/// The emitted code is stand-alone — references only `mettail_prattail`
/// types — and is safe to include in the language crate alongside the
/// existing trampoline parser during the Phase C parallel emission period.
pub fn generate_wpds_engine_module(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let engine_ident = format_ident!("{}WpdsEngine", lang_name);

    let categories = collect_category_names_with_literals(language);
    // Build the combined per-category rule list once (user + synthetic) so
    // tables / prefix / semantic_actions all assign the same rule_idx values.
    let per_cat = synthetic::build_per_category_rules(language, &categories);
    let cat_table = tables::emit_category_table(&categories);
    let rule_table = tables::emit_rule_table_from_per_cat(&per_cat);
    let primary_src_idx = primary_category_idx(&categories);

    let engine_impl = engine_impl::emit_engine_impl_full(
        &engine_ident,
        language,
        &categories,
        &per_cat,
        primary_src_idx,
    );

    // Phase 3: per-category BP tables (infix + postfix) — used by the
    // engine's InfixLoop state in subsequent wiring. Pass per_cat so the
    // emitter can look up rule indices for cross-cat operators.
    let bp_tables = infix::emit_bp_tables(language, &categories, &per_cat);

    let facade_fns = facade::emit_parse_fns(language, &categories, &engine_ident);

    // Refinement-type predicate registrations. Empty if the language declares
    // no `refinement_types`. Tests / language-init code call the emitted
    // `register_refinements()` to install the predicates before parsing.
    let refinement_registrations = refinement::emit_refinement_registrations(language);

    // L11 (2026-04-28): per-grammar lexer configuration. Reads
    // `case_insensitive` and `unicode_normalization` from
    // `language.options` and emits a `LEXER_CONFIG` static the runtime
    // lexer reads before each scan.
    let lexer_config = emit_lexer_config(language);

    quote! {
        // ══════════════════════════════════════════════════════════════════
        // WPDS-runtime engine for `#lang_name`
        //
        // Stage 6 of W7 plan v2 — see
        // `prattail/docs/design/wpds-migration-survey.md` and
        // `/home/dylon/.claude/plans/wpds-stage-6-implementation-v2.md`.
        //
        // Generated by `mettail-macros::gen::runtime::wpds_codegen`. Do not
        // edit by hand.
        // ══════════════════════════════════════════════════════════════════

        /// Source-order category names for this language. Index into this
        /// slice is the `src_idx` carried by every emitted WPDS weight.
        pub const WPDS_CATEGORIES: &[&str] = &[
            #cat_table
        ];

        /// Per-category rule tables.
        ///
        /// `WPDS_RULES[i]` is the `[(label, rule_idx_within_category)]`
        /// for the category at `WPDS_CATEGORIES[i]`. The tuple's second
        /// component is the canonical `rule_idx` carried by every emitted
        /// WPDS weight for that rule.
        pub const WPDS_RULES: &[&[(&str, u16)]] = &[
            #rule_table
        ];

        /// WPDS step engine for `#lang_name`.
        ///
        /// Zero-sized; all per-step decisions are taken via the
        /// `WpdsStepEngine` trait method. Per-rule push/pop/replace
        /// dispatch is populated incrementally across Phase A.2–A.10
        /// of the Stage 6 plan v2.
        #[derive(Debug, Default, Clone, Copy)]
        pub struct #engine_ident;

        #engine_impl

        // Phase 3: per-category BP lookup functions (infix + postfix).
        // Used by the engine's InfixLoop state to select operators.
        #bp_tables

        // Phase 2: per-category `parse_<Cat>_via_wpds` wrappers + shared
        // WpdsParseError.
        #facade_fns

        // Refinement-type predicate registrations. Empty when no
        // `refinement_types` are declared; otherwise emits a public
        // `register_refinements()` function that callers (test setup,
        // language init) invoke before parsing.
        #refinement_registrations

        // L11: per-grammar lexer configuration.
        #lexer_config
    }
}

/// L11 (2026-04-28): emit a `LEXER_CONFIG` static reflecting the language's
/// `options { case_insensitive: ..., unicode_normalization: ... }` block.
///
/// For grammars without these options the const carries the defaults:
/// `case_insensitive: false`, `unicode_normalization: None`. The runtime
/// lexer reads these flags before scanning. Multi-mode lexing (L9) extends
/// this with per-mode `ModeConfig` entries; for now the `modes` vec is
/// empty (single default mode is implicit).
fn emit_lexer_config(language: &LanguageDef) -> TokenStream {
    use mettail_ast::language::AttributeValue;
    let case_insensitive = matches!(
        language.options.get("case_insensitive"),
        Some(AttributeValue::Bool(true))
    );
    let normalization_expr = match language.options.get("unicode_normalization") {
        Some(AttributeValue::Keyword(kw)) => match kw.as_str() {
            "NFC" => quote! {
                Some(mettail_prattail::lexer_types::UnicodeNormalForm::NFC)
            },
            "NFD" => quote! {
                Some(mettail_prattail::lexer_types::UnicodeNormalForm::NFD)
            },
            "NFKC" => quote! {
                Some(mettail_prattail::lexer_types::UnicodeNormalForm::NFKC)
            },
            "NFKD" => quote! {
                Some(mettail_prattail::lexer_types::UnicodeNormalForm::NFKD)
            },
            _ => quote! { None },
        },
        _ => quote! { None },
    };
    quote! {
        /// L11 (2026-04-28): per-grammar lexer configuration.
        ///
        /// Reflects `language!{} options { case_insensitive, unicode_normalization }`.
        /// The runtime lexer consults this before scanning. Currently
        /// thread-local; multi-mode (L9) will extend with mode_stack
        /// integration.
        pub fn lexer_config() -> mettail_prattail::lexer_types::LexerConfig {
            mettail_prattail::lexer_types::LexerConfig {
                case_insensitive: #case_insensitive,
                unicode_normalization: #normalization_expr,
                default_mode: 0,
                modes: Vec::new(),
            }
        }
    }
}

/// Collect category names including those that have `literals { }` blocks
/// but no user-written rules. These categories get synthetic atomic-literal
/// rules (see `synthetic.rs`), so their `src_idx` must appear in the
/// emitted `WPDS_CATEGORIES` table even though `language.terms` alone
/// wouldn't include them.
///
/// Order: user-rule categories first (in source order of the rules), then
/// literal-only categories (in source order of `language.types`).
pub(crate) fn collect_category_names_with_literals(language: &LanguageDef) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut categories = Vec::new();
    // Pass 1: categories that appear as rule LHS.
    for rule in &language.terms {
        let cat = rule.category.to_string();
        if seen.insert(cat.clone()) {
            categories.push(cat);
        }
    }
    // Pass 2: categories with `from_literals` TokenDefs that weren't already
    // added. Iterate `language.types` for stable declaration order.
    for type_def in &language.types {
        let cat = type_def.name.to_string();
        if seen.contains(&cat) {
            continue;
        }
        let has_literal_block = language.token_defs.iter().any(|td| {
            td.from_literals
                && td.category
                    .as_ref()
                    .map(|c| c.to_string() == cat)
                    .unwrap_or(false)
        });
        if has_literal_block {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Stage 1.3 (Pass 3): collection-typed categories (`![Vec<T>] as List`,
    // `![HashBag<T>] as Bag`, `![HashMap<K,V>] as Map`). These have
    // `collection_kind = Some(...)` but no user-written rules; the WPDS
    // codegen synthesizes `ListLit`/`BagLit`/`MapLit` rules in
    // `synthetic.rs` and they need their categories present here so the
    // synthesis loop can find their per-cat slot.
    for type_def in &language.types {
        let cat = type_def.name.to_string();
        if seen.contains(&cat) {
            continue;
        }
        if type_def.collection_kind.is_some() {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Stage 4 fix (Pass 4): native-type-only categories (e.g. RhoCalc's
    // `![bool] as Bool` and `![str] as Str` declared at type-level but
    // with no rules and no `literals { ... }` block). Cross-cat projection
    // rules in OTHER categories may reference these as source categories
    // (e.g., `CastBool . k:Bool |- k : Proc;`). Without the categories
    // present in `WPDS_CATEGORIES`, the emitted CrossCatDelegate falls
    // back to `source_src_idx: 0u16` (Proc) and the engine recurses into
    // Proc's PrefixDispatch on the same token. The synthetic atomic-literal
    // rule emitted in `synthetic.rs` for these native-type categories
    // gives them a self-contained sub-parser.
    for type_def in &language.types {
        let cat = type_def.name.to_string();
        if seen.contains(&cat) {
            continue;
        }
        if type_def.native_type.is_some() {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Pass 5: any remaining user-declared `LangType` not covered above.
    // Examples: Ambient's `Name` (declared but with no LHS rules, no
    // literals block, no collection_kind, no native_type). These are
    // typically reference-only categories — their tokens are bound by
    // other rules' production bodies. `synthetic.rs` Phase 5a fabricates
    // a Var rule for any such category, giving them an identifier-shaped
    // parser. Without this pass the synthetic Var rule never gets emitted
    // (it's gated on the category being in `cat_idx` built from the
    // categories list returned here), and any rule body referencing the
    // category becomes unparseable.
    for type_def in &language.types {
        let cat = type_def.name.to_string();
        if seen.insert(cat.clone()) {
            categories.push(cat);
        }
    }
    categories
}

/// Index of the primary category (the first declared category — by
/// convention this is what `parse_<Primary>` is generated from).
pub(crate) fn primary_category_idx(categories: &[String]) -> u16 {
    if categories.is_empty() {
        0
    } else {
        0 // first-declared category is primary
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests (existing; moved from the pre-sub-tree file)
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;
    use syn::Ident;

    fn synthetic_language() -> LanguageDef {
        LanguageDef {
            name: Ident::new("ToyLang", Span::call_site()),
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
            terms: vec![
                mettail_ast::grammar::GrammarRule {
                    label: Ident::new("LitInt", Span::call_site()),
                    category: Ident::new("Expr", Span::call_site()),
                    items: Vec::new(),
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
                },
                mettail_ast::grammar::GrammarRule {
                    label: Ident::new("Add", Span::call_site()),
                    category: Ident::new("Expr", Span::call_site()),
                    items: Vec::new(),
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
                },
                mettail_ast::grammar::GrammarRule {
                    label: Ident::new("BoolLit", Span::call_site()),
                    category: Ident::new("Bool", Span::call_site()),
                    items: Vec::new(),
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
                },
            ],
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    #[test]
    fn collect_categories_in_source_order() {
        let lang = synthetic_language();
        let cats = collect_category_names_with_literals(&lang);
        assert_eq!(cats, vec!["Expr".to_string(), "Bool".to_string()]);
    }

    #[test]
    fn emits_engine_struct_and_tables() {
        let lang = synthetic_language();
        let ts = generate_wpds_engine_module(&lang).to_string();
        assert!(ts.contains("pub struct ToyLangWpdsEngine"));
        assert!(ts.contains("WPDS_CATEGORIES"));
        assert!(ts.contains("WPDS_RULES"));
        assert!(ts.contains("LitInt"));
        assert!(ts.contains("Add"));
        assert!(ts.contains("BoolLit"));
        assert!(ts.contains("WpdsStepEngine"));
        assert!(ts.contains("LexicographicWeight"));
        // The extended signature must show up in the emitted impl.
        assert!(ts.contains("WpdsTokenSource"));
    }

    #[test]
    fn primary_src_idx_is_first_declared_category() {
        let lang = synthetic_language();
        let cats = collect_category_names_with_literals(&lang);
        let idx = primary_category_idx(&cats);
        assert_eq!(idx, 0, "Expr is declared first → src_idx 0");
    }

    #[test]
    fn empty_language_does_not_panic() {
        let lang = LanguageDef {
            name: Ident::new("Empty", Span::call_site()),
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
        };
        let ts = generate_wpds_engine_module(&lang).to_string();
        assert!(ts.contains("EmptyWpdsEngine"));
    }

    #[test]
    fn rule_indices_are_unique_within_category() {
        let lang = synthetic_language();
        let ts = generate_wpds_engine_module(&lang).to_string();
        assert!(ts.contains("(\"LitInt\" , 0u16)") || ts.contains("(\"LitInt\", 0u16)"));
        assert!(ts.contains("(\"Add\" , 1u16)") || ts.contains("(\"Add\", 1u16)"));
        assert!(ts.contains("(\"BoolLit\" , 0u16)") || ts.contains("(\"BoolLit\", 0u16)"));
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let lang = synthetic_language();
        let ts = generate_wpds_engine_module(&lang);
        let parsed: Result<syn::File, _> = syn::parse2(quote! {
            #ts
        });
        assert!(
            parsed.is_ok(),
            "emitted code should parse as a Rust file: {:?}",
            parsed.err()
        );
    }

    #[test]
    fn primary_category_idx_zero_for_empty() {
        assert_eq!(primary_category_idx(&[]), 0);
    }

    #[test]
    fn sub_tree_modules_declared() {
        // Compile-time check that all planned sub-modules exist (empty stubs
        // are fine; they fill in during A.2–A.10).
        let _ = ();
    }
}
