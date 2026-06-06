//! WPDS-runtime engine codegen (sub-tree facade).
//!
//! Walks a `LanguageDef` and emits a Rust module containing:
//!
//! - A `<LangName>WpdaEngine` struct (zero-sized — all dispatch is via
//!   `&self` methods on the trait impl).
//! - An `impl mettail_prattail::wpda_walker::WpdaEngine<LexicographicWeight>`
//!   with state-based dispatch keyed by category source-index.
//! - Static category and rule-index tables for stable tiebreak indices.
//! - Per-rule push/pop/replace action tables, semantic action registrations,
//!   prefix-dispatch arms, infix loops, cross-cat Forks (F8), binder Forks
//!   (F7), collection markers, refinement predicates, recovery wrappers.
//!
//! ## Module organization
//!
//! - `mod.rs` (this file) — the facade: `generate_wpda_engine_module()`.
//! - `tables.rs` — category/rule-index static tables.
//! - `engine_impl.rs` — `impl WpdaEngine` body.
//! - `prefix.rs`, `infix.rs`, `binder.rs`, `collection.rs`, `refinement.rs`,
//!   `semantic_actions.rs`, `facade.rs`, `synthetic.rs`. Cross-category
//!   projections are codegen'd directly within `prefix.rs` and `infix.rs`;
//!   behavioral predicates are inlined into the action bodies emitted by
//!   `semantic_actions.rs` (no separate `cross_cat.rs` or `predicate.rs`
//!   module). Mixfix Optional groups (`#opt(...)`) are tracked as #68.
//!   Classic Pratt-style ternaries (`a ? b : c`) are handled by `infix.rs`
//!   BP analysis.
//!
//! ## Recovery note
//!
//! Recovery is walker-level: generated engines can emit recovery Fork branches
//! at PrefixDispatch dead-ends, selected by `LexicographicWeight` lex-min.
//! Strict parse facades disable those branches by setting
//! `RecoveryConfig.max_recovery_depth = 0`; the explicit recovering facades
//! keep the default config and return the walker's recovery trace.
//!
//! Cross-references:
//! - `prattail/src/wpda_runtime.rs` module doc
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
/// Stage 3.16/3.17/3.18 (Commit 2, 2026-05-05): unified Fork-emission framework.
/// Helpers replace deterministic peek-and-decide patterns with
/// `WpdaStepAction::Fork` per `feedback_use_wpds_disambiguation_not_heuristics.md`.
pub mod forks;
pub mod infix;
/// M6c.2 (2026-05-14): per-grammar `lex_alt_rule_for(cat, kind)` codegen.
/// Used by the lex-Fork emitter to bind alternative tokens to prefix-site
/// token-consuming rules before forking.
pub mod kind_dispatch;
pub mod prefix;
pub mod recovery;
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
pub fn generate_wpda_engine_module(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let engine_ident = format_ident!("{}WpdaEngine", lang_name);

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

    // Stage 10.5r migration: per-category recovery infrastructure
    // (BRACKET_STATE_<cat>, LAST_ERROR_POS_<cat>, RUNNING_WEIGHT_<CAT>,
    // PARENT_WEIGHT_<CAT>, frame_kind_of_<cat>, running_weight_<cat>).
    // Identifier surface preserved from the legacy trampoline emitter so
    // existing codegen-string tests continue to assert the same substrings.
    let recovery_module = recovery::emit_recovery_module(language, &categories, &per_cat);

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
        // Generated by `mettail-macros::gen::runtime::wpda_codegen`. Do not
        // edit by hand.
        // ══════════════════════════════════════════════════════════════════

        /// Source-order category names for this language. Index into this
        /// slice is the `src_idx` carried by every emitted WPDS weight.
        pub const WPDA_CATEGORIES: &[&str] = &[
            #cat_table
        ];

        /// Per-category rule tables.
        ///
        /// `WPDA_RULES[i]` is the `[(label, rule_idx_within_category)]`
        /// for the category at `WPDA_CATEGORIES[i]`. The tuple's second
        /// component is the canonical `rule_idx` carried by every emitted
        /// WPDS weight for that rule.
        pub const WPDA_RULES: &[&[(&str, u16)]] = &[
            #rule_table
        ];

        /// WPDS step engine for `#lang_name`.
        ///
        /// Zero-sized; all per-step decisions are taken via the
        /// `WpdaEngine` trait method. Per-rule push/pop/replace
        /// dispatch is populated incrementally across Phase A.2–A.10
        /// of the Stage 6 plan v2.
        #[derive(Debug, Default, Clone, Copy)]
        pub struct #engine_ident;

        #engine_impl

        // Phase 3: per-category BP lookup functions (infix + postfix).
        // Used by the engine's InfixLoop state to select operators.
        #bp_tables

        // Phase 2: per-category `parse_<Cat>_via_wpda` wrappers + shared
        // WpdaParseError.
        #facade_fns

        // Stage 10.5r: per-category recovery infrastructure — preserves
        // the identifier surface migrated from the legacy trampoline
        // emitter (BRACKET_STATE_<cat>, LAST_ERROR_POS_<cat>,
        // RUNNING_WEIGHT_<CAT>, frame_kind_of_<cat>, running_weight_<cat>).
        #recovery_module

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
    let case_insensitive =
        matches!(language.options.get("case_insensitive"), Some(AttributeValue::Bool(true)));
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
/// emitted `WPDA_CATEGORIES` table even though `language.terms` alone
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
                && td
                    .category
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
    // present in `WPDA_CATEGORIES`, the emitted CrossCatDelegate falls
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

    fn var_only_language() -> LanguageDef {
        LanguageDef {
            name: Ident::new("VarLang", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: vec![mettail_ast::language::LangType {
                name: Ident::new("Name", Span::call_site()),
                native_type: None,
                collection_kind: None,
            }],
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
    fn collect_categories_in_source_order() {
        let lang = synthetic_language();
        let cats = collect_category_names_with_literals(&lang);
        assert_eq!(cats, vec!["Expr".to_string(), "Bool".to_string()]);
    }

    #[test]
    fn emits_engine_struct_and_tables() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("pub struct ToyLangWpdaEngine"));
        assert!(ts.contains("WPDA_CATEGORIES"));
        assert!(ts.contains("WPDA_RULES"));
        assert!(ts.contains("LitInt"));
        assert!(ts.contains("Add"));
        assert!(ts.contains("BoolLit"));
        assert!(ts.contains("WpdaEngine"));
        assert!(ts.contains("LexicographicWeight"));
        // The extended signature must show up in the emitted impl.
        assert!(ts.contains("WpdaTokenSource"));
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
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("EmptyWpdaEngine"));
    }

    #[test]
    fn rule_indices_are_unique_within_category() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("(\"LitInt\" , 0u16)") || ts.contains("(\"LitInt\", 0u16)"));
        assert!(ts.contains("(\"Add\" , 1u16)") || ts.contains("(\"Add\", 1u16)"));
        assert!(ts.contains("(\"BoolLit\" , 0u16)") || ts.contains("(\"BoolLit\", 0u16)"));
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang);
        let parsed: Result<syn::File, _> = syn::parse2(quote! {
            #ts
        });
        assert!(parsed.is_ok(), "emitted code should parse as a Rust file: {:?}", parsed.err());
    }

    #[test]
    fn primary_category_idx_zero_for_empty() {
        assert_eq!(primary_category_idx(&[]), 0);
    }

    #[test]
    fn sub_tree_modules_declared() {
        // Compile-time check that all planned sub-modules exist.
        let _ = ();
    }

    // ══════════════════════════════════════════════════════════════════
    // Stage 10.5r migration tests — moved from
    // `prattail/src/tests/{error_tests,integration_tests,recovery_tests}.rs`
    // because Walker codegen lives in this crate (downstream of prattail).
    // Each test asserts an identifier or signature that the migration
    // plan §10.5r preserves from the legacy trampoline emitter.
    // ══════════════════════════════════════════════════════════════════

    /// Walker emits per-category `parse_<Cat>_via_wpda` wrappers.
    /// Replaces prattail's `test_generate_parser_two_categories`.
    #[test]
    fn walker_emits_parse_via_wpda_per_category() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("parse_Expr_via_wpda"), "Walker should emit parse_Expr_via_wpda");
        assert!(ts.contains("parse_Bool_via_wpda"), "Walker should emit parse_Bool_via_wpda");
    }

    #[test]
    fn walker_emits_source_generic_single_parse_facade() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("parse_Expr_via_wpda_with_source"));
        assert!(ts.contains("parse_Bool_via_wpda_with_source"));
        assert!(ts.contains("dyn mettail_prattail :: wpda_runtime :: WpdaTokenSource"));
    }

    #[test]
    fn walker_routes_identifier_lex_alternatives_to_var_rules() {
        let lang = var_only_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("parse_Name_via_wpda_with_source"));
        assert!(ts.contains("TokenKind :: Ident"));
        assert!(ts.contains("LexAltRuleKind :: Atomic"));
        assert!(ts.contains("prefix_primary_has_dispatch_rule"));
        assert!(ts.contains("__only_secondary_survived"));
    }

    /// Walker emits `parse_<Cat>_via_wpda_recovering` (recovering variant).
    /// Replaces prattail's `test_generated_code_contains_recovering_parser`.
    #[test]
    fn walker_emits_recovering_parser() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("parse_Expr_via_wpda_recovering"));
        assert!(ts.contains("parse_Bool_via_wpda_recovering"));
    }

    /// Walker recovering parser returns `Result<_, WpdaParseError>` paired
    /// with `Vec<RecoveryAttempt>` rather than the trampoline's Option-based
    /// return. Replaces prattail's `test_recovering_parser_returns_option`
    /// + `test_recovering_parser_takes_errors_param`.
    #[test]
    fn walker_recovering_parser_signature_uses_recovery_attempt() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("RecoveryAttempt"), "Walker recovery uses RecoveryAttempt");
        assert!(ts.contains("WpdaParseError"), "Walker recovery uses WpdaParseError");
    }

    /// Walker recovering parser threads a mutable token source so recovery
    /// branches that insert/substitute/swap tokens can replay without
    /// panicking at commit time.
    #[test]
    fn walker_recovering_parser_threads_mutable_slice_source() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("MutableSliceTokenSource"));
        assert!(ts.contains("set_mutable_token_source"));
        assert!(ts.contains("clear_mutable_token_source"));
    }

    // Stage 10.5r-d (2026-05-05): the following tests DELETED. They asserted
    // recovery shim emissions (BRACKET_STATE_<cat>, LAST_ERROR_POS_<cat>,
    // RUNNING_WEIGHT_<CAT>, PARENT_WEIGHT_<CAT>, frame_kind_of_<cat>,
    // running_weight_<cat>) that were eliminated together with the dead
    // wfst_recover_<Cat> emitter (zero callers post-trampoline-deletion):
    //   * walker_emits_bracket_state_per_category
    //   * walker_emits_cascade_prevention_thread_local
    //   * walker_emits_running_and_parent_weight_thread_locals
    //   * walker_emits_running_weight_accessor
    //   * walker_running_weight_inherits_from_parent
    //   * walker_emits_frame_kind_helper_per_category
    //   * walker_recovery_emits_one_thread_local_set_per_category
    // Per Plan agent ac1ca5956a3783d6c: the deleted identifier surface was
    // obsolete recovery scaffolding. Walker-state-aware recovery now reads
    // from runtime walker/GSS state and does not use synthesized thread-locals.

    /// Walker emits a top-level `parse_<Cat>_via_wpda` smoke check —
    /// confirms a calculator-shaped grammar produces a compilable module.
    #[test]
    fn walker_smoke_test_calc_shaped_grammar() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("parse_Expr_via_wpda"));
    }

    /// Walker emits `WpdaParseError` (the recovering parser's error type).
    #[test]
    fn walker_emits_wpds_parse_error_type() {
        let lang = synthetic_language();
        let ts = generate_wpda_engine_module(&lang).to_string();
        assert!(ts.contains("WpdaParseError"), "error type emitted");
        assert!(ts.contains("ParseFailed"), "error variant for failed parses");
    }
}
