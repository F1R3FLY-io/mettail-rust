//! Tests for panic-mode error recovery code generation.
//!
//! Validates that generated code includes:
//! - `sync_to` helper for advancing past errors
//! - `expect_token_rec` / `expect_ident_rec` recovery helpers
//! - `is_sync_<Cat>` sync predicate per category
//! - `parse_<Cat>_recovering` entry points
//! - Correct sync predicate tokens (FOLLOW set + structural delimiters)

use crate::{
    generate_parser, BeamWidthConfig, CategorySpec, LanguageSpec, LiteralPatterns, RuleSpec,
    SyntaxItemSpec,
};

/// Build a simple calculator spec (Int with Add, IVar, NumLit).
fn calculator_spec() -> LanguageSpec {
    let category_names = vec!["Int".to_string()];
    LanguageSpec {
        name: "Calculator".to_string(),
        types: vec![CategorySpec {
            name: "Int".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
            has_var: true,
        }],
        rules: vec![
            // NumLit: integer literal
            RuleSpec::classified("NumLit", "Int", vec![], &category_names),
            // Add: Int "+" Int
            RuleSpec::classified(
                "Add",
                "Int",
                vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
                &category_names,
            ),
            // IVar: variable
            RuleSpec::classified(
                "IVar",
                "Int",
                vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                &category_names,
            ),
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        literal_patterns: LiteralPatterns::default(),
        recovery_config: crate::recovery::RecoveryConfig::default(),
        semantic_dependency_groups: Vec::new(),
        custom_tokens: Vec::new(),
        modes: Vec::new(),
        sync: None,
        tree_invariants: Vec::new(),
        refinement_types: Vec::new(),
        guard_config: None,
    }
}

// Stage 10.5b conclusion (2026-05-05): the following 3 tests DELETED.
// `sync_to`, `expect_token_rec`, `expect_ident_rec` were trampoline-internal
// recovery helpers emitted by the now-deleted pratt::write_recovery_helpers.
// Walker recovery uses wfst_recover_<cat> + RecoveryAttempt directly; there
// is no sync_to / expect_*_rec equivalent. The recovery FEATURE is preserved
// via wfst_recover emission (asserted by macros::tests::walker_emits_*).

// ── Sync predicate generation ──

#[test]
fn test_generated_code_contains_sync_predicate() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("is_sync_Int"),
        "generated code should contain is_sync_Int sync predicate"
    );
}

#[test]
fn test_sync_predicate_includes_eof() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Extract the is_sync_Int function body
    let sync_fn_start = code_str
        .find("is_sync_Int")
        .expect("is_sync_Int should exist");
    let sync_fn_area =
        &code_str[sync_fn_start..sync_fn_start + 500.min(code_str.len() - sync_fn_start)];

    assert!(
        sync_fn_area.contains("Eof"),
        "sync predicate should always include Eof, got: {}",
        &sync_fn_area[..200.min(sync_fn_area.len())]
    );
}

#[test]
fn test_sync_predicate_includes_structural_delimiters() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Calculator includes () so RParen should be in the sync set
    let sync_fn_start = code_str
        .find("is_sync_Int")
        .expect("is_sync_Int should exist");
    let sync_fn_area =
        &code_str[sync_fn_start..sync_fn_start + 500.min(code_str.len() - sync_fn_start)];

    assert!(
        sync_fn_area.contains("RParen"),
        "sync predicate should include RParen (structural delimiter), got: {}",
        &sync_fn_area[..200.min(sync_fn_area.len())]
    );
}

// ── Recovering parser generation ──

// Stage 10.5r migration (2026-05-04): the following 3 tests MOVED to
// macros/src/gen/runtime/wpda_codegen/mod.rs::tests:
//   * test_generated_code_contains_recovering_parser → walker_emits_recovering_parser
//   * test_recovering_parser_takes_errors_param → walker_recovering_parser_signature_uses_recovery_attempt (combined)
//   * test_recovering_parser_returns_option → walker_recovering_parser_signature_uses_recovery_attempt (combined)
//
// Walker now emits `parse_<Cat>_via_wpda_recovering` returning
// `(Result<Cat, WpdaParseError>, Vec<RecoveryAttempt>)` — different signature
// from the trampoline's Option-based recovering parser. New tests assert
// against the Walker emission directly.

// ── Multi-category sync predicate ──

#[test]
fn test_multi_category_generates_separate_sync_predicates() {
    let mut spec = calculator_spec();
    spec.types.push(CategorySpec {
        name: "Bool".to_string(),
        native_type: Some("bool".to_string()),
        is_primary: false,
        has_var: true,
    });
    let category_names = vec!["Int".to_string(), "Bool".to_string()];
    spec.rules
        .push(RuleSpec::classified("BoolLit", "Bool", vec![], &category_names));
    spec.rules.push(RuleSpec::classified(
        "BVar",
        "Bool",
        vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
        &category_names,
    ));

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(code_str.contains("is_sync_Int"), "should generate sync predicate for Int");
    assert!(code_str.contains("is_sync_Bool"), "should generate sync predicate for Bool");

    // Stage 10.5 (2026-05-04): `parse_<Cat>_recovering` was emitted by trampoline.
    // Walker (WPDS) emits `parse_<Cat>_via_wpda_recovering` from `wpda_codegen/facade.rs`
    // — invisible to `generate_parser(spec)` because Walker codegen lives downstream
    // in the macros crate. Walker-side assertion lives in
    // `macros/src/gen/runtime/wpda_codegen/tests/*` (post-Stage-10.5r-d move).
}

// ── Recovering led loop uses sync ──

#[test]
fn test_recovering_parser_uses_sync_predicate() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The recovering parser should reference its sync predicate
    assert!(
        code_str.contains("is_sync_Int"),
        "recovering parser should use is_sync_Int sync predicate"
    );
}

// Stage 10.5r-d (2026-05-05): test_generated_code_contains_recovery_beam_width
// DELETED. RECOVERY_BEAM_WIDTH was emitted only as input to the dead
// wfst_recover_<cat> emitter; eliminated together with that chain.
#[cfg(any())]
#[test]
fn _disabled_test_generated_code_contains_recovery_beam_width() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("RECOVERY_BEAM_WIDTH"),
        "generated code should contain RECOVERY_BEAM_WIDTH constant"
    );
}

// ── Error cascade prevention (Sprint 15) ──

// Stage 10.5r migration (2026-05-04): cascade prevention + incremental
// bracket tracking tests MOVED to macros/src/gen/runtime/wpda_codegen/mod.rs::tests:
//   * test_generated_code_contains_cascade_prevention → walker_emits_cascade_prevention_thread_local
//   * test_generated_recovery_uses_incremental_bracket_tracking → walker_emits_bracket_state_per_category
//
// LAST_ERROR_POS_<cat> and BRACKET_STATE_<cat> thread-locals are now emitted
// by wpda_codegen/recovery.rs::emit_recovery_module. Identifier names preserved.

// ── RepairAction::describe() produces human-readable messages ──

#[test]
fn test_repair_action_describe() {
    use crate::recovery::RepairAction;

    let token_names: &[&str] = &["Plus", "Minus", "Integer", "RParen", "Semi"];

    // SkipToSync
    let action = RepairAction::SkipToSync {
        skip_count: 2,
        sync_token: 4, // Semi
    };
    assert_eq!(action.describe(token_names), "skip 2 token(s) to 'Semi'");

    // InsertToken
    let action = RepairAction::InsertToken { token: 3 }; // RParen
    assert_eq!(action.describe(token_names), "insert missing 'RParen'");

    // DeleteToken
    let action = RepairAction::DeleteToken;
    assert_eq!(action.describe(token_names), "delete unexpected token");

    // SubstituteToken
    let action = RepairAction::SubstituteToken { replacement: 0 }; // Plus
    assert_eq!(action.describe(token_names), "expected 'Plus' here");

    // SwapTokens
    let action = RepairAction::SwapTokens { pos_a: 0, pos_b: 1 };
    assert_eq!(action.describe(token_names), "swap adjacent tokens");

    // Composite
    let action = RepairAction::Composite {
        steps: vec![
            RepairAction::DeleteToken,
            RepairAction::SkipToSync {
                skip_count: 1,
                sync_token: 4,
            },
        ],
    };
    assert_eq!(
        action.describe(token_names),
        "delete unexpected token, skip 1 token(s) to 'Semi'"
    );

    // Out-of-range token ID
    let action = RepairAction::InsertToken { token: 99 };
    assert_eq!(action.describe(token_names), "insert missing '?'");
}

// ── Generated code uses RecoveryApplied ──

// Stage 10.5r migration (2026-05-04): RecoveryApplied test MOVED to
// macros/src/gen/runtime/wpda_codegen/mod.rs::tests::walker_emits_wpds_parse_error_type
// (Walker uses WpdaParseError::ParseFailed { attempts: Vec<RecoveryAttempt> } —
// the macro-side Cat::parse_recovering wrapper translates to ParseError variants).

// Stage 10.5r-d (2026-05-05): the following tests DELETED — they assert
// emissions (PARSE_SIMULATOR LazyLock, SIM_FIRST_SETS, SIM_FOLLOW_SETS,
// SIM_INFIX_SETS) from the dead emit_parse_simulator_static emitter:
//   * test_generated_code_contains_parse_simulator
//   * test_generated_code_contains_sim_first_sets

#[test]
fn test_generated_code_contains_token_to_id() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("token_to_id"),
        "generated code should contain token_to_id helper function"
    );
}

// Stage 10.5r-d (2026-05-05): test_generated_recovery_uses_tier3_simulation
// and test_generated_code_contains_frame_state DELETED — they assert
// emissions (simulate_after_repair, cost_multiplier, FRAME_STATE_INT) from
// the dead generate_wfst_recovery_fn emitter chain.

// Stage 10.5r migration (2026-05-04): frame_kind_helper test MOVED to
// macros/src/gen/runtime/wpda_codegen/mod.rs::tests::walker_emits_frame_kind_helper_per_category
// (frame_kind_of_<cat> per-category wrappers + shared frame_kind_of_wpds
// emitted by wpda_codegen/recovery.rs::emit_recovery_module).

// Stage 10.5r-d (2026-05-05): test_recovery_uses_frame_kind_multipliers
// and test_generated_recovery_uses_viterbi_multi_step DELETED — they
// assert emissions (frame_kind/frame_insert_mult, viterbi_multi_step,
// RECOVERY_SYNC_TOKENS_Int) from the dead generate_wfst_recovery_fn chain.

// ── Cross-category recovery (Sprint 10) ──

// Stage 10.5r-d (2026-05-05): test_multi_category_generates_cross_cat_casts
// DELETED — CROSS_CAT_CASTS_<cat> static was consumed only by the dead
// wfst_recover_<cat> function (Strategy 6); eliminated together with that chain.

#[test]
fn test_single_category_no_cross_cat_casts() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Single-category grammar has no cross-category casts
    assert!(
        !code_str.contains("CROSS_CAT_CASTS"),
        "single-category code should not contain CROSS_CAT_CASTS"
    );
}
