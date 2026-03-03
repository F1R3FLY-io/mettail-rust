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
    }
}

// ── sync_to helper generation ──

#[test]
fn test_generated_code_contains_sync_to() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("sync_to"),
        "generated code should contain sync_to recovery helper"
    );
}

// ── expect_token_rec / expect_ident_rec generation ──

#[test]
fn test_generated_code_contains_expect_token_rec() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("expect_token_rec"),
        "generated code should contain expect_token_rec recovery helper"
    );
}

#[test]
fn test_generated_code_contains_expect_ident_rec() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("expect_ident_rec"),
        "generated code should contain expect_ident_rec recovery helper"
    );
}

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

#[test]
fn test_generated_code_contains_recovering_parser() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("parse_Int_recovering"),
        "generated code should contain parse_Int_recovering function"
    );
}

#[test]
fn test_recovering_parser_takes_errors_param() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The recovering parser should take an errors accumulator
    let fn_start = code_str
        .find("parse_Int_recovering")
        .expect("parse_Int_recovering should exist");
    let fn_area = &code_str[fn_start..fn_start + 300.min(code_str.len() - fn_start)];

    assert!(
        fn_area.contains("errors"),
        "parse_Int_recovering should take an errors parameter, got: {}",
        &fn_area[..200.min(fn_area.len())]
    );
}

#[test]
fn test_recovering_parser_returns_option() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The recovering parser should return Option<Cat>
    let fn_start = code_str
        .find("parse_Int_recovering")
        .expect("parse_Int_recovering should exist");
    let fn_area = &code_str[fn_start..fn_start + 300.min(code_str.len() - fn_start)];

    assert!(
        fn_area.contains("Option"),
        "parse_Int_recovering should return Option<Int>, got: {}",
        &fn_area[..200.min(fn_area.len())]
    );
}

// ── Multi-category sync predicate ──

#[test]
fn test_multi_category_generates_separate_sync_predicates() {
    let mut spec = calculator_spec();
    spec.types.push(CategorySpec {
        name: "Bool".to_string(),
        native_type: Some("bool".to_string()),
        is_primary: false,
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
    assert!(
        code_str.contains("parse_Int_recovering"),
        "should generate recovering parser for Int"
    );
    assert!(
        code_str.contains("parse_Bool_recovering"),
        "should generate recovering parser for Bool"
    );
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

// ── Beam pruning constant (Sprint 4) ──

#[test]
fn test_generated_code_contains_recovery_beam_width() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("RECOVERY_BEAM_WIDTH"),
        "generated code should contain RECOVERY_BEAM_WIDTH constant"
    );
}

// ── Error cascade prevention (Sprint 15) ──

#[test]
fn test_generated_code_contains_cascade_prevention() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Should contain thread-local for tracking last error position
    assert!(
        code_str.contains("LAST_ERROR_POS_Int"),
        "recovering parser should use LAST_ERROR_POS_Int for cascade prevention"
    );
}

// ── Incremental bracket tracking (Sprint 2) ──

#[test]
fn test_generated_recovery_uses_incremental_bracket_tracking() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Should use thread-local BRACKET_STATE, not a backward scan
    assert!(
        code_str.contains("BRACKET_STATE_Int"),
        "recovering parser should use thread-local BRACKET_STATE_Int"
    );

    // Should NOT contain the old backward-scan pattern
    assert!(
        !code_str.contains("for i in 0 .. * pos"),
        "recovering parser should not use backward scan (O(pos) per error)"
    );
}

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

#[test]
fn test_generated_recovery_uses_recovery_applied() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The generated recovering parser should construct RecoveryApplied errors
    assert!(
        code_str.contains("RecoveryApplied"),
        "recovering parser should emit RecoveryApplied errors"
    );

    // The wfst_recover function should return Option<String>
    // TokenStream stringification may add spaces around angle brackets
    assert!(
        code_str.contains("Option < String >") || code_str.contains("Option<String>"),
        "wfst_recover should return Option<String> for repair description"
    );
}

// ── ParseSimulator Tier 3 activation (Sprint 1) ──

#[test]
fn test_generated_code_contains_parse_simulator() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("PARSE_SIMULATOR"),
        "generated code should contain PARSE_SIMULATOR LazyLock"
    );
}

#[test]
fn test_generated_code_contains_sim_first_sets() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("SIM_FIRST_SETS"),
        "generated code should contain SIM_FIRST_SETS static array"
    );
    assert!(
        code_str.contains("SIM_FOLLOW_SETS"),
        "generated code should contain SIM_FOLLOW_SETS static array"
    );
    assert!(
        code_str.contains("SIM_INFIX_SETS"),
        "generated code should contain SIM_INFIX_SETS static array"
    );
}

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

#[test]
fn test_generated_recovery_uses_tier3_simulation() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The wfst_recover function should call simulate_after_repair
    assert!(
        code_str.contains("simulate_after_repair"),
        "wfst_recover should call PARSE_SIMULATOR.simulate_after_repair()"
    );

    // Should compute sim_mult via cost_multiplier
    assert!(
        code_str.contains("cost_multiplier"),
        "wfst_recover should call PARSE_SIMULATOR.cost_multiplier()"
    );
}

// ── Frame kind propagation (Sprint 5) ──

#[test]
fn test_generated_code_contains_frame_state() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Thread-local FRAME_STATE for depth + frame kind tracking
    assert!(
        code_str.contains("FRAME_STATE_INT"),
        "generated code should contain FRAME_STATE_INT thread-local"
    );
}

#[test]
fn test_generated_code_contains_frame_kind_helper() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // frame_kind_of_Int helper maps stack top to FrameKind u8
    assert!(
        code_str.contains("frame_kind_of_Int"),
        "generated code should contain frame_kind_of_Int helper"
    );
}

#[test]
fn test_recovery_uses_frame_kind_multipliers() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The recovery function should read frame state and apply multipliers
    assert!(
        code_str.contains("frame_kind"),
        "wfst_recover should read frame_kind from FRAME_STATE thread-local"
    );
    assert!(
        code_str.contains("frame_insert_mult"),
        "wfst_recover should compute frame_insert_mult for Collection/Group"
    );
}

// ── Multi-token recovery sequences (Sprint 8) ──

#[test]
fn test_generated_recovery_uses_viterbi_multi_step() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The recovery function should call viterbi_multi_step for multi-step sequences
    assert!(
        code_str.contains("viterbi_multi_step"),
        "wfst_recover should call viterbi_multi_step for multi-step recovery"
    );

    // Should reference RECOVERY_SYNC_TOKENS for the sync set
    assert!(
        code_str.contains("RECOVERY_SYNC_TOKENS_Int"),
        "wfst_recover should use RECOVERY_SYNC_TOKENS_Int for Viterbi sync set"
    );
}

// ── Cross-category recovery (Sprint 10) ──

#[test]
fn test_multi_category_generates_cross_cat_casts() {
    let mut spec = calculator_spec();
    spec.types.push(CategorySpec {
        name: "Bool".to_string(),
        native_type: Some("bool".to_string()),
        is_primary: false,
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
    // Add a cast rule: BoolToInt (Bool → Int)
    spec.rules.push(RuleSpec::classified(
        "BoolToInt",
        "Int",
        vec![SyntaxItemSpec::NonTerminal {
            category: "Bool".to_string(),
            param_name: "val".to_string(),
        }],
        &category_names,
    ));

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Int has a cast from Bool, so CROSS_CAT_CASTS_Int should exist
    assert!(
        code_str.contains("CROSS_CAT_CASTS_Int"),
        "multi-category code with cast should contain CROSS_CAT_CASTS_Int"
    );
}

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
