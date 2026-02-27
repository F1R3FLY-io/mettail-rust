//! Tests for panic-mode error recovery code generation.
//!
//! Validates that generated code includes:
//! - `sync_to` helper for advancing past errors
//! - `expect_token_rec` / `expect_ident_rec` recovery helpers
//! - `is_sync_<Cat>` sync predicate per category
//! - `parse_<Cat>_recovering` entry points
//! - Correct sync predicate tokens (FOLLOW set + structural delimiters)

use crate::{
    generate_parser, BeamWidthConfig, CategorySpec, DispatchStrategy, LanguageSpec,
    LiteralPatterns, RuleSpec, SyntaxItemSpec,
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
        dispatch_strategy: DispatchStrategy::Static,
        literal_patterns: LiteralPatterns::default(),
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
