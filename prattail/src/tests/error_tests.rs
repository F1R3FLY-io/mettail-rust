//! Error case tests for PraTTaIL code generation.
//!
//! Validates that generated parser code includes proper error handling:
//! - ParseError variants (UnexpectedToken, UnexpectedEof, LexError, TrailingTokens)
//! - FIRST-set-based expected messages with friendly names
//! - Error position tracking via Range/Position

use crate::{
    binding_power::Associativity,
    generate_parser,
    CategorySpec, LanguageSpec, RuleSpec, SyntaxItemSpec,
};

/// Build a simple calculator spec for error tests.
fn calculator_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Calculator".to_string(),
        types: vec![CategorySpec {
            name: "Int".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
        }],
        rules: vec![
            // NumLit: integer literal
            RuleSpec {
                label: "NumLit".to_string(),
                category: "Int".to_string(),
                syntax: vec![],
                is_infix: false,
                associativity: Associativity::Left,
                is_var: false,
                is_literal: true,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: false,
                cross_source_category: None,
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            },
            // Add: Int "+" Int
            RuleSpec {
                label: "Add".to_string(),
                category: "Int".to_string(),
                syntax: vec![
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
                is_infix: true,
                associativity: Associativity::Left,
                is_var: false,
                is_literal: false,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: false,
                cross_source_category: None,
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            },
            // IVar: variable
            RuleSpec {
                label: "IVar".to_string(),
                category: "Int".to_string(),
                syntax: vec![SyntaxItemSpec::IdentCapture {
                    param_name: "v".to_string(),
                }],
                is_infix: false,
                associativity: Associativity::Left,
                is_var: true,
                is_literal: false,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: false,
                cross_source_category: None,
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            },
        ],
    }
}

/// Build a multi-category spec with Int and Bool.
fn typed_calc_spec() -> LanguageSpec {
    let mut spec = calculator_spec();
    spec.types.push(CategorySpec {
        name: "Bool".to_string(),
        native_type: Some("bool".to_string()),
        is_primary: false,
    });
    spec.rules.push(RuleSpec {
        label: "BoolLit".to_string(),
        category: "Bool".to_string(),
        syntax: vec![],
        is_infix: false,
        associativity: Associativity::Left,
        is_var: false,
        is_literal: true,
        has_binder: false,
        has_multi_binder: false,
        is_collection: false,
        collection_type: None,
        separator: None,
        is_cross_category: false,
        cross_source_category: None,
        is_cast: false,
        cast_source_category: None,
        is_unary_prefix: false,
        prefix_precedence: None,
        is_postfix: false,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
    });
    spec.rules.push(RuleSpec {
        label: "BVar".to_string(),
        category: "Bool".to_string(),
        syntax: vec![SyntaxItemSpec::IdentCapture {
            param_name: "v".to_string(),
        }],
        is_infix: false,
        associativity: Associativity::Left,
        is_var: true,
        is_literal: false,
        has_binder: false,
        has_multi_binder: false,
        is_collection: false,
        collection_type: None,
        separator: None,
        is_cross_category: false,
        cross_source_category: None,
        is_cast: false,
        cast_source_category: None,
        is_unary_prefix: false,
        prefix_precedence: None,
        is_postfix: false,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
    });
    spec
}

// ── ParseError enum generation ──

#[test]
fn test_generated_code_contains_parse_error_enum() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("ParseError"),
        "generated code should contain ParseError enum"
    );
    assert!(
        code_str.contains("UnexpectedToken"),
        "generated code should contain UnexpectedToken variant"
    );
    assert!(
        code_str.contains("UnexpectedEof"),
        "generated code should contain UnexpectedEof variant"
    );
    assert!(
        code_str.contains("LexError"),
        "generated code should contain LexError variant"
    );
    assert!(
        code_str.contains("TrailingTokens"),
        "generated code should contain TrailingTokens variant"
    );
}

#[test]
fn test_generated_code_contains_position_and_range() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("Position"),
        "generated code should contain Position struct"
    );
    assert!(
        code_str.contains("byte_offset"),
        "Position should have byte_offset field"
    );
    assert!(
        code_str.contains("Range"),
        "generated code should contain Range struct"
    );
}

// ── Expected message generation ──

#[test]
fn test_error_message_includes_integer_literal() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Int category with i32 native type should mention "integer literal" in expected messages
    assert!(
        code_str.contains("integer literal"),
        "expected messages for Int (i32) should include 'integer literal'"
    );
}

#[test]
fn test_error_message_includes_identifier() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Category with IVar should mention "identifier" in expected messages
    assert!(
        code_str.contains("identifier"),
        "expected messages should include 'identifier' for categories with Var rules"
    );
}

#[test]
fn test_error_message_includes_boolean_literal() {
    let spec = typed_calc_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Bool category with bool native type should mention "boolean literal"
    assert!(
        code_str.contains("boolean literal"),
        "expected messages for Bool (bool) should include 'boolean literal'"
    );
}

#[test]
fn test_error_message_includes_category_name() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The expected message should reference the category name
    assert!(
        code_str.contains("Int expression"),
        "expected messages should reference the category name (e.g., 'Int expression')"
    );
}

// ── Error helper function generation ──

#[test]
fn test_generated_code_contains_expect_token() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("expect_token"),
        "generated code should contain expect_token helper function"
    );
}

#[test]
fn test_generated_code_contains_expect_ident() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("expect_ident"),
        "generated code should contain expect_ident helper function"
    );
}

#[test]
fn test_generated_code_contains_format_error_context() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("format_error_context"),
        "generated code should contain format_error_context for source context display"
    );
}

// ── EOF error handling ──

#[test]
fn test_prefix_handler_has_eof_check() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // The prefix handler should check for EOF before matching tokens
    assert!(
        code_str.contains("UnexpectedEof"),
        "prefix handler should check for EOF and return UnexpectedEof"
    );
}

// ── Error implements std::error::Error ──

#[test]
fn test_parse_error_implements_error_trait() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("std :: error :: Error") || code_str.contains("error :: Error"),
        "ParseError should implement std::error::Error"
    );
}

// ── From<String> for ParseError ──

#[test]
fn test_parse_error_from_string() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("From < String > for ParseError")
            || code_str.contains("From<String> for ParseError"),
        "ParseError should implement From<String>"
    );
}

// ── Display for ParseError ──

#[test]
fn test_parse_error_display() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    assert!(
        code_str.contains("Display for ParseError")
            || code_str.contains("fmt :: Display for ParseError"),
        "ParseError should implement Display"
    );
}
