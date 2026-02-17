//! Integration tests for the full parser generation pipeline.

use crate::{
    binding_power::Associativity,
    generate_parser,
    CategorySpec, LanguageSpec, RuleSpec, SyntaxItemSpec,
};

/// Build a simple calculator language spec for testing.
fn calculator_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Calculator".to_string(),
        types: vec![
            CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
            },
        ],
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
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
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
            // Mul: Int "*" Int
            RuleSpec {
                label: "Mul".to_string(),
                category: "Int".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("*".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
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
                syntax: vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
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

#[test]
fn test_generate_parser_produces_code() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Should contain lexer components
    assert!(code_str.contains("Token"), "should contain Token enum");
    assert!(code_str.contains("Span"), "should contain Span struct");
    assert!(code_str.contains("lex"), "should contain lex function");

    // Should contain parser components
    assert!(code_str.contains("parse_Int"), "should contain parse_Int function");
    assert!(code_str.contains("infix_bp"), "should contain infix_bp function");
    assert!(code_str.contains("make_infix"), "should contain make_infix function");

    // Should contain parse entry point
    assert!(code_str.contains("parse"), "should contain parse method");
}

#[test]
fn test_generate_parser_code_size() {
    let spec = calculator_spec();
    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Count approximate lines (by counting newline-separated statements)
    let lines = code_str.matches(';').count() + code_str.matches('{').count();

    // For a simple calculator, generated code should be compact
    // (much less than LALRPOP's ~1,000 lines for Calculator)
    assert!(
        lines < 500,
        "generated code should be compact, got ~{} lines",
        lines
    );
}

#[test]
fn test_generate_parser_two_categories() {
    let spec = LanguageSpec {
        name: "TypedCalc".to_string(),
        types: vec![
            CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i32".to_string()),
                is_primary: true,
            },
            CategorySpec {
                name: "Bool".to_string(),
                native_type: Some("bool".to_string()),
                is_primary: false,
            },
        ],
        rules: vec![
            // Int rules
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
            RuleSpec {
                label: "Add".to_string(),
                category: "Int".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
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
            RuleSpec {
                label: "IVar".to_string(),
                category: "Int".to_string(),
                syntax: vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
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
            // Bool rules
            RuleSpec {
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
            },
            // Eq: cross-category: Int "==" Int → Bool
            RuleSpec {
                label: "Eq".to_string(),
                category: "Bool".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("==".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
                ],
                is_infix: false, // cross-category, not same-category infix
                associativity: Associativity::Left,
                is_var: false,
                is_literal: false,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: true,
                cross_source_category: Some("Int".to_string()),
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
            },
            RuleSpec {
                label: "BVar".to_string(),
                category: "Bool".to_string(),
                syntax: vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
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
    };

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Should contain both categories' parsers
    assert!(code_str.contains("parse_Int"), "should contain parse_Int");
    assert!(code_str.contains("parse_Bool"), "should contain parse_Bool");
}

#[test]
fn test_generate_parser_with_unary_prefix() {
    let mut spec = calculator_spec();

    // Add Sub as infix rule (shares "-" token with Neg)
    spec.rules.push(RuleSpec {
        label: "Sub".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
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
    });

    // Add Neg as unary prefix rule
    spec.rules.push(RuleSpec {
        label: "Neg".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
        ],
        is_infix: false,
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
        is_unary_prefix: true,
        prefix_precedence: None,
        is_postfix: false,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
    });

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Verify the Neg prefix handler function is generated
    assert!(code_str.contains("parse_neg"), "should contain parse_neg function");
    // Verify Minus token handling exists (for both prefix and infix)
    assert!(code_str.contains("Minus"), "should contain Minus token handling");
}

#[test]
fn test_generate_parser_with_optional() {
    let mut spec = calculator_spec();

    // Add a rule with an Optional syntax item:
    // IfExpr: "if" Int #opt("else" Int) → Int
    spec.rules.push(RuleSpec {
        label: "IfExpr".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::Terminal("if".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "cond".to_string() },
            SyntaxItemSpec::Optional {
                inner: vec![
                    SyntaxItemSpec::Terminal("else".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "alt".to_string() },
                ],
            },
        ],
        is_infix: false,
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
    });

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Verify the IfExpr RD handler is generated
    assert!(code_str.contains("parse_ifexpr"), "should contain parse_ifexpr function");
    // Verify optional group codegen (save/restore pattern)
    assert!(code_str.contains("saved_pos"), "should contain saved_pos for optional save/restore");
}

#[test]
fn test_generate_parser_with_right_associativity() {
    let mut spec = calculator_spec();

    // Add Pow as right-associative infix
    spec.rules.push(RuleSpec {
        label: "Pow".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("^".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
        ],
        is_infix: true,
        associativity: Associativity::Right,
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
    });

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Verify the Caret token and Pow handling exist
    assert!(code_str.contains("Caret"), "should contain Caret token for ^ operator");
    // Verify binding power table exists (Pow should have right-assoc bp pair)
    assert!(code_str.contains("infix_bp"), "should contain infix_bp function");
}

#[test]
fn test_generate_parser_with_postfix() {
    let mut spec = calculator_spec();

    // Add Fact as postfix operator: Int "!" → Int
    spec.rules.push(RuleSpec {
        label: "Fact".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("!".to_string()),
        ],
        is_infix: true, // participates in Pratt led loop
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
        is_postfix: true,
        has_rust_code: false,
        rust_code: None,
        eval_mode: None,
    });

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Verify postfix-specific generated code
    assert!(code_str.contains("postfix_bp"), "should contain postfix_bp function");
    assert!(code_str.contains("make_postfix"), "should contain make_postfix function");
    assert!(code_str.contains("Bang"), "should contain Bang token for ! operator");
    // Verify infix handling still exists for Add and Mul
    assert!(code_str.contains("infix_bp"), "should contain infix_bp function");
    assert!(code_str.contains("make_infix"), "should contain make_infix function");
}

#[test]
fn test_generate_parser_with_mixfix() {
    let mut spec = calculator_spec();

    // Add Ternary as mixfix operator: Int "?" Int ":" Int → Int
    spec.rules.push(RuleSpec {
        label: "Ternary".to_string(),
        category: "Int".to_string(),
        syntax: vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "cond".to_string() },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "then_val".to_string() },
            SyntaxItemSpec::Terminal(":".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "else_val".to_string() },
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
    });

    let code = generate_parser(&spec);
    let code_str = code.to_string();

    // Verify mixfix-specific generated code
    assert!(code_str.contains("mixfix_bp"), "should contain mixfix_bp function");
    // In trampolined parser, mixfix is handled inline in the infix loop (no separate handle_mixfix fn)
    assert!(code_str.contains("Question"), "should contain Question token for ? trigger");
    assert!(code_str.contains("Colon"), "should contain Colon token for : separator");
    assert!(code_str.contains("Ternary"), "should contain Ternary constructor");
    // Verify regular infix handling still exists for Add and Mul
    assert!(code_str.contains("infix_bp"), "should contain infix_bp function");
    assert!(code_str.contains("make_infix"), "should contain make_infix function");
}
