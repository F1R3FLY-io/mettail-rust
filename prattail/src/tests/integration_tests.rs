//! Integration tests for the full parser generation pipeline.

use crate::{
    binding_power::Associativity,
    generate_parser,
    CategorySpec, LanguageSpec, RuleSpec, SyntaxItemSpec,
};

/// Helper: extract category names from a slice of `CategorySpec`.
fn category_names(types: &[CategorySpec]) -> Vec<String> {
    types.iter().map(|t| t.name.clone()).collect()
}

/// Build a simple calculator language spec for testing.
fn calculator_spec() -> LanguageSpec {
    let types = vec![
        CategorySpec {
            name: "Int".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
        },
    ];
    let cat_names = category_names(&types);

    LanguageSpec {
        name: "Calculator".to_string(),
        types,
        rules: vec![
            // NumLit: integer literal
            RuleSpec::classified("NumLit", "Int", vec![], &cat_names),
            // Add: Int "+" Int
            RuleSpec::classified(
                "Add",
                "Int",
                vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
                ],
                &cat_names,
            ),
            // Mul: Int "*" Int
            RuleSpec::classified(
                "Mul",
                "Int",
                vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("*".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
                ],
                &cat_names,
            ),
            // IVar: variable
            RuleSpec::classified(
                "IVar",
                "Int",
                vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                &cat_names,
            ),
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
    let types = vec![
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
    ];
    let cat_names = category_names(&types);

    let spec = LanguageSpec {
        name: "TypedCalc".to_string(),
        types,
        rules: vec![
            // Int rules
            RuleSpec::classified("NumLit", "Int", vec![], &cat_names),
            RuleSpec::classified(
                "Add",
                "Int",
                vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
                ],
                &cat_names,
            ),
            RuleSpec::classified(
                "IVar",
                "Int",
                vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                &cat_names,
            ),
            // Bool rules
            RuleSpec::classified("BoolLit", "Bool", vec![], &cat_names),
            // Eq: cross-category: Int "==" Int → Bool
            // Note: classified() correctly derives is_infix=true for cross-category infix rules.
            // The original manual spec had is_infix=false which was incorrect.
            RuleSpec::classified(
                "Eq",
                "Bool",
                vec![
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
                    SyntaxItemSpec::Terminal("==".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
                ],
                &cat_names,
            ),
            RuleSpec::classified(
                "BVar",
                "Bool",
                vec![SyntaxItemSpec::IdentCapture { param_name: "v".to_string() }],
                &cat_names,
            ),
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
    let cat_names = category_names(&spec.types);

    // Add Sub as infix rule (shares "-" token with Neg)
    spec.rules.push(RuleSpec::classified(
        "Sub",
        "Int",
        vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
        ],
        &cat_names,
    ));

    // Add Neg as unary prefix rule
    spec.rules.push(RuleSpec::classified(
        "Neg",
        "Int",
        vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
        ],
        &cat_names,
    ));

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
    let cat_names = category_names(&spec.types);

    // Add a rule with an Optional syntax item:
    // IfExpr: "if" Int #opt("else" Int) → Int
    spec.rules.push(RuleSpec::classified(
        "IfExpr",
        "Int",
        vec![
            SyntaxItemSpec::Terminal("if".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "cond".to_string() },
            SyntaxItemSpec::Optional {
                inner: vec![
                    SyntaxItemSpec::Terminal("else".to_string()),
                    SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "alt".to_string() },
                ],
            },
        ],
        &cat_names,
    ));

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
    let cat_names = category_names(&spec.types);

    // Add Pow as right-associative infix
    let mut pow = RuleSpec::classified(
        "Pow",
        "Int",
        vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("^".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "b".to_string() },
        ],
        &cat_names,
    );
    pow.associativity = Associativity::Right;
    spec.rules.push(pow);

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
    let cat_names = category_names(&spec.types);

    // Add Fact as postfix operator: Int "!" → Int
    // classified() correctly derives is_postfix=true AND is_infix=true (postfix implies infix).
    spec.rules.push(RuleSpec::classified(
        "Fact",
        "Int",
        vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "a".to_string() },
            SyntaxItemSpec::Terminal("!".to_string()),
        ],
        &cat_names,
    ));

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
    let cat_names = category_names(&spec.types);

    // Add Ternary as mixfix operator: Int "?" Int ":" Int → Int
    spec.rules.push(RuleSpec::classified(
        "Ternary",
        "Int",
        vec![
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "cond".to_string() },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "then_val".to_string() },
            SyntaxItemSpec::Terminal(":".to_string()),
            SyntaxItemSpec::NonTerminal { category: "Int".to_string(), param_name: "else_val".to_string() },
        ],
        &cat_names,
    ));

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
