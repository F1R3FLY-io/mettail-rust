//! Integration tests for the full parser generation pipeline.

use crate::{
    binding_power::Associativity, generate_parser, BeamWidthConfig, CategorySpec, DispatchStrategy,
    LanguageSpec, RuleSpec, SyntaxItemSpec,
};

/// Helper: extract category names from a slice of `CategorySpec`.
fn category_names(types: &[CategorySpec]) -> Vec<String> {
    types.iter().map(|t| t.name.clone()).collect()
}

/// Build a simple calculator language spec for testing.
fn calculator_spec() -> LanguageSpec {
    let types = vec![CategorySpec {
        name: "Int".to_string(),
        native_type: Some("i32".to_string()),
        is_primary: true,
        has_var: true,
    }];
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
                &cat_names,
            ),
            // Mul: Int "*" Int
            RuleSpec::classified(
                "Mul",
                "Int",
                vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                    SyntaxItemSpec::Terminal("*".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "b".to_string(),
                    },
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
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
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
    assert!(lines < 500, "generated code should be compact, got ~{} lines", lines);
}

#[test]
fn test_generate_parser_two_categories() {
    let types = vec![
        CategorySpec {
            name: "Int".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
            has_var: true,
        },
        CategorySpec {
            name: "Bool".to_string(),
            native_type: Some("bool".to_string()),
            is_primary: false,
            has_var: true,
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
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "a".to_string(),
                    },
                    SyntaxItemSpec::Terminal("==".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "b".to_string(),
                    },
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
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
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
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ],
        &cat_names,
    ));

    // Add Neg as unary prefix rule
    spec.rules.push(RuleSpec::classified(
        "Neg",
        "Int",
        vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
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
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "cond".to_string(),
            },
            SyntaxItemSpec::Optional {
                inner: vec![
                    SyntaxItemSpec::Terminal("else".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Int".to_string(),
                        param_name: "alt".to_string(),
                    },
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
    assert!(
        code_str.contains("saved_pos"),
        "should contain saved_pos for optional save/restore"
    );
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
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("^".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
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
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
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
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "cond".to_string(),
            },
            SyntaxItemSpec::Terminal("?".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "then_val".to_string(),
            },
            SyntaxItemSpec::Terminal(":".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "else_val".to_string(),
            },
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

// ══════════════════════════════════════════════════════════════════════════════
// WFST lexer weight emission tests (feature = "wfst")
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "wfst")]
mod wfst_lexer_weight_tests {
    use super::*;
    use crate::automata::{
        codegen::generate_lexer_string,
        minimize::minimize_dfa,
        nfa::{build_nfa, BuiltinNeeds},
        partition::compute_equivalence_classes,
        subset::subset_construction,
        TerminalPattern, TokenKind,
    };

    /// Helper: generate lexer string from terminal specs.
    fn generate_lexer_for(terminal_specs: &[(&str, TokenKind)], needs: BuiltinNeeds) -> String {
        let terminals: Vec<TerminalPattern> = terminal_specs
            .iter()
            .map(|(text, kind)| TerminalPattern {
                text: text.to_string(),
                kind: kind.clone(),
                is_keyword: text.chars().all(|c| c.is_alphanumeric()),
            })
            .collect();
        let token_kinds: Vec<TokenKind> = terminal_specs.iter().map(|(_, k)| k.clone()).collect();
        let nfa = build_nfa(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let dfa = minimize_dfa(&dfa);
        let (code, _) = generate_lexer_string(&dfa, &partition, &token_kinds, "test");
        code
    }

    #[test]
    fn test_generated_code_contains_lex_weighted() {
        let code = generate_lexer_for(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("-", TokenKind::Fixed("-".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        assert!(
            code.contains("lex_weighted"),
            "generated lexer should contain lex_weighted function"
        );
        assert!(
            code.contains("accept_weight"),
            "generated lexer should contain accept_weight function"
        );
        assert!(
            code.contains("lex_weighted_with_file_id"),
            "generated lexer should contain lex_weighted_with_file_id function"
        );
    }

    #[test]
    fn test_generated_code_contains_weight_values() {
        let code = generate_lexer_for(
            &[("+", TokenKind::Fixed("+".to_string()))],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        // Fixed terminals have priority 10 → weight 0.0 (10 - 10)
        // Ident has priority 1 → weight 9.0 (10 - 1)
        // Integer has priority 2 → weight 8.0 (10 - 2)
        assert!(
            code.contains("0.0_f64"),
            "should contain weight 0.0 for Fixed terminals (priority 10)"
        );
        assert!(code.contains("9.0_f64"), "should contain weight 9.0 for Ident (priority 1)");
        assert!(code.contains("8.0_f64"), "should contain weight 8.0 for Integer (priority 2)");
    }

    #[test]
    fn test_generated_lex_weighted_is_valid_rust() {
        let code = generate_lexer_for(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("*", TokenKind::Fixed("*".to_string())),
                ("(", TokenKind::Fixed("(".to_string())),
                (")", TokenKind::Fixed(")".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: true,
                float: true,
                ..Default::default()
            },
        );

        // If this doesn't panic, the generated code is valid Rust
        let _ts: proc_macro2::TokenStream = code
            .parse()
            .expect("generated code with lex_weighted should be valid Rust");
    }

    #[test]
    fn test_lex_weighted_output_includes_f64_return_type() {
        let code = generate_lexer_for(
            &[("+", TokenKind::Fixed("+".to_string()))],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        // lex_weighted should return Vec<(Token<'a>, Range, f64)>
        assert!(
            code.contains("Vec<(Token<'a>, Range, f64)>"),
            "lex_weighted should return Vec<(Token<'a>, Range, f64)>"
        );
    }

    #[test]
    fn test_pipeline_generates_lex_weighted() {
        let spec = calculator_spec();
        let code = generate_parser(&spec);
        let code_str = code.to_string();

        assert!(
            code_str.contains("lex_weighted"),
            "pipeline-generated code should contain lex_weighted"
        );
        assert!(
            code_str.contains("accept_weight"),
            "pipeline-generated code should contain accept_weight"
        );
    }

    #[test]
    fn test_pipeline_generates_wfst_static_embedding() {
        // When dispatch strategy is Weighted, the pipeline should generate
        // CSR static arrays and LazyLock constructors for prediction WFSTs.
        let spec = calculator_spec_weighted();
        let code = generate_parser(&spec);
        let code_str = code.to_string();

        // Should contain WFST static arrays for the category
        assert!(
            code_str.contains("WFST_TRANSITIONS_"),
            "pipeline should generate WFST transition arrays"
        );
        assert!(
            code_str.contains("WFST_STATE_OFFSETS_"),
            "pipeline should generate WFST state offset arrays"
        );
        assert!(
            code_str.contains("WFST_TOKEN_NAMES_"),
            "pipeline should generate WFST token name arrays"
        );
        assert!(
            code_str.contains("WFST_BEAM_WIDTH_"),
            "pipeline should generate WFST beam width static"
        );
        assert!(code_str.contains("LazyLock"), "pipeline should generate LazyLock constructor");
        assert!(
            code_str.contains("PredictionWfst"),
            "pipeline should reference PredictionWfst in generated code"
        );
    }

    #[test]
    fn test_pipeline_wfst_static_embedding_valid_rust() {
        // The full generated code (with WFST statics) should be valid Rust
        let spec = calculator_spec_weighted();
        let code = generate_parser(&spec);
        // If generate_parser returns without panicking, the code parsed as TokenStream
        // successfully. Verify it's non-empty.
        assert!(!code.is_empty(), "generated code with WFST statics should not be empty");
    }

    /// Build a calculator spec with Weighted dispatch strategy to trigger WFST embedding.
    fn calculator_spec_weighted() -> LanguageSpec {
        #[allow(unused_imports)]
        use crate::RuleSpecInput;

        let types = vec![CategorySpec {
            name: "Int".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
            has_var: true,
        }];

        LanguageSpec::with_options(
            "Calculator".to_string(),
            types,
            vec![
                RuleSpecInput {
                    label: "NumLit".to_string(),
                    category: "Int".to_string(),
                    syntax: vec![],
                    associativity: Associativity::Left,
                    prefix_precedence: None,
                    has_rust_code: false,
                    rust_code: None,
                    eval_mode: None,
                },
                RuleSpecInput {
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
                    associativity: Associativity::Left,
                    prefix_precedence: None,
                    has_rust_code: false,
                    rust_code: None,
                    eval_mode: None,
                },
            ],
            BeamWidthConfig::Explicit(1.5),
            None,
            DispatchStrategy::Weighted,
        )
    }

    #[test]
    fn test_pipeline_generates_recovery_static_embedding() {
        // When dispatch strategy is Weighted, recovery WFST statics should be emitted
        let spec = calculator_spec_weighted();
        let code = generate_parser(&spec);
        let code_str = code.to_string();

        assert!(
            code_str.contains("RECOVERY_SYNC_TOKENS_"),
            "pipeline should generate recovery sync token arrays"
        );
        assert!(
            code_str.contains("RECOVERY_SYNC_SOURCES_"),
            "pipeline should generate recovery sync source arrays"
        );
        assert!(
            code_str.contains("RECOVERY_TOKEN_NAMES_"),
            "pipeline should generate recovery token name arrays"
        );
    }

    #[test]
    fn test_wfst_recovery_fn_has_context_params() {
        // The generated wfst_recover_Cat function should accept context parameters
        let spec = calculator_spec_weighted();
        let code = generate_parser(&spec);
        let code_str = code.to_string();

        // Should have the full context-aware signature
        assert!(
            code_str.contains("wfst_recover_"),
            "pipeline should generate wfst_recover function"
        );
        // Check for bracket balance parameters
        assert!(
            code_str.contains("open_parens") || code_str.contains("open_brackets"),
            "wfst_recover function should have bracket balance parameters"
        );
    }

    #[test]
    fn test_non_wfst_lex_unchanged() {
        // Verify that the standard lex() function is still present and unchanged
        let code = generate_lexer_for(
            &[("+", TokenKind::Fixed("+".to_string()))],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        // Standard lex should return Vec<(Token<'a>, Range)> (no weight)
        assert!(
            code.contains(
                "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String>"
            ),
            "standard lex() should return Vec<(Token<'a>, Range)> without weight"
        );
    }
}
