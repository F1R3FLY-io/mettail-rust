//! Tests for the lexer pipeline orchestration.

use crate::lexer::{extract_terminals, generate_lexer, GrammarRuleInfo, TypeInfo};

#[test]
fn test_extract_terminals_simple() {
    let rules = vec![
        GrammarRuleInfo {
            label: "Add".to_string(),
            category: "Int".to_string(),
            terminals: vec!["+".to_string()],
            is_infix: true,
        },
        GrammarRuleInfo {
            label: "Mul".to_string(),
            category: "Int".to_string(),
            terminals: vec!["*".to_string()],
            is_infix: true,
        },
    ];

    let types = vec![TypeInfo {
        name: "Int".to_string(),
        language_name: "Calculator".to_string(),
        native_type_name: Some("i32".to_string()),
    }];

    let input = extract_terminals(&rules, &types, false, &[]);

    assert!(input.needs.ident, "should need identifiers");
    assert!(input.needs.integer, "should need integers for i32 native type");
    assert!(!input.needs.float, "should not need floats");
    assert!(!input.needs.string_lit, "should not need string literals");

    // Should have at least + and * terminals
    assert!(input.terminals.iter().any(|t| t.text == "+"), "should include '+' terminal");
    assert!(input.terminals.iter().any(|t| t.text == "*"), "should include '*' terminal");
}

#[test]
fn test_extract_terminals_with_bool() {
    let rules = vec![GrammarRuleInfo {
        label: "And".to_string(),
        category: "Bool".to_string(),
        terminals: vec!["&&".to_string()],
        is_infix: true,
    }];

    let types = vec![TypeInfo {
        name: "Bool".to_string(),
        language_name: "Logic".to_string(),
        native_type_name: Some("bool".to_string()),
    }];

    let input = extract_terminals(&rules, &types, false, &[]);

    assert!(input.needs.boolean, "should need booleans for bool native type");

    // Should have "true" and "false" as keyword terminals
    assert!(
        input.terminals.iter().any(|t| t.text == "true"),
        "should include 'true' keyword"
    );
    assert!(
        input.terminals.iter().any(|t| t.text == "false"),
        "should include 'false' keyword"
    );
}

#[test]
fn test_generate_lexer_produces_code() {
    let rules = vec![GrammarRuleInfo {
        label: "Add".to_string(),
        category: "Int".to_string(),
        terminals: vec!["+".to_string()],
        is_infix: true,
    }];

    let types = vec![TypeInfo {
        name: "Int".to_string(),
        language_name: "Simple".to_string(),
        native_type_name: Some("i32".to_string()),
    }];

    let input = extract_terminals(&rules, &types, false, &[]);
    let (code, stats) = generate_lexer(&input);

    // Verify code is non-empty
    let code_str = code.to_string();
    assert!(!code_str.is_empty(), "generated code should not be empty");

    // Verify it contains expected elements
    assert!(code_str.contains("Token"), "should contain Token enum");
    assert!(code_str.contains("Span"), "should contain Span struct");
    assert!(code_str.contains("lex"), "should contain lex function");

    // Verify stats are reasonable
    assert!(stats.num_terminals > 0, "should have at least one terminal");
    assert!(stats.num_nfa_states > 0, "should have NFA states");
    assert!(stats.num_dfa_states > 0, "should have DFA states");
    assert!(stats.num_minimized_states > 0, "should have minimized states");
    assert!(
        stats.num_minimized_states <= stats.num_dfa_states,
        "minimized should have <= states than original DFA"
    );
    assert!(stats.num_equiv_classes > 0, "should have equivalence classes");
}

#[test]
fn test_lexer_stats_rhocalc() {
    let rules = vec![
        GrammarRuleInfo {
            label: "PZero".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["{}".to_string()],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "PDrop".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["*".to_string()],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "PPar".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["{".to_string(), "|".to_string(), "}".to_string()],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "POutput".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["!".to_string(), "(".to_string(), ")".to_string()],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "PInputs".to_string(),
            category: "Proc".to_string(),
            terminals: vec![
                "(".to_string(),
                "?".to_string(),
                ",".to_string(),
                ")".to_string(),
                ".".to_string(),
                "{".to_string(),
                "}".to_string(),
            ],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "Add".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["+".to_string()],
            is_infix: true,
        },
        GrammarRuleInfo {
            label: "Err".to_string(),
            category: "Proc".to_string(),
            terminals: vec!["error".to_string()],
            is_infix: false,
        },
        GrammarRuleInfo {
            label: "CastInt".to_string(),
            category: "Proc".to_string(),
            terminals: vec![],
            is_infix: false,
        },
    ];

    let types = vec![
        TypeInfo {
            name: "Proc".to_string(),
            language_name: "RhoCalc".to_string(),
            native_type_name: None,
        },
        TypeInfo {
            name: "Name".to_string(),
            language_name: "RhoCalc".to_string(),
            native_type_name: None,
        },
        TypeInfo {
            name: "Int".to_string(),
            language_name: "RhoCalc".to_string(),
            native_type_name: Some("i32".to_string()),
        },
    ];

    let input = extract_terminals(&rules, &types, false, &[]);
    let (_code, stats) = generate_lexer(&input);

    // RhoCalc should have reasonable stats
    assert!(
        stats.num_equiv_classes < 30,
        "RhoCalc should have <30 equivalence classes, got {}",
        stats.num_equiv_classes
    );
    assert!(
        stats.num_minimized_states < 30,
        "RhoCalc minimized DFA should have <30 states, got {}",
        stats.num_minimized_states
    );
}
