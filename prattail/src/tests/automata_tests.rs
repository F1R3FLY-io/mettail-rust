//! Tests for the automata pipeline: NFA construction, subset construction,
//! minimization, and alphabet partitioning.

use crate::automata::{
    codegen::generate_lexer_string,
    minimize::minimize_dfa,
    nfa::{build_nfa, build_nfa_for_mode, build_nfa_prefix_only, build_nfa_with_custom, BuiltinNeeds},
    partition::compute_equivalence_classes,
    subset::subset_construction,
    TerminalPattern, TokenKind, DEAD_STATE,
};
use crate::CustomTokenSpec;

/// Build a complete automata pipeline for a set of terminals and verify
/// the resulting DFA recognizes the expected tokens.
fn build_pipeline(
    terminals: &[(&str, TokenKind)],
    needs: BuiltinNeeds,
) -> (crate::automata::Dfa, crate::automata::partition::AlphabetPartition) {
    let terminal_patterns: Vec<TerminalPattern> = terminals
        .iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind: kind.clone(),
            is_keyword: text.chars().all(|c| c.is_alphanumeric() || c == '_'),
        })
        .collect();

    let nfa = build_nfa(&terminal_patterns, &needs, &crate::LiteralPatterns::default());
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);

    (min_dfa, partition)
}

/// Simulate lexing a string through the DFA, returning the accepted token kind.
fn lex_string(
    dfa: &crate::automata::Dfa,
    partition: &crate::automata::partition::AlphabetPartition,
    input: &str,
) -> Option<TokenKind> {
    let bytes = input.as_bytes();
    let mut state = dfa.start;

    for &byte in bytes {
        let class = partition.classify(byte);
        state = dfa.transition(state, class);
        if state == DEAD_STATE {
            return None;
        }
    }

    dfa.states[state as usize].accept.clone()
}

#[test]
fn test_single_char_operators() {
    let (dfa, partition) = build_pipeline(
        &[
            ("+", TokenKind::Fixed("+".to_string())),
            ("-", TokenKind::Fixed("-".to_string())),
            ("*", TokenKind::Fixed("*".to_string())),
            ("/", TokenKind::Fixed("/".to_string())),
        ],
        BuiltinNeeds::default(),
    );

    assert_eq!(lex_string(&dfa, &partition, "+"), Some(TokenKind::Fixed("+".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "-"), Some(TokenKind::Fixed("-".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "*"), Some(TokenKind::Fixed("*".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "/"), Some(TokenKind::Fixed("/".to_string())));
}

#[test]
fn test_multi_char_operators() {
    let (dfa, partition) = build_pipeline(
        &[
            ("==", TokenKind::Fixed("==".to_string())),
            ("!=", TokenKind::Fixed("!=".to_string())),
            ("<=", TokenKind::Fixed("<=".to_string())),
            (">=", TokenKind::Fixed(">=".to_string())),
        ],
        BuiltinNeeds::default(),
    );

    assert_eq!(lex_string(&dfa, &partition, "=="), Some(TokenKind::Fixed("==".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "!="), Some(TokenKind::Fixed("!=".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "<="), Some(TokenKind::Fixed("<=".to_string())));
    assert_eq!(lex_string(&dfa, &partition, ">="), Some(TokenKind::Fixed(">=".to_string())));
}

#[test]
fn test_identifiers() {
    let (dfa, partition) = build_pipeline(&[], BuiltinNeeds { ident: true, ..Default::default() });

    assert_eq!(lex_string(&dfa, &partition, "x"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "foo"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "hello_world"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "_private"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "x123"), Some(TokenKind::Ident));
}

#[test]
fn test_integers() {
    let (dfa, partition) =
        build_pipeline(&[], BuiltinNeeds { integer: true, ..Default::default() });

    assert_eq!(lex_string(&dfa, &partition, "0"), Some(TokenKind::Integer));
    assert_eq!(lex_string(&dfa, &partition, "42"), Some(TokenKind::Integer));
    assert_eq!(lex_string(&dfa, &partition, "123456"), Some(TokenKind::Integer));
}

#[test]
fn test_floats() {
    let (dfa, partition) = build_pipeline(&[], BuiltinNeeds { float: true, ..Default::default() });

    assert_eq!(lex_string(&dfa, &partition, "3.14"), Some(TokenKind::Float));
    assert_eq!(lex_string(&dfa, &partition, "0.0"), Some(TokenKind::Float));

    // Scientific notation: [eE][+-]?[0-9]+
    assert_eq!(lex_string(&dfa, &partition, "1.0E2"), Some(TokenKind::Float));
    assert_eq!(lex_string(&dfa, &partition, "1.0e2"), Some(TokenKind::Float));
    assert_eq!(lex_string(&dfa, &partition, "2.5e-1"), Some(TokenKind::Float));
    assert_eq!(lex_string(&dfa, &partition, "2.5E+3"), Some(TokenKind::Float));
    assert_eq!(lex_string(&dfa, &partition, "1.23e10"), Some(TokenKind::Float));

    // Partial exponent (no digits after 'e') should NOT match Float
    assert_eq!(lex_string(&dfa, &partition, "1.0e"), None);
    assert_eq!(lex_string(&dfa, &partition, "1.0e+"), None);
    assert_eq!(lex_string(&dfa, &partition, "1.0E-"), None);
}

#[test]
fn test_keyword_vs_ident_priority() {
    let (dfa, partition) = build_pipeline(
        &[
            ("error", TokenKind::Fixed("error".to_string())),
            ("true", TokenKind::True),
            ("false", TokenKind::False),
        ],
        BuiltinNeeds { ident: true, ..Default::default() },
    );

    // Keywords should be recognized as their specific token kind
    assert_eq!(
        lex_string(&dfa, &partition, "error"),
        Some(TokenKind::Fixed("error".to_string()))
    );
    assert_eq!(lex_string(&dfa, &partition, "true"), Some(TokenKind::True));
    assert_eq!(lex_string(&dfa, &partition, "false"), Some(TokenKind::False));

    // Non-keywords should be identifiers
    assert_eq!(lex_string(&dfa, &partition, "errors"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "truefalse"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "x"), Some(TokenKind::Ident));
}

#[test]
fn test_delimiters() {
    let (dfa, partition) = build_pipeline(
        &[
            ("(", TokenKind::Fixed("(".to_string())),
            (")", TokenKind::Fixed(")".to_string())),
            ("{", TokenKind::Fixed("{".to_string())),
            ("}", TokenKind::Fixed("}".to_string())),
            ("{}", TokenKind::Fixed("{}".to_string())),
        ],
        BuiltinNeeds::default(),
    );

    assert_eq!(lex_string(&dfa, &partition, "("), Some(TokenKind::Fixed("(".to_string())));
    assert_eq!(lex_string(&dfa, &partition, ")"), Some(TokenKind::Fixed(")".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "{"), Some(TokenKind::Fixed("{".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "}"), Some(TokenKind::Fixed("}".to_string())));

    // "{}" should be recognized as a single token (maximal munch)
    assert_eq!(lex_string(&dfa, &partition, "{}"), Some(TokenKind::Fixed("{}".to_string())));
}

#[test]
fn test_rhocalc_terminals() {
    let (dfa, partition) = build_pipeline(
        &[
            ("+", TokenKind::Fixed("+".to_string())),
            ("*", TokenKind::Fixed("*".to_string())),
            ("!", TokenKind::Fixed("!".to_string())),
            ("?", TokenKind::Fixed("?".to_string())),
            ("@", TokenKind::Fixed("@".to_string())),
            (".", TokenKind::Fixed(".".to_string())),
            (",", TokenKind::Fixed(",".to_string())),
            ("|", TokenKind::Fixed("|".to_string())),
            (":", TokenKind::Fixed(":".to_string())),
            ("^", TokenKind::Fixed("^".to_string())),
            ("(", TokenKind::Fixed("(".to_string())),
            (")", TokenKind::Fixed(")".to_string())),
            ("{", TokenKind::Fixed("{".to_string())),
            ("}", TokenKind::Fixed("}".to_string())),
            ("[", TokenKind::Fixed("[".to_string())),
            ("]", TokenKind::Fixed("]".to_string())),
            ("{}", TokenKind::Fixed("{}".to_string())),
            ("error", TokenKind::Fixed("error".to_string())),
        ],
        BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        },
    );

    // Verify all terminals are recognized
    assert_eq!(lex_string(&dfa, &partition, "+"), Some(TokenKind::Fixed("+".to_string())));
    assert_eq!(lex_string(&dfa, &partition, "{}"), Some(TokenKind::Fixed("{}".to_string())));
    assert_eq!(
        lex_string(&dfa, &partition, "error"),
        Some(TokenKind::Fixed("error".to_string()))
    );
    assert_eq!(lex_string(&dfa, &partition, "x"), Some(TokenKind::Ident));
    assert_eq!(lex_string(&dfa, &partition, "42"), Some(TokenKind::Integer));

    // Verify minimization keeps state count reasonable
    assert!(
        dfa.states.len() <= 30,
        "RhoCalc DFA should have at most 30 states after minimization, got {}",
        dfa.states.len()
    );

    // Verify equivalence class compression
    assert!(
        partition.num_classes < 25,
        "RhoCalc should have fewer than 25 equivalence classes, got {}",
        partition.num_classes
    );
}

#[test]
fn test_minimization_reduces_states() {
    // Build with and without minimization and compare
    let terminals: Vec<TerminalPattern> = ["+", "-", "*", "/", "==", "!=", "(", ")", "{", "}"]
        .iter()
        .map(|t| TerminalPattern {
            text: t.to_string(),
            kind: TokenKind::Fixed(t.to_string()),
            is_keyword: false,
        })
        .collect();

    let needs = BuiltinNeeds {
        ident: true,
        integer: true,
        float: false,
        string_lit: false,
        boolean: false,
    };

    let nfa = build_nfa(&terminals, &needs, &crate::LiteralPatterns::default());
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);

    assert!(
        min_dfa.states.len() <= dfa.states.len(),
        "minimized DFA ({}) should have no more states than unminimized ({})",
        min_dfa.states.len(),
        dfa.states.len()
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase 1A: DAFSA vs prefix-only codegen identity tests
// ══════════════════════════════════════════════════════════════════════════════

/// Helper: run full automata pipeline (NFA → partition → DFA → minimize → codegen string)
/// for a given NFA, returning the generated code and token_kinds used.
fn run_codegen_pipeline(
    terminals: &[TerminalPattern],
    needs: &BuiltinNeeds,
    use_prefix_only: bool,
) -> String {
    let nfa = if use_prefix_only {
        build_nfa_prefix_only(terminals, needs)
    } else {
        build_nfa(terminals, needs, &crate::LiteralPatterns::default())
    };
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);

    // Collect token kinds (same logic as lexer.rs)
    let mut token_kinds: Vec<TokenKind> = vec![TokenKind::Eof];
    if needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if needs.integer {
        token_kinds.push(TokenKind::Integer);
    }
    if needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if needs.boolean {
        token_kinds.push(TokenKind::True);
        token_kinds.push(TokenKind::False);
    }
    if needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    for terminal in terminals {
        token_kinds.push(terminal.kind.clone());
    }

    let (code, _strategy, _variant_map, _ambiguity) =
        generate_lexer_string(&min_dfa, &partition, &token_kinds, "test", &[]);
    code
}

/// Build terminal set for the Ambient Calculus grammar.
fn ambient_terminals() -> (Vec<TerminalPattern>, BuiltinNeeds) {
    let terms: Vec<(&str, TokenKind)> = vec![
        ("(", TokenKind::Fixed("(".to_string())),
        (")", TokenKind::Fixed(")".to_string())),
        (",", TokenKind::Fixed(",".to_string())),
        (".", TokenKind::Fixed(".".to_string())),
        ("0", TokenKind::Fixed("0".to_string())),
        ("[", TokenKind::Fixed("[".to_string())),
        ("]", TokenKind::Fixed("]".to_string())),
        ("{", TokenKind::Fixed("{".to_string())),
        ("}", TokenKind::Fixed("}".to_string())),
        ("|", TokenKind::Fixed("|".to_string())),
        ("in", TokenKind::Fixed("in".to_string())),
        ("new", TokenKind::Fixed("new".to_string())),
        ("open", TokenKind::Fixed("open".to_string())),
        ("out", TokenKind::Fixed("out".to_string())),
    ];

    let terminals: Vec<TerminalPattern> = terms
        .into_iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind,
            is_keyword: text.chars().all(|c| c.is_alphanumeric() || c == '_'),
        })
        .collect();

    let needs = BuiltinNeeds { ident: true, ..Default::default() };

    (terminals, needs)
}

/// Build terminal set for the Calculator grammar.
fn calculator_terminals() -> (Vec<TerminalPattern>, BuiltinNeeds) {
    let terms: Vec<(&str, TokenKind)> = vec![
        ("!", TokenKind::Fixed("!".to_string())),
        ("&&", TokenKind::Fixed("&&".to_string())),
        ("(", TokenKind::Fixed("(".to_string())),
        (")", TokenKind::Fixed(")".to_string())),
        ("+", TokenKind::Fixed("+".to_string())),
        ("++", TokenKind::Fixed("++".to_string())),
        (",", TokenKind::Fixed(",".to_string())),
        ("-", TokenKind::Fixed("-".to_string())),
        (":", TokenKind::Fixed(":".to_string())),
        ("==", TokenKind::Fixed("==".to_string())),
        ("?", TokenKind::Fixed("?".to_string())),
        ("[", TokenKind::Fixed("[".to_string())),
        ("]", TokenKind::Fixed("]".to_string())),
        ("^", TokenKind::Fixed("^".to_string())),
        ("false", TokenKind::False),
        ("not", TokenKind::Fixed("not".to_string())),
        ("true", TokenKind::True),
        ("{", TokenKind::Fixed("{".to_string())),
        ("|", TokenKind::Fixed("|".to_string())),
        ("}", TokenKind::Fixed("}".to_string())),
        ("~", TokenKind::Fixed("~".to_string())),
    ];

    let terminals: Vec<TerminalPattern> = terms
        .into_iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind,
            is_keyword: text.chars().all(|c| c.is_alphanumeric() || c == '_'),
        })
        .collect();

    let needs = BuiltinNeeds {
        ident: true,
        integer: true,
        float: true,
        boolean: true,
        string_lit: true,
    };

    (terminals, needs)
}

/// Build terminal set for the Lambda Calculus grammar.
fn lambda_terminals() -> (Vec<TerminalPattern>, BuiltinNeeds) {
    let terms: Vec<(&str, TokenKind)> = vec![
        ("(", TokenKind::Fixed("(".to_string())),
        (")", TokenKind::Fixed(")".to_string())),
        (",", TokenKind::Fixed(",".to_string())),
        (".", TokenKind::Fixed(".".to_string())),
        ("[", TokenKind::Fixed("[".to_string())),
        ("]", TokenKind::Fixed("]".to_string())),
        ("lam ", TokenKind::Fixed("lam ".to_string())),
        ("{", TokenKind::Fixed("{".to_string())),
        ("}", TokenKind::Fixed("}".to_string())),
    ];

    let terminals: Vec<TerminalPattern> = terms
        .into_iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind,
            is_keyword: text
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == ' '),
        })
        .collect();

    let needs = BuiltinNeeds { ident: true, ..Default::default() };

    (terminals, needs)
}

/// Build terminal set for the RhoCalc grammar.
fn rhocalc_terminals() -> (Vec<TerminalPattern>, BuiltinNeeds) {
    let terms: Vec<(&str, TokenKind)> = vec![
        ("!", TokenKind::Fixed("!".to_string())),
        ("(", TokenKind::Fixed("(".to_string())),
        (")", TokenKind::Fixed(")".to_string())),
        ("+", TokenKind::Fixed("+".to_string())),
        (",", TokenKind::Fixed(",".to_string())),
        (".", TokenKind::Fixed(".".to_string())),
        (":", TokenKind::Fixed(":".to_string())),
        ("?", TokenKind::Fixed("?".to_string())),
        ("@", TokenKind::Fixed("@".to_string())),
        ("[", TokenKind::Fixed("[".to_string())),
        ("]", TokenKind::Fixed("]".to_string())),
        ("^", TokenKind::Fixed("^".to_string())),
        ("error", TokenKind::Fixed("error".to_string())),
        ("{", TokenKind::Fixed("{".to_string())),
        ("{}", TokenKind::Fixed("{}".to_string())),
        ("|", TokenKind::Fixed("|".to_string())),
        ("}", TokenKind::Fixed("}".to_string())),
        ("*", TokenKind::Fixed("*".to_string())),
    ];

    let terminals: Vec<TerminalPattern> = terms
        .into_iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind,
            is_keyword: text.chars().all(|c| c.is_alphanumeric() || c == '_'),
        })
        .collect();

    let needs = BuiltinNeeds {
        ident: true,
        integer: true,
        ..Default::default()
    };

    (terminals, needs)
}

#[test]
fn test_dafsa_vs_prefix_identical_codegen_ambient() {
    let (terminals, needs) = ambient_terminals();
    let dafsa_code = run_codegen_pipeline(&terminals, &needs, false);
    let prefix_code = run_codegen_pipeline(&terminals, &needs, true);
    assert_eq!(
        dafsa_code, prefix_code,
        "Ambient: DAFSA and prefix-only should produce identical lexer code"
    );
}

#[test]
fn test_dafsa_vs_prefix_identical_codegen_calculator() {
    let (terminals, needs) = calculator_terminals();
    let dafsa_code = run_codegen_pipeline(&terminals, &needs, false);
    let prefix_code = run_codegen_pipeline(&terminals, &needs, true);
    assert_eq!(
        dafsa_code, prefix_code,
        "Calculator: DAFSA and prefix-only should produce identical lexer code"
    );
}

#[test]
fn test_dafsa_vs_prefix_identical_codegen_lambda() {
    let (terminals, needs) = lambda_terminals();
    let dafsa_code = run_codegen_pipeline(&terminals, &needs, false);
    let prefix_code = run_codegen_pipeline(&terminals, &needs, true);
    assert_eq!(
        dafsa_code, prefix_code,
        "Lambda: DAFSA and prefix-only should produce identical lexer code"
    );
}

#[test]
fn test_dafsa_vs_prefix_identical_codegen_rhocalc() {
    let (terminals, needs) = rhocalc_terminals();
    let dafsa_code = run_codegen_pipeline(&terminals, &needs, false);
    let prefix_code = run_codegen_pipeline(&terminals, &needs, true);
    assert_eq!(
        dafsa_code, prefix_code,
        "RhoCalc: DAFSA and prefix-only should produce identical lexer code"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Custom token NFA unit tests
// ══════════════════════════════════════════════════════════════════════════════

/// Helper to create a [`CustomTokenSpec`] with common defaults.
fn custom_token(name: &str, pattern: &str, priority: u8) -> CustomTokenSpec {
    CustomTokenSpec {
        name: name.to_string(),
        pattern: pattern.to_string(),
        category: None,
        payload_type: None,
        constructor_code: None,
        is_builtin_override: false,
        priority,
        push_mode: None,
        is_pop: false,
        stream: None,
    }
}

/// Build pipeline with custom tokens.
fn build_pipeline_with_custom(
    terminals: &[(&str, TokenKind)],
    needs: BuiltinNeeds,
    custom_tokens: &[CustomTokenSpec],
) -> (crate::automata::Dfa, crate::automata::partition::AlphabetPartition) {
    let terminal_patterns: Vec<TerminalPattern> = terminals
        .iter()
        .map(|(text, kind)| TerminalPattern {
            text: text.to_string(),
            kind: kind.clone(),
            is_keyword: text.chars().all(|c| c.is_alphanumeric() || c == '_'),
        })
        .collect();

    let nfa = build_nfa_with_custom(
        &terminal_patterns,
        &needs,
        &crate::LiteralPatterns::default(),
        custom_tokens,
    );
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);

    (min_dfa, partition)
}

/// Build pipeline for a mode's custom tokens only.
fn build_mode_pipeline(
    custom_tokens: &[CustomTokenSpec],
) -> (crate::automata::Dfa, crate::automata::partition::AlphabetPartition) {
    let nfa = build_nfa_for_mode(custom_tokens);
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);
    (min_dfa, partition)
}

#[test]
fn test_custom_token_nfa() {
    let hex_token = custom_token("HexLiteral", "0x[0-9a-fA-F]+", 2);
    let (dfa, partition) = build_pipeline_with_custom(&[], BuiltinNeeds::default(), &[hex_token]);

    // "0xFF" should be accepted as Custom("HexLiteral")
    assert_eq!(
        lex_string(&dfa, &partition, "0xFF"),
        Some(TokenKind::Custom("HexLiteral".into())),
        "0xFF should be recognized as a HexLiteral custom token"
    );

    // "0xGG" should NOT match — 'G' is not a valid hex digit
    assert_eq!(
        lex_string(&dfa, &partition, "0xGG"),
        None,
        "0xGG should not match any token (G is not a hex digit)"
    );
}

#[test]
fn test_custom_token_priority() {
    let alpha_num = custom_token("AlphaNum", "[a-z0-9]+", 2);
    let hex_lit = custom_token("HexLit", "[0-9a-f]+", 5);
    let (dfa, partition) =
        build_pipeline_with_custom(&[], BuiltinNeeds::default(), &[alpha_num, hex_lit]);

    // "xyz" contains letters outside hex range — only AlphaNum can match
    assert_eq!(
        lex_string(&dfa, &partition, "xyz"),
        Some(TokenKind::Custom("AlphaNum".into())),
        "xyz should match AlphaNum (not valid hex)"
    );

    // "999" is valid for both patterns; the higher-priority HexLit should win
    assert_eq!(
        lex_string(&dfa, &partition, "999"),
        Some(TokenKind::Custom("HexLit".into())),
        "999 is valid hex and alphanumeric — higher-priority HexLit should win"
    );
}

#[test]
fn test_builtin_override_pattern() {
    // Create a custom spec with is_builtin_override = true.
    // The NFA builder skips builtin overrides (they modify LiteralPatterns instead),
    // so "0xFF" should NOT be recognized as Custom("Integer").
    let override_spec = CustomTokenSpec {
        name: "Integer".to_string(),
        pattern: "0x[0-9a-fA-F]+|[0-9]+".to_string(),
        category: None,
        payload_type: None,
        constructor_code: None,
        is_builtin_override: true,
        priority: 2,
        push_mode: None,
        is_pop: false,
        stream: None,
    };

    let (dfa, partition) =
        build_pipeline_with_custom(&[], BuiltinNeeds::default(), &[override_spec]);

    // Since the override path modifies LiteralPatterns (not the NFA custom fragment),
    // "0xFF" should NOT match Custom("Integer").
    assert_ne!(
        lex_string(&dfa, &partition, "0xFF"),
        Some(TokenKind::Custom("Integer".into())),
        "builtin override should NOT appear as a Custom token in the NFA"
    );
}

#[test]
fn test_multi_mode_nfa() {
    let string_chars = custom_token("StringChars", "[^\"\\\\]+", 2);
    let string_end = custom_token("StringEnd", "\"", 2);
    let (dfa, partition) = build_mode_pipeline(&[string_chars, string_end]);

    // "hello world" (non-quote, non-backslash chars) → StringChars
    assert_eq!(
        lex_string(&dfa, &partition, "hello world"),
        Some(TokenKind::Custom("StringChars".into())),
        "plain text should match StringChars in string mode"
    );

    // A lone double-quote → StringEnd
    assert_eq!(
        lex_string(&dfa, &partition, "\""),
        Some(TokenKind::Custom("StringEnd".into())),
        "a double-quote should match StringEnd in string mode"
    );

    // Empty string matches nothing (no token consumes zero characters)
    assert_eq!(
        lex_string(&dfa, &partition, ""),
        None,
        "empty input should not match any mode token"
    );
}

#[test]
fn test_custom_token_alongside_builtins() {
    let bin_literal = custom_token("BinLiteral", "0b[01]+", 2);
    let needs = BuiltinNeeds {
        ident: true,
        integer: true,
        ..Default::default()
    };
    let (dfa, partition) = build_pipeline_with_custom(&[], needs, &[bin_literal]);

    // "foo" → Ident (built-in)
    assert_eq!(
        lex_string(&dfa, &partition, "foo"),
        Some(TokenKind::Ident),
        "foo should be recognized as a built-in Ident"
    );

    // "42" → Integer (built-in)
    assert_eq!(
        lex_string(&dfa, &partition, "42"),
        Some(TokenKind::Integer),
        "42 should be recognized as a built-in Integer"
    );

    // "0b1010" → Custom("BinLiteral")
    assert_eq!(
        lex_string(&dfa, &partition, "0b1010"),
        Some(TokenKind::Custom("BinLiteral".into())),
        "0b1010 should be recognized as a BinLiteral custom token"
    );

    // "0b2" should NOT fully match BinLiteral ('2' is not a binary digit).
    // The DFA may partially match "0b" then die on '2', or match "0" as Integer
    // prefix then die. Either way, it must not yield Custom("BinLiteral").
    assert_ne!(
        lex_string(&dfa, &partition, "0b2"),
        Some(TokenKind::Custom("BinLiteral".into())),
        "0b2 should not match BinLiteral (2 is not a binary digit)"
    );
}
