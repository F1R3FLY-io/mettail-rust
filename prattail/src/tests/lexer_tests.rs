//! Tests for the lexer pipeline orchestration.

use crate::lexer::{extract_terminals, generate_lexer, GrammarRuleInfo, TypeInfo};
use crate::runtime_types::skip_whitespace_scalar;
#[cfg(feature = "simd-whitespace")]
use crate::runtime_types::skip_whitespace_simd;

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
    assert!(code_str.contains("Range"), "should contain Range struct");
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

// ══════════════════════════════════════════════════════════════════════════════
// AL03: SIMD whitespace skipping tests
// ══════════════════════════════════════════════════════════════════════════════

/// Helper: run scalar skip and return (pos, line, col).
fn scalar_skip(input: &[u8], pos: usize, line: usize, col: usize) -> (usize, usize, usize) {
    skip_whitespace_scalar(input, pos, line, col)
}

/// Helper: run SIMD skip and return (pos, line, col) — only available with feature.
#[cfg(feature = "simd-whitespace")]
fn simd_skip(input: &[u8], pos: usize, line: usize, col: usize) -> (usize, usize, usize) {
    let r = skip_whitespace_simd(input, pos, line, col);
    (r.pos, r.line, r.col)
}

#[test]
fn test_skip_whitespace_scalar_empty() {
    let (pos, line, col) = scalar_skip(b"", 0, 0, 0);
    assert_eq!((pos, line, col), (0, 0, 0));
}

#[test]
fn test_skip_whitespace_scalar_no_whitespace() {
    let (pos, line, col) = scalar_skip(b"hello", 0, 0, 0);
    assert_eq!((pos, line, col), (0, 0, 0));
}

#[test]
fn test_skip_whitespace_scalar_spaces_only() {
    let (pos, line, col) = scalar_skip(b"   hello", 0, 0, 0);
    assert_eq!(pos, 3);
    assert_eq!(line, 0);
    assert_eq!(col, 3);
}

#[test]
fn test_skip_whitespace_scalar_newlines() {
    let (pos, line, col) = scalar_skip(b"\n\n  hello", 0, 0, 0);
    assert_eq!(pos, 4);
    assert_eq!(line, 2);
    assert_eq!(col, 2);
}

#[test]
fn test_skip_whitespace_scalar_mixed() {
    let input = b"  \t\r\n  \t\nhello";
    let (pos, line, col) = scalar_skip(input, 0, 0, 0);
    assert_eq!(pos, 9);
    assert_eq!(line, 2);
    assert_eq!(col, 0, "last ws char is newline so col resets");
}

#[test]
fn test_skip_whitespace_scalar_all_whitespace() {
    let input = b"   \n\t\r  ";
    let (pos, line, col) = scalar_skip(input, 0, 0, 0);
    assert_eq!(pos, input.len());
    assert_eq!(line, 1);
    // After \n: col resets to 0, then \t(1) \r(2) space(3) space(4)
    assert_eq!(col, 4);
}

#[test]
fn test_skip_whitespace_scalar_start_offset() {
    let input = b"abc   def";
    let (pos, line, col) = scalar_skip(input, 3, 0, 3);
    assert_eq!(pos, 6);
    assert_eq!(line, 0);
    assert_eq!(col, 6);
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_empty() {
    let (pos, line, col) = simd_skip(b"", 0, 0, 0);
    assert_eq!((pos, line, col), (0, 0, 0));
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_no_whitespace() {
    let (pos, line, col) = simd_skip(b"hello", 0, 0, 0);
    assert_eq!((pos, line, col), (0, 0, 0));
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_spaces_only() {
    let (pos, line, col) = simd_skip(b"   hello", 0, 0, 0);
    assert_eq!(pos, 3);
    assert_eq!(line, 0);
    assert_eq!(col, 3);
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_short() {
    // Test inputs shorter than 16 bytes (scalar tail path only)
    let inputs: &[&[u8]] = &[
        b"",
        b" ",
        b"  \t\n",
        b"   hello",
        b"\n\nhello",
        b"\r\n\t world",
        b"no_ws_here",
    ];
    for input in inputs {
        let scalar = scalar_skip(input, 0, 0, 0);
        let simd = simd_skip(input, 0, 0, 0);
        assert_eq!(scalar, simd, "mismatch for input {:?}", String::from_utf8_lossy(input));
    }
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_exact_16() {
    // Exactly 16 bytes of whitespace
    let input = b"                hello";  // 16 spaces + "hello"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for 16-space input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_over_16() {
    // More than 16 bytes of whitespace (exercises full SIMD + tail)
    let input = b"                      hello";  // 22 spaces + "hello"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for 22-space input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_with_newlines() {
    // Whitespace run > 16 bytes containing newlines
    let input = b"    \n    \n    \n    \nhello";  // 4*5=20 ws bytes + "hello"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for newline-heavy input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_mixed_ws() {
    // Mix of space, tab, CR, LF
    let input = b" \t\r\n \t\r\n \t\r\n \t\r\n \t\r\nX";  // 20 ws bytes + "X"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for mixed whitespace");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_all_whitespace() {
    // Input is entirely whitespace (no non-ws terminator)
    let input = b"                                ";  // 32 spaces
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for all-whitespace input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_partial_chunk() {
    // Non-ws byte in the middle of the first 16-byte chunk
    let input = b"       X        ";  // 7 spaces + X + 8 spaces
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for partial-chunk input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_with_offset() {
    // Starting from a non-zero offset
    let input = b"abcde     \n    fgh";
    let scalar = scalar_skip(input, 5, 0, 5);
    let simd = simd_skip(input, 5, 0, 5);
    assert_eq!(scalar, simd, "mismatch for offset input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_large() {
    // Large whitespace run: 200 spaces with interspersed newlines
    let mut input = Vec::with_capacity(220);
    for i in 0..200 {
        if i % 30 == 29 {
            input.push(b'\n');
        } else if i % 10 == 9 {
            input.push(b'\t');
        } else {
            input.push(b' ');
        }
    }
    input.extend_from_slice(b"token");

    let scalar = scalar_skip(&input, 0, 0, 0);
    let simd = simd_skip(&input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for large whitespace run");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_cr_lf_sequences() {
    // Windows-style \r\n line endings, > 16 bytes
    let input = b"  \r\n  \r\n  \r\n  \r\n  \r\nhello";
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for CR+LF sequences");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_15_bytes() {
    // Exactly 15 bytes of whitespace (just under SIMD lane width)
    let input = b"               X";  // 15 spaces + "X"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for 15-byte input");
}

#[cfg(feature = "simd-whitespace")]
#[test]
fn test_skip_whitespace_simd_matches_scalar_17_bytes() {
    // 17 bytes of whitespace (SIMD chunk + 1 tail byte)
    let input = b"                 X";  // 17 spaces + "X"
    let scalar = scalar_skip(input, 0, 0, 0);
    let simd = simd_skip(input, 0, 0, 0);
    assert_eq!(scalar, simd, "mismatch for 17-byte input");
}
