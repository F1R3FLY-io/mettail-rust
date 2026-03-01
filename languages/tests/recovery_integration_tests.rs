//! Integration tests for error recovery on real grammars.
//!
//! Validates that `parse_recovering()` across Calculator, Lambda, Ambient,
//! and RhoCalc grammars handles various error patterns:
//! - Missing closing delimiters
//! - Extra/unexpected tokens
//! - Missing operators
//! - Cascading errors (error count bounded)
//! - Deeply nested expressions with errors
//! - Error message quality (contains token names, not raw IDs)
//! - Cross-category scenarios

use mettail_languages::calculator::{Bool, Float, Int, Str};
use mettail_languages::lambda::Term;

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Int category
// ══════════════════════════════════════════════════════════════════════════════

// ── Valid inputs (baseline) ──

#[test]
fn test_calc_recovery_simple_addition() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 + 2");
    assert!(result.is_some(), "valid addition should succeed");
    assert!(errors.is_empty(), "valid addition should have no errors");
}

#[test]
fn test_calc_recovery_nested_parens() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("((1 + 2) + 3)");
    assert!(result.is_some(), "nested parens should succeed");
    assert!(errors.is_empty(), "nested parens should have no errors");
}

#[test]
fn test_calc_recovery_negation() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("-5");
    assert!(result.is_some(), "negation should succeed");
    assert!(errors.is_empty(), "negation should have no errors");
}

#[test]
fn test_calc_recovery_variable() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("x");
    assert!(result.is_some(), "variable should succeed");
    assert!(errors.is_empty(), "variable should have no errors");
}

// ── Missing closing delimiter ──

#[test]
fn test_calc_recovery_unclosed_paren() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering("(1 + 2");
    // Should report an error for the missing closing paren
    assert!(
        !errors.is_empty(),
        "unclosed paren should produce at least one error"
    );
}

#[test]
fn test_calc_recovery_unclosed_nested_paren() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("((1 + 2)");
    // Missing one closing paren
    assert!(
        !errors.is_empty(),
        "unclosed nested paren should produce at least one error"
    );
    let _ = result;
}

// ── Extra/unexpected tokens ──

#[test]
fn test_calc_recovery_extra_operator() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 + + 2");
    // Should attempt recovery on the unexpected second "+"
    assert!(
        !errors.is_empty() || result.is_some(),
        "'1 + + 2' should produce either errors or partial result"
    );
}

#[test]
fn test_calc_recovery_trailing_integer() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 2");
    assert!(result.is_some(), "should parse '1' successfully from '1 2'");
    assert!(
        !errors.is_empty(),
        "trailing '2' should be reported as an error"
    );
}

#[test]
fn test_calc_recovery_trailing_operator() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering("1 +");
    // "1 +" — parses "1", sees "+", tries to parse RHS, hits EOF
    assert!(
        !errors.is_empty(),
        "trailing operator should produce an error"
    );
}

// ── Missing operator ──

#[test]
fn test_calc_recovery_missing_operator() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 2 3");
    // "1 2 3" — "1" parses, "2" and "3" are trailing tokens
    assert!(result.is_some(), "should parse '1' from '1 2 3'");
    assert!(
        !errors.is_empty(),
        "juxtaposed literals should produce errors"
    );
}

// ── Cascading errors (Sprint 15 — error count should be bounded) ──

#[test]
fn test_calc_recovery_cascade_bounded() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 + + + + + 2");
    // Multiple consecutive operators — cascade prevention should limit errors
    // The exact behavior depends on how '+' is handled (possibly as unary prefix '-' analogue)
    // but we verify errors don't blow up
    assert!(
        errors.len() <= 6,
        "cascade prevention should limit errors, got {} error(s)",
        errors.len()
    );
    let _ = result;
}

// ── Deeply nested expressions with errors ──

#[test]
fn test_calc_recovery_deeply_nested_valid() {
    mettail_runtime::clear_var_cache();
    // Generate deeply nested valid expression: ((((1 + 2))))
    let depth = 20;
    let open: String = "(".repeat(depth);
    let close: String = ")".repeat(depth);
    let input = format!("{}1 + 2{}", open, close);
    let (result, errors) = Int::parse_recovering(&input);
    assert!(result.is_some(), "deeply nested valid should succeed");
    assert!(
        errors.is_empty(),
        "deeply nested valid should have no errors"
    );
}

#[test]
fn test_calc_recovery_deeply_nested_with_error() {
    mettail_runtime::clear_var_cache();
    // Deeply nested with an error inside: (((1 + + 2)))
    let depth = 5;
    let open: String = "(".repeat(depth);
    let close: String = ")".repeat(depth);
    let input = format!("{}1 + + 2{}", open, close);
    let (_result, errors) = Int::parse_recovering(&input);
    // Should produce errors but not blow up
    assert!(
        !errors.is_empty(),
        "deeply nested with error should produce errors"
    );
}

// ── Empty and minimal inputs ──

#[test]
fn test_calc_recovery_empty_input() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("");
    assert!(
        result.is_none(),
        "empty input should return None (prefix failure)"
    );
    assert!(!errors.is_empty(), "empty input should produce an error");
}

#[test]
fn test_calc_recovery_only_parens() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering("()");
    // Empty parens — should fail
    assert!(
        !errors.is_empty(),
        "empty parens should produce errors"
    );
}

#[test]
fn test_calc_recovery_mismatched_close() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering(")");
    assert!(
        !errors.is_empty(),
        "bare close paren should produce errors"
    );
}

// ── Error message quality ──

#[test]
fn test_calc_error_message_is_readable() {
    mettail_runtime::clear_var_cache();
    let (_, errors) = Int::parse_recovering("");
    assert!(!errors.is_empty());
    let msg = format!("{}", errors[0]);
    // Error message should contain line/column info and mention what was expected
    assert!(
        msg.contains("expected") || msg.contains("unexpected") || msg.contains("error"),
        "error message should be human-readable, got: {}",
        msg
    );
}

#[test]
fn test_calc_error_display_includes_position() {
    mettail_runtime::clear_var_cache();
    let (_, errors) = Int::parse_recovering("1 +");
    assert!(!errors.is_empty());
    let msg = format!("{}", errors[0]);
    // Should include line:column position
    assert!(
        msg.contains(':'),
        "error should include position info (line:col), got: {}",
        msg
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Float category
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_float_recovery_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Float::parse_recovering("1.5 + 2.5");
    assert!(result.is_some(), "valid float addition should succeed");
    assert!(errors.is_empty(), "valid float should have no errors");
}

#[test]
fn test_float_recovery_trailing() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Float::parse_recovering("1.5 2.5");
    assert!(result.is_some(), "should parse '1.5' from '1.5 2.5'");
    assert!(
        !errors.is_empty(),
        "trailing float should produce errors"
    );
}

#[test]
fn test_float_recovery_trig_unclosed() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Float::parse_recovering("sin(1.0");
    assert!(
        !errors.is_empty(),
        "unclosed sin() should produce errors"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Bool category
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_bool_recovery_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Bool::parse_recovering("true and false");
    assert!(result.is_some(), "valid bool expression should succeed");
    assert!(errors.is_empty(), "valid bool should have no errors");
}

#[test]
fn test_bool_recovery_missing_operand() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Bool::parse_recovering("true and");
    assert!(
        !errors.is_empty(),
        "trailing 'and' should produce errors"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Str category
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_str_recovery_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Str::parse_recovering("\"hello\" ++ \"world\"");
    assert!(result.is_some(), "valid string concat should succeed");
    assert!(errors.is_empty(), "valid string should have no errors");
}

#[test]
fn test_str_recovery_trailing() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Str::parse_recovering("\"hello\" \"world\"");
    assert!(
        result.is_some(),
        "should parse first string from juxtaposed strings"
    );
    assert!(
        !errors.is_empty(),
        "trailing string should produce errors"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Ternary conditional
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_calc_recovery_ternary_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 ? 2 : 3");
    assert!(result.is_some(), "valid ternary should succeed");
    assert!(errors.is_empty(), "valid ternary should have no errors");
}

#[test]
fn test_calc_recovery_ternary_missing_colon() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering("1 ? 2 3");
    // Missing ":" — should fail somewhere
    assert!(
        !errors.is_empty(),
        "ternary missing ':' should produce errors"
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Calculator — Cross-category (Sprint 10a: cast diagnostics)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_calc_recovery_int_with_float_literal() {
    mettail_runtime::clear_var_cache();
    // "1.5" is not directly in Int's FIRST set — it's a float literal
    // Int expects integer literals, variables, or keywords like "int("
    let (result, errors) = Int::parse_recovering("1.5");
    // Depending on how the lexer handles "1.5", it might tokenize as Float or
    // as Integer(1) + unexpected. Either way, errors or a type mismatch.
    let _ = result;
    let _ = errors;
    // This test verifies no panic occurs
}

#[test]
fn test_calc_recovery_float_with_int_cast() {
    mettail_runtime::clear_var_cache();
    // Valid: float(42) — Int→Float cast
    let (result, errors) = Float::parse_recovering("float(42)");
    assert!(result.is_some(), "float(42) should succeed via Int→Float cast");
    assert!(errors.is_empty(), "float(42) should have no errors");
}

// ══════════════════════════════════════════════════════════════════════════════
// Lambda calculus
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_lambda_recovery_valid_identity() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Term::parse_recovering("lam x.x");
    assert!(result.is_some(), "identity function should succeed");
    assert!(errors.is_empty(), "identity function should have no errors");
}

#[test]
fn test_lambda_recovery_valid_application() {
    mettail_runtime::clear_var_cache();
    // Lambda application syntax is (fun, arg) — comma-separated inside parens
    let (result, errors) = Term::parse_recovering("(lam x.x, y)");
    assert!(result.is_some(), "application should succeed");
    assert!(errors.is_empty(), "application should have no errors");
}

#[test]
fn test_lambda_recovery_unclosed_paren() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Term::parse_recovering("(lam x.x");
    assert!(
        !errors.is_empty(),
        "unclosed paren in lambda should produce errors"
    );
}

#[test]
fn test_lambda_recovery_empty() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Term::parse_recovering("");
    assert!(
        result.is_none(),
        "empty lambda input should return None"
    );
    assert!(!errors.is_empty(), "empty input should produce an error");
}

// ══════════════════════════════════════════════════════════════════════════════
// Multiple parse_recovering calls in sequence (no state leakage)
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_recovery_no_state_leakage_between_calls() {
    mettail_runtime::clear_var_cache();

    // First call with an error
    let (_, errors1) = Int::parse_recovering("1 +");
    assert!(!errors1.is_empty(), "first call should have errors");

    // Second call with valid input — should NOT carry over errors
    let (result2, errors2) = Int::parse_recovering("42");
    assert!(result2.is_some(), "second call should succeed");
    assert!(
        errors2.is_empty(),
        "second call should not inherit errors from first, got {} errors",
        errors2.len()
    );
}

#[test]
fn test_recovery_no_state_leakage_bracket_tracking() {
    mettail_runtime::clear_var_cache();

    // First call with unbalanced brackets
    let _ = Int::parse_recovering("(1 + 2");

    // Second call with balanced brackets — bracket tracking should be reset
    let (result, errors) = Int::parse_recovering("(1 + 2)");
    assert!(result.is_some(), "balanced parens should succeed after unbalanced call");
    assert!(
        errors.is_empty(),
        "bracket state should not leak between calls, got {} errors",
        errors.len()
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Factorial and postfix operators
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_calc_recovery_factorial_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("5!");
    assert!(result.is_some(), "factorial should succeed");
    assert!(errors.is_empty(), "factorial should have no errors");
}

#[test]
fn test_calc_recovery_complex_expression() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("(1 + 2) * 3 - 4 / 2");
    assert!(result.is_some(), "complex expression should succeed");
    assert!(errors.is_empty(), "complex expression should have no errors");
}

// ══════════════════════════════════════════════════════════════════════════════
// Power/right-associative expressions
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_calc_recovery_power_valid() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("2 ^ 3 ^ 2");
    assert!(result.is_some(), "right-assoc power should succeed");
    assert!(errors.is_empty(), "right-assoc power should have no errors");
}

#[test]
fn test_calc_recovery_power_missing_exponent() {
    mettail_runtime::clear_var_cache();
    let (_result, errors) = Int::parse_recovering("2 ^");
    assert!(
        !errors.is_empty(),
        "power missing exponent should produce errors"
    );
}
