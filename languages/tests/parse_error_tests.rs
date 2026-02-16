//! End-to-end error handling tests for the Calculator language.
//!
//! Tests that parse errors are correctly generated, positioned, and formatted
//! when parsing invalid Calculator expressions.

use mettail_languages::calculator::Int;

// ── LexError: invalid characters ──

#[test]
fn test_lex_error_invalid_character() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("@");
    assert!(result.is_err(), "should fail on invalid character");
    let err = result.unwrap_err();
    // LexError is produced for unrecognized characters
    assert!(
        format!("{:?}", err).contains("LexError"),
        "invalid character should produce LexError, got: {:?}",
        err
    );
}

#[test]
fn test_lex_error_hash_character() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("#");
    assert!(result.is_err(), "should fail on # character");
}

// ── UnexpectedToken: wrong token type ──

#[test]
fn test_unexpected_token_operator_at_start() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("+");
    assert!(result.is_err(), "should fail when expression starts with +");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    assert!(
        err_debug.contains("UnexpectedToken") || err_debug.contains("UnexpectedEof"),
        "starting with + should produce UnexpectedToken or UnexpectedEof, got: {}",
        err_debug
    );
}

#[test]
fn test_unexpected_token_double_operator() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 + + 2");
    assert!(
        result.is_err(),
        "should fail on consecutive operators (1 + + 2)"
    );
}

// ── TrailingTokens: extra tokens after valid expression ──

#[test]
fn test_trailing_tokens_two_literals() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 2");
    assert!(result.is_err(), "should fail on trailing literal (1 2)");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    assert!(
        err_debug.contains("TrailingTokens"),
        "extra literal after expression should produce TrailingTokens, got: {}",
        err_debug
    );
}

#[test]
fn test_trailing_tokens_extra_paren() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 )");
    assert!(result.is_err(), "should fail on trailing close-paren");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    assert!(
        err_debug.contains("TrailingTokens"),
        "extra ) after expression should produce TrailingTokens, got: {}",
        err_debug
    );
}

// ── UnexpectedEof: premature end of input ──

#[test]
fn test_unexpected_eof_incomplete_addition() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 +");
    assert!(result.is_err(), "should fail on incomplete expression (1 +)");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    // The lexer always emits an Eof token, so the prefix handler sees Token::Eof
    // as an unexpected token rather than hitting the pos >= len check.
    // Both UnexpectedEof and UnexpectedToken with found="Eof" are acceptable.
    assert!(
        err_debug.contains("UnexpectedEof") || err_debug.contains("Eof"),
        "incomplete expression should report EOF-related error, got: {}",
        err_debug
    );
}

#[test]
fn test_unexpected_eof_empty_input() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("");
    assert!(result.is_err(), "should fail on empty input");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    // Empty input produces a single Eof token; the prefix handler sees
    // Token::Eof as an unexpected token (not pos >= len).
    assert!(
        err_debug.contains("UnexpectedEof") || err_debug.contains("Eof"),
        "empty input should report EOF-related error, got: {}",
        err_debug
    );
}

#[test]
fn test_unexpected_eof_unclosed_paren() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("(1 + 2");
    assert!(result.is_err(), "should fail on unclosed parenthesis");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    assert!(
        err_debug.contains("UnexpectedEof") || err_debug.contains("UnexpectedToken"),
        "unclosed paren should produce UnexpectedEof or UnexpectedToken, got: {}",
        err_debug
    );
}

// ── Error position accuracy ──

#[test]
fn test_trailing_token_position() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 2");
    let err = result.unwrap_err();
    let range = err.range();
    // "1 2" — the trailing "2" starts at byte_offset 2, column 2
    assert_eq!(
        range.start.column, 2,
        "trailing '2' should be at column 2, got {}",
        range.start.column
    );
    assert_eq!(
        range.start.line, 0,
        "should be on line 0, got {}",
        range.start.line
    );
}

#[test]
fn test_eof_error_position() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 +");
    let err = result.unwrap_err();
    let range = err.range();
    // EOF position should be at or near the end of the input
    assert!(
        range.start.byte_offset >= 2,
        "EOF error should have byte_offset >= 2 (end of '1 +'), got {}",
        range.start.byte_offset
    );
}

// ── Error display formatting ──

#[test]
fn test_error_display_includes_position() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("1 2");
    let err = result.unwrap_err();
    let display = format!("{}", err);
    // Display should include "line:column" format (1-indexed in display)
    assert!(
        display.contains(':'),
        "error display should contain line:column separator, got: {}",
        display
    );
}

#[test]
fn test_parse_with_source_includes_caret() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_with_source("1 2");
    assert!(result.is_err(), "should fail on trailing tokens");
    let err_msg = result.unwrap_err();
    // parse_with_source should include the source line and a caret
    assert!(
        err_msg.contains('^'),
        "parse_with_source error should include caret (^), got: {}",
        err_msg
    );
}

#[test]
fn test_parse_with_source_includes_source_line() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_with_source("1 2");
    assert!(result.is_err(), "should fail on trailing tokens");
    let err_msg = result.unwrap_err();
    // Should include the source line itself
    assert!(
        err_msg.contains("1 2"),
        "parse_with_source error should include the source line '1 2', got: {}",
        err_msg
    );
}

// ── Nested expression errors ──

#[test]
fn test_error_inside_parentheses() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("(1 +)");
    assert!(
        result.is_err(),
        "should fail on incomplete expression inside parens"
    );
}

#[test]
fn test_empty_parentheses() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse_structured("()");
    assert!(result.is_err(), "should fail on empty parentheses");
}

// ── parse() convenience wrapper ──

#[test]
fn test_parse_returns_string_error() {
    mettail_runtime::clear_var_cache();
    let result = Int::parse("1 2");
    assert!(result.is_err(), "parse() should fail on trailing tokens");
    let err_msg = result.unwrap_err();
    // parse() returns a string error from Display
    assert!(
        !err_msg.is_empty(),
        "parse() error string should not be empty"
    );
}

// ── Bool category errors ──

#[test]
fn test_bool_parse_error() {
    use mettail_languages::calculator::Bool;
    mettail_runtime::clear_var_cache();
    let result = Bool::parse_structured("");
    assert!(result.is_err(), "empty input should fail for Bool");
    let err = result.unwrap_err();
    let err_debug = format!("{:?}", err);
    // Same as Int: empty input produces Eof token, seen as UnexpectedToken
    assert!(
        err_debug.contains("UnexpectedEof") || err_debug.contains("Eof"),
        "empty Bool input should report EOF-related error, got: {}",
        err_debug
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Error recovery tests — parse_recovering()
// ══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_recovery_valid_input_no_errors() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 + 2");
    assert!(
        result.is_some(),
        "valid input should produce Some result"
    );
    assert!(
        errors.is_empty(),
        "valid input should produce no errors, got {} error(s)",
        errors.len()
    );
}

#[test]
fn test_recovery_single_literal() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("42");
    assert!(result.is_some(), "single literal should parse successfully");
    assert!(errors.is_empty(), "single literal should have no errors");
}

#[test]
fn test_recovery_lex_error_returns_none() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("@");
    assert!(
        result.is_none(),
        "lex error should return None (unrecoverable)"
    );
    assert!(
        !errors.is_empty(),
        "lex error should produce at least one error"
    );
}

#[test]
fn test_recovery_prefix_error_returns_none() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("+");
    // A bare "+" has no valid prefix — should fail prefix and return None
    assert!(
        result.is_none(),
        "bare operator should fail prefix and return None"
    );
    assert!(
        !errors.is_empty(),
        "prefix failure should produce at least one error"
    );
}

#[test]
fn test_recovery_infix_error_partial_result() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 + + 2");
    // "1 + + 2": parse "1", see "+", parse RHS gets "+2" where "+" triggers
    // prefix error or Neg-like behavior. Whether we get Some or None depends
    // on the prefix handler. Either way, errors should be non-empty.
    assert!(
        !errors.is_empty() || result.is_some(),
        "should produce either errors or a partial result for '1 + + 2'"
    );
}

#[test]
fn test_recovery_trailing_tokens_reported() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("1 2");
    // "1 2" — "1" parses fine, "2" is a trailing token. The recovering parser
    // should report this as a TrailingTokens error.
    assert!(
        result.is_some(),
        "should successfully parse '1' from '1 2'"
    );
    assert!(
        !errors.is_empty(),
        "should report trailing tokens error for '1 2'"
    );
    let err_debug = format!("{:?}", errors[0]);
    assert!(
        err_debug.contains("TrailingTokens"),
        "trailing '2' should produce TrailingTokens, got: {}",
        err_debug
    );
}

#[test]
fn test_recovery_empty_input() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("");
    assert!(
        result.is_none(),
        "empty input should return None (prefix failure)"
    );
    assert!(
        !errors.is_empty(),
        "empty input should produce an error"
    );
}

#[test]
fn test_recovery_complex_valid_expression() {
    mettail_runtime::clear_var_cache();
    let (result, errors) = Int::parse_recovering("(1 + 2) + 3");
    assert!(
        result.is_some(),
        "complex valid expression should parse successfully"
    );
    assert!(
        errors.is_empty(),
        "complex valid expression should have no errors"
    );
}
