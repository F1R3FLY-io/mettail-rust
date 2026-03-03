//! Pretty-printing utilities for terms and error display.
//!
//! Provides indented multi-line formatting for complex terms
//! and rich source-context error rendering with caret pointing and ANSI colors.

use colored::Colorize;

// ══════════════════════════════════════════════════════════════════════════════
// Parsed error structure (extracted from deterministic ParseError::Display format)
// ══════════════════════════════════════════════════════════════════════════════

/// Components extracted from a `ParseError` display string.
struct ParsedError<'a> {
    line: usize,   // 1-indexed
    column: usize, // 1-indexed
    kind: ErrorKind<'a>,
    hint: Option<&'a str>,
}

enum ErrorKind<'a> {
    /// `expected X, found Y`
    UnexpectedToken { expected: &'a str, found: &'a str },
    /// `unexpected end of input, expected X`
    UnexpectedEof { expected: &'a str },
    /// `unexpected X after parsing`
    TrailingTokens { found: &'a str },
    /// `unexpected character '...'` or `unexpected byte 0x..`
    LexError { message: &'a str },
    /// Recovery applied: `{original} (recovered: {repair})`
    Recovery { message: &'a str },
}

/// Parse the deterministic `ParseError::Display` format into components.
///
/// Formats handled:
/// - `L:C: expected X, found Y\n  = hint: ...`
/// - `L:C: unexpected end of input, expected X\n  = hint: ...`
/// - `L:C: unexpected X after parsing\n  = hint: ...`
/// - `L:C: unexpected character '...'\n  = hint: ...`
/// - `L:C: unexpected byte 0x..\n  = hint: ...`
/// - `L:C: ... (recovered: ...)\n  = hint: ...`
fn parse_error_string(error_msg: &str) -> Option<ParsedError<'_>> {
    // Split off hint if present
    let (main_line, hint) = if let Some(idx) = error_msg.find("\n  = hint: ") {
        let hint_text = &error_msg[idx + "\n  = hint: ".len()..];
        (&error_msg[..idx], Some(hint_text.trim()))
    } else {
        (error_msg, None)
    };

    // Parse L:C: prefix
    let mut parts = main_line.splitn(3, ':');
    let line: usize = parts.next()?.trim().parse().ok()?;
    let column: usize = parts.next()?.trim().parse().ok()?;
    let rest = parts.next()?.trim();

    let kind = if rest.starts_with("expected ") {
        // UnexpectedToken: "expected X, found Y"
        if let Some(found_idx) = rest.find(", found ") {
            let expected = &rest["expected ".len()..found_idx];
            let found = &rest[found_idx + ", found ".len()..];
            ErrorKind::UnexpectedToken { expected, found }
        } else {
            ErrorKind::LexError { message: rest }
        }
    } else if rest.starts_with("unexpected end of input, expected ") {
        let expected = &rest["unexpected end of input, expected ".len()..];
        ErrorKind::UnexpectedEof { expected }
    } else if rest.ends_with("after parsing") || rest.contains("after parsing") {
        // TrailingTokens: "unexpected X after parsing"
        let found = rest
            .strip_prefix("unexpected ")
            .and_then(|s| s.strip_suffix(" after parsing"))
            .unwrap_or(rest);
        ErrorKind::TrailingTokens { found }
    } else if rest.contains("(recovered:") {
        ErrorKind::Recovery { message: rest }
    } else {
        // LexError or other
        ErrorKind::LexError { message: rest }
    };

    Some(ParsedError { line, column, kind, hint })
}

// ══════════════════════════════════════════════════════════════════════════════
// Rich error display with colors and box-drawing
// ══════════════════════════════════════════════════════════════════════════════

/// Format a parse error with rich colored output, box-drawing gutter, and contextual hints.
///
/// Produces rustc-style diagnostic output:
/// ```text
/// error: unexpected integer `4` after parsing
///  --> 1:5
///   │
/// 1 │ 3 ! 4
///   │     ^
///   = hint: the parser finished but input remains; check for missing operators or extra tokens
/// ```
pub fn format_parse_error_with_context(input: &str, error_msg: &str) -> String {
    match parse_error_string(error_msg) {
        Some(parsed) => format_rich_error(input, &parsed),
        None => {
            // Fallback: just return raw message
            error_msg.to_string()
        }
    }
}

/// Check if an error string looks like a ParseError (starts with `L:C:` format).
///
/// Used by the REPL to decide between rich display (parse errors) and plain display
/// (non-parse errors like "Unknown command" or "No language loaded").
pub fn is_parse_error(error_msg: &str) -> bool {
    parse_error_string(error_msg).is_some()
}

fn format_rich_error(input: &str, parsed: &ParsedError<'_>) -> String {
    let mut out = String::with_capacity(512);

    // Line 1: error label + summary
    let summary = match &parsed.kind {
        ErrorKind::UnexpectedToken { expected, found } => {
            format!("expected {}, found {}", expected, found)
        }
        ErrorKind::UnexpectedEof { expected } => {
            format!("unexpected end of input, expected {}", expected)
        }
        ErrorKind::TrailingTokens { found } => {
            format!("unexpected {} after parsing", found)
        }
        ErrorKind::LexError { message } => message.to_string(),
        ErrorKind::Recovery { message } => message.to_string(),
    };
    out.push_str(&format!("{}{} {}\n", "error".red().bold(), ":".bold(), summary));

    // Source context
    let lines: Vec<&str> = input.lines().collect();
    let line_0idx = parsed.line.saturating_sub(1);
    let col_0idx = parsed.column.saturating_sub(1);

    // Compute gutter width from line number (used for consistent alignment)
    let line_num = format!("{}", parsed.line);
    let gutter_width = line_num.len() + 1; // space after number
    let gutter_pad = " ".repeat(gutter_width);
    let arrow_pad = " ".repeat(line_num.len());

    if line_0idx < lines.len() {
        let source_line = lines[line_0idx];

        // Location line: " --> L:C"
        out.push_str(&format!(
            "{}{} {}:{}\n",
            arrow_pad,
            "-->".blue().bold(),
            parsed.line,
            parsed.column,
        ));

        // Blank gutter line
        out.push_str(&format!("{}{}\n", gutter_pad, "│".blue().bold()));

        // Source line: "N │ source code here"
        out.push_str(&format!(
            "{} {} {}\n",
            line_num.blue().bold(),
            "│".blue().bold(),
            source_line,
        ));

        // Caret line: "  │     ^^^"
        let caret_col = col_0idx.min(source_line.len());

        // Determine caret length from the found token
        let caret_len = estimate_caret_length(source_line, caret_col);

        out.push_str(&format!(
            "{}{} {}{}\n",
            gutter_pad,
            "│".blue().bold(),
            " ".repeat(caret_col),
            "^".repeat(caret_len).red().bold(),
        ));
    } else {
        // No source context available
        out.push_str(&format!(
            "{}{} {}:{}\n",
            arrow_pad,
            "-->".blue().bold(),
            parsed.line,
            parsed.column,
        ));
    }

    // Hint (with blank │ separator)
    if let Some(hint) = parsed.hint {
        out.push_str(&format!(
            "{}{} {}{}",
            gutter_pad,
            "=".blue().bold(),
            "hint: ".green(),
            hint.green(),
        ));
    }

    out
}

/// Estimate how many characters the caret should span.
///
/// Looks at the source line starting at `col` and measures the "token" length
/// heuristically (alphanumeric/underscore run, or quoted string, or single char).
fn estimate_caret_length(source_line: &str, col: usize) -> usize {
    if col >= source_line.len() {
        return 1;
    }
    let rest = &source_line[col..];
    let bytes = rest.as_bytes();

    if bytes.is_empty() {
        return 1;
    }

    // Quoted string: measure to closing quote
    if bytes[0] == b'"' || bytes[0] == b'\'' {
        let quote = bytes[0];
        for (i, &b) in bytes.iter().enumerate().skip(1) {
            if b == quote {
                return i + 1;
            }
        }
        return rest.len().max(1);
    }

    // Alphanumeric/underscore/dollar run
    if bytes[0].is_ascii_alphanumeric() || bytes[0] == b'_' || bytes[0] == b'$' {
        let len = bytes
            .iter()
            .take_while(|&&b| b.is_ascii_alphanumeric() || b == b'_' || b == b'$')
            .count();
        return len.max(1);
    }

    // Operator: measure multi-char operators (!=, ==, <=, >=, ->, <-, etc.)
    if bytes.len() >= 2 {
        let two = &bytes[..2];
        if matches!(
            two,
            b"!=" | b"==" | b"<=" | b">=" | b"->" | b"<-" | b"&&" | b"||" | b"$$" | b"::"
        ) {
            return 2;
        }
    }

    // Single character
    1
}

// ══════════════════════════════════════════════════════════════════════════════
// Term pretty-printing
// ══════════════════════════════════════════════════════════════════════════════

fn indent_str(level: usize) -> String {
    "    ".repeat(level)
}

pub fn format_term_pretty(term_str: &str) -> String {
    // Simple heuristic-based pretty printer
    // Works on the display string since we don't have access to the AST here

    let mut result = String::new();
    let mut chars = term_str.chars().peekable();

    // Track nesting depth
    let mut paren_depth: i32 = 0; // () nesting
    let mut bracket_depth: i32 = 0; // [] nesting
    let mut brace_depth: i32 = 0; // {} nesting (for indentation)

    while let Some(ch) = chars.next() {
        match ch {
            '{' => {
                // If this is not the first brace and comes after content, add newline + indent
                if !result.is_empty() && !result.ends_with('\n') {
                    // Check if we just closed parens (common pattern: `for(...){`)
                    // OR if we're already nested in braces (nested collections)
                    // BUT NOT if we're inside parens (function args like `done2!({...})`)
                    let should_break =
                        (result.ends_with(')') || brace_depth > 0) && paren_depth == 0;

                    if should_break {
                        result.push('\n');
                        result.push_str(&indent_str(brace_depth as usize));
                    } else {
                        result.push(' ');
                    }
                } else if result.is_empty() {
                    // Very first character - just add space after
                }

                result.push(ch);
                result.push(' ');
                brace_depth += 1;
            },
            '}' => {
                result.push(' ');
                brace_depth = brace_depth.saturating_sub(1);
                result.push(ch);
            },
            '(' => {
                paren_depth += 1;
                result.push(ch);
            },
            ')' => {
                paren_depth = paren_depth.saturating_sub(1);
                result.push(ch);
            },
            '[' => {
                bracket_depth += 1;
                result.push(ch);
            },
            ']' => {
                bracket_depth = bracket_depth.saturating_sub(1);
                result.push(ch);
            },
            // Collection separators: comma, pipe, semicolon
            ',' | '|' | ';' => {
                // Separators are collection-level if:
                // 1. We're inside braces (collection context)
                // 2. NOT inside parentheses (function args)
                // Note: bracket depth doesn't matter - [...{...|...}...] has collection separators inside
                if brace_depth > 0 && paren_depth == 0 {
                    // This separator is at collection level - put it at start of new line (prefix style)
                    result.push('\n');
                    // Indent based on nesting depth (brace_depth - 1, since we're inside the braces)
                    result.push_str(&indent_str((brace_depth - 1) as usize));
                    result.push(ch);
                    result.push(' ');
                } else {
                    // This separator is inside parens/outside collections, just add space if needed
                    result.push(ch);
                    if let Some(&next) = chars.peek() {
                        if next != ' ' {
                            result.push(' ');
                        }
                    }
                }
            },
            ' ' => {
                // Only add space if not at start of result and previous char wasn't a space
                if !result.is_empty() && !result.ends_with(' ') && !result.ends_with('\n') {
                    result.push(ch);
                }
            },
            _ => {
                result.push(ch);
            },
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_pretty_print() {
        let input = "{a!(0), for(a->x){*x}}";
        let output = format_term_pretty(input);

        assert!(output.contains('\n'));
        assert!(output.contains("    ")); // Has indentation
    }

    #[test]
    fn test_nested_pretty_print() {
        let input = "{for(fork1->f1){for(fork2->f2){done1!({*f1, *f2})}}}";
        let output = format_term_pretty(input);

        // Check multiple indentation levels
        let lines: Vec<&str> = output.lines().collect();
        assert!(lines.len() >= 3, "Expected at least 3 lines, got {}", lines.len());

        // Verify we have increasing indentation
        assert!(output.contains("    { "));
        assert!(output.contains("        { "));
    }

    // -- Rich error display tests --

    #[test]
    fn test_parse_error_unexpected_token() {
        let input = "3 ! 4";
        let error = "1:3: expected an Int expression (one of: integer literal, identifier, `+`), found `!`\n  = hint: this token cannot start a Int expression";
        let result = format_parse_error_with_context(input, error);
        // Should contain the source line
        assert!(result.contains("3 ! 4"), "should contain source line");
        // Should contain caret
        assert!(result.contains("^"), "should contain caret marker");
        // Should contain hint
        assert!(result.contains("hint"), "should contain hint");
    }

    #[test]
    fn test_parse_error_trailing_tokens() {
        let input = "3 + 4 5";
        let error = "1:7: unexpected integer `5` after parsing\n  = hint: the parser finished but input remains; check for missing operators or extra tokens";
        let result = format_parse_error_with_context(input, error);
        assert!(result.contains("3 + 4 5"), "should contain source line");
        assert!(result.contains("hint"), "should contain hint");
    }

    #[test]
    fn test_parse_error_eof() {
        let input = "3 +";
        let error = "1:4: unexpected end of input, expected an Int expression (one of: integer literal, identifier)";
        let result = format_parse_error_with_context(input, error);
        assert!(result.contains("3 +"), "should contain source line");
        assert!(result.contains("expected"), "should contain expected info");
    }

    #[test]
    fn test_parse_error_lex_error() {
        let input = "3 @ 4";
        let error = "1:3: unexpected character '@'";
        let result = format_parse_error_with_context(input, error);
        assert!(result.contains("3 @ 4"), "should contain source line");
        assert!(result.contains("^"), "should contain caret marker");
    }

    #[test]
    fn test_parse_error_no_hint() {
        let input = "x + y";
        let error = "1:1: expected integer literal, found identifier `x`";
        let result = format_parse_error_with_context(input, error);
        assert!(result.contains("x + y"), "should contain source line");
        assert!(!result.contains("hint"), "should not contain hint when none present");
    }

    #[test]
    fn test_unparseable_error_fallback() {
        let error = "something went wrong";
        let result = format_parse_error_with_context("input", error);
        assert_eq!(result, "something went wrong");
    }

    #[test]
    fn test_caret_length_alphanumeric() {
        assert_eq!(estimate_caret_length("hello world", 0), 5);
        assert_eq!(estimate_caret_length("hello world", 6), 5);
    }

    #[test]
    fn test_caret_length_operator() {
        assert_eq!(estimate_caret_length("a != b", 2), 2);
        assert_eq!(estimate_caret_length("a + b", 2), 1);
    }

    #[test]
    fn test_caret_length_quoted() {
        assert_eq!(estimate_caret_length("\"hello\" world", 0), 7);
    }
}
