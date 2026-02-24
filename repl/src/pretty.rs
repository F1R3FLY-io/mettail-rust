//! Pretty-printing utilities for terms and error display.
//!
//! Provides indented multi-line formatting for complex terms
//! and source-context error rendering with caret pointing.

/// Format a parse error with source context snippet and caret.
///
/// Takes the original input text and the error message (which should contain
/// `line:column:` prefix). Extracts line/column from the error, renders the
/// relevant source line with a caret pointing to the error location.
pub fn format_parse_error_with_context(input: &str, error_msg: &str) -> String {
    // Try to extract line:column from the error message (format: "line:col: ...")
    let (line_1idx, col_1idx) = match parse_line_col(error_msg) {
        Some((l, c)) => (l, c),
        None => return error_msg.to_string(), // fallback to raw message
    };

    // Convert 1-indexed to 0-indexed
    let line_0idx = line_1idx.saturating_sub(1);
    let col_0idx = col_1idx.saturating_sub(1);

    // Find the source line
    let lines: Vec<&str> = input.lines().collect();
    if line_0idx >= lines.len() {
        return error_msg.to_string();
    }

    let source_line = lines[line_0idx];
    let caret_pos = col_0idx.min(source_line.len());

    // Build the display
    let mut result = String::new();
    result.push_str(error_msg);
    result.push('\n');
    // Line number gutter
    let line_num = format!("{:>4} | ", line_1idx);
    result.push_str(&line_num);
    result.push_str(source_line);
    result.push('\n');
    // Caret line
    let gutter_width = line_num.len();
    result.push_str(&" ".repeat(gutter_width + caret_pos));
    result.push('^');
    result
}

/// Parse "line:col: ..." from an error message. Returns (line, col) both 1-indexed.
fn parse_line_col(msg: &str) -> Option<(usize, usize)> {
    let mut parts = msg.splitn(3, ':');
    let line: usize = parts.next()?.trim().parse().ok()?;
    let col: usize = parts.next()?.trim().parse().ok()?;
    Some((line, col))
}

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
}
