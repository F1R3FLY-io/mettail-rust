//! Runtime type definitions shared between generated parsers and the PraTTaIL library.
//!
//! These types are defined once here and imported by generated code via
//! `use mettail_prattail::runtime_types::*;`, eliminating ~200 lines of
//! duplicated definitions from every generated parser.
//!
//! ## Generic lex loop
//!
//! The `lex_core()` and `lex_weighted_core()` functions factor out the DFA
//! lex loop into a monomorphizable generic function. Each generated lexer
//! provides grammar-specific closures for `dfa_next`, `is_accepting`, and
//! `accept_token`; the compiler monomorphizes away the closure overhead.

use std::borrow::Cow;
use std::fmt;

/// A position in source code. All fields are 0-indexed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub byte_offset: usize,
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn zero() -> Self {
        Position {
            byte_offset: 0,
            line: 0,
            column: 0,
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

/// A range in source code with beginning and ending positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub start: Position,
    pub end: Position,
    pub file_id: Option<u32>,
}

impl Range {
    pub fn zero() -> Self {
        Range {
            start: Position::zero(),
            end: Position::zero(),
            file_id: None,
        }
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

/// Structured parse error with source location.
///
/// The `expected` field uses `Cow<'static, str>` so that the common case
/// (static string from generated code) is zero-alloc, while cast-rule
/// diagnostics can append dynamic hints at no cost on the happy path.
///
/// The optional `hint` field provides contextual fix suggestions (e.g.,
/// "did you forget `)`?"). When `None`, no hint is shown — this is the
/// common case for generated code, keeping it zero-alloc on the happy path.
#[derive(Debug, Clone)]
pub enum ParseError {
    UnexpectedToken {
        expected: Cow<'static, str>,
        found: String,
        range: Range,
        hint: Option<Cow<'static, str>>,
    },
    UnexpectedEof {
        expected: Cow<'static, str>,
        range: Range,
        hint: Option<Cow<'static, str>>,
    },
    LexError {
        message: String,
        position: Position,
    },
    TrailingTokens {
        found: String,
        range: Range,
        hint: Option<Cow<'static, str>>,
    },
    /// A recovery action was applied to continue parsing past an error.
    ///
    /// Wraps the original error with a human-readable description of the
    /// repair that was applied (e.g., "skip 2 token(s) to ';'").
    RecoveryApplied {
        original_error: Box<ParseError>,
        repair_description: String,
        range: Range,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken {
                expected,
                found,
                range,
                hint,
            } => {
                write!(
                    f,
                    "{}:{}: expected {}, found {}",
                    range.start.line + 1,
                    range.start.column + 1,
                    expected,
                    found
                )?;
                if let Some(h) = hint {
                    write!(f, "\n  = hint: {}", h)?;
                }
                Ok(())
            },
            ParseError::UnexpectedEof { expected, range, hint } => {
                write!(
                    f,
                    "{}:{}: unexpected end of input, expected {}",
                    range.start.line + 1,
                    range.start.column + 1,
                    expected
                )?;
                if let Some(h) = hint {
                    write!(f, "\n  = hint: {}", h)?;
                }
                Ok(())
            },
            ParseError::LexError { message, position } => {
                write!(f, "{}:{}: {}", position.line + 1, position.column + 1, message)
            }
            ParseError::TrailingTokens { found, range, hint } => {
                write!(
                    f,
                    "{}:{}: unexpected {} after parsing",
                    range.start.line + 1,
                    range.start.column + 1,
                    found
                )?;
                if let Some(h) = hint {
                    write!(f, "\n  = hint: {}", h)?;
                }
                Ok(())
            },
            ParseError::RecoveryApplied {
                original_error,
                repair_description,
                ..
            } => write!(f, "{} (recovered: {})", original_error, repair_description),
        }
    }
}

impl ParseError {
    /// Get the source range where this error occurred.
    pub fn range(&self) -> Range {
        match self {
            ParseError::UnexpectedToken { range, .. } => *range,
            ParseError::UnexpectedEof { range, .. } => *range,
            ParseError::LexError { position, .. } => Range {
                start: *position,
                end: *position,
                file_id: None,
            },
            ParseError::TrailingTokens { range, .. } => *range,
            ParseError::RecoveryApplied { range, .. } => *range,
        }
    }
}

impl std::error::Error for ParseError {}

impl From<String> for ParseError {
    fn from(message: String) -> Self {
        ParseError::LexError {
            message,
            position: Position::zero(),
        }
    }
}

/// Format a source context snippet with caret pointing to the error.
pub fn format_error_context(input: &str, range: &Range) -> String {
    let line_start = input[..range.start.byte_offset]
        .rfind('\n')
        .map_or(0, |p| p + 1);
    let line_end = input[range.start.byte_offset..]
        .find('\n')
        .map_or(input.len(), |p| p + range.start.byte_offset);
    let source_line = &input[line_start..line_end];
    let caret_col = range.start.column;
    let caret_len =
        if range.end.byte_offset > range.start.byte_offset && range.end.line == range.start.line {
            range.end.byte_offset - range.start.byte_offset
        } else {
            1
        };
    format!(
        "{}\n{}{}",
        source_line,
        " ".repeat(caret_col),
        "^".repeat(caret_len)
    )
}

// ══════════════════════════════════════════════════════════════════════════════
// Generic lex loop — monomorphized at each call site via closures
// ══════════════════════════════════════════════════════════════════════════════

/// Core DFA lexing loop, shared across all generated lexers.
///
/// Returns `(Vec<(T, Range)>, Position)` where `T` is the grammar's `Token<'a>`
/// type and `Position` is the final cursor position (for the Eof token).
/// The generated lex variants (`lex`, `lex_with_file_id`, `lex_weighted`,
/// etc.) become thin wrappers calling this function with grammar-specific
/// closures. The compiler monomorphizes each call site, inlining the closures
/// for zero overhead.
///
/// # Parameters
///
/// - `input` — the full source string
/// - `file_id` — optional file identifier for multi-file projects
/// - `char_class` — 256-byte equivalence class lookup table
/// - `dfa_next` — `(state, class) -> next_state` (u32::MAX = dead)
/// - `is_accepting` — `state -> bool` (IS_ACCEPTING bitmap check)
/// - `accept_token` — `(state, text_slice) -> Option<Token>` (called once per token)
#[inline(always)]
pub fn lex_core<'a, T>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_token: impl Fn(u32, &'a str) -> Option<T>,
) -> Result<(Vec<(T, Range)>, Position), String> {
    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    let mut tokens: Vec<(T, Range)> = Vec::with_capacity(input.len() / 2);

    while pos < bytes.len() {
        // Skip whitespace
        while pos < bytes.len() && is_whitespace(bytes[pos]) {
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else {
                col += 1;
            }
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }

        let start = pos;
        let start_line = line;
        let start_col = col;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize, usize, usize)> = None;

        if is_accepting(0) {
            last_accept = Some((0, pos, line, col));
        }

        while pos < bytes.len() {
            let class = char_class[bytes[pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else if bytes[pos] & 0xC0 != 0x80 {
                col += 1;
            }
            pos += 1;
            if is_accepting(state) {
                last_accept = Some((state, pos, line, col));
            }
        }

        match last_accept {
            Some((accept_state, end, end_line, end_col)) => {
                pos = end;
                line = end_line;
                col = end_col;
                let text = &input[start..end];
                if let Some(token) = accept_token(accept_state, text) {
                    tokens.push((
                        token,
                        Range {
                            start: Position {
                                byte_offset: start,
                                line: start_line,
                                column: start_col,
                            },
                            end: Position {
                                byte_offset: end,
                                line: end_line,
                                column: end_col,
                            },
                            file_id,
                        },
                    ));
                }
            }
            None => {
                let ch = bytes[start] as char;
                let msg = if ch.is_ascii() {
                    format!(
                        "{}:{}: unexpected character '{}'",
                        line + 1, col + 1, ch,
                    )
                } else {
                    format!(
                        "{}:{}: unexpected byte 0x{:02X}",
                        line + 1, col + 1, bytes[start],
                    )
                };
                return Err(msg);
            }
        }
    }

    let eof_pos = Position {
        byte_offset: pos,
        line,
        column: col,
    };
    Ok((tokens, eof_pos))
}

/// Core DFA lexing loop with weight emission (for WFST-weighted lexing).
///
/// Same as `lex_core` but also calls `accept_weight(state) -> f64` to
/// attach tropical weights to each token. Returns the final cursor position
/// for the Eof token.
#[inline(always)]
pub fn lex_weighted_core<'a, T>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_token: impl Fn(u32, &'a str) -> Option<T>,
    accept_weight: impl Fn(u32) -> f64,
) -> Result<(Vec<(T, Range, f64)>, Position), String> {
    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    let mut tokens: Vec<(T, Range, f64)> = Vec::with_capacity(input.len() / 2);

    while pos < bytes.len() {
        while pos < bytes.len() && is_whitespace(bytes[pos]) {
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else {
                col += 1;
            }
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }

        let start = pos;
        let start_line = line;
        let start_col = col;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize, usize, usize)> = None;

        if is_accepting(0) {
            last_accept = Some((0, pos, line, col));
        }

        while pos < bytes.len() {
            let class = char_class[bytes[pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else if bytes[pos] & 0xC0 != 0x80 {
                col += 1;
            }
            pos += 1;
            if is_accepting(state) {
                last_accept = Some((state, pos, line, col));
            }
        }

        match last_accept {
            Some((accept_state, end, end_line, end_col)) => {
                pos = end;
                line = end_line;
                col = end_col;
                let text = &input[start..end];
                if let Some(token) = accept_token(accept_state, text) {
                    let weight = accept_weight(accept_state);
                    tokens.push((
                        token,
                        Range {
                            start: Position {
                                byte_offset: start,
                                line: start_line,
                                column: start_col,
                            },
                            end: Position {
                                byte_offset: end,
                                line: end_line,
                                column: end_col,
                            },
                            file_id,
                        },
                        weight,
                    ));
                }
            }
            None => {
                let ch = bytes[start] as char;
                let msg = if ch.is_ascii() {
                    format!(
                        "{}:{}: unexpected character '{}'",
                        line + 1, col + 1, ch,
                    )
                } else {
                    format!(
                        "{}:{}: unexpected byte 0x{:02X}",
                        line + 1, col + 1, bytes[start],
                    )
                };
                return Err(msg);
            }
        }
    }

    let eof_pos = Position {
        byte_offset: pos,
        line,
        column: col,
    };
    Ok((tokens, eof_pos))
}

/// B3: Generic DFA lex loop that produces a `TokenSource` with lattice construction
/// for ambiguous accepting states.
///
/// Same DFA walk as `lex_weighted_core`, but at multi-accept states, emits ALL
/// alternative tokenizations as lattice edges. When no ambiguity is detected
/// (all accept states are unambiguous), returns `TokenSource::Linear` — zero
/// overhead vs the non-lattice path.
///
/// The `accept_alternatives` callback returns `(token, weight)` pairs for all
/// valid tokenizations at a given DFA accept state. For unambiguous states, it
/// returns a single-element slice. For multi-accept states, it returns all
/// alternatives sorted by weight (best first).
///
/// Generic over `T` (token type) and dispatched via closures so the compiler
/// monomorphizes away all closure overhead.
pub fn lex_lattice_core<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_alternatives: impl Fn(u32, &'a str) -> Vec<(T, f64)>,
) -> Result<(crate::lattice::TokenSource<T, Range>, Position), String> {
    use crate::automata::semiring::TropicalWeight;
    use crate::lattice::{TokenLattice, TokenSource};

    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    // Collect tokens with position tracking; detect ambiguity
    let mut linear_tokens: Vec<(T, Range)> = Vec::with_capacity(input.len() / 2);
    let mut has_ambiguity = false;
    // For lattice construction (lazy: only populated if ambiguity detected)
    struct TokenAlts<T> {
        range: Range,
        alternatives: Vec<(T, f64)>,
    }
    let mut token_alts: Vec<TokenAlts<T>> = Vec::new();

    while pos < bytes.len() {
        while pos < bytes.len() && is_whitespace(bytes[pos]) {
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else {
                col += 1;
            }
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }

        let start = pos;
        let start_line = line;
        let start_col = col;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize, usize, usize)> = None;

        if is_accepting(0) {
            last_accept = Some((0, pos, line, col));
        }

        while pos < bytes.len() {
            let class = char_class[bytes[pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            if bytes[pos] == b'\n' {
                line += 1;
                col = 0;
            } else if bytes[pos] & 0xC0 != 0x80 {
                col += 1;
            }
            pos += 1;
            if is_accepting(state) {
                last_accept = Some((state, pos, line, col));
            }
        }

        match last_accept {
            Some((accept_state, end, end_line, end_col)) => {
                pos = end;
                line = end_line;
                col = end_col;
                let text = &input[start..end];
                let alts = accept_alternatives(accept_state, text);
                if alts.is_empty() {
                    // No token produced (e.g., whitespace-only state) — skip
                    continue;
                }
                let range = Range {
                    start: Position {
                        byte_offset: start,
                        line: start_line,
                        column: start_col,
                    },
                    end: Position {
                        byte_offset: end,
                        line: end_line,
                        column: end_col,
                    },
                    file_id,
                };
                if alts.len() > 1 {
                    has_ambiguity = true;
                }
                // Always record for lattice construction (lazy)
                if !has_ambiguity && alts.len() == 1 {
                    linear_tokens.push((alts[0].0.clone(), range));
                }
                token_alts.push(TokenAlts {
                    range,
                    alternatives: alts,
                });
            }
            None => {
                let ch = bytes[start] as char;
                let msg = if ch.is_ascii() {
                    format!(
                        "{}:{}: unexpected character '{}'",
                        line + 1, col + 1, ch,
                    )
                } else {
                    format!(
                        "{}:{}: unexpected byte 0x{:02X}",
                        line + 1, col + 1, bytes[start],
                    )
                };
                return Err(msg);
            }
        }
    }

    let eof_pos = Position {
        byte_offset: pos,
        line,
        column: col,
    };

    if !has_ambiguity {
        // Fast path: no lexical ambiguity detected — return linear
        Ok((TokenSource::Linear(linear_tokens), eof_pos))
    } else {
        // Slow path: construct a lattice with branching at ambiguous positions.
        // Node layout: node i = position before token i; node N = after last token.
        // Each token_alts[i] produces edges from node i to node i+1 (one per alternative).
        let num_nodes = token_alts.len() + 1;
        let mut lattice: TokenLattice<T, Range> = TokenLattice::with_capacity(num_nodes);
        lattice.ensure_nodes(num_nodes);

        for (i, ta) in token_alts.iter().enumerate() {
            for (token, weight) in &ta.alternatives {
                lattice.add_edge(
                    i,
                    i + 1,
                    token.clone(),
                    ta.range,
                    TropicalWeight::new(*weight),
                );
            }
        }

        Ok((TokenSource::Lattice(lattice), eof_pos))
    }
}

#[inline(always)]
pub fn is_whitespace(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r')
}
