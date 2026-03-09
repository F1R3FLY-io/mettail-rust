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
        #[cfg(feature = "simd-whitespace")]
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        #[cfg(not(feature = "simd-whitespace"))]
        {
            while pos < bytes.len() && is_whitespace(bytes[pos]) {
                if bytes[pos] == b'\n' {
                    line += 1;
                    col = 0;
                } else {
                    col += 1;
                }
                pos += 1;
            }
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
        #[cfg(feature = "simd-whitespace")]
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        #[cfg(not(feature = "simd-whitespace"))]
        {
            while pos < bytes.len() && is_whitespace(bytes[pos]) {
                if bytes[pos] == b'\n' {
                    line += 1;
                    col = 0;
                } else {
                    col += 1;
                }
                pos += 1;
            }
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
        #[cfg(feature = "simd-whitespace")]
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        #[cfg(not(feature = "simd-whitespace"))]
        {
            while pos < bytes.len() && is_whitespace(bytes[pos]) {
                if bytes[pos] == b'\n' {
                    line += 1;
                    col = 0;
                } else {
                    col += 1;
                }
                pos += 1;
            }
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

// ══════════════════════════════════════════════════════════════════════════════
// AL03: SIMD-accelerated whitespace skipping (feature = "simd-whitespace")
// ══════════════════════════════════════════════════════════════════════════════

/// Result of SIMD whitespace skipping: the new cursor position and updated
/// line/column tracking.
#[cfg(feature = "simd-whitespace")]
#[derive(Debug, Clone, Copy)]
pub struct SkipResult {
    pub pos: usize,
    pub line: usize,
    pub col: usize,
}

/// Skip whitespace using portable SIMD (16-byte lanes).
///
/// Processes 16 bytes at a time, comparing against all four whitespace
/// characters (space, tab, newline, carriage return) in parallel. Falls
/// back to scalar processing for the tail (< 16 bytes) and for newline
/// counting within SIMD chunks.
///
/// # Safety
///
/// Uses only safe `std::simd` APIs. No unsafe code.
#[cfg(feature = "simd-whitespace")]
#[inline]
pub fn skip_whitespace_simd(bytes: &[u8], mut pos: usize, mut line: usize, mut col: usize) -> SkipResult {
    use std::simd::{Simd, cmp::SimdPartialEq};

    const LANE_WIDTH: usize = 16;

    let space = Simd::<u8, LANE_WIDTH>::splat(b' ');
    let tab = Simd::<u8, LANE_WIDTH>::splat(b'\t');
    let newline = Simd::<u8, LANE_WIDTH>::splat(b'\n');
    let cr = Simd::<u8, LANE_WIDTH>::splat(b'\r');

    // ── SIMD phase: process 16-byte chunks ──────────────────────────────
    while pos + LANE_WIDTH <= bytes.len() {
        let chunk = Simd::<u8, LANE_WIDTH>::from_slice(&bytes[pos..pos + LANE_WIDTH]);

        // Compare chunk against each whitespace character and OR the masks
        let is_ws = chunk.simd_eq(space)
            | chunk.simd_eq(tab)
            | chunk.simd_eq(newline)
            | chunk.simd_eq(cr);

        if is_ws.all() {
            // Entire 16-byte chunk is whitespace — count newlines for line tracking
            for i in 0..LANE_WIDTH {
                if bytes[pos + i] == b'\n' {
                    line += 1;
                    col = 0;
                } else {
                    col += 1;
                }
            }
            pos += LANE_WIDTH;
        } else if !is_ws.test(0) {
            // First byte is not whitespace — stop immediately
            break;
        } else {
            // Partial whitespace chunk — find first non-whitespace byte
            let mask = is_ws.to_bitmask();
            // trailing_ones() counts consecutive 1-bits from bit 0
            let ws_count = mask.trailing_ones() as usize;
            for i in 0..ws_count {
                if bytes[pos + i] == b'\n' {
                    line += 1;
                    col = 0;
                } else {
                    col += 1;
                }
            }
            pos += ws_count;
            // Non-whitespace found within this chunk — stop
            break;
        }
    }

    // ── Scalar tail: remaining bytes (< 16) ─────────────────────────────
    while pos < bytes.len() && is_whitespace(bytes[pos]) {
        if bytes[pos] == b'\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
        pos += 1;
    }

    SkipResult { pos, line, col }
}

/// Scalar whitespace skip (non-SIMD fallback, always available).
///
/// Used when `simd-whitespace` feature is not enabled and also as the
/// reference implementation for testing SIMD correctness.
#[inline]
pub fn skip_whitespace_scalar(bytes: &[u8], mut pos: usize, mut line: usize, mut col: usize) -> (usize, usize, usize) {
    while pos < bytes.len() && is_whitespace(bytes[pos]) {
        if bytes[pos] == b'\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
        pos += 1;
    }
    (pos, line, col)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

    #[test]
    fn test_position_zero() {
        let p = Position::zero();
        assert_eq!(p.byte_offset, 0);
        assert_eq!(p.line, 0);
        assert_eq!(p.column, 0);
    }

    #[test]
    fn test_position_display() {
        // Display is 1-indexed: line+1, column+1
        let p = Position { byte_offset: 0, line: 0, column: 0 };
        assert_eq!(p.to_string(), "1:1");

        let p2 = Position { byte_offset: 42, line: 3, column: 7 };
        assert_eq!(p2.to_string(), "4:8");
    }

    #[test]
    fn test_range_zero() {
        let r = Range::zero();
        assert_eq!(r.start, Position::zero());
        assert_eq!(r.end, Position::zero());
        assert_eq!(r.file_id, None);
    }

    #[test]
    fn test_range_display() {
        let r = Range {
            start: Position { byte_offset: 0, line: 0, column: 0 },
            end: Position { byte_offset: 5, line: 0, column: 5 },
            file_id: None,
        };
        // Format: "start-end" where start and end use Position::Display (1-indexed)
        assert_eq!(r.to_string(), "1:1-1:6");
    }

    #[test]
    fn test_parse_error_unexpected_token_display() {
        let err = ParseError::UnexpectedToken {
            expected: Cow::Borrowed("number or identifier"),
            found: "'+'".to_string(),
            range: Range {
                start: Position { byte_offset: 10, line: 2, column: 4 },
                end: Position { byte_offset: 11, line: 2, column: 5 },
                file_id: None,
            },
            hint: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("expected number or identifier"), "msg: {}", msg);
        assert!(msg.contains("found '+'"), "msg: {}", msg);
        assert!(msg.starts_with("3:5:"), "should show 1-indexed line:col, msg: {}", msg);
    }

    #[test]
    fn test_parse_error_unexpected_eof_display() {
        let err = ParseError::UnexpectedEof {
            expected: Cow::Borrowed("')'"),
            range: Range {
                start: Position { byte_offset: 20, line: 1, column: 10 },
                end: Position { byte_offset: 20, line: 1, column: 10 },
                file_id: None,
            },
            hint: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("unexpected end of input"), "msg: {}", msg);
        assert!(msg.contains("expected ')'"), "msg: {}", msg);
    }

    #[test]
    fn test_parse_error_lex_error_display() {
        let err = ParseError::LexError {
            message: "invalid character '@'".to_string(),
            position: Position { byte_offset: 5, line: 0, column: 5 },
        };
        let msg = err.to_string();
        assert!(msg.contains("invalid character '@'"), "msg: {}", msg);
        assert!(msg.starts_with("1:6:"), "should show 1-indexed position, msg: {}", msg);
    }

    #[test]
    fn test_parse_error_trailing_tokens_display() {
        let err = ParseError::TrailingTokens {
            found: "'}'".to_string(),
            range: Range {
                start: Position { byte_offset: 15, line: 0, column: 15 },
                end: Position { byte_offset: 16, line: 0, column: 16 },
                file_id: None,
            },
            hint: None,
        };
        let msg = err.to_string();
        assert!(msg.contains("unexpected '}'"), "msg: {}", msg);
        assert!(msg.contains("after parsing"), "msg: {}", msg);
    }

    #[test]
    fn test_parse_error_recovery_display() {
        let inner = ParseError::UnexpectedToken {
            expected: Cow::Borrowed("';'"),
            found: "'}'".to_string(),
            range: Range {
                start: Position { byte_offset: 5, line: 0, column: 5 },
                end: Position { byte_offset: 6, line: 0, column: 6 },
                file_id: None,
            },
            hint: None,
        };
        let err = ParseError::RecoveryApplied {
            original_error: Box::new(inner),
            repair_description: "skip 1 token(s) to ';'".to_string(),
            range: Range {
                start: Position { byte_offset: 5, line: 0, column: 5 },
                end: Position { byte_offset: 8, line: 0, column: 8 },
                file_id: None,
            },
        };
        let msg = err.to_string();
        assert!(msg.contains("recovered: skip 1 token(s) to ';'"), "msg: {}", msg);
        assert!(msg.contains("expected ';'"), "should include original error, msg: {}", msg);
    }

    #[test]
    fn test_parse_error_range_accessor() {
        let range1 = Range {
            start: Position { byte_offset: 0, line: 0, column: 0 },
            end: Position { byte_offset: 3, line: 0, column: 3 },
            file_id: Some(1),
        };
        let range2 = Range {
            start: Position { byte_offset: 10, line: 1, column: 2 },
            end: Position { byte_offset: 15, line: 1, column: 7 },
            file_id: Some(2),
        };

        // UnexpectedToken
        let e1 = ParseError::UnexpectedToken {
            expected: Cow::Borrowed("x"),
            found: "y".to_string(),
            range: range1,
            hint: None,
        };
        assert_eq!(e1.range(), range1);

        // UnexpectedEof
        let e2 = ParseError::UnexpectedEof {
            expected: Cow::Borrowed("x"),
            range: range2,
            hint: None,
        };
        assert_eq!(e2.range(), range2);

        // LexError — constructs a Range from the position
        let pos = Position { byte_offset: 7, line: 0, column: 7 };
        let e3 = ParseError::LexError {
            message: "bad".to_string(),
            position: pos,
        };
        let r3 = e3.range();
        assert_eq!(r3.start, pos);
        assert_eq!(r3.end, pos);
        assert_eq!(r3.file_id, None);

        // TrailingTokens
        let e4 = ParseError::TrailingTokens {
            found: "z".to_string(),
            range: range1,
            hint: None,
        };
        assert_eq!(e4.range(), range1);

        // RecoveryApplied
        let e5 = ParseError::RecoveryApplied {
            original_error: Box::new(ParseError::LexError {
                message: "x".to_string(),
                position: Position::zero(),
            }),
            repair_description: "skip".to_string(),
            range: range2,
        };
        assert_eq!(e5.range(), range2);
    }

    #[test]
    fn test_parse_error_from_string() {
        let err: ParseError = "something went wrong".to_string().into();
        match &err {
            ParseError::LexError { message, position } => {
                assert_eq!(message, "something went wrong");
                assert_eq!(*position, Position::zero());
            }
            other => panic!("expected LexError variant, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_error_context() {
        let input = "let x = 42\nlet y = @bad\nlet z = 0";
        // Error at '@' on line 1, column 8, byte_offset = 11 (line 0) + 8 = 19
        let byte_offset = input.find('@').expect("'@' not found in input");
        let range = Range {
            start: Position {
                byte_offset,
                line: 1,
                column: 8,
            },
            end: Position {
                byte_offset: byte_offset + 1,
                line: 1,
                column: 9,
            },
            file_id: None,
        };
        let ctx = format_error_context(input, &range);
        // Should contain the source line
        assert!(ctx.contains("let y = @bad"), "should contain source line, got: {}", ctx);
        // Should contain the caret ('^') pointing at column 8
        assert!(ctx.contains('^'), "should contain caret, got: {}", ctx);
        // The caret should be indented by 8 spaces
        let lines: Vec<&str> = ctx.lines().collect();
        assert_eq!(lines.len(), 2, "should have source line + caret line, got: {:?}", lines);
        assert_eq!(&lines[1][..8], "        ", "8 spaces of indent before caret");
        assert_eq!(&lines[1][8..9], "^", "caret at column 8");
    }

    #[test]
    fn test_parse_error_unexpected_token_with_hint() {
        let err = ParseError::UnexpectedToken {
            expected: Cow::Borrowed("')'"),
            found: "'}'".to_string(),
            range: Range::zero(),
            hint: Some(Cow::Borrowed("did you forget ')' ?")),
        };
        let msg = err.to_string();
        assert!(msg.contains("hint: did you forget ')' ?"), "hint should appear, msg: {}", msg);
    }
}
