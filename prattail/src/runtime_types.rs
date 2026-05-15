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

use crate::automata::utf8::decode_char_at;

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

/// Character-based range — absolute character offsets from start of input.
///
/// Used by editor-protocol APIs (LSP, etc.) and the incremental re-lex
/// machinery, both of which index by Unicode code point rather than UTF-8
/// byte offset. Convert with `Range::to_char_offset(input)` and
/// `Range::from_char_offset(input, start, end)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CharRange {
    pub start_chars: usize,
    pub end_chars: usize,
}

impl CharRange {
    pub fn zero() -> Self {
        CharRange { start_chars: 0, end_chars: 0 }
    }

    /// Width of the range in characters (saturating to 0 if reversed).
    pub fn len(&self) -> usize {
        self.end_chars.saturating_sub(self.start_chars)
    }

    pub fn is_empty(&self) -> bool {
        self.end_chars <= self.start_chars
    }
}

impl Range {
    pub fn zero() -> Self {
        Range {
            start: Position::zero(),
            end: Position::zero(),
            file_id: None,
        }
    }

    /// Compute the absolute character offsets corresponding to this range's
    /// byte-based positions, given the source text.
    ///
    /// Byte offsets that exceed `input.len()` are saturated to the input's
    /// byte length (the corresponding character offset is `input.chars().count()`).
    pub fn to_char_offset(&self, input: &str) -> CharRange {
        let start_byte = self.start.byte_offset.min(input.len());
        let end_byte = self.end.byte_offset.min(input.len());
        let start_chars = input[..start_byte].chars().count();
        let end_chars = input[..end_byte].chars().count();
        CharRange { start_chars, end_chars }
    }

    /// Construct a `Range` from absolute character offsets, computing the
    /// corresponding byte offsets, line numbers, and per-line columns by
    /// walking `input`.
    ///
    /// If a character offset exceeds the input's character count, it is
    /// clamped to the end of the input. `file_id` is set to `None`; callers
    /// that need a non-None file_id should overwrite it after construction.
    pub fn from_char_offset(input: &str, start_chars: usize, end_chars: usize) -> Self {
        let start = byte_to_position(input, char_to_byte(input, start_chars));
        let end = byte_to_position(input, char_to_byte(input, end_chars));
        Range {
            start,
            end,
            file_id: None,
        }
    }
}

/// Convert an absolute character offset to a UTF-8 byte offset within `input`.
///
/// If `char_offset` is past the end of `input`, returns `input.len()`. The
/// returned byte offset is always at a valid UTF-8 char boundary.
#[inline]
fn char_to_byte(input: &str, char_offset: usize) -> usize {
    input
        .char_indices()
        .nth(char_offset)
        .map(|(b, _)| b)
        .unwrap_or(input.len())
}

/// Walk `input` to compute the `Position` (byte_offset/line/column) at the
/// given UTF-8 byte offset. `byte_offset` must be on a char boundary or
/// equal to `input.len()`.
#[inline]
fn byte_to_position(input: &str, byte_offset: usize) -> Position {
    let mut line: usize = 0;
    let mut column: usize = 0;
    for (b, ch) in input.char_indices() {
        if b >= byte_offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            column = 0;
        } else {
            column += 1;
        }
    }
    Position {
        byte_offset,
        line,
        column,
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
    /// M11.7 (2026-05-14): the walker was configured with
    /// `CursorBoundingMode::AmbiguityBudget(budget)` and the live frontier
    /// exceeded that budget at the indicated `position`.
    ///
    /// Distinct from `UnexpectedToken` / `UnexpectedEof` because the input
    /// IS parseable — the parser just produced more ambiguity than the
    /// caller's budget allows. Callers can react by relaxing the budget,
    /// switching strategy, or surfacing a user-facing "input too
    /// ambiguous" message.
    AmbiguityBudget {
        budget: usize,
        actual: usize,
        range: Range,
        hint: Option<Cow<'static, str>>,
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
            ParseError::AmbiguityBudget { budget, actual, range, hint } => {
                write!(
                    f,
                    "{}:{}: input too ambiguous: frontier of {} cursors exceeds budget of {}",
                    range.start.line + 1,
                    range.start.column + 1,
                    actual,
                    budget,
                )?;
                if let Some(h) = hint {
                    write!(f, "\n  = hint: {}", h)?;
                }
                Ok(())
            }
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
            ParseError::AmbiguityBudget { range, .. } => *range,
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
            // Count characters (not bytes) for correct caret width with multi-byte UTF-8
            input[range.start.byte_offset..range.end.byte_offset].chars().count()
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
        // Skip whitespace (ASCII fast path + Unicode fallback)
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        // Unicode whitespace fallback (zero-cost for ASCII input: branch not taken)
        while pos < bytes.len() && bytes[pos] >= 0x80 {
            match decode_char_at(input, pos) {
                Some((ch, ch_len)) if ch.is_whitespace() => {
                    col += 1;
                    pos += ch_len;
                }
                _ => break,
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
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1, col + 1, ch.escape_debug(),
                );
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
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        // Unicode whitespace fallback
        while pos < bytes.len() && bytes[pos] >= 0x80 {
            match decode_char_at(input, pos) {
                Some((ch, ch_len)) if ch.is_whitespace() => {
                    col += 1;
                    pos += ch_len;
                }
                _ => break,
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
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1, col + 1, ch.escape_debug(),
                );
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
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        // Unicode whitespace fallback
        while pos < bytes.len() && bytes[pos] >= 0x80 {
            match decode_char_at(input, pos) {
                Some((ch, ch_len)) if ch.is_whitespace() => {
                    col += 1;
                    pos += ch_len;
                }
                _ => break,
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
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1, col + 1, ch.escape_debug(),
                );
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

/// L-substrate Piece #1 (2026-05-13): multi-accept DFA scanner producing a
/// `LexStream` with multi-LENGTH alternatives per byte position.
///
/// Unlike `lex_lattice_core` (which only reports SAME-END-BYTE ambiguity),
/// this function records EVERY accepting state visited along the DFA walk
/// — so input `-3` produces `entries[0].alternatives = [Integer(-3)@end=2,
/// Minus@end=1]` (longest first). The walker's PrefixDispatch lex-Fork
/// emission consumes these to spawn parallel cursors.
///
/// The PRIMARY timeline (the longest-match path) populates the rest of
/// `entries[1..]`. Secondary (shorter-match) timelines are NOT materialized
/// here — they're re-lexed on demand at Fork-commit time by
/// `MutableMultiTokenSource::commit_alternative`.
///
/// The `token_to_kind` callback converts the language-specific `Token<'a>`
/// (returned by `accept_alternatives`) to the kind-only `TokenKind`
/// carried by `LexAlternative`.
///
/// Returns the populated `LexStream` and the post-EOF `Position`.
pub fn lex_stream_core<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_alternatives: impl Fn(u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
) -> Result<(crate::lexer_types::LexStream, Position), String> {
    use crate::automata::semiring::TropicalWeight;
    use crate::lexer_types::{LexAlternative, LexEntry, LexStream};

    let _ = file_id;
    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    let mut stream = LexStream::new();
    stream.entries.reserve(input.len() / 2);

    while pos < bytes.len() {
        {
            let result = skip_whitespace_simd(bytes, pos, line, col);
            pos = result.pos;
            line = result.line;
            col = result.col;
        }
        while pos < bytes.len() && bytes[pos] >= 0x80 {
            match decode_char_at(input, pos) {
                Some((ch, ch_len)) if ch.is_whitespace() => {
                    col += 1;
                    pos += ch_len;
                }
                _ => break,
            }
        }
        if pos >= bytes.len() {
            break;
        }

        let start = pos;
        let mut walk_pos = pos;
        let mut walk_line = line;
        let mut walk_col = col;
        let mut state: u32 = 0;
        // Record EVERY accepting state visited along the walk —
        // (accept_state, end_byte, end_line, end_col).
        let mut accepts: Vec<(u32, usize, usize, usize)> = Vec::new();

        if is_accepting(0) {
            accepts.push((0, walk_pos, walk_line, walk_col));
        }

        while walk_pos < bytes.len() {
            let class = char_class[bytes[walk_pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            if bytes[walk_pos] == b'\n' {
                walk_line += 1;
                walk_col = 0;
            } else if bytes[walk_pos] & 0xC0 != 0x80 {
                walk_col += 1;
            }
            walk_pos += 1;
            if is_accepting(state) {
                accepts.push((state, walk_pos, walk_line, walk_col));
            }
        }

        if accepts.is_empty() {
            let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
            let msg = format!(
                "{}:{}: unexpected character '{}'",
                line + 1,
                col + 1,
                ch.escape_debug(),
            );
            return Err(msg);
        }

        // Build alternatives from ALL accepts. Longest-first ordering for
        // primary canonical (`lex_alt_idx == 0` per
        // `LexicographicWeight::lex_cmp`). Same-end-byte alternatives
        // (from accept_alternatives) are emitted in their existing
        // priority order (best weight first).
        let mut alternatives: Vec<LexAlternative> = Vec::with_capacity(accepts.len() * 2);
        for &(accept_state, accept_end, _, _) in accepts.iter().rev() {
            let alt_text = &input[start..accept_end];
            let alt_tokens = accept_alternatives(accept_state, alt_text);
            for (token, weight) in alt_tokens {
                let kind = token_to_kind(&token);
                alternatives.push(LexAlternative {
                    kind,
                    text: alt_text.to_string(),
                    end_byte: accept_end,
                    weight: TropicalWeight::new(weight),
                });
            }
        }

        if alternatives.is_empty() {
            // No token produced at any visited accept state (e.g., all
            // accepts were whitespace-only). Advance one byte and
            // continue; otherwise we'd loop forever.
            // The longest accept advanced walk_pos; consume it.
            let (longest_state, longest_end, longest_line, longest_col) =
                *accepts.last().expect("accepts non-empty above");
            let _ = longest_state;
            pos = longest_end;
            line = longest_line;
            col = longest_col;
            continue;
        }

        // Advance to the longest accept's end position (canonical primary).
        let (_, longest_end, longest_line, longest_col) =
            *accepts.last().expect("accepts non-empty above");
        pos = longest_end;
        line = longest_line;
        col = longest_col;

        stream.entries.push(LexEntry {
            byte_start: start,
            alternatives,
        });
    }

    let eof_pos = Position {
        byte_offset: pos,
        line,
        column: col,
    };
    Ok((stream, eof_pos))
}

/// M2 (2026-05-13): build a [`LexDag`] over the input bytes.
///
/// Parallel to [`lex_stream_core`] but produces a DAG of token-boundary
/// nodes connected by edges (one per accepting state visited at each
/// byte position). The DAG replaces the flat `Vec<LexEntry>` for inputs
/// with multi-LENGTH lex ambiguity (e.g., `-3` lexing as both
/// `Integer(-3)@end=2` and `Minus@end=1`).
///
/// **Algorithm** (worklist scan):
/// 1. Start with byte position 0 on the worklist.
/// 2. For each byte position `b` in the worklist:
///    a. Allocate a node at `b`.
///    b. Walk the DFA from `b`, recording every accepting state visited.
///    c. For each accept, emit a `LexDagEdge` from `b → b.end_byte`.
///    d. Add each new `end_byte` to the worklist.
/// 3. After all reachable byte positions are scanned, fix up
///    `target_node` indices and sort each node's edges longest-first.
/// 4. Append an EOF sentinel node at `input.len()` with no edges.
///
/// **Result**: a DAG where:
/// - For unambiguous inputs, every node has exactly one outgoing edge
///   (a chain). `has_ambiguity() == false`. Callers can `linear_path()`
///   and route to the fast `SliceTokenSource` path.
/// - For ambiguous inputs (multi-length accepts at one position), the
///   relevant nodes have ≥2 outgoing edges. The walker's
///   `LatticeTokenSource` (M3) exposes these to the engine via
///   `peek_alternatives` for Fork emission.
///
/// **Complexity**: O(input_length × avg_DFA_walk_per_position). Each byte
/// position is scanned at most once (deduplicated via `byte_to_node`).
/// For non-ambiguous inputs, behavior is byte-for-byte equivalent to
/// `lex_stream_core` in cost.
///
/// The `token_to_kind` callback converts the language-specific `Token<'a>`
/// (from `accept_alternatives`) to the kind-only `TokenKind` carried by
/// `LexDagEdge`.
pub fn lex_dag_core<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_alternatives: impl Fn(u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
) -> Result<crate::lexer_types::LexDag, String> {
    use crate::automata::semiring::TropicalWeight;
    use crate::lexer_types::{LexDag, LexDagEdge, LexDagNode};
    use std::collections::{BTreeMap, VecDeque};

    let _ = file_id;
    let bytes = input.as_bytes();
    let mut byte_to_node: BTreeMap<usize, usize> = BTreeMap::new();
    let mut nodes: Vec<LexDagNode> = Vec::new();
    // (raw edges with `target_byte` instead of `target_node` — fix up after
    // all nodes are allocated)
    let mut raw_edges: Vec<(usize, Vec<(crate::automata::TokenKind, String, usize, TropicalWeight)>)> =
        Vec::new();
    let mut worklist: VecDeque<usize> = VecDeque::new();
    worklist.push_back(0);
    // M6c.7.1 (2026-05-14): primary-chain tracking for soft-fail
    // semantics. A position is "primary" if it's reachable via the
    // maximal-munch (longest-end) accept at some node, OR if it's the
    // initial position (byte 0). When the DFA fails to scan from a
    // primary position, that's a TRUE input error and we hard-fail
    // (matching `lex` parity). When it fails at a SECONDARY-only
    // position (only reachable via a non-longest alt's downstream),
    // we soft-fail: allocate an orphan node with empty edges. The
    // secondary alt's lex-Fork branch in the walker spawns a cursor
    // that lands at the orphan, sees `peek_kind = Eof`, fails to
    // dispatch in the parser state machine, and dies naturally —
    // pure rule-out by structural evidence (the alt's downstream
    // doesn't lex, so the alt cannot contribute to any valid parse).
    let mut primary_targets: std::collections::HashSet<usize> =
        std::collections::HashSet::new();
    primary_targets.insert(0);
    // M6c.8.1 (2026-05-14): canonical EOF sentinel index, captured
    // when we allocate the node at `byte_start == bytes.len()`.
    // `byte_to_node` is keyed on the worklist's PRE-WS-skip `start`,
    // not the post-skip `pos` — so `byte_to_node[bytes.len()]` may
    // miss when the EOF sentinel is reached via a `start` < bytes.len()
    // followed by WS skip to bytes.len(). Capture during allocation
    // instead.
    let mut eof_node_idx: Option<usize> = None;

    while let Some(start) = worklist.pop_front() {
        if byte_to_node.contains_key(&start) {
            continue;
        }
        // Skip whitespace at this position; the resulting `pos` becomes
        // the actual node's byte_start. This keeps the DAG semantically
        // aligned with `lex_stream_core` (whitespace is non-token).
        // line/col tracking is not needed here — the DAG only carries
        // byte positions; error reporting upstream handles line/col.
        let mut pos = start;
        {
            let result = skip_whitespace_simd(bytes, pos, 0, 0);
            pos = result.pos;
        }
        while pos < bytes.len() && bytes[pos] >= 0x80 {
            match decode_char_at(input, pos) {
                Some((ch, ch_len)) if ch.is_whitespace() => {
                    pos += ch_len;
                }
                _ => break,
            }
        }

        let node_idx = nodes.len();
        byte_to_node.insert(start, node_idx);
        nodes.push(LexDagNode {
            byte_start: pos,
            edges: Vec::new(),
        });
        raw_edges.push((node_idx, Vec::new()));

        if pos >= bytes.len() {
            // EOF sentinel: no edges, but still allocated so callers can
            // observe the node. M6c.8.1: capture the EOF index for
            // `LexDag.eof_node`. Multiple worklist starts may reach
            // bytes.len() (only happens with overlapping accepts that
            // all reach EOF — rare; first writer wins).
            if eof_node_idx.is_none() {
                eof_node_idx = Some(node_idx);
            }
            continue;
        }

        // Walk the DFA from `pos`, recording every accepting state.
        let mut walk_pos = pos;
        let mut state: u32 = 0;
        let mut accepts: Vec<(u32, usize)> = Vec::new();
        if is_accepting(0) {
            accepts.push((0, walk_pos));
        }
        while walk_pos < bytes.len() {
            let class = char_class[bytes[walk_pos] as usize];
            let next = dfa_next(state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            walk_pos += 1;
            if is_accepting(state) {
                accepts.push((state, walk_pos));
            }
        }

        if accepts.is_empty() {
            // M6c.7.1 (2026-05-14): soft-fail for secondary-alt dead-ends.
            // If this position is reachable ONLY via a non-primary
            // (shorter-than-maximal-munch) alt's downstream, the
            // failure is structural rule-out by evidence: the alt
            // cannot contribute to any valid parse, so the
            // corresponding lex-Fork branch in the walker spawns a
            // cursor that lands at the orphan node (empty edges →
            // peek_kind = Eof), fails to dispatch, dies naturally.
            //
            // If `start` IS on the primary maximal-munch chain
            // (reachable via the longest-end accept of some node),
            // this is a true input error that `lex` would ALSO fail
            // on. Preserve the hard-fail surface.
            if !primary_targets.contains(&start) {
                // Orphan node: already allocated at line 977 with
                // empty `edges`. raw_edges[node_idx] stays empty;
                // fixup loop below emits no edges for this node.
                continue;
            }
            let (ch, _ch_len) = decode_char_at(input, pos).unwrap_or(('\u{FFFD}', 1));
            return Err(format!(
                "unexpected character '{}' at byte {}",
                ch.escape_debug(),
                pos
            ));
        }

        // For each accept, emit a raw edge (target_byte = end_byte).
        // Order by end_byte DESCENDING (longest-first) so edges[0] is
        // the canonical primary.
        accepts.sort_by(|a, b| b.1.cmp(&a.1));
        // M6c.4-bugfix (2026-05-14): apply longest-match-per-kind
        // filtering HERE (during edge collection) rather than only at
        // the edge-fixup step below. This is critical for cursor
        // pos-advancement correctness: the walker's
        // `advance_cursor_pos(cursor, 1)` increments `cursor.pos` by 1,
        // which (for LatticeTokenSource) is the NEXT node id. If we
        // queue intermediate accept end_bytes to the worklist
        // unconditionally, the DAG gets ORPHAN intermediate nodes (no
        // incoming edges after dedup) interleaved with real nodes.
        // E.g., for `merge` (Ident accepts at end=1, 2, 3, 4, 5), the
        // worklist allocates 5 intermediate nodes before reaching the
        // longest accept at end=5. After edge dedup keeps only the
        // longest per kind, those 4 intermediate nodes are orphans —
        // but they're still indexed in `dag.nodes`. The walker's
        // `pos += 1` then advances into orphan territory, producing
        // bogus peek_kind/peek_text values and walker termination
        // beyond the legitimate input boundary (e.g., pos=10 for a
        // 9-byte input).
        //
        // The fix: filter accepts to LONGEST per kind BEFORE queueing
        // their end_bytes to the worklist. This keeps node IDs dense
        // and aligned with token positions.
        let mut seen_kinds_this_node: std::collections::HashSet<
            crate::automata::TokenKind,
        > = std::collections::HashSet::new();
        // M6c.7.1: the longest end_byte is the primary maximal-munch
        // target. Track it to propagate primary-chain status through
        // the worklist; secondary alts (shorter end_bytes) get
        // soft-fail semantics when their downstream can't lex.
        let primary_end_byte = accepts.first().map(|a| a.1);
        for (accept_state, end_byte) in accepts.iter() {
            let text = &input[pos..*end_byte];
            let alt_tokens = accept_alternatives(*accept_state, text);
            let mut emitted_any_for_this_accept = false;
            for (token, weight) in alt_tokens {
                let kind = token_to_kind(&token);
                if !seen_kinds_this_node.insert(kind.clone()) {
                    // Already have a longer-or-equal edge for this kind
                    // at this node — drop the redundant shorter accept.
                    continue;
                }
                raw_edges[node_idx].1.push((
                    kind,
                    text.to_string(),
                    *end_byte,
                    TropicalWeight(weight),
                ));
                emitted_any_for_this_accept = true;
            }
            // Queue the target byte position for scanning ONLY if at
            // least one edge survived the longest-per-kind filter for
            // this accept. Otherwise the accept is fully redundant and
            // creating an orphan node would just confuse the walker's
            // pos-advancement.
            if emitted_any_for_this_accept && !byte_to_node.contains_key(end_byte) {
                worklist.push_back(*end_byte);
                // M6c.7.1: mark primary-chain targets so soft-fail
                // logic at the worklist pop above can distinguish
                // dead-end secondaries (soft-fail) from primary-chain
                // dead-ends (hard-fail, preserves `lex` parity).
                if Some(*end_byte) == primary_end_byte {
                    primary_targets.insert(*end_byte);
                }
            }
        }
    }

    // Fix up raw_edges: convert target_byte → target_node via byte_to_node.
    // Whitespace-skipped target bytes (when end_byte falls in a run of
    // whitespace) resolve to the node at the SKIPPED position, since
    // byte_to_node is keyed by the raw end_byte but the worklist allocates
    // nodes at the post-skip byte.
    //
    // M6b (2026-05-14): dedupe edges by `(kind, text, end_byte)`. The
    // codegen-emitted `accept_alternatives` may produce duplicate
    // (Token, weight) pairs when two literal rules share a regex pattern
    // (e.g., Int's NumLit and UInt32's UInt32Lit both matching `[0-9]+`
    // both emit `Token::Integer(...)` at the same DFA state).
    //
    // M6c.4 (2026-05-14): ALSO collapse same-kind multi-length entries to
    // their longest match. The DFA's accepting-state traversal naturally
    // emits one accept per intermediate state on the way to the longest
    // match. For identifiers like `MergeMap`, that yields 8 same-kind
    // entries: `Ident "M"`, `Ident "Me"`, ..., `Ident "MergeMap"`. These
    // are NOT semantically distinct alternatives — they're DFA-implementation
    // artifacts of greedy longest-match. Without this collapse, the
    // walker's lex-Fork emits one branch per prefix and the cursor count
    // explodes per identifier (O(N^k) where N is identifier length, k is
    // identifiers in input). The longest-match-per-kind rule preserves
    // genuine cross-kind multi-length ambiguity like `-3` (Minus@end=1
    // vs Integer@end=2) while eliminating same-kind redundancy.
    //
    // Ordering note: `accepts` is sorted longest-first at line ~1021, so
    // iteration sees longest-length entries before shorter ones. The
    // `seen` set keyed by `kind` ensures the FIRST entry for each kind
    // (= longest-match) wins.
    for (node_idx, edges) in raw_edges.into_iter() {
        let mut alt_idx_counter: u16 = 0;
        let mut seen: std::collections::HashSet<(
            crate::automata::TokenKind,
            String,
            usize,
        )> = std::collections::HashSet::new();
        // M6c.4: per-kind longest-match filter. Iterates edges in the
        // order they were collected (longest end_byte first per the
        // sort at line ~1021); the FIRST entry for each kind is the
        // longest, and subsequent same-kind entries are dropped.
        let mut seen_kinds: std::collections::HashSet<
            crate::automata::TokenKind,
        > = std::collections::HashSet::new();
        for (kind, text, end_byte, weight) in edges {
            let target_node = match byte_to_node.get(&end_byte) {
                Some(&idx) => idx,
                None => {
                    // No node allocated for this end_byte — should be
                    // impossible given the worklist scan, but be defensive.
                    continue;
                }
            };
            let key = (kind.clone(), text.clone(), end_byte);
            if !seen.insert(key) {
                // Duplicate (kind, text, end_byte) — already pushed.
                continue;
            }
            if !seen_kinds.insert(kind.clone()) {
                // Same kind already has a (longer) edge — drop this
                // shorter-prefix accept.
                continue;
            }
            nodes[node_idx].edges.push(LexDagEdge {
                kind,
                text,
                end_byte,
                target_node,
                weight,
                alt_idx: alt_idx_counter,
            });
            alt_idx_counter += 1;
        }
    }

    // M6c.8.1 (2026-05-14): record the EOF sentinel index. The worklist
    // always seeds byte 0 and reaches `bytes.len()` along the primary
    // chain (the longest accept's end_byte chain), so `bytes.len()` is
    // always allocated as a node. For empty input, the very first pop
    // allocates node 0 at byte 0 (= `bytes.len()`); that's the EOF
    // sentinel.
    let eof_node = eof_node_idx.unwrap_or_else(|| {
        debug_assert!(
            false,
            "EOF sentinel must be allocated by lex_dag_core"
        );
        // Defensive fallback: last node (may be an orphan, but
        // better than panicking in release).
        nodes.len().saturating_sub(1)
    });
    Ok(LexDag {
        nodes,
        byte_to_node,
        eof_node,
    })
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

    // ── L7: UTF-8 char/byte offset helpers ────────────────────────────────

    #[test]
    fn char_range_zero_and_len() {
        let cr = CharRange::zero();
        assert_eq!(cr.start_chars, 0);
        assert_eq!(cr.end_chars, 0);
        assert_eq!(cr.len(), 0);
        assert!(cr.is_empty());

        let cr2 = CharRange { start_chars: 3, end_chars: 7 };
        assert_eq!(cr2.len(), 4);
        assert!(!cr2.is_empty());

        // Reversed (start > end) saturates to 0
        let cr3 = CharRange { start_chars: 7, end_chars: 3 };
        assert_eq!(cr3.len(), 0);
        assert!(cr3.is_empty());
    }

    #[test]
    fn range_to_char_offset_ascii() {
        let input = "hello world";
        let r = Range {
            start: Position { byte_offset: 6, line: 0, column: 6 },
            end: Position { byte_offset: 11, line: 0, column: 11 },
            file_id: None,
        };
        let cr = r.to_char_offset(input);
        assert_eq!(cr.start_chars, 6);
        assert_eq!(cr.end_chars, 11);
    }

    #[test]
    fn range_to_char_offset_unicode() {
        // "héllo" — 'é' is 2 bytes (U+00E9), 5 chars, 6 bytes total.
        let input = "héllo";
        assert_eq!(input.len(), 6);
        assert_eq!(input.chars().count(), 5);

        // Range covering "éllo" (chars 1..5, bytes 1..6)
        let r = Range {
            start: Position { byte_offset: 1, line: 0, column: 1 },
            end: Position { byte_offset: 6, line: 0, column: 5 },
            file_id: None,
        };
        let cr = r.to_char_offset(input);
        assert_eq!(cr.start_chars, 1);
        assert_eq!(cr.end_chars, 5);
    }

    #[test]
    fn range_to_char_offset_clamps_oversize_byte() {
        let input = "abc";
        let r = Range {
            start: Position { byte_offset: 1, line: 0, column: 1 },
            end: Position { byte_offset: 999, line: 0, column: 999 },
            file_id: None,
        };
        let cr = r.to_char_offset(input);
        assert_eq!(cr.start_chars, 1);
        assert_eq!(cr.end_chars, 3); // clamped to chars().count()
    }

    #[test]
    fn range_from_char_offset_ascii_single_line() {
        let input = "hello world";
        let r = Range::from_char_offset(input, 6, 11);
        assert_eq!(r.start.byte_offset, 6);
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.column, 6);
        assert_eq!(r.end.byte_offset, 11);
        assert_eq!(r.end.line, 0);
        assert_eq!(r.end.column, 11);
        assert_eq!(r.file_id, None);
    }

    #[test]
    fn range_from_char_offset_multi_line() {
        // "abc\ndef\nghi" — chars: a(0)b(1)c(2)\n(3)d(4)e(5)f(6)\n(7)g(8)h(9)i(10)
        let input = "abc\ndef\nghi";
        let r = Range::from_char_offset(input, 5, 9);
        // char 5 = 'e' on line 1, col 1
        assert_eq!(r.start.byte_offset, 5);
        assert_eq!(r.start.line, 1);
        assert_eq!(r.start.column, 1);
        // char 9 = 'h' on line 2, col 1
        assert_eq!(r.end.byte_offset, 9);
        assert_eq!(r.end.line, 2);
        assert_eq!(r.end.column, 1);
    }

    #[test]
    fn range_from_char_offset_unicode() {
        // "α=β\nγ" — α(2 bytes), =(1), β(2), \n(1), γ(2). Chars: α(0),=(1),β(2),\n(3),γ(4).
        let input = "α=β\nγ";
        let r = Range::from_char_offset(input, 2, 4);
        // char 2 = 'β' at byte 3, line 0, col 2
        assert_eq!(r.start.byte_offset, 3);
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.column, 2);
        // char 4 = 'γ' at byte 6, line 1, col 0
        assert_eq!(r.end.byte_offset, 6);
        assert_eq!(r.end.line, 1);
        assert_eq!(r.end.column, 0);
    }

    #[test]
    fn range_from_char_offset_clamps_to_end() {
        let input = "abc";
        let r = Range::from_char_offset(input, 999, 1_000_000);
        assert_eq!(r.start.byte_offset, input.len());
        assert_eq!(r.end.byte_offset, input.len());
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.column, 3);
    }

    #[test]
    fn range_char_byte_round_trip_ascii() {
        let input = "the quick brown fox";
        let original = Range {
            start: Position { byte_offset: 4, line: 0, column: 4 },
            end: Position { byte_offset: 9, line: 0, column: 9 },
            file_id: None,
        };
        let cr = original.to_char_offset(input);
        let restored = Range::from_char_offset(input, cr.start_chars, cr.end_chars);
        // byte_offset / line / column round-trip exactly for in-range positions
        assert_eq!(restored.start, original.start);
        assert_eq!(restored.end, original.end);
    }

    #[test]
    fn range_char_byte_round_trip_unicode_multiline() {
        // Layout:
        //   🦀(4 bytes 0..4) ' '(4..5) r(5) u(6) s(7) t(8) \n(9)
        //   日(10..13) 本(13..16) 語(16..19) \n(19)
        //   a(20) s(21) c(22) i(23) i(24)
        // Char indices:
        //   🦀=0 ' '=1 r=2 u=3 s=4 t=5 \n=6 日=7 本=8 語=9 \n=10 a=11 ...
        let input = "🦀 rust\n日本語\nascii";
        let original = Range {
            start: Position { byte_offset: 5, line: 0, column: 2 },
            end: Position { byte_offset: 19, line: 1, column: 3 },
            file_id: None,
        };
        let cr = original.to_char_offset(input);
        assert_eq!(cr.start_chars, 2);
        assert_eq!(cr.end_chars, 10);
        let restored = Range::from_char_offset(input, cr.start_chars, cr.end_chars);
        assert_eq!(restored.start, original.start);
        assert_eq!(restored.end, original.end);
    }

    // ──────────────────────────────────────────────────────────────────
    // M2 (2026-05-13): lex_dag_core unit tests
    // ──────────────────────────────────────────────────────────────────

    /// Minimal DFA encoding for the M2 tests: two tokens, `Minus` and
    /// `Integer`. The DFA recognizes `-?\d+` (Integer) AND `-` (Minus).
    /// State 0: start. State 1: just saw `-` (accepts Minus AND continues
    /// toward Integer). State 2: saw `\d+` (accepts Integer). State u32::MAX:
    /// no transition.
    fn make_test_dfa() -> (
        [u8; 256],
        impl Fn(u32, u8) -> u32,
        impl Fn(u32) -> bool,
        impl for<'a> Fn(u32, &'a str) -> Vec<(crate::automata::TokenKind, f64)>,
        impl Fn(&crate::automata::TokenKind) -> crate::automata::TokenKind,
    ) {
        // char_class: '-' → 0, '0'..='9' → 1, else → 2 (no-transition).
        let mut char_class = [2u8; 256];
        char_class[b'-' as usize] = 0;
        for c in b'0'..=b'9' {
            char_class[c as usize] = 1;
        }
        // state 0: '-' → 1, digit → 2
        // state 1: '-' → MAX, digit → 2
        // state 2: '-' → MAX, digit → 2
        let dfa_next = |s: u32, c: u8| -> u32 {
            match (s, c) {
                (0, 0) => 1,
                (0, 1) => 2,
                (1, 1) => 2,
                (2, 1) => 2,
                _ => u32::MAX,
            }
        };
        let is_accepting = |s: u32| -> bool { s == 1 || s == 2 };
        // Both accept states emit ONE alternative each.
        let accept_alternatives = |s: u32, text: &str| -> Vec<(crate::automata::TokenKind, f64)> {
            let _ = text;
            match s {
                1 => vec![(crate::automata::TokenKind::Fixed("-".to_string()), 0.0)],
                2 => vec![(crate::automata::TokenKind::Integer, 0.0)],
                _ => Vec::new(),
            }
        };
        // Identity for this test (we pass TokenKind in, get TokenKind out).
        let token_to_kind = |t: &crate::automata::TokenKind| -> crate::automata::TokenKind {
            t.clone()
        };
        (
            char_class,
            dfa_next,
            is_accepting,
            accept_alternatives,
            token_to_kind,
        )
    }

    #[test]
    fn lex_dag_minus_3_has_ambiguity() {
        // Input "-3": DFA visits state 1 (accepts Minus) at byte 1, then
        // state 2 (accepts Integer) at byte 2. Expected DAG:
        //   node 0 (byte_start=0): edges = [Integer@end=2, Minus@end=1]
        //   node 1 (byte_start=1, allocated for Minus's target): edges = [Integer@end=2]
        //   node 2 (byte_start=2, EOF sentinel): edges = []
        let (cc, dfa_next, is_acc, accept_alts, to_kind) = make_test_dfa();
        let dag = lex_dag_core("-3", None, &cc, dfa_next, is_acc, accept_alts, to_kind)
            .expect("lex_dag should succeed");
        assert!(dag.has_ambiguity(), "DAG should have multi-length ambiguity for `-3`");
        // Node 0 has 2 edges, longest-first.
        let node_0 = &dag.nodes[0];
        assert_eq!(node_0.byte_start, 0);
        assert_eq!(node_0.edges.len(), 2);
        assert_eq!(node_0.edges[0].end_byte, 2); // Integer first (longest)
        assert_eq!(node_0.edges[1].end_byte, 1); // Minus second (shorter)
        assert!(matches!(
            node_0.edges[0].kind,
            crate::automata::TokenKind::Integer
        ));
        assert!(matches!(
            node_0.edges[1].kind,
            crate::automata::TokenKind::Fixed(ref s) if s == "-"
        ));
        // The shorter alt's target (byte 1) is also a node with its own edge.
        let target_for_minus = node_0.edges[1].target_node;
        let node_1 = &dag.nodes[target_for_minus];
        assert_eq!(node_1.byte_start, 1);
        assert_eq!(node_1.edges.len(), 1);
        assert_eq!(node_1.edges[0].end_byte, 2);
        assert!(matches!(
            node_1.edges[0].kind,
            crate::automata::TokenKind::Integer
        ));
    }

    #[test]
    fn lex_dag_linear_3_no_ambiguity() {
        // Input "3": only state 2 (Integer) reached. One edge.
        let (cc, dfa_next, is_acc, accept_alts, to_kind) = make_test_dfa();
        let dag = lex_dag_core("3", None, &cc, dfa_next, is_acc, accept_alts, to_kind)
            .expect("lex_dag should succeed");
        assert!(!dag.has_ambiguity(), "DAG should be linear for `3`");
        let node_0 = &dag.nodes[0];
        assert_eq!(node_0.edges.len(), 1);
        assert!(matches!(
            node_0.edges[0].kind,
            crate::automata::TokenKind::Integer
        ));
    }

    #[test]
    fn lex_dag_alt_idx_assignment() {
        // For `-3`, node 0's edges should carry alt_idx 0 (primary/longest)
        // and alt_idx 1 (secondary/shorter).
        let (cc, dfa_next, is_acc, accept_alts, to_kind) = make_test_dfa();
        let dag = lex_dag_core("-3", None, &cc, dfa_next, is_acc, accept_alts, to_kind)
            .expect("lex_dag should succeed");
        let node_0 = &dag.nodes[0];
        assert_eq!(node_0.edges[0].alt_idx, 0);
        assert_eq!(node_0.edges[1].alt_idx, 1);
    }

    #[test]
    fn lex_dag_linear_path_returns_primary_chain() {
        // For `-3!` (but with our test DFA, just `-3`), `linear_path()`
        // should return [(Integer, "-3")] — the longest-first primary
        // path, ignoring the Minus alt.
        let (cc, dfa_next, is_acc, accept_alts, to_kind) = make_test_dfa();
        let dag = lex_dag_core("-3", None, &cc, dfa_next, is_acc, accept_alts, to_kind)
            .expect("lex_dag should succeed");
        let path = dag.linear_path();
        assert_eq!(path.len(), 1);
        assert!(matches!(path[0].0, crate::automata::TokenKind::Integer));
        assert_eq!(path[0].1, "-3");
    }

    #[test]
    fn lex_dag_unrecognized_byte_errors() {
        let (cc, dfa_next, is_acc, accept_alts, to_kind) = make_test_dfa();
        let result = lex_dag_core("abc", None, &cc, dfa_next, is_acc, accept_alts, to_kind);
        assert!(result.is_err());
    }
}
