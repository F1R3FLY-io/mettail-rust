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
        Position { byte_offset: 0, line: 0, column: 0 }
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
        Range { start, end, file_id: None }
    }

    /// Construct a `Range` from absolute UTF-8 byte offsets, computing line
    /// and column positions by walking `input`.
    ///
    /// Offsets past the input length are clamped to `input.len()`. The helper
    /// does not slice at the provided offsets, so callers may pass parser or
    /// lexer boundary offsets without separately proving they are char
    /// boundaries.
    pub fn from_byte_offsets(input: &str, start_byte: usize, end_byte: usize) -> Self {
        let start = byte_to_position(input, start_byte.min(input.len()));
        let end = byte_to_position(input, end_byte.min(input.len()));
        Range { start, end, file_id: None }
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
    Position { byte_offset, line, column }
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
    /// `CursorBoundingMode::AmbiguityBudget(budget)` and the number of DISTINCT
    /// REALIZED TERMS the goal admits exceeded that budget (checked whole-run at
    /// resolve — see the `CursorBoundingMode` rustdoc). `actual` is therefore a
    /// reading count, not a live-frontier cursor count.
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
    /// Forest reconstruction failed before any candidate term could be
    /// published by that realization request.
    ///
    /// This is deliberately separate from syntax and ambiguity errors.
    RealizationFailed {
        error: crate::wpda_runtime::RealizationError,
        range: Range,
    },
}

#[path = "runtime_types/parse_error_lifecycle.rs"]
mod parse_error_lifecycle;

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
            ParseError::RealizationFailed { range, .. } => *range,
        }
    }
}

impl std::error::Error for ParseError {}

impl From<String> for ParseError {
    fn from(message: String) -> Self {
        ParseError::LexError { message, position: Position::zero() }
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
            input[range.start.byte_offset..range.end.byte_offset]
                .chars()
                .count()
        } else {
            1
        };
    format!("{}\n{}{}", source_line, " ".repeat(caret_col), "^".repeat(caret_len))
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
                },
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
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1,
                    col + 1,
                    ch.escape_debug(),
                );
                return Err(msg);
            },
        }
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };
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
                },
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
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1,
                    col + 1,
                    ch.escape_debug(),
                );
                return Err(msg);
            },
        }
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };
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
                },
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
                token_alts.push(TokenAlts { range, alternatives: alts });
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                let msg = format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1,
                    col + 1,
                    ch.escape_debug(),
                );
                return Err(msg);
            },
        }
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };

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
                lattice.add_edge(i, i + 1, token.clone(), ta.range, TropicalWeight::new(*weight));
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
                },
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
            let msg =
                format!("{}:{}: unexpected character '{}'", line + 1, col + 1, ch.escape_debug(),);
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

        stream
            .entries
            .push(LexEntry { byte_start: start, alternatives });
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };
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
/// A raw (target-unresolved) outgoing edge produced by [`expand_lex_node`].
///
/// Carries everything a [`crate::lexer_types::LexDagEdge`] needs EXCEPT the
/// `target_node` index. The target is resolved by the caller (eager
/// `lex_dag_core`'s fix-up pass, or the lazy token source's on-demand
/// `byte_to_node` lookup) once the node at `end_byte` has been allocated.
#[derive(Debug, Clone)]
pub struct RawLexEdge {
    /// Token kind for this alternative.
    pub kind: crate::automata::TokenKind,
    /// Owned text of the matched bytes (`input[byte_start..end_byte]`).
    pub text: String,
    /// Byte position AFTER consuming this alt's bytes (= the successor
    /// node's enqueued `start`).
    pub end_byte: usize,
    /// Priority weight (lower = higher priority).
    pub weight: crate::automata::semiring::TropicalWeight,
    /// Sibling-edge ordinal at this node (matches the `alt_idx` convention
    /// of [`crate::lexer_types::LexDagEdge`] / `LexAlternative`).
    pub alt_idx: u16,
}

/// The outcome of expanding ONE byte position into a [`crate::lexer_types::LexDagNode`].
///
/// Produced by [`expand_lex_node`]; consumed by both the eager
/// [`lex_dag_core`] worklist and the lazy `LazyLatticeTokenSource`. It
/// carries the post-whitespace-skip `byte_start`, the surviving (raw)
/// outgoing edges (longest-first, per-kind deduped), the SUCCESSOR byte
/// positions the caller must enqueue (in edge order, the SAME order the
/// eager worklist would push them), and an `is_eof` flag set when the
/// position sits at `input.len()` (the EOF sentinel).
#[derive(Debug, Clone)]
pub struct ExpandedLexNode {
    /// Post-whitespace-skip byte offset where the node begins.
    pub byte_start: usize,
    /// Surviving raw outgoing edges (longest-first, longest-per-kind).
    pub edges: Vec<RawLexEdge>,
    /// Successor byte positions to enqueue, in the exact order the eager
    /// worklist pushes them (one per surviving accept whose edge set is
    /// non-empty, longest-first, deduped against already-enqueued bytes by
    /// the caller). For each successor, `is_primary` marks whether it is the
    /// maximal-munch (longest) target — used by the caller to propagate
    /// primary-chain status into `primary_targets` (M6c.7.1 soft-fail).
    pub successors: Vec<LexSuccessor>,
    /// Whether this node is the EOF sentinel (`byte_start == input.len()`).
    pub is_eof: bool,
}

/// A successor byte position emitted by [`expand_lex_node`], tagged with
/// whether it lies on the primary maximal-munch chain (M6c.7.1).
#[derive(Debug, Clone, Copy)]
pub struct LexSuccessor {
    /// The successor byte position (= the edge's `end_byte`, the enqueued
    /// `start` for the next node).
    pub byte: usize,
    /// Whether this successor is the longest (maximal-munch) accept of the
    /// node — propagates primary-chain status for soft-fail semantics.
    pub is_primary: bool,
}

/// Expand a SINGLE byte position into a lex-DAG node — the per-node body of
/// the [`lex_dag_core`] worklist scan, factored out so the eager DAG builder
/// and the lazy `LazyLatticeTokenSource` share byte-identical node-expansion
/// logic.
///
/// **Inputs**:
/// - `input` / `start`: the byte position to expand (the raw, pre-WS-skip
///   worklist `start`).
/// - the lexer closures (`char_class`, `dfa_next`, `is_accepting`,
///   `accept_alternatives`, `token_to_kind`) — identical to those passed to
///   [`lex_dag_core`].
/// - `start_is_primary`: whether `start` was reached via a primary
///   (maximal-munch) accept of some already-expanded node (or is byte 0).
///   This is the M6c.7.1 soft-fail discriminator: a DFA dead-end at a
///   primary position is a TRUE input error (hard-fail, `lex` parity); a
///   dead-end at a secondary-only position is a structural rule-out
///   (soft-fail: an orphan node with empty edges).
///
/// **Output**: `Ok(ExpandedLexNode)` describing the node (post-WS `byte_start`,
/// surviving longest-per-kind edges, ordered successors with primary flags,
/// `is_eof`). A soft-fail (secondary dead-end) yields an EMPTY-edge node with
/// no successors. A hard-fail (primary dead-end) returns `Err`.
///
/// **Determinism / equivalence**: the edge survival filter (longest-per-kind),
/// edge ordering (longest-first), and successor ordering are IDENTICAL to the
/// inline worklist body, so a caller that drives `expand_lex_node` in the same
/// FIFO worklist discipline (seed `[0]`, skip already-allocated `start`s,
/// enqueue `successors` in order) reconstructs the exact same node-id
/// allocation order — hence byte-identical `LexDag` output (verified by
/// `lex_dag_core`'s own unit tests, which now route through this function).
pub fn expand_lex_node<'a, T: Clone>(
    input: &'a str,
    start: usize,
    char_class: &[u8; 256],
    dfa_next: &impl Fn(u32, u8) -> u32,
    is_accepting: &impl Fn(u32) -> bool,
    accept_alternatives: &impl Fn(u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: &impl Fn(&T) -> crate::automata::TokenKind,
    start_is_primary: bool,
) -> Result<ExpandedLexNode, String> {
    // Non-modal path: ONE DFA governs every byte (mode is the constant 0) and
    // whitespace is ALWAYS skipped (no mode is `raw`). Drive the shared
    // `expand_lex_node_impl` with constant mode-0 / never-raw closures — the
    // edge-survival, successor discovery, and soft-fail logic are then
    // BYTE-IDENTICAL to the pre-L9 inline body (guarded by this module's
    // `lex_dag_*` unit tests, which route the non-modal DAG through here).
    // [L9 decision D-2 — share the body rather than duplicate it.]
    expand_lex_node_impl(
        input,
        start,
        |_pos| 0u8,
        |_mode| false,
        |_mode, b| char_class[b as usize],
        |_mode, s, c| dfa_next(s, c),
        |_mode, s| is_accepting(s),
        |_mode, s, text| accept_alternatives(s, text),
        |t| token_to_kind(t),
        // Task #18: no non-modal grammar can route a token to an alternative
        // channel — `-> stream` forces the MODAL codegen path (`lexer.rs`
        // `has_streams` gate), so every accept here is on `DEFAULT` (id 0) and
        // the trivia branch is statically dead.
        |_mode, _state| 0u8,
        start_is_primary,
    )
}

/// Shared per-node expansion body for BOTH the non-modal [`expand_lex_node`]
/// and the multi-mode [`expand_lex_node_modal`] (L9). Everything that differs
/// between the two paths is a closure parameter:
///
/// - `resolve_mode(byte) -> u8`: the lexer mode active at `byte`. The non-modal
///   wrapper passes a constant `0`; the modal wrapper indexes its precomputed
///   `mode_at` map (a pure function of position under the Delimiter Unambiguity
///   Invariant, so memoization-by-position stays sound).
/// - `is_raw(mode) -> bool`: whether `mode` is a RAW guest mode (whitespace is
///   token content ⇒ the leading-whitespace skip is suppressed). Non-modal
///   passes constant `false` ⇒ the unconditional skip of the original body.
/// - `char_class(mode, byte)`, `dfa_next(mode, state, class)`,
///   `is_accepting(mode, state)`, `accept_alternatives(mode, state, text)`: the
///   per-mode DFA tables. The non-modal wrapper ignores `mode`.
/// - `stream_id(mode, accept_state) -> u8`: the token CHANNEL an accepting state
///   routes to — `0` = `DEFAULT` (the parse stream), non-zero = an alternative
///   named channel declared by `-> CHANNEL` in the grammar's `tokens {}` block
///   (task #18). See the trivia rule below. The non-modal wrapper passes a
///   constant `0`.
///
/// A whole token is lexed in ONE mode (the DFA never changes mode mid-token) and
/// a whitespace run never crosses a push/pop boundary, so the mode is resolved
/// once and the inner DFA walk / edge discovery are structurally identical to
/// the single-DFA body.
///
/// ## ★ Task #18 — the trivia rule for alternative token channels
///
/// A token routed to a non-`DEFAULT` channel (comments, and any other class a
/// grammar declares with `-> CHANNEL`) is **TRIVIA**: it is lexical apparatus
/// that the parser must not see. It is resolved by exactly the rule that already
/// governs every other token — **maximal munch** — and NOT by any new
/// disambiguation:
///
/// 1. Accepts occur at strictly increasing end offsets, so the maximal-munch
///    accept at a position is UNIQUE. If its state routes to a non-`DEFAULT`
///    channel, the span is trivia: `pos` advances past it and the scan restarts
///    — structurally identical to the leading-whitespace skip immediately above,
///    which is the discard this generalizes from a hard-coded byte class to a
///    DECLARED token class.
/// 2. Otherwise, channel-routed accepts at SHORTER lengths are dropped: a
///    channel token can never be a parser token, so it must never become a DAG
///    edge.
///
/// Because trivia only ever REMOVES a span from the scan (never adds an
/// alternative), the resulting lex DAG over a source containing trivia is the
/// DAG of that source with the trivia bytes elided — so the parse forest, the
/// elected term, and the parse COUNT are all unchanged. Retention happens
/// beside the parser (`lex_with_streams` → `LexResult.streams`), never inside
/// it.
#[inline]
#[allow(clippy::too_many_arguments)]
fn expand_lex_node_impl<'a, T: Clone>(
    input: &'a str,
    start: usize,
    resolve_mode: impl Fn(usize) -> u8,
    is_raw: impl Fn(u8) -> bool,
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    accept_alternatives: impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
    stream_id: impl Fn(u8, u32) -> u8,
    start_is_primary: bool,
) -> Result<ExpandedLexNode, String> {
    use crate::automata::semiring::TropicalWeight;

    let bytes = input.as_bytes();

    // Skip leading TRIVIA at this position: interleaved whitespace runs and
    // maximal-munch tokens routed to an alternative channel (task #18). The
    // resulting `pos` becomes the node's byte_start, exactly as the pure
    // whitespace skip did before — this keeps the DAG aligned with
    // `lex_stream_core` (trivia is non-token). Whitespace is skipped only when
    // the mode active at the position is not a RAW guest mode; a whitespace run
    // never crosses a push/pop boundary, so the mode at `start` equals the mode
    // at the post-skip token start. line/col tracking is not needed here — the
    // DAG only carries byte positions.
    let mut pos = start;
    let (mode, mut accepts) = loop {
        if pos < bytes.len() && !is_raw(resolve_mode(pos)) {
            {
                let result = skip_whitespace_simd(bytes, pos, 0, 0);
                pos = result.pos;
            }
            while pos < bytes.len() && bytes[pos] >= 0x80 {
                match decode_char_at(input, pos) {
                    Some((ch, ch_len)) if ch.is_whitespace() => {
                        pos += ch_len;
                    },
                    _ => break,
                }
            }
        }

        if pos >= bytes.len() {
            // EOF sentinel: no edges, no successors. M6c.8.1: the caller
            // captures the EOF index when it allocates this node.
            return Ok(ExpandedLexNode {
                byte_start: pos,
                edges: Vec::new(),
                successors: Vec::new(),
                is_eof: true,
            });
        }

        // The mode governing the token that starts at `pos`.
        let mode = resolve_mode(pos);

        // Walk the DFA from `pos`, recording every accepting state.
        let mut walk_pos = pos;
        let mut state: u32 = 0;
        let mut accepts: Vec<(u32, usize)> = Vec::new();
        if is_accepting(mode, 0) {
            accepts.push((0, walk_pos));
        }
        while walk_pos < bytes.len() {
            let class = char_class(mode, bytes[walk_pos]);
            let next = dfa_next(mode, state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            walk_pos += 1;
            if is_accepting(mode, state) {
                accepts.push((state, walk_pos));
            }
        }

        if accepts.is_empty() {
            // M6c.7.1 (2026-05-14): soft-fail for secondary-alt dead-ends.
            // If this position is reachable ONLY via a non-primary
            // (shorter-than-maximal-munch) alt's downstream, the failure is
            // structural rule-out by evidence: the alt cannot contribute to any
            // valid parse, so the corresponding lex-Fork branch in the walker
            // spawns a cursor that lands at the orphan node (empty edges →
            // peek_kind = Eof), fails to dispatch, dies naturally.
            //
            // If `start` IS on the primary maximal-munch chain (reachable via
            // the longest-end accept of some node), this is a true input error
            // that `lex` would ALSO fail on. Preserve the hard-fail surface.
            if !start_is_primary {
                // Orphan node: empty edges, no successors.
                return Ok(ExpandedLexNode {
                    byte_start: pos,
                    edges: Vec::new(),
                    successors: Vec::new(),
                    is_eof: false,
                });
            }
            let (ch, _ch_len) = decode_char_at(input, pos).unwrap_or(('\u{FFFD}', 1));
            return Err(format!("unexpected character '{}' at byte {}", ch.escape_debug(), pos));
        }

        // For each accept, emit an edge (target resolved later). Order by
        // end_byte DESCENDING (longest-first) so edges[0] is the canonical
        // primary.
        accepts.sort_by(|a, b| b.1.cmp(&a.1));

        // ★ Task #18 trivia rule (step 1): the maximal-munch accept is unique
        // (accepts sit at strictly increasing end offsets). If it routes to an
        // alternative channel the whole span is trivia — advance and re-scan,
        // exactly as the whitespace skip above does. The `end > pos` guard makes
        // a (malformed) zero-width channel token fall through to the normal path
        // instead of spinning forever.
        let (primary_state, primary_end) = accepts[0];
        if stream_id(mode, primary_state) != 0 && primary_end > pos {
            pos = primary_end;
            continue;
        }

        break (mode, accepts);
    };

    // ★ Task #18 trivia rule (step 2): a channel-routed accept SHORTER than the
    // maximal munch is dropped outright. It is not trivia (the span the scan
    // consumes here is the DEFAULT maximal munch, not the channel token), and it
    // can never be a parser token, so it must never become a DAG edge. This is
    // pure removal — it can only shrink the alternative set, never add to it.
    accepts.retain(|(accept_state, _)| stream_id(mode, *accept_state) == 0);

    // M6c.4-bugfix (2026-05-14): apply longest-match-per-kind filtering HERE
    // (during edge collection) so node ids stay dense and aligned with token
    // positions. Without this, the DAG gets ORPHAN intermediate nodes for
    // same-kind prefix accepts (e.g. `merge` accepting Ident at end=1..5).
    let mut edges: Vec<RawLexEdge> = Vec::new();
    let mut successors: Vec<LexSuccessor> = Vec::new();
    mettail_grammar_core::visit_lexical_survivors(
        accepts,
        |accept_state, end_byte| {
            accept_alternatives(mode, accept_state, &input[pos..end_byte])
                .into_iter()
                .map(|(token, weight)| (token_to_kind(&token), weight))
        },
        |kind, weight, end_byte, ordinal| {
            let alt_idx = u16::try_from(ordinal)
                .map_err(|_| "lexer alternative ordinal exceeds u16".to_string())?;
            edges.push(RawLexEdge {
                kind,
                text: input[pos..end_byte].to_string(),
                end_byte,
                weight: TropicalWeight(weight),
                alt_idx,
            });
            Ok(())
        },
        |byte, is_primary| {
            successors.push(LexSuccessor { byte, is_primary });
            Ok(())
        },
    )
    .map_err(|error| match error {
        mettail_grammar_core::LexicalSelectionError::Visitor(message) => message,
        mettail_grammar_core::LexicalSelectionError::OrdinalOverflow => {
            "lexer alternative ordinal exceeds usize".to_string()
        },
    })?;

    Ok(ExpandedLexNode {
        byte_start: pos,
        edges,
        successors,
        is_eof: false,
    })
}

/// Multi-mode (L9) analogue of [`expand_lex_node`]: expands ONE byte position
/// into a lex-DAG node using the DFA of the mode active at that position.
///
/// `mode_at` is the byte→mode map from [`compute_mode_map`] (a pure function of
/// position under the Delimiter Unambiguity Invariant). `char_class`,
/// `dfa_next`, `is_accepting`, `accept_alternatives` are the mode-dispatched
/// lexer shims (their first parameter is the mode id); `is_raw` reports whether
/// a mode suppresses the leading-whitespace skip; `stream_id` reports the token
/// CHANNEL an accepting state routes to (`0` = `DEFAULT`, non-zero = an
/// alternative channel declared `-> CHANNEL`, whose tokens are TRIVIA — task
/// #18). All other semantics — soft-fail on a secondary-only dead-end,
/// longest-per-kind edge survival, successor ordering — are shared verbatim with
/// the non-modal path via [`expand_lex_node_impl`].
#[allow(clippy::too_many_arguments)]
pub fn expand_lex_node_modal<'a, T: Clone>(
    input: &'a str,
    start: usize,
    mode_at: &[u8],
    char_class: &impl Fn(u8, u8) -> u8,
    dfa_next: &impl Fn(u8, u32, u8) -> u32,
    is_accepting: &impl Fn(u8, u32) -> bool,
    accept_alternatives: &impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: &impl Fn(&T) -> crate::automata::TokenKind,
    is_raw: &impl Fn(u8) -> bool,
    stream_id: &impl Fn(u8, u32) -> u8,
    start_is_primary: bool,
) -> Result<ExpandedLexNode, String> {
    expand_lex_node_impl(
        input,
        start,
        |pos| mode_at[pos],
        |mode| is_raw(mode),
        |mode, b| char_class(mode, b),
        |mode, s, c| dfa_next(mode, s, c),
        |mode, s| is_accepting(mode, s),
        |mode, s, text| accept_alternatives(mode, s, text),
        |t| token_to_kind(t),
        |mode, s| stream_id(mode, s),
        start_is_primary,
    )
}

pub fn lex_dag_core<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    char_class: &[u8; 256],
    dfa_next: impl Fn(u32, u8) -> u32,
    is_accepting: impl Fn(u32) -> bool,
    accept_alternatives: impl Fn(u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
) -> Result<crate::lexer_types::LexDag, String> {
    let _ = file_id;
    // The eager worklist discipline is shared with `lex_dag_core_modal` via
    // `lex_dag_build`; the only per-path difference is which expander produces
    // each node (single-DFA `expand_lex_node` here).
    lex_dag_build(|start, start_is_primary| {
        expand_lex_node(
            input,
            start,
            char_class,
            &dfa_next,
            &is_accepting,
            &accept_alternatives,
            &token_to_kind,
            start_is_primary,
        )
    })
}

/// Multi-mode (L9) analogue of [`lex_dag_core`]: builds a [`crate::lexer_types::LexDag`]
/// over `input` where each byte position is expanded with the DFA of its mode
/// (from `mode_at`, a pure function of position under the Delimiter Unambiguity
/// Invariant). The worklist discipline — FIFO order, `byte_to_node` dedup,
/// M6c.7.1 primary-chain propagation, EOF-first-writer, per-kind longest-match
/// fixup — is shared verbatim with the non-modal path via [`lex_dag_build`], so
/// memoization-by-position stays sound (mode is a pure function of position).
#[allow(clippy::too_many_arguments)]
pub fn lex_dag_core_modal<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    mode_at: &[u8],
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    accept_alternatives: impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
    is_raw: impl Fn(u8) -> bool,
    stream_id: impl Fn(u8, u32) -> u8,
) -> Result<crate::lexer_types::LexDag, String> {
    let _ = file_id;
    lex_dag_build(|start, start_is_primary| {
        expand_lex_node_modal(
            input,
            start,
            mode_at,
            &char_class,
            &dfa_next,
            &is_accepting,
            &accept_alternatives,
            &token_to_kind,
            &is_raw,
            &stream_id,
            start_is_primary,
        )
    })
}

/// Shared eager DAG-builder driver for [`lex_dag_core`] and
/// [`lex_dag_core_modal`]. `expand(start, start_is_primary)` yields the node at
/// a byte position (single-DFA or mode-dispatched); everything else — the FIFO
/// worklist, `byte_to_node` dedup, M6c.7.1 primary-chain propagation,
/// EOF-first-writer-wins, and the per-kind longest-match edge fixup — is
/// identical across both paths, so the non-modal DAG output is byte-for-byte
/// unchanged (guarded by this module's `lex_dag_*` unit tests).
fn lex_dag_build(
    expand: impl Fn(usize, bool) -> Result<ExpandedLexNode, String>,
) -> Result<crate::lexer_types::LexDag, String> {
    use crate::automata::semiring::TropicalWeight;
    use crate::lexer_types::{LexDag, LexDagEdge, LexDagNode};
    use std::collections::{BTreeMap, VecDeque};

    let mut byte_to_node: BTreeMap<usize, usize> = BTreeMap::new();
    let mut nodes: Vec<LexDagNode> = Vec::new();
    // (raw edges with `target_byte` instead of `target_node` — fix up after
    // all nodes are allocated)
    let mut raw_edges: Vec<(
        usize,
        Vec<(crate::automata::TokenKind, String, usize, TropicalWeight)>,
    )> = Vec::new();
    let mut worklist: VecDeque<usize> = VecDeque::new();
    worklist.push_back(0);
    // M6c.7.1 (2026-05-14): primary-chain tracking for soft-fail
    // semantics. A position is "primary" if every edge from byte zero to
    // that position is the maximal-munch (longest-end) accept of its parent,
    // or if it is the initial position itself. When the DFA fails to scan from a
    // primary position, that's a TRUE input error and we hard-fail
    // (matching `lex` parity). When it fails at a SECONDARY-only
    // position (only reachable via a non-longest alt's downstream),
    // we soft-fail: allocate an orphan node with empty edges. The
    // secondary alt's lex-Fork branch in the walker spawns a cursor
    // that lands at the orphan, sees `peek_kind = Eof`, fails to
    // dispatch in the parser state machine, and dies naturally —
    // pure rule-out by structural evidence (the alt's downstream
    // doesn't lex, so the alt cannot contribute to any valid parse).
    let mut primary_targets: std::collections::HashSet<usize> = std::collections::HashSet::new();
    primary_targets.insert(0);
    // M6c.8.1 (2026-05-14): canonical EOF sentinel index, captured
    // when we allocate the node at `byte_start == bytes.len()`.
    // `byte_to_node` is keyed on the worklist's PRE-WS-skip `start`,
    // not the post-skip `pos` — so `byte_to_node[bytes.len()]` may
    // miss when the EOF sentinel is reached via a `start` < bytes.len()
    // followed by WS skip to bytes.len(). Capture during allocation
    // instead.
    let mut eof_node_idx: Option<usize> = None;

    // M2L (2026-06-17): the per-node DFA-walk + edge-survival + successor
    // discovery is factored into `expand_lex_node` so the eager builder and
    // the lazy `LazyLatticeTokenSource` share byte-identical node expansion.
    // The worklist discipline (seed `[0]`, skip already-allocated `start`s,
    // FIFO order, global `byte_to_node` enqueue dedup, EOF-first-writer-wins,
    // M6c.7.1 primary-chain propagation) stays HERE in the eager driver.
    while let Some(start) = worklist.pop_front() {
        if byte_to_node.contains_key(&start) {
            continue;
        }
        let start_is_primary = primary_targets.contains(&start);
        let expanded = expand(start, start_is_primary)?;

        let node_idx = nodes.len();
        byte_to_node.insert(start, node_idx);
        nodes.push(LexDagNode {
            byte_start: expanded.byte_start,
            edges: Vec::new(),
        });
        raw_edges.push((node_idx, Vec::new()));

        if expanded.is_eof {
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

        // Store the surviving raw edges (longest-first, longest-per-kind;
        // target_node resolved by the fix-up pass below via `byte_to_node`).
        for edge in expanded.edges.into_iter() {
            raw_edges[node_idx]
                .1
                .push((edge.kind, edge.text, edge.end_byte, edge.weight));
        }

        // Queue successors in `expand_lex_node`'s edge order, applying the
        // GLOBAL `byte_to_node` dedup (a position already allocated by a
        // sibling node is not re-enqueued) and propagating M6c.7.1
        // primary-chain status.
        for succ in expanded.successors.into_iter() {
            if !byte_to_node.contains_key(&succ.byte) {
                worklist.push_back(succ.byte);
                // Global primary-chain membership is transitive: a locally
                // longest edge reached from a secondary branch remains
                // secondary. Promoting it here used to turn harmless dead-end
                // alternatives (notably Ident prefixes of FLT fence openers)
                // into hard lexer errors.
                if start_is_primary && succ.is_primary {
                    primary_targets.insert(succ.byte);
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
        let mut seen: std::collections::HashSet<(crate::automata::TokenKind, String, usize)> =
            std::collections::HashSet::new();
        // M6c.4: per-kind longest-match filter. Iterates edges in the
        // order they were collected (longest end_byte first per the
        // sort at line ~1021); the FIRST entry for each kind is the
        // longest, and subsequent same-kind entries are dropped.
        let mut seen_kinds: std::collections::HashSet<crate::automata::TokenKind> =
            std::collections::HashSet::new();
        for (kind, text, end_byte, weight) in edges {
            let target_node = match byte_to_node.get(&end_byte) {
                Some(&idx) => idx,
                None => {
                    // No node allocated for this end_byte — should be
                    // impossible given the worklist scan, but be defensive.
                    continue;
                },
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
        debug_assert!(false, "EOF sentinel must be allocated by lex_dag_build");
        // Defensive fallback: last node (may be an orphan, but
        // better than panicking in release).
        nodes.len().saturating_sub(1)
    });
    Ok(LexDag { nodes, byte_to_node, eof_node })
}

// ══════════════════════════════════════════════════════════════════════════════
// L9 multi-mode runtime cores (additive — no non-modal consumer). `compute_mode_map`
// segments the input into per-byte modes; the `*_core_modal` scanners mirror their
// non-modal siblings but select each token's DFA by position. See the L9 design.
// ══════════════════════════════════════════════════════════════════════════════

/// L9 mode segmentation: compute the byte→mode map for `input` in ONE
/// left-to-right maximal-munch scan, maintaining the lexer mode stack exactly as
/// the generated linear modal lexer does (push on a `push_target` accept, pop on
/// a `should_pop` accept). Under the Delimiter Unambiguity Invariant the mode is
/// a step function that changes only at push/pop boundaries on the unique primary
/// chain, so `mode_at[b]` is well-defined for EVERY byte `b` and per-position DAG
/// expansion ([`expand_lex_node_modal`]) can select each token's DFA by position
/// alone (memoization-by-position stays sound — mode is a pure fn of position).
///
/// Returns `Err` if a byte cannot be lexed in its active mode, or if the mode
/// stack does not return to `[0]` at end of input (an opener whose closer never
/// arrived — an unterminated guest region).
///
/// The closures are the mode-dispatched lexer shims: `char_class(mode, byte)`,
/// `dfa_next(mode, state, class)`, `is_accepting(mode, state)`,
/// `push_target(mode, accept_state) -> u8` (`u8::MAX` = no push),
/// `should_pop(mode, accept_state) -> bool`, and `is_raw(mode) -> bool` (a RAW
/// guest mode does not skip leading whitespace — it is token content).
#[allow(clippy::too_many_arguments)]
pub fn compute_mode_map(
    input: &str,
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    push_target: impl Fn(u8, u32) -> u8,
    should_pop: impl Fn(u8, u32) -> bool,
    is_raw: impl Fn(u8) -> bool,
) -> Result<Vec<u8>, String> {
    let bytes = input.as_bytes();
    let n = bytes.len();
    // Preallocate the full map; every byte is assigned its enclosing mode.
    let mut mode_at: Vec<u8> = vec![0u8; n];
    let mut mode_stack: Vec<u8> = vec![0u8];
    let mut pos: usize = 0;

    while pos < n {
        let mode = *mode_stack.last().expect("mode stack is never empty");

        // Leading-whitespace skip (non-raw modes only). Whitespace never carries
        // a push/pop token, so each skipped byte keeps the enclosing mode.
        if !is_raw(mode) {
            let ws_start = pos;
            let result = skip_whitespace_simd(bytes, pos, 0, 0);
            pos = result.pos;
            while pos < n && bytes[pos] >= 0x80 {
                match decode_char_at(input, pos) {
                    Some((ch, ch_len)) if ch.is_whitespace() => {
                        pos += ch_len;
                    },
                    _ => break,
                }
            }
            mode_at[ws_start..pos].fill(mode);
            if pos >= n {
                break;
            }
        }

        // Maximal-munch DFA walk in the active mode.
        let start_pos = pos;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize)> = None;
        if is_accepting(mode, 0) {
            last_accept = Some((0, pos));
        }
        let mut walk = pos;
        while walk < n {
            let class = char_class(mode, bytes[walk]);
            let next = dfa_next(mode, state, class);
            if next == u32::MAX {
                break;
            }
            state = next;
            walk += 1;
            if is_accepting(mode, state) {
                last_accept = Some((state, walk));
            }
        }

        match last_accept {
            Some((accept_state, end)) => {
                // Advance over the token, assigning the active mode to its bytes.
                // A zero-length accept (an epsilon-accepting start state) cannot
                // occur for token DFAs, but guard against a non-advancing loop.
                if end > start_pos {
                    mode_at[start_pos..end].fill(mode);
                    pos = end;
                } else {
                    mode_at[start_pos] = mode;
                    pos = start_pos + 1;
                }
                // Apply push/pop AFTER the token — identical order to the
                // generated linear modal lexer (codegen write_modal_lex_functions).
                let target = push_target(mode, accept_state);
                if target != u8::MAX {
                    mode_stack.push(target);
                }
                if should_pop(mode, accept_state) {
                    mode_stack.pop();
                    if mode_stack.is_empty() {
                        mode_stack.push(0u8);
                    }
                }
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start_pos).unwrap_or(('\u{FFFD}', 1));
                return Err(format!(
                    "unexpected character '{}' at byte {}",
                    ch.escape_debug(),
                    start_pos
                ));
            },
        }
    }

    // DUI end-of-input invariant: the mode stack must have returned to [0].
    // A residual named mode means a guest-region opener was never balanced.
    if mode_stack.len() != 1 || mode_stack[0] != 0 {
        return Err(format!(
            "unterminated region: mode stack {:?} at end of input (expected [0]) — \
             a guest-mode opener has no matching closer",
            mode_stack
        ));
    }

    Ok(mode_at)
}

/// Multi-mode (L9) analogue of [`lex_weighted_core`]. Mirrors the maximal-munch
/// weighted scan but selects each token's DFA by `mode_at[pos]` and takes the
/// primary (best-weight, longest) alternative from the mode-dispatched
/// `accept_alternatives` — which is exactly `(accept_token, accept_weight)` for
/// that accept state, so the token stream matches the non-modal path.
#[allow(clippy::too_many_arguments)]
pub fn lex_weighted_core_modal<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    mode_at: &[u8],
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    accept_alternatives: impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    is_raw: impl Fn(u8) -> bool,
    stream_id: impl Fn(u8, u32) -> u8,
) -> Result<(Vec<(T, Range, f64)>, Position), String> {
    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    let mut tokens: Vec<(T, Range, f64)> = Vec::with_capacity(input.len() / 2);

    while pos < bytes.len() {
        let mode = mode_at[pos];
        if !is_raw(mode) {
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
                    },
                    _ => break,
                }
            }
            if pos >= bytes.len() {
                break;
            }
        }

        let start = pos;
        let start_line = line;
        let start_col = col;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize, usize, usize)> = None;
        if is_accepting(mode, 0) {
            last_accept = Some((0, pos, line, col));
        }
        while pos < bytes.len() {
            let class = char_class(mode, bytes[pos]);
            let next = dfa_next(mode, state, class);
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
            if is_accepting(mode, state) {
                last_accept = Some((state, pos, line, col));
            }
        }

        match last_accept {
            Some((accept_state, end, end_line, end_col)) => {
                pos = end;
                line = end_line;
                col = end_col;
                // ★ Task #18: the maximal munch routed to an alternative channel
                // is TRIVIA — consumed, but never delivered to the parse stream.
                if stream_id(mode, accept_state) != 0 && end > start {
                    continue;
                }
                let text = &input[start..end];
                if let Some((token, weight)) = accept_alternatives(mode, accept_state, text)
                    .into_iter()
                    .next()
                {
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
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                return Err(format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1,
                    col + 1,
                    ch.escape_debug(),
                ));
            },
        }
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };
    Ok((tokens, eof_pos))
}

/// Multi-mode (L9) analogue of [`lex_lattice_core`]. Same maximal-munch scan and
/// lazy `Linear`-vs-`Lattice` decision, but selects each token's DFA by
/// `mode_at[pos]` (whitespace skip suppressed in RAW modes).
#[allow(clippy::too_many_arguments)]
pub fn lex_lattice_core_modal<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    mode_at: &[u8],
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    accept_alternatives: impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    is_raw: impl Fn(u8) -> bool,
    stream_id: impl Fn(u8, u32) -> u8,
) -> Result<(crate::lattice::TokenSource<T, Range>, Position), String> {
    use crate::automata::semiring::TropicalWeight;
    use crate::lattice::{TokenLattice, TokenSource};

    let bytes = input.as_bytes();
    let mut pos: usize = 0;
    let mut line: usize = 0;
    let mut col: usize = 0;
    let mut linear_tokens: Vec<(T, Range)> = Vec::with_capacity(input.len() / 2);
    let mut has_ambiguity = false;
    struct TokenAlts<T> {
        range: Range,
        alternatives: Vec<(T, f64)>,
    }
    let mut token_alts: Vec<TokenAlts<T>> = Vec::new();

    while pos < bytes.len() {
        let mode = mode_at[pos];
        if !is_raw(mode) {
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
                    },
                    _ => break,
                }
            }
            if pos >= bytes.len() {
                break;
            }
        }

        let start = pos;
        let start_line = line;
        let start_col = col;
        let mut state: u32 = 0;
        let mut last_accept: Option<(u32, usize, usize, usize)> = None;
        if is_accepting(mode, 0) {
            last_accept = Some((0, pos, line, col));
        }
        while pos < bytes.len() {
            let class = char_class(mode, bytes[pos]);
            let next = dfa_next(mode, state, class);
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
            if is_accepting(mode, state) {
                last_accept = Some((state, pos, line, col));
            }
        }

        match last_accept {
            Some((accept_state, end, end_line, end_col)) => {
                pos = end;
                line = end_line;
                col = end_col;
                // ★ Task #18: the maximal munch routed to an alternative channel
                // is TRIVIA — consumed, but never delivered to the parse stream.
                if stream_id(mode, accept_state) != 0 && end > start {
                    continue;
                }
                let text = &input[start..end];
                let alts = accept_alternatives(mode, accept_state, text);
                if alts.is_empty() {
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
                if !has_ambiguity && alts.len() == 1 {
                    linear_tokens.push((alts[0].0.clone(), range));
                }
                token_alts.push(TokenAlts { range, alternatives: alts });
            },
            None => {
                let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
                return Err(format!(
                    "{}:{}: unexpected character '{}'",
                    line + 1,
                    col + 1,
                    ch.escape_debug(),
                ));
            },
        }
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };

    if !has_ambiguity {
        Ok((TokenSource::Linear(linear_tokens), eof_pos))
    } else {
        let num_nodes = token_alts.len() + 1;
        let mut lattice: TokenLattice<T, Range> = TokenLattice::with_capacity(num_nodes);
        lattice.ensure_nodes(num_nodes);
        for (i, ta) in token_alts.iter().enumerate() {
            for (token, weight) in &ta.alternatives {
                lattice.add_edge(i, i + 1, token.clone(), ta.range, TropicalWeight::new(*weight));
            }
        }
        Ok((TokenSource::Lattice(lattice), eof_pos))
    }
}

/// Multi-mode (L9) analogue of [`lex_stream_core`]. Records EVERY accepting state
/// visited (multi-LENGTH alternatives, longest-first) at each position, using the
/// DFA of `mode_at[pos]`; whitespace skip is suppressed in RAW modes.
#[allow(clippy::too_many_arguments)]
pub fn lex_stream_core_modal<'a, T: Clone>(
    input: &'a str,
    file_id: Option<u32>,
    mode_at: &[u8],
    char_class: impl Fn(u8, u8) -> u8,
    dfa_next: impl Fn(u8, u32, u8) -> u32,
    is_accepting: impl Fn(u8, u32) -> bool,
    accept_alternatives: impl Fn(u8, u32, &'a str) -> Vec<(T, f64)>,
    token_to_kind: impl Fn(&T) -> crate::automata::TokenKind,
    is_raw: impl Fn(u8) -> bool,
    stream_id: impl Fn(u8, u32) -> u8,
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
        let mode = mode_at[pos];
        if !is_raw(mode) {
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
                    },
                    _ => break,
                }
            }
            if pos >= bytes.len() {
                break;
            }
        }

        let start = pos;
        let mut walk_pos = pos;
        let mut walk_line = line;
        let mut walk_col = col;
        let mut state: u32 = 0;
        let mut accepts: Vec<(u32, usize, usize, usize)> = Vec::new();
        if is_accepting(mode, 0) {
            accepts.push((0, walk_pos, walk_line, walk_col));
        }
        while walk_pos < bytes.len() {
            let class = char_class(mode, bytes[walk_pos]);
            let next = dfa_next(mode, state, class);
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
            if is_accepting(mode, state) {
                accepts.push((state, walk_pos, walk_line, walk_col));
            }
        }

        if accepts.is_empty() {
            let (ch, _ch_len) = decode_char_at(input, start).unwrap_or(('\u{FFFD}', 1));
            return Err(format!(
                "{}:{}: unexpected character '{}'",
                line + 1,
                col + 1,
                ch.escape_debug(),
            ));
        }

        // ★ Task #18 trivia rule (step 1): `accepts` is ordered by strictly
        // increasing end offset, so `.last()` IS the unique maximal munch. When
        // it routes to an alternative channel the whole span is TRIVIA —
        // consumed, but contributing no entry to the parse stream.
        {
            let (longest_state, longest_end, longest_line, longest_col) =
                *accepts.last().expect("accepts non-empty above");
            if stream_id(mode, longest_state) != 0 && longest_end > start {
                pos = longest_end;
                line = longest_line;
                col = longest_col;
                continue;
            }
        }

        let mut alternatives: Vec<LexAlternative> = Vec::with_capacity(accepts.len() * 2);
        for &(accept_state, accept_end, _, _) in accepts.iter().rev() {
            // ★ Task #18 trivia rule (step 2): a channel-routed accept shorter
            // than the maximal munch can never be a parser token — drop it.
            if stream_id(mode, accept_state) != 0 {
                continue;
            }
            let alt_text = &input[start..accept_end];
            let alt_tokens = accept_alternatives(mode, accept_state, alt_text);
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
            let (longest_state, longest_end, longest_line, longest_col) =
                *accepts.last().expect("accepts non-empty above");
            let _ = longest_state;
            pos = longest_end;
            line = longest_line;
            col = longest_col;
            continue;
        }

        let (_, longest_end, longest_line, longest_col) =
            *accepts.last().expect("accepts non-empty above");
        pos = longest_end;
        line = longest_line;
        col = longest_col;

        stream
            .entries
            .push(LexEntry { byte_start: start, alternatives });
    }

    let eof_pos = Position { byte_offset: pos, line, column: col };
    Ok((stream, eof_pos))
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
pub fn skip_whitespace_simd(
    bytes: &[u8],
    mut pos: usize,
    mut line: usize,
    mut col: usize,
) -> SkipResult {
    use std::simd::{cmp::SimdPartialEq, Simd};

    const LANE_WIDTH: usize = 16;

    let space = Simd::<u8, LANE_WIDTH>::splat(b' ');
    let tab = Simd::<u8, LANE_WIDTH>::splat(b'\t');
    let newline = Simd::<u8, LANE_WIDTH>::splat(b'\n');
    let cr = Simd::<u8, LANE_WIDTH>::splat(b'\r');

    // ── SIMD phase: process 16-byte chunks ──────────────────────────────
    while pos + LANE_WIDTH <= bytes.len() {
        let chunk = Simd::<u8, LANE_WIDTH>::from_slice(&bytes[pos..pos + LANE_WIDTH]);

        // Compare chunk against each whitespace character and OR the masks
        let is_ws =
            chunk.simd_eq(space) | chunk.simd_eq(tab) | chunk.simd_eq(newline) | chunk.simd_eq(cr);

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
pub fn skip_whitespace_scalar(
    bytes: &[u8],
    mut pos: usize,
    mut line: usize,
    mut col: usize,
) -> (usize, usize, usize) {
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
            },
            other => panic!("expected LexError variant, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_error_context() {
        let input = "let x = 42\nlet y = @bad\nlet z = 0";
        // Error at '@' on line 1, column 8, byte_offset = 11 (line 0) + 8 = 19
        let byte_offset = input.find('@').expect("'@' not found in input");
        let range = Range {
            start: Position { byte_offset, line: 1, column: 8 },
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
    fn range_from_byte_offsets_clamps_to_end() {
        let input = "abc";
        let r = Range::from_byte_offsets(input, 1, 1_000_000);
        assert_eq!(r.start.byte_offset, 1);
        assert_eq!(r.end.byte_offset, input.len());
        assert_eq!(r.start.line, 0);
        assert_eq!(r.start.column, 1);
        assert_eq!(r.end.line, 0);
        assert_eq!(r.end.column, 3);
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
        let token_to_kind =
            |t: &crate::automata::TokenKind| -> crate::automata::TokenKind { t.clone() };
        (char_class, dfa_next, is_accepting, accept_alternatives, token_to_kind)
    }

    #[test]
    fn lex_dag_minus_3_has_ambiguity() {
        // Input "-3": DFA visits state 1 (accepts Minus) at byte 1, then
        // state 2 (accepts Integer) at byte 2. Expected DAG:
        //   node 0 (byte_start=0): edges = [Integer@end=2, Minus@end=1]
        //   one target node at byte_start=1: edges = [Integer@end=2]
        //   one target node at byte_start=2: EOF sentinel, edges = []
        // The target node ids are allocation order, not byte order.
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
        assert!(matches!(node_0.edges[0].kind, crate::automata::TokenKind::Integer));
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
        assert!(matches!(node_1.edges[0].kind, crate::automata::TokenKind::Integer));
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
        assert!(matches!(node_0.edges[0].kind, crate::automata::TokenKind::Integer));
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

    // ──────────────────────────────────────────────────────────────────
    // L9 (2026-07-23): multi-mode runtime-core tests. A hand-coded 3-mode
    // FLT-like toy: default mode recognizes Ident=[a-z]+ and three openers —
    // `lam\`` (push flt_body_backtick), `box{` (push flt_body_brace), and
    // ``` fen``` ``` (push flt_body_fence). Each guest mode recognizes its own
    // closer + a shared GuestChunk kind; the brace mode also nests on `{`.
    // ──────────────────────────────────────────────────────────────────

    fn tk(name: &str) -> crate::automata::TokenKind {
        crate::automata::TokenKind::Custom(name.to_string())
    }

    /// Union-alphabet char class (mode-independent for the toy): the tag letters
    /// get distinct classes; every other lowercase letter shares class 9; the
    /// delimiter bytes get 10..13; all else is 255 (no transition).
    fn toy_cc(_mode: u8, b: u8) -> u8 {
        match b {
            b'a' => 0,
            b'b' => 1,
            b'e' => 2,
            b'f' => 3,
            b'l' => 4,
            b'm' => 5,
            b'n' => 6,
            b'o' => 7,
            b'x' => 8,
            b'`' => 10,
            b'{' => 11,
            b'}' => 12,
            b'$' => 13,
            c if c.is_ascii_lowercase() => 9,
            _ => 255,
        }
    }

    fn toy_dnext(mode: u8, state: u32, c: u8) -> u32 {
        match mode {
            // Default mode: Ident + the three openers.
            0 => match state {
                0 => match c {
                    4 => 1,           // 'l' → lam-prefix
                    1 => 10,          // 'b' → box-prefix
                    3 => 20,          // 'f' → fen-prefix
                    x if x <= 9 => 5, // any other letter → generic Ident
                    _ => u32::MAX,
                },
                1 => match c {
                    0 => 2,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                2 => match c {
                    5 => 3,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                3 => match c {
                    10 => 4, // "lam" + '`' → FltOpenBacktick
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                10 => match c {
                    7 => 11,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                11 => match c {
                    8 => 12,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                12 => match c {
                    11 => 13, // "box" + '{' → FltOpenBrace
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                20 => match c {
                    2 => 21,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                21 => match c {
                    6 => 22,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                22 => match c {
                    10 => 23,
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                23 => match c {
                    10 => 24,
                    _ => u32::MAX,
                },
                24 => match c {
                    10 => 25, // "fen" + "```" → FltOpenFence
                    _ => u32::MAX,
                },
                5 => match c {
                    x if x <= 9 => 5,
                    _ => u32::MAX,
                },
                _ => u32::MAX,
            },
            // flt_body_backtick: '`' closer, GuestChunk = [^`]+.
            1 => match state {
                0 => {
                    if c == 10 {
                        1
                    } else {
                        2
                    }
                },
                2 => {
                    if c == 10 {
                        u32::MAX
                    } else {
                        2
                    }
                },
                _ => u32::MAX,
            },
            // flt_body_brace: '{' nests, '}' closes, GuestChunk = [^{}]+.
            2 => match state {
                0 => match c {
                    11 => 1,
                    12 => 2,
                    _ => 3,
                },
                3 => match c {
                    11 | 12 => u32::MAX,
                    _ => 3,
                },
                _ => u32::MAX,
            },
            // flt_body_fence: "```" closer, GuestChunk = [^`]+.
            3 => match state {
                0 => {
                    if c == 10 {
                        1
                    } else {
                        4
                    }
                },
                1 => {
                    if c == 10 {
                        2
                    } else {
                        u32::MAX
                    }
                },
                2 => {
                    if c == 10 {
                        3
                    } else {
                        u32::MAX
                    }
                },
                4 => {
                    if c == 10 {
                        u32::MAX
                    } else {
                        4
                    }
                },
                _ => u32::MAX,
            },
            _ => u32::MAX,
        }
    }

    fn toy_isacc(mode: u8, state: u32) -> bool {
        match mode {
            0 => matches!(state, 1 | 2 | 3 | 4 | 5 | 10 | 11 | 12 | 13 | 20 | 21 | 22 | 25),
            1 => matches!(state, 1 | 2),
            2 => matches!(state, 1 | 2 | 3),
            3 => matches!(state, 3 | 4),
            _ => false,
        }
    }

    fn toy_alts(mode: u8, state: u32, _text: &str) -> Vec<(crate::automata::TokenKind, f64)> {
        use crate::automata::TokenKind;
        match mode {
            0 => match state {
                4 => vec![(tk("FltOpenBacktick"), 0.0)],
                13 => vec![(tk("FltOpenBrace"), 0.0)],
                25 => vec![(tk("FltOpenFence"), 0.0)],
                1 | 2 | 3 | 5 | 10 | 11 | 12 | 20 | 21 | 22 => vec![(TokenKind::Ident, 0.0)],
                _ => vec![],
            },
            1 => match state {
                1 => vec![(tk("FltCloseBacktick"), 0.0)],
                2 => vec![(tk("GuestChunk"), 0.0)],
                _ => vec![],
            },
            2 => match state {
                1 => vec![(tk("FltBraceNest"), 0.0)],
                2 => vec![(tk("FltCloseBrace"), 0.0)],
                3 => vec![(tk("GuestChunk"), 0.0)],
                _ => vec![],
            },
            3 => match state {
                3 => vec![(tk("FltCloseFence"), 0.0)],
                4 => vec![(tk("GuestChunk"), 0.0)],
                _ => vec![],
            },
            _ => vec![],
        }
    }

    fn toy_push(mode: u8, state: u32) -> u8 {
        match mode {
            0 => match state {
                4 => 1,
                13 => 2,
                25 => 3,
                _ => u8::MAX,
            },
            2 => match state {
                1 => 2, // nested '{' re-pushes the brace mode
                _ => u8::MAX,
            },
            _ => u8::MAX,
        }
    }

    fn toy_pop(mode: u8, state: u32) -> bool {
        match mode {
            1 => state == 1,
            2 => state == 2,
            3 => state == 3,
            _ => false,
        }
    }

    fn toy_israw(_mode: u8) -> bool {
        false
    }

    /// Task #18: every accept on the `DEFAULT` channel — the shape of EVERY grammar that declares
    /// no `-> CHANNEL` annotation, and the fixture the pre-#18 modal tests are re-driven with, so
    /// their expectations are unchanged by construction.
    fn toy_stream_none(_mode: u8, _state: u32) -> u8 {
        0
    }

    /// Task #18: routes the guest-mode `GuestChunk` accept (mode 1, state 2) to channel 1, leaving
    /// every other accept on `DEFAULT`. Exercises the trivia rule directly on the core, independent
    /// of any generated grammar: the chunk's span must be CONSUMED and contribute no edge/token,
    /// while the surrounding opener/closer are untouched.
    fn toy_stream_chunk(mode: u8, state: u32) -> u8 {
        match (mode, state) {
            (1, 2) => 1,
            _ => 0,
        }
    }

    fn toy_to_kind(t: &crate::automata::TokenKind) -> crate::automata::TokenKind {
        t.clone()
    }

    #[test]
    fn compute_mode_map_backtick_balanced() {
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced backtick region");
        assert_eq!(map, vec![0, 0, 0, 0, 1, 1, 1]);
    }

    #[test]
    fn compute_mode_map_brace_nested() {
        // "box{a{b}c}" — the mode stack IS the brace balancer; the whole
        // region is mode 2 (flt_body_brace) after the 4-byte opener.
        let map = compute_mode_map(
            "box{a{b}c}",
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_push,
            toy_pop,
            toy_israw,
        )
        .expect("balanced nested braces");
        assert_eq!(map, vec![0, 0, 0, 0, 2, 2, 2, 2, 2, 2]);
    }

    #[test]
    fn compute_mode_map_fence_balanced() {
        let map = compute_mode_map(
            "fen```hi```",
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_push,
            toy_pop,
            toy_israw,
        )
        .expect("balanced fence region");
        assert_eq!(map, vec![0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3]);
    }

    #[test]
    fn compute_mode_map_unbalanced_errors() {
        // Opener with no closer → the mode stack is [0, 1] at EOF.
        let err =
            compute_mode_map("lam`hi", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect_err("unterminated backtick region must error");
        assert!(err.contains("unterminated"), "diagnostic should mention unterminated: {err}");
    }

    #[test]
    fn compute_mode_map_empty_and_ws_only() {
        let empty =
            compute_mode_map("", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("empty input");
        assert!(empty.is_empty());
        // Whitespace-only stays in the default mode (non-raw ⇒ skipped).
        let ws =
            compute_mode_map("   ", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("whitespace-only input");
        assert_eq!(ws, vec![0, 0, 0]);
    }

    #[test]
    fn expand_modal_primary_opener_wins_secondary_ident() {
        // At byte 0 of "lam`x`", maximal munch selects FltOpenBacktick@4; the
        // shorter Ident@3 survives as the SECONDARY edge (intra-mode ambiguity
        // preserved — two surviving edges of different kinds).
        let map =
            compute_mode_map("lam`x`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        assert_eq!(map, vec![0, 0, 0, 0, 1, 1]);
        let node = expand_lex_node_modal(
            "lam`x`",
            0,
            &map,
            &toy_cc,
            &toy_dnext,
            &toy_isacc,
            &toy_alts,
            &toy_to_kind,
            &toy_israw,
            &toy_stream_none,
            true,
        )
        .expect("expand ok");
        assert_eq!(node.edges.len(), 2, "opener + ident co-accepts survive");
        assert_eq!(node.edges[0].kind, tk("FltOpenBacktick"));
        assert_eq!(node.edges[0].end_byte, 4);
        assert_eq!(node.edges[1].kind, crate::automata::TokenKind::Ident);
        assert_eq!(node.edges[1].end_byte, 3);
        assert_eq!(node.successors.len(), 2);
        assert_eq!(node.successors[0].byte, 4);
        assert!(node.successors[0].is_primary);
        assert_eq!(node.successors[1].byte, 3);
        assert!(!node.successors[1].is_primary);
    }

    #[test]
    fn expand_modal_secondary_deadend_soft_fails() {
        // Following the secondary Ident@3 edge lands the cursor at byte 3 (the
        // '`'), still in the DEFAULT mode where a bare '`' has no token. As a
        // NON-primary position this is a structural rule-out (soft-fail: an
        // orphan node), NOT an input error.
        let map =
            compute_mode_map("lam`x`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let orphan = expand_lex_node_modal(
            "lam`x`",
            3,
            &map,
            &toy_cc,
            &toy_dnext,
            &toy_isacc,
            &toy_alts,
            &toy_to_kind,
            &toy_israw,
            &toy_stream_none,
            false,
        )
        .expect("secondary dead-end is a soft-fail (Ok orphan)");
        assert!(orphan.edges.is_empty());
        assert!(orphan.successors.is_empty());
        assert!(!orphan.is_eof);
        // The SAME dead-end on the primary chain is a hard input error.
        let hard = expand_lex_node_modal(
            "lam`x`",
            3,
            &map,
            &toy_cc,
            &toy_dnext,
            &toy_isacc,
            &toy_alts,
            &toy_to_kind,
            &toy_israw,
            &toy_stream_none,
            true,
        );
        assert!(hard.is_err(), "primary-chain dead-end must hard-fail");
    }

    #[test]
    fn locally_primary_edge_does_not_promote_a_secondary_chain() {
        use std::cell::RefCell;

        let observed = RefCell::new(Vec::new());
        let _ = lex_dag_build(|start, start_is_primary| {
            observed.borrow_mut().push((start, start_is_primary));
            let successors = match start {
                0 => vec![
                    LexSuccessor { byte: 2, is_primary: true },
                    LexSuccessor { byte: 1, is_primary: false },
                ],
                // This edge is longest only relative to a secondary parent.
                1 => vec![LexSuccessor { byte: 3, is_primary: true }],
                _ => Vec::new(),
            };
            Ok(ExpandedLexNode {
                byte_start: start,
                edges: Vec::new(),
                successors,
                is_eof: start == 2 || start == 3,
            })
        })
        .expect("synthetic lattice builds");

        assert!(observed.borrow().contains(&(2, true)));
        assert!(
            observed.borrow().contains(&(3, false)),
            "a locally longest edge cannot make its secondary prefix globally primary",
        );
    }

    #[test]
    fn lex_dag_core_modal_primary_chain() {
        // The DAG's primary (maximal-munch) chain over "lam`hi`" is
        // FltOpenBacktick · GuestChunk · FltCloseBacktick.
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let dag = lex_dag_core_modal(
            "lam`hi`",
            None,
            &map,
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_alts,
            toy_to_kind,
            toy_israw,
            toy_stream_none,
        )
        .expect("modal dag builds");
        assert!(dag.has_ambiguity(), "opener vs ident is genuine intra-mode ambiguity");
        let path = dag.linear_path();
        let kinds: Vec<_> = path.iter().map(|(k, _)| k.clone()).collect();
        assert_eq!(kinds, vec![tk("FltOpenBacktick"), tk("GuestChunk"), tk("FltCloseBacktick")]);
    }

    #[test]
    fn lex_weighted_core_modal_token_stream() {
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let (tokens, _eof) = lex_weighted_core_modal(
            "lam`hi`",
            None,
            &map,
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_alts,
            toy_israw,
            toy_stream_none,
        )
        .expect("modal weighted lex");
        let kinds: Vec<_> = tokens.iter().map(|(k, _, _)| k.clone()).collect();
        assert_eq!(kinds, vec![tk("FltOpenBacktick"), tk("GuestChunk"), tk("FltCloseBacktick")]);
    }

    // ── Task #18: the alternative-token-channel trivia rule, gated on the CORE ──────────────
    //
    // These drive the `*_core_modal` scanners with a `stream_id` that routes ONE accept off
    // `DEFAULT`, so the rule is proven independently of any generated grammar: a channel-routed
    // maximal munch is CONSUMED (its span advances the scan) but contributes no token and no DAG
    // edge, exactly as a whitespace run does — while every neighbouring token is untouched.

    #[test]
    fn channel_routed_accept_is_skipped_as_trivia_by_the_weighted_scanner() {
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let (tokens, _eof) = lex_weighted_core_modal(
            "lam`hi`",
            None,
            &map,
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_alts,
            toy_israw,
            toy_stream_chunk,
        )
        .expect("modal weighted lex with a routed chunk");
        let kinds: Vec<_> = tokens.iter().map(|(k, _, _)| k.clone()).collect();
        assert_eq!(
            kinds,
            vec![tk("FltOpenBacktick"), tk("FltCloseBacktick")],
            "the routed GuestChunk must be consumed as TRIVIA — present in the scan, absent from \
             the DEFAULT stream — while the opener and closer are untouched"
        );
    }

    #[test]
    fn channel_routed_accept_produces_no_dag_edge() {
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let dag = lex_dag_core_modal(
            "lam`hi`",
            None,
            &map,
            toy_cc,
            toy_dnext,
            toy_isacc,
            toy_alts,
            toy_to_kind,
            toy_israw,
            toy_stream_chunk,
        )
        .expect("modal dag builds with a routed chunk");
        for node in &dag.nodes {
            for edge in &node.edges {
                assert_ne!(
                    edge.kind,
                    tk("GuestChunk"),
                    "a channel-routed token must never become a DAG edge — the parser would see it"
                );
            }
        }
        let kinds: Vec<_> = dag.linear_path().iter().map(|(k, _)| k.clone()).collect();
        assert_eq!(kinds, vec![tk("FltOpenBacktick"), tk("FltCloseBacktick")]);
    }

    #[test]
    fn channel_routed_trivia_advances_the_node_start_like_whitespace() {
        // Expanding the node at byte 4 (the `hi` chunk): with the chunk routed, the trivia is
        // consumed and the node BEGINS at byte 6 — precisely the way a leading whitespace run
        // already moves `byte_start` past itself.
        let map =
            compute_mode_map("lam`hi`", toy_cc, toy_dnext, toy_isacc, toy_push, toy_pop, toy_israw)
                .expect("balanced");
        let node = expand_lex_node_modal(
            "lam`hi`",
            4,
            &map,
            &toy_cc,
            &toy_dnext,
            &toy_isacc,
            &toy_alts,
            &toy_to_kind,
            &toy_israw,
            &toy_stream_chunk,
            true,
        )
        .expect("expand ok");
        assert_eq!(
            node.byte_start, 6,
            "the routed chunk's span is consumed before the node starts"
        );
        assert_eq!(node.edges.len(), 1);
        assert_eq!(node.edges[0].kind, tk("FltCloseBacktick"));

        // …and with NOTHING routed, the very same position yields the chunk as an ordinary token,
        // so the difference is attributable to the routing alone.
        let plain = expand_lex_node_modal(
            "lam`hi`",
            4,
            &map,
            &toy_cc,
            &toy_dnext,
            &toy_isacc,
            &toy_alts,
            &toy_to_kind,
            &toy_israw,
            &toy_stream_none,
            true,
        )
        .expect("expand ok");
        assert_eq!(plain.byte_start, 4);
        assert_eq!(plain.edges[0].kind, tk("GuestChunk"));
    }
}
