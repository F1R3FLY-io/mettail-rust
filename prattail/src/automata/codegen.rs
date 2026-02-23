//! DFA → Rust lexer code generation.
//!
//! Converts a minimized DFA with alphabet partitioning into Rust source code.
//! Two strategies are available:
//! - **Direct-coded** (default for ≤30 DFA states): each state becomes a match arm
//! - **Table-driven** (default for >30 states): transition table with row-displacement compression
//!
//! ## Performance
//!
//! Code generation uses string-based construction with a single `TokenStream::parse()`
//! at the end, rather than building up `TokenStream` incrementally with `quote!`. This
//! eliminates O(states × classes) intermediate `TokenStream` allocations that dominated
//! the previous implementation (~46% of codegen time was proc_macro2 overhead).

use std::fmt::Write;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use super::{partition::AlphabetPartition, Dfa, TokenKind, DEAD_STATE};

/// Threshold: use direct-coded for small DFAs, table-driven for larger ones.
const DIRECT_CODED_THRESHOLD: usize = 30;

// ══════════════════════════════════════════════════════════════════════════════
// Primary API — string-based codegen with single TokenStream parse
// ══════════════════════════════════════════════════════════════════════════════

/// Generate the complete lexer code as a TokenStream.
///
/// Includes:
/// - `Token` enum definition
/// - `Span` struct
/// - Equivalence class lookup table
/// - The `lex()` function
///
/// Uses string-based code generation internally to avoid per-element
/// proc_macro2 allocations. The entire output is built as a single String
/// and parsed into a TokenStream once.
pub fn generate_lexer_code(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    language_name: &str,
) -> (TokenStream, CodegenStrategy) {
    let (buf, strategy) = generate_lexer_string(dfa, partition, token_kinds, language_name);
    let ts = buf
        .parse::<TokenStream>()
        .expect("generated lexer code must be valid Rust");
    (ts, strategy)
}

/// Generate the complete lexer code as a `String` (no proc_macro2 parsing).
///
/// This is the string-based entry point used by the combined lexer+parser
/// codegen path. The caller appends parser code to this string and does a
/// single `str::parse::<TokenStream>()` at the end.
///
/// Returns the generated code string and which codegen strategy was selected.
pub fn generate_lexer_string(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    _language_name: &str,
) -> (String, CodegenStrategy) {
    // Estimate buffer size: ~8KB for typical grammars, scales with DFA size
    let estimated_size = 4096 + dfa.states.len() * partition.num_classes * 16;
    let mut buf = String::with_capacity(estimated_size);

    write_token_enum(&mut buf, token_kinds);
    write_position_and_range_defs(&mut buf);
    write_parse_error_enum(&mut buf);

    let strategy = if dfa.states.len() <= DIRECT_CODED_THRESHOLD {
        write_direct_coded_lexer(&mut buf, dfa, partition);
        CodegenStrategy::DirectCoded
    } else {
        write_compressed_lexer(&mut buf, dfa, partition)
    };

    (buf, strategy)
}

// ══════════════════════════════════════════════════════════════════════════════
// String-based writers — zero proc_macro2 allocations
// ══════════════════════════════════════════════════════════════════════════════

/// Write the Token enum to a string buffer.
///
/// Generates `Token<'a>` with borrowed `&'a str` for string-carrying variants
/// (Ident, StringLit, Dollar, DoubleDollar), eliminating allocations during lexing.
fn write_token_enum(buf: &mut String, token_kinds: &[TokenKind]) {
    let mut seen = std::collections::HashSet::<String>::new();

    buf.push_str("#[derive(Debug, Clone, PartialEq)] pub enum Token<'a> {");

    // Always include Eof and Ident
    buf.push_str("Eof,");
    seen.insert("Eof".to_string());

    buf.push_str("Ident(&'a str),");
    seen.insert("Ident".to_string());

    for kind in token_kinds {
        match kind {
            TokenKind::Eof | TokenKind::Ident => {},
            TokenKind::Integer => {
                if seen.insert("Integer".to_string()) {
                    buf.push_str("Integer(i64),");
                }
            },
            TokenKind::Float => {
                if seen.insert("Float".to_string()) {
                    buf.push_str("Float(f64),");
                }
            },
            TokenKind::True | TokenKind::False => {
                if seen.insert("Boolean".to_string()) {
                    buf.push_str("Boolean(bool),");
                }
            },
            TokenKind::StringLit => {
                if seen.insert("StringLit".to_string()) {
                    buf.push_str("StringLit(&'a str),");
                }
            },
            TokenKind::Fixed(text) => {
                let variant_name = terminal_to_variant_name(text);
                if seen.insert(variant_name.clone()) {
                    write!(buf, "{},", variant_name).unwrap();
                }
            },
            TokenKind::Dollar => {
                if seen.insert("Dollar".to_string()) {
                    buf.push_str("Dollar(&'a str),");
                }
            },
            TokenKind::DoubleDollar => {
                if seen.insert("DoubleDollar".to_string()) {
                    buf.push_str("DoubleDollar(&'a str),");
                }
            },
        }
    }

    buf.push('}');
}

/// Write the Position, Range definitions to a string buffer.
fn write_position_and_range_defs(buf: &mut String) {
    buf.push_str(
        "/// A position in source code. All fields are 0-indexed.\n\
         #[derive(Debug, Clone, Copy, PartialEq, Eq)] \
         pub struct Position { \
             pub byte_offset: usize, \
             pub line: usize, \
             pub column: usize, \
         }\n\
         impl Position { \
             pub fn zero() -> Self { Position { byte_offset: 0, line: 0, column: 0 } } \
         }\n\
         impl ::std::fmt::Display for Position { \
             fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result { \
                 write!(f, \"{}:{}\", self.line + 1, self.column + 1) \
             } \
         }\n\
         /// A range in source code with beginning and ending positions.\n\
         #[derive(Debug, Clone, Copy, PartialEq, Eq)] \
         pub struct Range { \
             pub start: Position, \
             pub end: Position, \
             pub file_id: Option<u32>, \
         }\n\
         impl Range { \
             pub fn zero() -> Self { Range { start: Position::zero(), end: Position::zero(), file_id: None } } \
         }\n\
         impl ::std::fmt::Display for Range { \
             fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result { \
                 write!(f, \"{}-{}\", self.start, self.end) \
             } \
         }\n\
         /// Backward-compatible type alias for migration.\n\
         pub type Span = Range;\n",
    );
}

/// Write the ParseError enum definition to a string buffer.
fn write_parse_error_enum(buf: &mut String) {
    buf.push_str(
        "/// Structured parse error with source location.\n\
         #[derive(Debug, Clone)] \
         pub enum ParseError { \
             UnexpectedToken { expected: &'static str, found: String, range: Range }, \
             UnexpectedEof { expected: &'static str, range: Range }, \
             LexError { message: String, position: Position }, \
             TrailingTokens { found: String, range: Range }, \
         }\n\
         impl ::std::fmt::Display for ParseError { \
             fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result { \
                 match self { \
                     ParseError::UnexpectedToken { expected, found, range } => { \
                         write!(f, \"{}:{}: expected {}, found {}\", range.start.line + 1, range.start.column + 1, expected, found) \
                     } \
                     ParseError::UnexpectedEof { expected, range } => { \
                         write!(f, \"{}:{}: unexpected end of input, expected {}\", range.start.line + 1, range.start.column + 1, expected) \
                     } \
                     ParseError::LexError { message, position } => { \
                         write!(f, \"{}:{}: {}\", position.line + 1, position.column + 1, message) \
                     } \
                     ParseError::TrailingTokens { found, range } => { \
                         write!(f, \"{}:{}: unexpected {} after parsing\", range.start.line + 1, range.start.column + 1, found) \
                     } \
                 } \
             } \
         }\n\
         impl ParseError { \
             /// Get the source range where this error occurred.\n\
             pub fn range(&self) -> Range { \
                 match self { \
                     ParseError::UnexpectedToken { range, .. } => *range, \
                     ParseError::UnexpectedEof { range, .. } => *range, \
                     ParseError::LexError { position, .. } => Range { start: *position, end: *position, file_id: None }, \
                     ParseError::TrailingTokens { range, .. } => *range, \
                 } \
             } \
         }\n\
         impl ::std::error::Error for ParseError {}\n\
         impl From<String> for ParseError { \
             fn from(message: String) -> Self { \
                 ParseError::LexError { message, position: Position::zero() } \
             } \
         }\n\
         /// Format a source context snippet with caret pointing to the error.\n\
         pub fn format_error_context(input: &str, range: &Range) -> String { \
             let line_start = input[..range.start.byte_offset].rfind('\\n').map_or(0, |p| p + 1); \
             let line_end = input[range.start.byte_offset..].find('\\n').map_or(input.len(), |p| p + range.start.byte_offset); \
             let source_line = &input[line_start..line_end]; \
             let caret_col = range.start.column; \
             let caret_len = if range.end.byte_offset > range.start.byte_offset && range.end.line == range.start.line { \
                 range.end.byte_offset - range.start.byte_offset \
             } else { 1 }; \
             format!(\"{}\\n{}{}\", source_line, \" \".repeat(caret_col), \"^\".repeat(caret_len)) \
         }\n",
    );
}

/// Write the equivalence class table as a Rust array literal to a string buffer.
fn write_class_table(buf: &mut String, partition: &AlphabetPartition) {
    buf.push_str("static CHAR_CLASS: [u8; 256] = [");
    for (i, &class) in partition.byte_to_class.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", class).unwrap();
    }
    buf.push_str("];");
}

/// Write the accept_token match arms to a string buffer.
fn write_accept_arms(buf: &mut String, dfa: &Dfa) {
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(ref kind) = state.accept {
            write!(buf, "{}u32 => Some(", state_idx).unwrap();
            write_token_constructor(buf, kind);
            buf.push_str("),");
        }
    }
    buf.push_str("_ => None }");
}

/// Write the accept_weight match arms to a string buffer.
///
/// Returns the tropical weight (as raw f64) for each accepting DFA state.
/// Non-accepting states return `f64::INFINITY` (tropical zero / unreachable).
/// Used by `lex_weighted()` to emit `(Token, Range, f64)` triples.
#[cfg(feature = "wfst")]
fn write_accept_weight_arms(buf: &mut String, dfa: &Dfa) {
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if state.accept.is_some() {
            write!(buf, "{}u32 => {:.1}_f64,", state_idx, state.weight.value()).unwrap();
        }
    }
    buf.push_str("_ => f64::INFINITY }");
}

/// Write the DFA transition match arms to a string buffer.
fn write_transition_arms(buf: &mut String, dfa: &Dfa) {
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        let has_transitions = state.transitions.iter().any(|&t| t != super::DEAD_STATE);
        if !has_transitions {
            continue;
        }
        write!(buf, "{}u32 => match class {{", state_idx).unwrap();
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != super::DEAD_STATE {
                write!(buf, "{}u8 => {}u32,", class_id, target).unwrap();
            }
        }
        buf.push_str("_ => u32::MAX },");
    }
    buf.push_str("_ => u32::MAX }");
}

/// Write the flat transition table to a string buffer (for table-driven lexer).
///
/// Superseded by `write_comb_tables()` — preserved for reference and testing.
#[allow(dead_code)]
fn write_transition_table(buf: &mut String, dfa: &Dfa, num_classes: usize) {
    let table_size = dfa.states.len() * num_classes;
    write!(buf, "static TRANSITIONS: [u32; {}] = [", table_size).unwrap();
    let mut first = true;
    for state in &dfa.states {
        for &target in &state.transitions {
            if !first {
                buf.push(',');
            }
            first = false;
            write!(buf, "{}", target).unwrap();
        }
    }
    buf.push_str("];");
}

/// Write a TokenKind constructor expression to a string buffer.
///
/// Zero-copy: string-carrying variants borrow from the input `text` slice
/// rather than allocating new `String`s.
fn write_token_constructor(buf: &mut String, kind: &TokenKind) {
    match kind {
        TokenKind::Eof => buf.push_str("Token::Eof"),
        TokenKind::Ident => buf.push_str("Token::Ident(text)"),
        TokenKind::Integer => {
            buf.push_str("Token::Integer(text.parse::<i64>().expect(\"invalid integer literal\"))");
        },
        TokenKind::Float => {
            buf.push_str("Token::Float(text.parse::<f64>().expect(\"invalid float literal\"))");
        },
        TokenKind::True => buf.push_str("Token::Boolean(true)"),
        TokenKind::False => buf.push_str("Token::Boolean(false)"),
        TokenKind::StringLit => {
            buf.push_str("Token::StringLit(&text[1..text.len()-1])");
        },
        TokenKind::Fixed(text) => {
            let variant_name = terminal_to_variant_name(text);
            write!(buf, "Token::{}", variant_name).unwrap();
        },
        TokenKind::Dollar => buf.push_str("Token::Dollar(&text[1..])"),
        TokenKind::DoubleDollar => {
            buf.push_str("Token::DoubleDollar(&text[2..text.len()-1])");
        },
    }
}

/// Write a complete direct-coded lexer to a string buffer.
fn write_direct_coded_lexer(buf: &mut String, dfa: &Dfa, partition: &AlphabetPartition) {
    write_class_table(buf, partition);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    buf.push_str(
        "fn is_whitespace(b: u8) -> bool { matches!(b, b' ' | b'\\t' | b'\\n' | b'\\r') }",
    );

    // lex() function with line/column tracking — zero-copy: Token<'a> borrows from input
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }\n\
         pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range)>, String> { \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
         while pos < bytes.len() && is_whitespace(bytes[pos]) { \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } else { col += 1; } \
         pos += 1; } \
         if pos >= bytes.len() { break; } \
         let start = pos; \
         let start_line = line; \
         let start_col = col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if let Some(_) = accept_token(0, &input[start..start]) { last_accept = Some((0, pos, line, col)); } \
         while pos < bytes.len() { \
         let class = CHAR_CLASS[bytes[pos] as usize]; \
         let next = dfa_next(state, class); \
         if next == u32::MAX { break; } \
         state = next; \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } \
         else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
         pos += 1; \
         if accept_token(state, &input[start..pos]).is_some() { last_accept = Some((state, pos, line, col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         pos = end; line = end_line; col = end_col; \
         let text = &input[start..end]; \
         if let Some(token) = accept_token(accept_state, text) { \
         tokens.push((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id })); } } \
         None => { return Err(format!(\"{}:{}: unexpected character '{}'\", \
         line + 1, col + 1, bytes[start] as char)); } \
         } } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id })); \
         Ok(tokens) }",
    );

    // dfa_next() function
    buf.push_str("fn dfa_next(state: u32, class: u8) -> u32 {");
    write_transition_arms(buf, dfa);
    buf.push('}');

    // accept_token() function — returns Token<'a> borrowing from text
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // WFST weight emission: accept_weight() + lex_weighted()
    #[cfg(feature = "wfst")]
    {
        buf.push_str(
            "/// Get the tropical weight for an accepting DFA state.\n\
                       /// Lower weight = higher priority. Non-accepting returns infinity.\n\
                       fn accept_weight(state: u32) -> f64 {",
        );
        write_accept_weight_arms(buf, dfa);
        buf.push('}');
        write_lex_weighted_function_direct_coded(buf);
    }
}

/// Write the `lex_weighted()` function for direct-coded lexers (inline DFA transitions).
///
/// Direct-coded lexers don't use `dfa_next()` — they inline the transition logic.
/// This function generates the weighted lex variant for the direct-coded path.
#[cfg(feature = "wfst")]
fn write_lex_weighted_function_direct_coded(buf: &mut String) {
    buf.push_str(
        "/// Lex with weight emission: each token carries its tropical weight \
         /// (lower = higher priority). Requires the `wfst` feature.\n\
         pub fn lex_weighted<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         lex_weighted_with_file_id(input, None) \
         }\n\
         /// Lex with weight emission and explicit file ID.\n\
         pub fn lex_weighted_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range, f64)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
         while pos < bytes.len() && is_whitespace(bytes[pos]) { \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } else { col += 1; } \
         pos += 1; } \
         if pos >= bytes.len() { break; } \
         let start = pos; \
         let start_line = line; \
         let start_col = col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if let Some(_) = accept_token(0, &input[start..start]) { last_accept = Some((0, pos, line, col)); } \
         while pos < bytes.len() { \
         let class = CHAR_CLASS[bytes[pos] as usize]; \
         let next = dfa_next(state, class); \
         if next == u32::MAX { break; } \
         state = next; \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } \
         else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
         pos += 1; \
         if accept_token(state, &input[start..pos]).is_some() { last_accept = Some((state, pos, line, col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         pos = end; line = end_line; col = end_col; \
         let text = &input[start..end]; \
         if let Some(token) = accept_token(accept_state, text) { \
         let weight = accept_weight(accept_state); \
         tokens.push((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id }, weight)); } } \
         None => { return Err(format!(\"{}:{}: unexpected character '{}'\", \
         line + 1, col + 1, bytes[start] as char)); } \
         } } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }, 0.0_f64)); \
         Ok(tokens) }",
    );
}

/// Write a complete table-driven lexer to a string buffer (flat transition table).
///
/// Superseded by `write_comb_driven_lexer()` and `write_bitmap_driven_lexer()`
/// — preserved for reference and testing.
#[allow(dead_code)]
fn write_table_driven_lexer(buf: &mut String, dfa: &Dfa, partition: &AlphabetPartition) {
    let num_classes = partition.num_classes;

    write_class_table(buf, partition);
    write_transition_table(buf, dfa, num_classes);

    write!(
        buf,
        "const NUM_STATES: usize = {}; const NUM_CLASSES: usize = {}; const DEAD: u32 = u32::MAX;",
        dfa.states.len(),
        num_classes
    )
    .unwrap();

    buf.push_str(
        "fn is_whitespace(b: u8) -> bool { matches!(b, b' ' | b'\\t' | b'\\n' | b'\\r') }",
    );

    // lex() function with line/column tracking — zero-copy: Token<'a> borrows from input
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }\n\
         pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range)>, String> { \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
         while pos < bytes.len() && is_whitespace(bytes[pos]) { \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } else { col += 1; } \
         pos += 1; } \
         if pos >= bytes.len() { break; } \
         let start = pos; \
         let start_line = line; \
         let start_col = col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if accept_token(0, &input[start..start]).is_some() { last_accept = Some((0, pos, line, col)); } \
         while pos < bytes.len() { \
         let class = CHAR_CLASS[bytes[pos] as usize] as usize; \
         let next = TRANSITIONS[state as usize * NUM_CLASSES + class]; \
         if next == DEAD { break; } \
         state = next; \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } \
         else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
         pos += 1; \
         if accept_token(state, &input[start..pos]).is_some() { last_accept = Some((state, pos, line, col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         pos = end; line = end_line; col = end_col; \
         let text = &input[start..end]; \
         if let Some(token) = accept_token(accept_state, text) { \
         tokens.push((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id })); } } \
         None => { return Err(format!(\"{}:{}: unexpected character '{}'\", \
         line + 1, col + 1, bytes[start] as char)); } \
         } } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id })); \
         Ok(tokens) }",
    );

    // accept_token() function — returns Token<'a> borrowing from text
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');
}

// ══════════════════════════════════════════════════════════════════════════════
// Compressed table codegen — comb (row displacement) + bitmap strategies
// ══════════════════════════════════════════════════════════════════════════════

/// Which codegen strategy was selected for the lexer's transition table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenStrategy {
    /// Direct-coded (match arms): for ≤30 DFA states.
    DirectCoded,
    /// Row displacement (comb) compression: BASE/NEXT/CHECK/DEFAULT arrays.
    CombCompressed,
    /// Bitmap + popcount indexing: BITMAPS/OFFSETS/TARGETS arrays.
    BitmapCompressed,
}

/// Row-displacement (comb) compressed transition table.
///
/// Classic technique from `flex`/`re2c`: sparse rows are packed into a shared
/// linear array by finding non-colliding offsets. Lookup:
/// ```text
/// idx = BASE[state] + class
/// next = if CHECK[idx] == state { NEXT[idx] } else { DEFAULT[state] }
/// ```
#[derive(Debug, Clone)]
pub struct CombTable {
    /// Displacement offset per state.
    pub base: Vec<u32>,
    /// Default transition per state (typically DEAD_STATE).
    pub default: Vec<u32>,
    /// Packed target states.
    pub next: Vec<u32>,
    /// Owner state for collision detection.
    pub check: Vec<u32>,
}

impl CombTable {
    /// Total size in u32 entries (for size comparison).
    pub fn total_entries(&self) -> usize {
        self.base.len() + self.default.len() + self.next.len() + self.check.len()
    }

    /// Total size in bytes (for size comparison).
    pub fn total_bytes(&self) -> usize {
        self.total_entries() * 4
    }
}

/// Bitmap-compressed transition table for sparse DFA states.
///
/// Each state stores a `u32` bitmap (bit `i` set iff class `i` has a non-DEAD
/// transition) plus a dense array of only live targets. Lookup uses bit-test +
/// popcount indexing: O(1) with hardware POPCNT.
///
/// Requires `num_classes ≤ 32` (fits in `u32` bitmap).
#[derive(Debug, Clone)]
pub struct BitmapTables {
    /// One bitmap per state.
    pub bitmaps: Vec<u32>,
    /// Starting index into `targets` for each state.
    pub offsets: Vec<u16>,
    /// Dense array of only live (non-DEAD) target states.
    pub targets: Vec<u32>,
}

impl BitmapTables {
    /// Total size in bytes (for size comparison).
    pub fn total_bytes(&self) -> usize {
        self.bitmaps.len() * 4 + self.offsets.len() * 2 + self.targets.len() * 4
    }
}

/// Sparsity analysis of a DFA's transition table.
#[derive(Debug, Clone)]
pub struct SparsityInfo {
    /// Number of live (non-DEAD) transitions per state.
    pub live_per_state: Vec<usize>,
    /// Total number of live transitions across all states.
    pub total_live: usize,
    /// Fraction of transitions that are DEAD (0.0 to 1.0).
    pub dead_fraction: f64,
}

/// Analyze the sparsity of a DFA's transition table.
pub fn analyze_sparsity(dfa: &Dfa) -> SparsityInfo {
    let mut live_per_state = Vec::with_capacity(dfa.states.len());
    let mut total_live = 0usize;
    let total_entries = dfa.states.len() * dfa.num_classes;

    for state in &dfa.states {
        let live = state
            .transitions
            .iter()
            .filter(|&&t| t != DEAD_STATE)
            .count();
        live_per_state.push(live);
        total_live += live;
    }

    let dead_fraction = if total_entries > 0 {
        1.0 - (total_live as f64 / total_entries as f64)
    } else {
        0.0
    };

    SparsityInfo {
        live_per_state,
        total_live,
        dead_fraction,
    }
}

/// Compress a DFA transition table using row displacement (comb) packing.
///
/// Algorithm:
/// 1. Extract sparse rows: for each state, collect non-DEAD entries as `(class_id, target)`
/// 2. Sort rows by density (densest first) for better packing
/// 3. Greedy offset search: for each row, find smallest offset where no non-default
///    entries collide with previously placed rows
/// 4. Pad NEXT/CHECK to `max(base) + num_classes` to eliminate bounds checking
pub fn compress_rows_comb(dfa: &Dfa, num_classes: usize) -> CombTable {
    let num_states = dfa.states.len();

    // Extract sparse rows: (state_idx, [(class_id, target)])
    let mut sparse_rows: Vec<(usize, Vec<(usize, u32)>)> = Vec::with_capacity(num_states);
    for (state_idx, state) in dfa.states.iter().enumerate() {
        let entries: Vec<(usize, u32)> = state
            .transitions
            .iter()
            .enumerate()
            .filter(|(_, &t)| t != DEAD_STATE)
            .map(|(class_id, &target)| (class_id, target))
            .collect();
        sparse_rows.push((state_idx, entries));
    }

    // Sort by density (densest first) for better packing
    // sort_unstable_by: no temp allocation, ~10% faster than sort_by for small slices
    sparse_rows.sort_unstable_by_key(|row| std::cmp::Reverse(row.1.len()));

    // Greedy offset search
    let mut base = vec![0u32; num_states];
    let default = vec![u32::MAX; num_states]; // DEAD_STATE
                                              // Start with a reasonable size, will grow as needed
    let initial_capacity = num_states * 2 + num_classes;
    let mut next = vec![u32::MAX; initial_capacity];
    let mut check = vec![u32::MAX; initial_capacity]; // u32::MAX means "unoccupied"
    let mut high_water: usize = 0;

    for (state_idx, entries) in &sparse_rows {
        if entries.is_empty() {
            base[*state_idx] = 0; // doesn't matter, will always hit DEFAULT
            continue;
        }

        // Find smallest offset d where no entries collide
        let mut d: usize = 0;
        'search: loop {
            let needed = d + num_classes;
            // Grow arrays if needed
            if needed > next.len() {
                let new_len = needed + num_classes;
                next.resize(new_len, u32::MAX);
                check.resize(new_len, u32::MAX);
            }

            // Check for collisions
            let mut collides = false;
            for &(class_id, _) in entries {
                let idx = d + class_id;
                if check[idx] != u32::MAX {
                    collides = true;
                    break;
                }
            }
            if !collides {
                break 'search;
            }
            d += 1;
        }

        // Place this row at offset d
        base[*state_idx] = d as u32;
        for &(class_id, target) in entries {
            let idx = d + class_id;
            next[idx] = target;
            check[idx] = *state_idx as u32;
            if idx >= high_water {
                high_water = idx + 1;
            }
        }
    }

    // Pad to max(base) + num_classes to eliminate bounds checks in generated code
    let pad_to = if high_water > 0 {
        let max_base = *base.iter().max().unwrap_or(&0) as usize;
        max_base + num_classes
    } else {
        num_classes
    };
    if pad_to > next.len() {
        next.resize(pad_to, u32::MAX);
        check.resize(pad_to, u32::MAX);
    }
    // Truncate to padded size (remove excess slack)
    next.truncate(pad_to);
    check.truncate(pad_to);

    CombTable { base, default, next, check }
}

/// Build bitmap-compressed transition tables for a DFA.
///
/// Requires `num_classes ≤ 32` (each state's live transitions fit in a `u32` bitmap).
/// Lookup uses bit-test + popcount: O(1) with hardware POPCNT.
pub fn build_bitmap_tables(dfa: &Dfa) -> BitmapTables {
    assert!(
        dfa.num_classes <= 32,
        "bitmap compression requires num_classes <= 32, got {}",
        dfa.num_classes
    );

    let num_states = dfa.states.len();
    let mut bitmaps = Vec::with_capacity(num_states);
    let mut offsets = Vec::with_capacity(num_states);
    let mut targets = Vec::new();

    for state in &dfa.states {
        let mut bitmap: u32 = 0;
        let offset = targets.len() as u16;
        offsets.push(offset);

        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                bitmap |= 1u32 << (class_id as u32);
                targets.push(target);
            }
        }
        bitmaps.push(bitmap);
    }

    BitmapTables { bitmaps, offsets, targets }
}

/// Write the comb-compressed transition tables as static arrays.
fn write_comb_tables(buf: &mut String, comb: &CombTable) {
    // BASE array
    write!(buf, "static BASE: [u32; {}] = [", comb.base.len()).unwrap();
    for (i, &b) in comb.base.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", b).unwrap();
    }
    buf.push_str("];");

    // DEFAULT array
    write!(buf, "static DEFAULT: [u32; {}] = [", comb.default.len()).unwrap();
    for (i, &d) in comb.default.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", d).unwrap();
    }
    buf.push_str("];");

    // NEXT array
    write!(buf, "static NEXT: [u32; {}] = [", comb.next.len()).unwrap();
    for (i, &n) in comb.next.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", n).unwrap();
    }
    buf.push_str("];");

    // CHECK array
    write!(buf, "static CHECK: [u32; {}] = [", comb.check.len()).unwrap();
    for (i, &c) in comb.check.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", c).unwrap();
    }
    buf.push_str("];");
}

/// Write the bitmap-compressed transition tables as static arrays.
fn write_bitmap_tables(buf: &mut String, tables: &BitmapTables) {
    // BITMAPS array
    write!(buf, "static BITMAPS: [u32; {}] = [", tables.bitmaps.len()).unwrap();
    for (i, &b) in tables.bitmaps.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", b).unwrap();
    }
    buf.push_str("];");

    // OFFSETS array
    write!(buf, "static OFFSETS: [u16; {}] = [", tables.offsets.len()).unwrap();
    for (i, &o) in tables.offsets.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", o).unwrap();
    }
    buf.push_str("];");

    // TARGETS array
    write!(buf, "static TARGETS: [u32; {}] = [", tables.targets.len()).unwrap();
    for (i, &t) in tables.targets.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", t).unwrap();
    }
    buf.push_str("];");
}

/// Select and write the best compressed lexer strategy.
///
/// Compares comb vs bitmap table sizes and picks the smaller one.
/// Returns which strategy was selected.
fn write_compressed_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
) -> CodegenStrategy {
    let num_classes = partition.num_classes;
    let comb = compress_rows_comb(dfa, num_classes);

    if num_classes <= 32 {
        let bitmap = build_bitmap_tables(dfa);
        if bitmap.total_bytes() <= comb.total_bytes() {
            write_bitmap_driven_lexer(buf, dfa, partition, &bitmap);
            return CodegenStrategy::BitmapCompressed;
        }
    }

    write_comb_driven_lexer(buf, dfa, partition, &comb);
    CodegenStrategy::CombCompressed
}

/// Write a complete comb-compressed lexer to a string buffer.
fn write_comb_driven_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
    comb: &CombTable,
) {
    write_class_table(buf, partition);
    write_comb_tables(buf, comb);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    buf.push_str(
        "fn is_whitespace(b: u8) -> bool { matches!(b, b' ' | b'\\t' | b'\\n' | b'\\r') }",
    );

    // dfa_next function using comb lookup
    write!(
        buf,
        "#[inline(always)] fn dfa_next(state: u32, class: u8) -> u32 {{ \
         let idx = BASE[state as usize] as usize + class as usize; \
         if CHECK[idx] == state {{ NEXT[idx] }} else {{ DEFAULT[state as usize] }} \
         }}"
    )
    .unwrap();

    // lex() function — same structure as table-driven, using dfa_next()
    write_lex_function_with_dfa_next(buf);

    // accept_token() function
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // WFST weight emission: accept_weight() + lex_weighted()
    #[cfg(feature = "wfst")]
    {
        buf.push_str(
            "/// Get the tropical weight for an accepting DFA state.\n\
                       /// Lower weight = higher priority. Non-accepting returns infinity.\n\
                       fn accept_weight(state: u32) -> f64 {",
        );
        write_accept_weight_arms(buf, dfa);
        buf.push('}');
        write_lex_weighted_function_with_dfa_next(buf);
    }
}

/// Write a complete bitmap-compressed lexer to a string buffer.
fn write_bitmap_driven_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
    tables: &BitmapTables,
) {
    write_class_table(buf, partition);
    write_bitmap_tables(buf, tables);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    buf.push_str(
        "fn is_whitespace(b: u8) -> bool { matches!(b, b' ' | b'\\t' | b'\\n' | b'\\r') }",
    );

    // dfa_next function using bitmap+popcount lookup
    buf.push_str(
        "#[inline(always)] fn dfa_next(state: u32, class: u8) -> u32 { \
         let bitmap = BITMAPS[state as usize]; \
         let bit = 1u32 << (class as u32); \
         if bitmap & bit == 0 { return u32::MAX; } \
         let index = (bitmap & (bit - 1)).count_ones() as usize; \
         TARGETS[OFFSETS[state as usize] as usize + index] \
         }",
    );

    // lex() function — same structure, using dfa_next()
    write_lex_function_with_dfa_next(buf);

    // accept_token() function
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // WFST weight emission: accept_weight() + lex_weighted()
    #[cfg(feature = "wfst")]
    {
        buf.push_str(
            "/// Get the tropical weight for an accepting DFA state.\n\
                       /// Lower weight = higher priority. Non-accepting returns infinity.\n\
                       fn accept_weight(state: u32) -> f64 {",
        );
        write_accept_weight_arms(buf, dfa);
        buf.push('}');
        write_lex_weighted_function_with_dfa_next(buf);
    }
}

/// Write the lex() function body that uses a `dfa_next(state, class)` function.
///
/// Shared between comb-driven and bitmap-driven lexers (both define `dfa_next`
/// with the same signature but different lookup strategies).
fn write_lex_function_with_dfa_next(buf: &mut String) {
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }\n\
         pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range)>, String> { \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
         while pos < bytes.len() && is_whitespace(bytes[pos]) { \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } else { col += 1; } \
         pos += 1; } \
         if pos >= bytes.len() { break; } \
         let start = pos; \
         let start_line = line; \
         let start_col = col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if let Some(_) = accept_token(0, &input[start..start]) { last_accept = Some((0, pos, line, col)); } \
         while pos < bytes.len() { \
         let class = CHAR_CLASS[bytes[pos] as usize]; \
         let next = dfa_next(state, class); \
         if next == u32::MAX { break; } \
         state = next; \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } \
         else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
         pos += 1; \
         if accept_token(state, &input[start..pos]).is_some() { last_accept = Some((state, pos, line, col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         pos = end; line = end_line; col = end_col; \
         let text = &input[start..end]; \
         if let Some(token) = accept_token(accept_state, text) { \
         tokens.push((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id })); } } \
         None => { return Err(format!(\"{}:{}: unexpected character '{}'\", \
         line + 1, col + 1, bytes[start] as char)); } \
         } } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id })); \
         Ok(tokens) }",
    );
}

/// Write the `lex_weighted()` function body that uses `dfa_next(state, class)` and `accept_weight(state)`.
///
/// Returns `Vec<(Token<'a>, Range, f64)>` where the `f64` is the tropical weight
/// (lower = higher priority). Feature-gated: only emitted when `wfst` feature is enabled.
///
/// Shared between comb-driven and bitmap-driven lexers.
#[cfg(feature = "wfst")]
fn write_lex_weighted_function_with_dfa_next(buf: &mut String) {
    buf.push_str(
        "/// Lex with weight emission: each token carries its tropical weight \
         /// (lower = higher priority). Requires the `wfst` feature.\n\
         pub fn lex_weighted<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         lex_weighted_with_file_id(input, None) \
         }\n\
         /// Lex with weight emission and explicit file ID.\n\
         pub fn lex_weighted_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range, f64)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
         while pos < bytes.len() && is_whitespace(bytes[pos]) { \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } else { col += 1; } \
         pos += 1; } \
         if pos >= bytes.len() { break; } \
         let start = pos; \
         let start_line = line; \
         let start_col = col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if let Some(_) = accept_token(0, &input[start..start]) { last_accept = Some((0, pos, line, col)); } \
         while pos < bytes.len() { \
         let class = CHAR_CLASS[bytes[pos] as usize]; \
         let next = dfa_next(state, class); \
         if next == u32::MAX { break; } \
         state = next; \
         if bytes[pos] == b'\\n' { line += 1; col = 0; } \
         else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
         pos += 1; \
         if accept_token(state, &input[start..pos]).is_some() { last_accept = Some((state, pos, line, col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         pos = end; line = end_line; col = end_col; \
         let text = &input[start..end]; \
         if let Some(token) = accept_token(accept_state, text) { \
         let weight = accept_weight(accept_state); \
         tokens.push((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id }, weight)); } } \
         None => { return Err(format!(\"{}:{}: unexpected character '{}'\", \
         line + 1, col + 1, bytes[start] as char)); } \
         } } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }, 0.0_f64)); \
         Ok(tokens) }",
    );
}

// Preserved for reference: the original flat table-driven lexer.
// Superseded by write_comb_driven_lexer() and write_bitmap_driven_lexer().
// #[allow(dead_code)]
// fn write_table_driven_lexer(buf, dfa, partition) { ... }

// ══════════════════════════════════════════════════════════════════════════════
// Legacy quote!-based API — kept for sub-function benchmarking comparison
// ══════════════════════════════════════════════════════════════════════════════

/// Generate the Token enum with variants for all token kinds.
///
/// Uses `quote!` macro (legacy). The primary `generate_lexer_code` uses
/// string-based generation instead.
pub fn generate_token_enum(token_kinds: &[TokenKind]) -> TokenStream {
    let mut variants = Vec::new();
    let mut seen = std::collections::HashSet::new();

    // Always include these
    variants.push(quote! {
        /// End of input
        Eof
    });
    seen.insert("Eof".to_string());

    variants.push(quote! {
        /// Identifier
        Ident(String)
    });
    seen.insert("Ident".to_string());

    for kind in token_kinds {
        match kind {
            TokenKind::Eof | TokenKind::Ident => {},
            TokenKind::Integer => {
                if seen.insert("Integer".to_string()) {
                    variants.push(quote! {
                        /// Integer literal
                        Integer(i64)
                    });
                }
            },
            TokenKind::Float => {
                if seen.insert("Float".to_string()) {
                    variants.push(quote! {
                        /// Float literal
                        Float(f64)
                    });
                }
            },
            TokenKind::True | TokenKind::False => {
                if seen.insert("Boolean".to_string()) {
                    variants.push(quote! {
                        /// Boolean literal
                        Boolean(bool)
                    });
                }
            },
            TokenKind::StringLit => {
                if seen.insert("StringLit".to_string()) {
                    variants.push(quote! {
                        /// String literal
                        StringLit(String)
                    });
                }
            },
            TokenKind::Fixed(text) => {
                let variant_name = terminal_to_variant_name(text);
                if seen.insert(variant_name.clone()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let doc = format!("Terminal: `{}`", text);
                    variants.push(quote! {
                        #[doc = #doc]
                        #variant_ident
                    });
                }
            },
            TokenKind::Dollar => {
                if seen.insert("Dollar".to_string()) {
                    variants.push(quote! {
                        /// Dollar-prefixed identifier ($proc, $name, etc.)
                        Dollar(String)
                    });
                }
            },
            TokenKind::DoubleDollar => {
                if seen.insert("DoubleDollar".to_string()) {
                    variants.push(quote! {
                        /// Double-dollar application ($$proc(, $$name(, etc.)
                        DoubleDollar(String)
                    });
                }
            },
        }
    }

    quote! {
        #[derive(Debug, Clone, PartialEq)]
        pub enum Token {
            #(#variants),*
        }
    }
}

/// Generate the Position + Range type definitions (legacy quote!-based API).
pub fn generate_span_def() -> TokenStream {
    quote! {
        /// A position in source code. All fields are 0-indexed.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct Position {
            pub byte_offset: usize,
            pub line: usize,
            pub column: usize,
        }
        impl Position {
            pub fn zero() -> Self { Position { byte_offset: 0, line: 0, column: 0 } }
        }
        impl ::std::fmt::Display for Position {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
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
                Range { start: Position::zero(), end: Position::zero(), file_id: None }
            }
        }
        impl ::std::fmt::Display for Range {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                write!(f, "{}-{}", self.start, self.end)
            }
        }
        /// Backward-compatible type alias.
        pub type Span = Range;
    }
}

/// Generate a direct-coded lexer (each DFA state as a match arm).
///
/// Uses `quote!` macro (legacy). The primary `generate_lexer_code` uses
/// string-based generation instead.
pub fn generate_direct_coded_lexer(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    _token_kinds: &[TokenKind],
) -> TokenStream {
    // Generate the equivalence class lookup table
    let class_table = generate_class_table(partition);

    // Generate accept table
    let accept_arms = generate_accept_match_arms(dfa);

    // Generate the DFA transition logic
    let transition_arms = generate_transition_match_arms(dfa, partition);

    let num_classes_lit = partition.num_classes;

    quote! {
        /// Equivalence class lookup table (byte → class ID)
        static CHAR_CLASS: [u8; 256] = #class_table;

        /// Number of equivalence classes
        const NUM_CLASSES: usize = #num_classes_lit;

        /// Whitespace equivalence class
        fn is_whitespace(b: u8) -> bool {
            matches!(b, b' ' | b'\t' | b'\n' | b'\r')
        }

        /// Lex a complete input string into a vector of (Token, Span) pairs.
        pub fn lex(input: &str) -> Result<Vec<(Token, Span)>, String> {
            let bytes = input.as_bytes();
            let mut pos: usize = 0;
            let mut tokens: Vec<(Token, Span)> = Vec::with_capacity(input.len() / 2);

            while pos < bytes.len() {
                // Skip whitespace
                while pos < bytes.len() && is_whitespace(bytes[pos]) {
                    pos += 1;
                }
                if pos >= bytes.len() {
                    break;
                }

                let start = pos;
                let mut state: u32 = 0; // DFA start state
                let mut last_accept: Option<(u32, usize)> = None; // (state, end_pos)

                // Check if start state is accepting
                if let Some(_) = accept_token(0, &input[start..start]) {
                    last_accept = Some((0, pos));
                }

                // Maximal munch: run DFA until dead state, record last accept
                while pos < bytes.len() {
                    let class = CHAR_CLASS[bytes[pos] as usize];
                    let next = dfa_next(state, class);
                    if next == u32::MAX {
                        break;
                    }
                    state = next;
                    pos += 1;
                    if accept_token(state, &input[start..pos]).is_some() {
                        last_accept = Some((state, pos));
                    }
                }

                match last_accept {
                    Some((accept_state, end)) => {
                        pos = end;
                        let text = &input[start..end];
                        if let Some(token) = accept_token(accept_state, text) {
                            tokens.push((token, Span { start, end }));
                        }
                    }
                    None => {
                        return Err(format!(
                            "unexpected character '{}' at position {}",
                            bytes[start] as char, start
                        ));
                    }
                }
            }

            tokens.push((Token::Eof, Span { start: pos, end: pos }));
            Ok(tokens)
        }

        /// DFA transition function
        fn dfa_next(state: u32, class: u8) -> u32 {
            #transition_arms
        }

        /// Map an accepting DFA state + matched text to a Token
        fn accept_token(state: u32, text: &str) -> Option<Token> {
            #accept_arms
        }
    }
}

/// Generate a table-driven lexer (for larger DFAs).
///
/// Uses `quote!` macro (legacy). The primary `generate_lexer_code` uses
/// string-based generation instead.
pub fn generate_table_driven_lexer(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    _token_kinds: &[TokenKind],
) -> TokenStream {
    let class_table = generate_class_table(partition);
    let num_states = dfa.states.len();
    let num_classes = partition.num_classes;

    // Build flat transition table: transitions[state * num_classes + class] = next_state
    // DfaState.transitions is already a dense array, so we can directly flatten it.
    let mut transitions: Vec<u32> = Vec::with_capacity(num_states * num_classes);
    for state in &dfa.states {
        transitions.extend_from_slice(&state.transitions);
    }

    let transitions_tokens: Vec<proc_macro2::TokenTree> = transitions
        .iter()
        .map(|&t| proc_macro2::TokenTree::Literal(proc_macro2::Literal::u32_suffixed(t)))
        .collect();

    let accept_arms = generate_accept_match_arms(dfa);
    let num_states_lit = num_states;
    let num_classes_lit = num_classes;
    let table_size = transitions.len();

    quote! {
        /// Equivalence class lookup table (byte → class ID)
        static CHAR_CLASS: [u8; 256] = #class_table;

        /// DFA transition table (flat: state * NUM_CLASSES + class → next_state)
        static TRANSITIONS: [u32; #table_size] = [#(#transitions_tokens),*];

        const NUM_STATES: usize = #num_states_lit;
        const NUM_CLASSES: usize = #num_classes_lit;
        const DEAD: u32 = u32::MAX;

        fn is_whitespace(b: u8) -> bool {
            matches!(b, b' ' | b'\t' | b'\n' | b'\r')
        }

        /// Lex a complete input string into a vector of (Token, Span) pairs.
        pub fn lex(input: &str) -> Result<Vec<(Token, Span)>, String> {
            let bytes = input.as_bytes();
            let mut pos: usize = 0;
            let mut tokens: Vec<(Token, Span)> = Vec::with_capacity(input.len() / 2);

            while pos < bytes.len() {
                // Skip whitespace
                while pos < bytes.len() && is_whitespace(bytes[pos]) {
                    pos += 1;
                }
                if pos >= bytes.len() {
                    break;
                }

                let start = pos;
                let mut state: u32 = 0;
                let mut last_accept: Option<(u32, usize)> = None;

                if accept_token(0, &input[start..start]).is_some() {
                    last_accept = Some((0, pos));
                }

                while pos < bytes.len() {
                    let class = CHAR_CLASS[bytes[pos] as usize] as usize;
                    let next = TRANSITIONS[state as usize * NUM_CLASSES + class];
                    if next == DEAD {
                        break;
                    }
                    state = next;
                    pos += 1;
                    if accept_token(state, &input[start..pos]).is_some() {
                        last_accept = Some((state, pos));
                    }
                }

                match last_accept {
                    Some((accept_state, end)) => {
                        pos = end;
                        let text = &input[start..end];
                        if let Some(token) = accept_token(accept_state, text) {
                            tokens.push((token, Span { start, end }));
                        }
                    }
                    None => {
                        return Err(format!(
                            "unexpected character '{}' at position {}",
                            bytes[start] as char, start
                        ));
                    }
                }
            }

            tokens.push((Token::Eof, Span { start: pos, end: pos }));
            Ok(tokens)
        }

        /// Map an accepting DFA state + matched text to a Token
        fn accept_token(state: u32, text: &str) -> Option<Token> {
            #accept_arms
        }
    }
}

/// Generate the equivalence class lookup table as a Rust array literal.
///
/// Uses `proc_macro2::Literal` directly instead of individual `quote!` calls
/// for each of the 256 entries, reducing TokenStream allocation overhead.
pub fn generate_class_table(partition: &AlphabetPartition) -> TokenStream {
    let entries: Vec<proc_macro2::TokenTree> = partition
        .byte_to_class
        .iter()
        .map(|&c| proc_macro2::TokenTree::Literal(proc_macro2::Literal::u8_suffixed(c)))
        .collect();

    quote! { [#(#entries),*] }
}

/// Generate match arms for the accept_token function.
pub fn generate_accept_match_arms(dfa: &Dfa) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::new();

    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(ref kind) = state.accept {
            let state_lit = state_idx as u32;
            let token_expr = token_kind_to_constructor(kind);
            arms.push(quote! {
                #state_lit => Some(#token_expr)
            });
        }
    }

    arms.push(quote! { _ => None });

    quote! {
        match state {
            #(#arms),*
        }
    }
}

/// Generate match arms for the dfa_next transition function (direct-coded).
pub fn generate_transition_match_arms(dfa: &Dfa, _partition: &AlphabetPartition) -> TokenStream {
    let mut state_arms: Vec<TokenStream> = Vec::new();

    for (state_idx, state) in dfa.states.iter().enumerate() {
        // Check if any transition is non-dead
        let has_transitions = state.transitions.iter().any(|&t| t != super::DEAD_STATE);
        if !has_transitions {
            continue;
        }

        let state_lit = state_idx as u32;
        let mut class_arms: Vec<TokenStream> = Vec::new();

        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != super::DEAD_STATE {
                let class_lit = class_id as u8;
                let target_lit = target;
                class_arms.push(quote! {
                    #class_lit => #target_lit
                });
            }
        }
        class_arms.push(quote! { _ => u32::MAX });

        state_arms.push(quote! {
            #state_lit => match class {
                #(#class_arms),*
            }
        });
    }

    state_arms.push(quote! { _ => u32::MAX });

    quote! {
        match state {
            #(#state_arms),*
        }
    }
}

/// Convert a TokenKind to a Token constructor expression.
pub fn token_kind_to_constructor(kind: &TokenKind) -> TokenStream {
    match kind {
        TokenKind::Eof => quote! { Token::Eof },
        TokenKind::Ident => quote! { Token::Ident(text.to_string()) },
        TokenKind::Integer => quote! {
            Token::Integer(text.parse::<i64>().expect("invalid integer literal"))
        },
        TokenKind::Float => quote! {
            Token::Float(text.parse::<f64>().expect("invalid float literal"))
        },
        TokenKind::True => quote! { Token::Boolean(true) },
        TokenKind::False => quote! { Token::Boolean(false) },
        TokenKind::StringLit => quote! {
            Token::StringLit(text[1..text.len()-1].to_string())
        },
        TokenKind::Fixed(text) => {
            let variant_name = terminal_to_variant_name(text);
            let variant_ident = format_ident!("{}", variant_name);
            quote! { Token::#variant_ident }
        },
        TokenKind::Dollar => quote! {
            Token::Dollar(text[1..].to_string())
        },
        TokenKind::DoubleDollar => quote! {
            Token::DoubleDollar(text[2..text.len()-1].to_string())
        },
    }
}

/// Convert a terminal string to a Rust-safe variant name.
///
/// Examples:
/// - `"+"` → `Plus`
/// - `"*"` → `Star`
/// - `"!"` → `Bang`
/// - `"=="` → `EqEq`
/// - `"{}"` → `EmptyBraces`
/// - `"("` → `LParen`
/// - `"error"` → `KwError`
pub fn terminal_to_variant_name(terminal: &str) -> String {
    match terminal {
        "+" => "Plus".to_string(),
        "-" => "Minus".to_string(),
        "*" => "Star".to_string(),
        "/" => "Slash".to_string(),
        "%" => "Percent".to_string(),
        "!" => "Bang".to_string(),
        "?" => "Question".to_string(),
        "@" => "At".to_string(),
        "." => "Dot".to_string(),
        "," => "Comma".to_string(),
        "|" => "Pipe".to_string(),
        ":" => "Colon".to_string(),
        ";" => "Semi".to_string(),
        "^" => "Caret".to_string(),
        "~" => "Tilde".to_string(),
        "#" => "Hash".to_string(),
        "&" => "Amp".to_string(),
        "=" => "Eq".to_string(),
        "<" => "Lt".to_string(),
        ">" => "Gt".to_string(),
        "(" => "LParen".to_string(),
        ")" => "RParen".to_string(),
        "{" => "LBrace".to_string(),
        "}" => "RBrace".to_string(),
        "[" => "LBracket".to_string(),
        "]" => "RBracket".to_string(),
        "{}" => "EmptyBraces".to_string(),
        "==" => "EqEq".to_string(),
        "!=" => "BangEq".to_string(),
        "<=" => "LtEq".to_string(),
        ">=" => "GtEq".to_string(),
        "&&" => "AmpAmp".to_string(),
        "||" => "PipePipe".to_string(),
        "++" => "PlusPlus".to_string(),
        "--" => "MinusMinus".to_string(),
        "**" => "StarStar".to_string(),
        "->" => "Arrow".to_string(),
        "=>" => "FatArrow".to_string(),
        "<-" => "LArrow".to_string(),
        "::" => "ColonColon".to_string(),
        ".." => "DotDot".to_string(),
        "<<" => "LtLt".to_string(),
        ">>" => "GtGt".to_string(),
        ">>>" => "GtGtGt".to_string(),
        _ => {
            // $-prefixed terminals: "$proc" → "DollarProc", "$$name(" → "DdollarNameLp"
            if terminal.starts_with("$$") && terminal.ends_with('(') {
                let inner = &terminal[2..terminal.len() - 1];
                if !inner.is_empty() && inner.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    let mut result = String::from("Ddollar");
                    let mut capitalize_next = true;
                    for c in inner.chars() {
                        if capitalize_next {
                            result.extend(c.to_uppercase());
                            capitalize_next = false;
                        } else {
                            result.push(c);
                        }
                    }
                    result.push_str("Lp");
                    return result;
                }
            } else if let Some(inner) = terminal.strip_prefix('$') {
                if !inner.is_empty() && inner.chars().all(|c| c.is_alphanumeric() || c == '_') {
                    let mut result = String::from("Dollar");
                    let mut capitalize_next = true;
                    for c in inner.chars() {
                        if capitalize_next {
                            result.extend(c.to_uppercase());
                            capitalize_next = false;
                        } else {
                            result.push(c);
                        }
                    }
                    return result;
                }
            }
            // For keywords and other multi-character terminals,
            // capitalize the first letter and prefix with Kw
            if terminal.chars().all(|c| c.is_alphanumeric() || c == '_') {
                let mut result = String::from("Kw");
                let mut capitalize_next = true;
                for c in terminal.chars() {
                    if capitalize_next {
                        result.extend(c.to_uppercase());
                        capitalize_next = false;
                    } else {
                        result.push(c);
                    }
                }
                result
            } else {
                // Fallback: encode each character
                let mut result = String::from("Tok");
                for c in terminal.chars() {
                    result.push_str(&format!("_{:02x}", c as u32));
                }
                result
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::{
        minimize::minimize_dfa,
        nfa::{build_nfa, BuiltinNeeds},
        partition::compute_equivalence_classes,
        subset::subset_construction,
        DfaState, TerminalPattern,
    };

    #[test]
    fn test_terminal_to_variant_name() {
        assert_eq!(terminal_to_variant_name("+"), "Plus");
        assert_eq!(terminal_to_variant_name("*"), "Star");
        assert_eq!(terminal_to_variant_name("=="), "EqEq");
        assert_eq!(terminal_to_variant_name("{}"), "EmptyBraces");
        assert_eq!(terminal_to_variant_name("("), "LParen");
        assert_eq!(terminal_to_variant_name("error"), "KwError");
        assert_eq!(terminal_to_variant_name("true"), "KwTrue");
    }

    #[test]
    fn test_terminal_to_variant_name_dollar() {
        // Single-dollar: $cat → DollarCat
        assert_eq!(terminal_to_variant_name("$proc"), "DollarProc");
        assert_eq!(terminal_to_variant_name("$name"), "DollarName");
        assert_eq!(terminal_to_variant_name("$int"), "DollarInt");
        assert_eq!(terminal_to_variant_name("$term"), "DollarTerm");

        // Double-dollar with opening paren: $$cat( → DdollarCatLp
        assert_eq!(terminal_to_variant_name("$$proc("), "DdollarProcLp");
        assert_eq!(terminal_to_variant_name("$$name("), "DdollarNameLp");
        assert_eq!(terminal_to_variant_name("$$int("), "DdollarIntLp");
        assert_eq!(terminal_to_variant_name("$$term("), "DdollarTermLp");
    }

    /// Helper: build a minimized DFA from terminal specs for compression testing.
    fn build_test_dfa(
        terminal_specs: &[(&str, TokenKind)],
        needs: BuiltinNeeds,
    ) -> (Dfa, AlphabetPartition) {
        let terminals: Vec<TerminalPattern> = terminal_specs
            .iter()
            .map(|(text, kind)| TerminalPattern {
                text: text.to_string(),
                kind: kind.clone(),
                is_keyword: text.chars().all(|c| c.is_alphanumeric()),
            })
            .collect();
        let nfa = build_nfa(&terminals, &needs);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        (minimize_dfa(&dfa), partition)
    }

    // ══════════════════════════════════════════════════════════════════════
    // Comb (row displacement) compression tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_comb_empty_dfa() {
        // Single state, no transitions
        let dfa = Dfa::new(4);
        let comb = compress_rows_comb(&dfa, 4);
        // All defaults should be DEAD
        assert_eq!(comb.default.len(), 1);
        assert_eq!(comb.default[0], u32::MAX);
    }

    #[test]
    fn test_comb_dense_dfa() {
        // Fully dense state: verify comb table ≤ flat table size
        let num_classes = 12;
        let mut dfa = Dfa::new(num_classes);
        // Make state 0 have transitions to states 1-12
        for class_id in 0..num_classes {
            let target = dfa.add_state(DfaState::with_classes(num_classes));
            dfa.set_transition(0, class_id as u8, target);
        }

        let comb = compress_rows_comb(&dfa, num_classes);
        let flat_entries = dfa.states.len() * num_classes;
        // Comb should not be significantly larger than flat for dense DFA
        // (overhead is base + default arrays)
        assert!(
            comb.next.len() + comb.check.len() <= flat_entries * 3,
            "comb NEXT+CHECK ({}) should not vastly exceed flat ({})",
            comb.next.len() + comb.check.len(),
            flat_entries
        );
    }

    #[test]
    fn test_comb_sparse_dfa() {
        // Sparse DFA: most transitions are DEAD. Verify significant compression.
        let num_classes = 16;
        let num_states = 20;
        let mut dfa = Dfa::new(num_classes);
        // Add states with only 1-2 live transitions each
        for s in 1..num_states {
            let state = dfa.add_state(DfaState::with_classes(num_classes));
            dfa.set_transition(state, 0, 0); // one transition to state 0
            if s % 3 == 0 {
                dfa.set_transition(state, 1, 0); // occasional second transition
            }
        }

        let comb = compress_rows_comb(&dfa, num_classes);
        let flat_entries = dfa.states.len() * num_classes;
        // With ~90% DEAD transitions, comb should compress significantly
        assert!(
            comb.next.len() < flat_entries,
            "comb NEXT ({}) should be smaller than flat ({}) for sparse DFA",
            comb.next.len(),
            flat_entries
        );
    }

    #[test]
    fn test_comb_lookup_matches_flat() {
        // For every (state, class), comb lookup must equal flat lookup.
        let (dfa, partition) = build_test_dfa(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("++", TokenKind::Fixed("++".to_string())),
                ("-", TokenKind::Fixed("-".to_string())),
                ("->", TokenKind::Fixed("->".to_string())),
                ("=", TokenKind::Fixed("=".to_string())),
                ("==", TokenKind::Fixed("==".to_string())),
                ("!=", TokenKind::Fixed("!=".to_string())),
                ("(", TokenKind::Fixed("(".to_string())),
                (")", TokenKind::Fixed(")".to_string())),
                ("error", TokenKind::Fixed("error".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        let num_classes = partition.num_classes;
        let comb = compress_rows_comb(&dfa, num_classes);

        for (state_idx, state) in dfa.states.iter().enumerate() {
            for class_id in 0..num_classes {
                let flat_result = state.transitions[class_id];
                // Comb lookup
                let idx = comb.base[state_idx] as usize + class_id;
                let comb_result = if comb.check[idx] == state_idx as u32 {
                    comb.next[idx]
                } else {
                    comb.default[state_idx]
                };
                assert_eq!(
                    flat_result, comb_result,
                    "mismatch at state={}, class={}: flat={}, comb={}",
                    state_idx, class_id, flat_result, comb_result
                );
            }
        }
    }

    #[test]
    fn test_comb_collision_detection() {
        // Two states sharing transitions on the same class get different offsets
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        let s2 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(s1, 0, 0); // both have transition on class 0
        dfa.set_transition(s2, 0, 0);

        let comb = compress_rows_comb(&dfa, num_classes);
        // They can't share the same base offset (both write to base+0)
        assert_ne!(
            comb.base[s1 as usize], comb.base[s2 as usize],
            "colliding states should get different base offsets"
        );
    }

    #[test]
    fn test_comb_compression_ratio_report() {
        // Print flat vs comb sizes for visibility
        let specs = vec![
            ("+", TokenKind::Fixed("+".to_string())),
            ("++", TokenKind::Fixed("++".to_string())),
            ("-", TokenKind::Fixed("-".to_string())),
            ("->", TokenKind::Fixed("->".to_string())),
            ("=", TokenKind::Fixed("=".to_string())),
            ("==", TokenKind::Fixed("==".to_string())),
            ("!=", TokenKind::Fixed("!=".to_string())),
            ("(", TokenKind::Fixed("(".to_string())),
            (")", TokenKind::Fixed(")".to_string())),
            ("{", TokenKind::Fixed("{".to_string())),
            ("}", TokenKind::Fixed("}".to_string())),
            ("[", TokenKind::Fixed("[".to_string())),
            ("]", TokenKind::Fixed("]".to_string())),
            (",", TokenKind::Fixed(",".to_string())),
            ("error", TokenKind::Fixed("error".to_string())),
        ];
        let (dfa, partition) = build_test_dfa(
            &specs,
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        let num_classes = partition.num_classes;
        let flat_bytes = dfa.states.len() * num_classes * 4;
        let comb = compress_rows_comb(&dfa, num_classes);
        let comb_bytes = comb.total_bytes();
        let sparsity = analyze_sparsity(&dfa);

        eprintln!("Comb compression ratio report:");
        eprintln!(
            "  DFA: {} states, {} classes, {:.1}% dead",
            dfa.states.len(),
            num_classes,
            sparsity.dead_fraction * 100.0
        );
        eprintln!("  Flat:  {} bytes ({} entries)", flat_bytes, dfa.states.len() * num_classes);
        eprintln!(
            "  Comb:  {} bytes (NEXT: {}, CHECK: {}, BASE: {}, DEFAULT: {})",
            comb_bytes,
            comb.next.len(),
            comb.check.len(),
            comb.base.len(),
            comb.default.len()
        );
        if flat_bytes > 0 {
            eprintln!("  Ratio: {:.1}%", comb_bytes as f64 / flat_bytes as f64 * 100.0);
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // Bitmap compression tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_bitmap_tables_simple() {
        // 2-state, 4-class DFA with known bitmaps
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(0, 0, s1); // state 0, class 0 → s1
        dfa.set_transition(0, 2, s1); // state 0, class 2 → s1

        let tables = build_bitmap_tables(&dfa);

        // State 0 has classes 0 and 2 set → bitmap = 0b0101 = 5
        assert_eq!(tables.bitmaps[0], 5);
        assert_eq!(tables.targets[tables.offsets[0] as usize], s1); // class 0
        assert_eq!(tables.targets[tables.offsets[0] as usize + 1], s1); // class 2

        // State 1 has no transitions → bitmap = 0
        assert_eq!(tables.bitmaps[s1 as usize], 0);
    }

    #[test]
    fn test_bitmap_lookup_equivalence() {
        // For every (state, class), bitmap lookup must equal flat lookup.
        let (dfa, partition) = build_test_dfa(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("-", TokenKind::Fixed("-".to_string())),
                ("*", TokenKind::Fixed("*".to_string())),
                ("==", TokenKind::Fixed("==".to_string())),
                ("!=", TokenKind::Fixed("!=".to_string())),
                ("(", TokenKind::Fixed("(".to_string())),
                (")", TokenKind::Fixed(")".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        assert!(partition.num_classes <= 32, "bitmap test requires ≤32 classes");

        let tables = build_bitmap_tables(&dfa);

        for (state_idx, state) in dfa.states.iter().enumerate() {
            for class_id in 0..partition.num_classes {
                let flat_result = state.transitions[class_id];
                // Bitmap lookup
                let bitmap = tables.bitmaps[state_idx];
                let bit = 1u32 << (class_id as u32);
                let bitmap_result = if bitmap & bit == 0 {
                    DEAD_STATE
                } else {
                    let index = (bitmap & (bit - 1)).count_ones() as usize;
                    tables.targets[tables.offsets[state_idx] as usize + index]
                };
                assert_eq!(
                    flat_result, bitmap_result,
                    "mismatch at state={}, class={}: flat={}, bitmap={}",
                    state_idx, class_id, flat_result, bitmap_result
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "bitmap compression requires num_classes <= 32")]
    fn test_bitmap_num_classes_guard() {
        // Must panic for num_classes > 32
        let mut dfa = Dfa::new(33);
        dfa.states[0].transitions = vec![DEAD_STATE; 33];
        build_bitmap_tables(&dfa);
    }

    #[test]
    fn test_bitmap_codegen_valid_tokenstream() {
        // Generated code must parse as valid Rust TokenStream
        let (dfa, partition) = build_test_dfa(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("-", TokenKind::Fixed("-".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: true,
                ..Default::default()
            },
        );

        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Fixed("+".to_string()),
            TokenKind::Fixed("-".to_string()),
        ];

        let (code, _strategy) = generate_lexer_string(&dfa, &partition, &token_kinds, "test");
        // If this doesn't panic, the generated code is valid Rust
        let _ts: TokenStream = code
            .parse()
            .expect("generated compressed lexer should be valid Rust");
    }
}
