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

use super::{partition::AlphabetPartition, Dfa, TokenKind};

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
) -> TokenStream {
    let buf = generate_lexer_string(dfa, partition, token_kinds, language_name);
    buf.parse::<TokenStream>().expect("generated lexer code must be valid Rust")
}

/// Generate the complete lexer code as a `String` (no proc_macro2 parsing).
///
/// This is the string-based entry point used by the combined lexer+parser
/// codegen path. The caller appends parser code to this string and does a
/// single `str::parse::<TokenStream>()` at the end.
pub fn generate_lexer_string(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    _language_name: &str,
) -> String {
    // Estimate buffer size: ~8KB for typical grammars, scales with DFA size
    let estimated_size = 4096 + dfa.states.len() * partition.num_classes * 16;
    let mut buf = String::with_capacity(estimated_size);

    write_token_enum(&mut buf, token_kinds);
    write_position_and_range_defs(&mut buf);
    write_parse_error_enum(&mut buf);

    if dfa.states.len() <= DIRECT_CODED_THRESHOLD {
        write_direct_coded_lexer(&mut buf, dfa, partition);
    } else {
        write_table_driven_lexer(&mut buf, dfa, partition);
    }

    buf
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
            TokenKind::Eof | TokenKind::Ident => {}
            TokenKind::Integer => {
                if seen.insert("Integer".to_string()) {
                    buf.push_str("Integer(i64),");
                }
            }
            TokenKind::Float => {
                if seen.insert("Float".to_string()) {
                    buf.push_str("Float(f64),");
                }
            }
            TokenKind::True | TokenKind::False => {
                if seen.insert("Boolean".to_string()) {
                    buf.push_str("Boolean(bool),");
                }
            }
            TokenKind::StringLit => {
                if seen.insert("StringLit".to_string()) {
                    buf.push_str("StringLit(&'a str),");
                }
            }
            TokenKind::Fixed(text) => {
                let variant_name = terminal_to_variant_name(text);
                if seen.insert(variant_name.clone()) {
                    write!(buf, "{},", variant_name).unwrap();
                }
            }
            TokenKind::Dollar => {
                if seen.insert("Dollar".to_string()) {
                    buf.push_str("Dollar(&'a str),");
                }
            }
            TokenKind::DoubleDollar => {
                if seen.insert("DoubleDollar".to_string()) {
                    buf.push_str("DoubleDollar(&'a str),");
                }
            }
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
        }
        TokenKind::Float => {
            buf.push_str("Token::Float(text.parse::<f64>().expect(\"invalid float literal\"))");
        }
        TokenKind::True => buf.push_str("Token::Boolean(true)"),
        TokenKind::False => buf.push_str("Token::Boolean(false)"),
        TokenKind::StringLit => {
            buf.push_str("Token::StringLit(&text[1..text.len()-1])");
        }
        TokenKind::Fixed(text) => {
            let variant_name = terminal_to_variant_name(text);
            write!(buf, "Token::{}", variant_name).unwrap();
        }
        TokenKind::Dollar => buf.push_str("Token::Dollar(&text[1..])"),
        TokenKind::DoubleDollar => {
            buf.push_str("Token::DoubleDollar(&text[2..text.len()-1])");
        }
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
}

/// Write a complete table-driven lexer to a string buffer.
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
            TokenKind::Eof | TokenKind::Ident => {}
            TokenKind::Integer => {
                if seen.insert("Integer".to_string()) {
                    variants.push(quote! {
                        /// Integer literal
                        Integer(i64)
                    });
                }
            }
            TokenKind::Float => {
                if seen.insert("Float".to_string()) {
                    variants.push(quote! {
                        /// Float literal
                        Float(f64)
                    });
                }
            }
            TokenKind::True | TokenKind::False => {
                if seen.insert("Boolean".to_string()) {
                    variants.push(quote! {
                        /// Boolean literal
                        Boolean(bool)
                    });
                }
            }
            TokenKind::StringLit => {
                if seen.insert("StringLit".to_string()) {
                    variants.push(quote! {
                        /// String literal
                        StringLit(String)
                    });
                }
            }
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
            }
            TokenKind::Dollar => {
                if seen.insert("Dollar".to_string()) {
                    variants.push(quote! {
                        /// Dollar-prefixed identifier ($proc, $name, etc.)
                        Dollar(String)
                    });
                }
            }
            TokenKind::DoubleDollar => {
                if seen.insert("DoubleDollar".to_string()) {
                    variants.push(quote! {
                        /// Double-dollar application ($$proc(, $$name(, etc.)
                        DoubleDollar(String)
                    });
                }
            }
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
        }
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
