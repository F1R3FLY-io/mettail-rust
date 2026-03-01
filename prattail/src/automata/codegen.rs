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

use super::{partition::AlphabetPartition, semiring::TropicalWeight, Dfa, StateId, TokenKind, DEAD_STATE};

/// Threshold: use direct-coded for small DFAs, table-driven for larger ones.
const DIRECT_CODED_THRESHOLD: usize = 30;

// ══════════════════════════════════════════════════════════════════════════════
// Token variant map — compact integer IDs for token kinds
// ══════════════════════════════════════════════════════════════════════════════

/// Bidirectional mapping between token variant names and compact integer IDs.
///
/// Used by the composed dispatch tables and `TokenFilter` bitset to reference
/// token kinds by a single `u8` instead of matching on enum variant names.
/// IDs are assigned in declaration order during `write_token_enum()`, so they
/// are deterministic across compilations.
#[derive(Debug, Clone)]
pub struct TokenVariantMap {
    /// Token variant name → compact ID (e.g., "Ident" → 1).
    pub name_to_id: std::collections::BTreeMap<String, u8>,
    /// Compact ID → token variant name (e.g., 1 → "Ident").
    pub id_to_name: Vec<String>,
    /// Total number of distinct token variants.
    pub count: u8,
}

impl TokenVariantMap {
    /// Build a `TokenVariantMap` from the token kinds used in a grammar.
    ///
    /// Assigns IDs in a deterministic order: Eof (0), Ident (1), then
    /// remaining kinds in the order they appear in `token_kinds`, deduplicated.
    pub fn from_token_kinds(token_kinds: &[TokenKind]) -> Self {
        let mut name_to_id = std::collections::BTreeMap::new();
        let mut id_to_name = Vec::new();

        let mut insert = |name: String| {
            if !name_to_id.contains_key(&name) {
                let id = id_to_name.len() as u8;
                name_to_id.insert(name.clone(), id);
                id_to_name.push(name);
            }
        };

        // Always include Eof and Ident first (stable IDs)
        insert("Eof".to_string());
        insert("Ident".to_string());

        for kind in token_kinds {
            let name = match kind {
                TokenKind::Eof => "Eof".to_string(),
                TokenKind::Ident => "Ident".to_string(),
                TokenKind::Integer => "Integer".to_string(),
                TokenKind::Float => "Float".to_string(),
                TokenKind::True | TokenKind::False => "Boolean".to_string(),
                TokenKind::StringLit => "StringLit".to_string(),
                TokenKind::Fixed(text) => terminal_to_variant_name(text),
                TokenKind::Dollar => "Dollar".to_string(),
                TokenKind::DoubleDollar => "DoubleDollar".to_string(),
            };
            insert(name);
        }

        let count = id_to_name.len() as u8;
        TokenVariantMap {
            name_to_id,
            id_to_name,
            count,
        }
    }

    /// Look up the ID for a token variant name, or `None` if not in the map.
    pub fn get_id(&self, name: &str) -> Option<u8> {
        self.name_to_id.get(name).copied()
    }

    /// Look up the token variant name for an ID, or `None` if out of range.
    pub fn get_name(&self, id: u8) -> Option<&str> {
        self.id_to_name.get(id as usize).map(|s| s.as_str())
    }

    /// Look up the ID for a `TokenKind`.
    pub fn kind_to_id(&self, kind: &TokenKind) -> Option<u8> {
        let name = match kind {
            TokenKind::Eof => "Eof".to_string(),
            TokenKind::Ident => "Ident".to_string(),
            TokenKind::Integer => "Integer".to_string(),
            TokenKind::Float => "Float".to_string(),
            TokenKind::True | TokenKind::False => "Boolean".to_string(),
            TokenKind::StringLit => "StringLit".to_string(),
            TokenKind::Fixed(text) => terminal_to_variant_name(text),
            TokenKind::Dollar => "Dollar".to_string(),
            TokenKind::DoubleDollar => "DoubleDollar".to_string(),
        };
        self.get_id(&name)
    }
}

/// A compact bitset of token variant IDs, supporting up to 64 variants.
///
/// Used for efficient FIRST-set membership tests in the generated parser.
/// Each bit position corresponds to a `TokenVariantMap` ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TokenFilter(pub u64);

impl TokenFilter {
    /// Filter containing all token variants.
    pub const ALL: Self = TokenFilter(!0u64);

    /// Empty filter (no tokens).
    pub const EMPTY: Self = TokenFilter(0);

    /// Create a filter containing a single token variant ID.
    #[inline]
    pub fn singleton(id: u8) -> Self {
        debug_assert!(id < 64, "TokenFilter supports at most 64 variants");
        TokenFilter(1u64 << id)
    }

    /// Test whether a token variant ID is in this filter.
    #[inline]
    pub fn contains(&self, id: u8) -> bool {
        id < 64 && (self.0 & (1u64 << id)) != 0
    }

    /// Union of two filters.
    #[inline]
    pub fn union(self, other: Self) -> Self {
        TokenFilter(self.0 | other.0)
    }

    /// Intersection of two filters.
    #[inline]
    pub fn intersection(self, other: Self) -> Self {
        TokenFilter(self.0 & other.0)
    }

    /// Whether this filter is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Number of token variants in this filter.
    #[inline]
    pub fn count(&self) -> u32 {
        self.0.count_ones()
    }
}

/// Lexer analysis: information about ambiguous DFA states.
///
/// Returned alongside the lexer code string so the parser codegen can
/// build composed dispatch tables for context-sensitive lexing.
#[derive(Debug, Clone)]
pub struct LexerAmbiguityInfo {
    /// Whether the DFA has any ambiguous accepting states.
    pub has_ambiguous: bool,
    /// Ambiguous states: `(dfa_state_id, alternatives)` sorted by weight ascending.
    /// Empty if `has_ambiguous` is false.
    pub ambiguous_states: Vec<(StateId, Vec<(TokenKind, TropicalWeight)>)>,
}

/// Analyze a DFA for multi-accept ambiguity.
pub fn analyze_ambiguity(dfa: &Dfa) -> LexerAmbiguityInfo {
    let has_ambiguous = dfa.has_ambiguous_accepts();
    let ambiguous_states = if has_ambiguous {
        dfa.ambiguous_states()
            .into_iter()
            .map(|(id, alts)| (id, alts.to_vec()))
            .collect()
    } else {
        Vec::new()
    };
    LexerAmbiguityInfo {
        has_ambiguous,
        ambiguous_states,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Primary API — string-based codegen with single TokenStream parse
// ══════════════════════════════════════════════════════════════════════════════

/// Generate the complete lexer code as a TokenStream.
///
/// Includes:
/// - `Token` enum definition
/// - `Position` and `Range` structs
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
    let (buf, strategy, _variant_map, _ambiguity) =
        generate_lexer_string(dfa, partition, token_kinds, language_name);
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
/// Returns the generated code string, codegen strategy, token variant map,
/// and DFA ambiguity info.
pub fn generate_lexer_string(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    _language_name: &str,
) -> (String, CodegenStrategy, TokenVariantMap, LexerAmbiguityInfo) {
    // Estimate buffer size: ~8KB for typical grammars, scales with DFA size
    let estimated_size = 4096 + dfa.states.len() * partition.num_classes * 16;
    let mut buf = String::with_capacity(estimated_size);

    write_token_enum(&mut buf, token_kinds);
    write_runtime_types_import(&mut buf);

    let strategy = if dfa.states.len() <= DIRECT_CODED_THRESHOLD {
        write_direct_coded_lexer(&mut buf, dfa, partition);
        CodegenStrategy::DirectCoded
    } else {
        write_compressed_lexer(&mut buf, dfa, partition)
    };

    let variant_map = TokenVariantMap::from_token_kinds(token_kinds);
    let ambiguity_info = analyze_ambiguity(dfa);

    (buf, strategy, variant_map, ambiguity_info)
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

/// Write `use mettail_prattail::runtime_types::*;` to a string buffer.
///
/// This replaces the previously inlined Position/Range/ParseError struct definitions
/// with a single import from the runtime crate. Generated code uses the shared
/// definitions (~200 lines removed from each generated parser).
fn write_runtime_types_import(buf: &mut String) {
    buf.push_str("use mettail_prattail::runtime_types::*;");
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

/// Write an IS_ACCEPTING check to a string buffer.
///
/// For DFAs with ≤128 states: emits a `const IS_ACCEPTING: u128 = 0b...;` bitmap
/// where bit `i` is set iff state `i` is accepting. The inner lex loop checks
/// `(IS_ACCEPTING >> state) & 1 != 0` instead of calling `accept_token()`.
///
/// For DFAs with >128 states: emits a `static IS_ACCEPTING: [bool; N] = [...];`
/// array with `IS_ACCEPTING[state as usize]` lookup.
///
/// This eliminates the expensive `accept_token()` call (which creates a `&str`
/// slice and enters a match dispatch) on every character in the DFA inner loop.
fn write_is_accepting_check(buf: &mut String, dfa: &Dfa) {
    let n = dfa.states.len();
    if n <= 128 {
        let mut bitmap: u128 = 0;
        for (i, state) in dfa.states.iter().enumerate() {
            if state.accept.is_some() {
                bitmap |= 1u128 << i;
            }
        }
        write!(buf, "const IS_ACCEPTING: u128 = {};", bitmap).unwrap();
        buf.push_str(
            "#[inline(always)] fn is_accepting_state(state: u32) -> bool { \
             state < 128 && (IS_ACCEPTING >> state) & 1 != 0 \
             }",
        );
    } else {
        write!(buf, "static IS_ACCEPTING: [bool; {}] = [", n).unwrap();
        for (i, state) in dfa.states.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            if state.accept.is_some() {
                buf.push_str("true");
            } else {
                buf.push_str("false");
            }
        }
        buf.push_str("];");
        buf.push_str(
            "#[inline(always)] fn is_accepting_state(state: u32) -> bool { \
             (state as usize) < IS_ACCEPTING.len() && IS_ACCEPTING[state as usize] \
             }",
        );
    }
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

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // dfa_next() function
    buf.push_str("fn dfa_next(state: u32, class: u8) -> u32 {");
    write_transition_arms(buf, dfa);
    buf.push('}');

    // accept_token() function — returns Token<'a> borrowing from text
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // lex()/lex_with_file_id() via lex_core() — DFA loop is in the runtime crate
    write_lex_via_core(buf);

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str(
        "fn accept_weight(state: u32) -> f64 {",
    );
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);
}

/// Write `lex()`/`lex_with_file_id()` that delegate to `mettail_prattail::runtime_types::lex_core()`.
///
/// The grammar-specific `CHAR_CLASS`, `dfa_next`, `is_accepting_state`, and `accept_token`
/// are passed as closures. The compiler monomorphizes away the closure overhead.
/// `lex_core()` returns `(tokens, eof_position)` — the Eof token is appended with zero overhead.
fn write_lex_via_core(buf: &mut String) {
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }\n\
         pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range)>, String> { \
         let (mut tokens, eof_pos) = mettail_prattail::runtime_types::lex_core( \
         input, file_id, &CHAR_CLASS, dfa_next, is_accepting_state, accept_token)?; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id })); \
         Ok(tokens) }",
    );
}

/// Write `lex_weighted()`/`lex_weighted_with_file_id()` that delegate to
/// `mettail_prattail::runtime_types::lex_weighted_core()`.
///
/// `lex_weighted_core()` returns `(tokens, eof_position)` — Eof appended with weight 0.0.
fn write_lex_weighted_via_core(buf: &mut String) {
    buf.push_str(
        "pub fn lex_weighted<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         lex_weighted_with_file_id(input, None) \
         }\n\
         pub fn lex_weighted_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range, f64)>, String> { \
         let (mut tokens, eof_pos) = mettail_prattail::runtime_types::lex_weighted_core( \
         input, file_id, &CHAR_CLASS, dfa_next, is_accepting_state, accept_token, accept_weight)?; \
         tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }, 0.0_f64)); \
         Ok(tokens) }",
    );
}


// ══════════════════════════════════════════════════════════════════════════════
// Incremental Lexer struct + LexerAdapter codegen (Phase 6D)
// ══════════════════════════════════════════════════════════════════════════════

/// Emit per-category expected-token description constants.
///
/// Generates `const EXPECTED_<CAT>: &str = "...";` for each category, using
/// the FIRST set to build a human-readable description of valid tokens.
/// Used by `next_token_for_category()` and `LexerAdapter` error messages.
///
/// Always emitted as part of the context-sensitive lexing infrastructure.
pub fn write_expected_category_descriptions(
    buf: &mut String,
    expected_messages: &[(String, String)],
) {
    for (cat_name, msg) in expected_messages {
        let escaped = msg.replace('\\', "\\\\").replace('"', "\\\"");
        write!(
            buf,
            "const EXPECTED_{}: &str = \"{}\";",
            cat_name.to_uppercase(),
            escaped,
        )
        .unwrap();
    }
}

/// Write the `Lexer<'a>` struct and associated methods to a string buffer.
///
/// The Lexer struct provides incremental (token-at-a-time) lexing, as opposed
/// to the batch `lex()` function that eagerly tokenizes the entire input.
///
/// Two methods:
/// - `next_token()`: unfiltered, identical to the inner loop of `lex()`
/// - `next_token_for_category(category_id)`: uses composed dispatch for ambiguous states
///
/// Always emitted as part of the context-sensitive lexing infrastructure.
pub fn write_lexer_struct(
    buf: &mut String,
    ambiguity_info: &LexerAmbiguityInfo,
    category_names: &[String],
) {

    buf.push_str(
        "pub struct Lexer<'a> { \
         input: &'a str, \
         bytes: &'a [u8], \
         pos: usize, \
         line: usize, \
         col: usize, \
         file_id: Option<u32>, \
         } \
         impl<'a> Lexer<'a> { \
         pub fn new(input: &'a str, file_id: Option<u32>) -> Self { \
         Lexer { input, bytes: input.as_bytes(), pos: 0, line: 0, col: 0, file_id } \
         } \
         pub fn is_eof(&self) -> bool { self.pos >= self.bytes.len() } \
         pub fn position(&self) -> Position { \
         Position { byte_offset: self.pos, line: self.line, column: self.col } \
         } \
         ",
    );

    // next_token() — identical to the inner loop of lex()
    // Uses is_accepting_state() bitmap in inner loop; accept_token() only once after loop.
    buf.push_str(
        "pub fn next_token(&mut self) -> Result<(Token<'a>, Range), String> { \
         while self.pos < self.bytes.len() && is_whitespace(self.bytes[self.pos]) { \
         if self.bytes[self.pos] == b'\\n' { self.line += 1; self.col = 0; } else { self.col += 1; } \
         self.pos += 1; } \
         if self.pos >= self.bytes.len() { \
         let eof_pos = Position { byte_offset: self.pos, line: self.line, column: self.col }; \
         return Ok((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id: self.file_id })); \
         } \
         let start = self.pos; \
         let start_line = self.line; \
         let start_col = self.col; \
         let mut state: u32 = 0; \
         let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
         if is_accepting_state(0) { last_accept = Some((0, self.pos, self.line, self.col)); } \
         while self.pos < self.bytes.len() { \
         let class = CHAR_CLASS[self.bytes[self.pos] as usize]; \
         let next = dfa_next(state, class); \
         if next == u32::MAX { break; } \
         state = next; \
         if self.bytes[self.pos] == b'\\n' { self.line += 1; self.col = 0; } \
         else if self.bytes[self.pos] & 0xC0 != 0x80 { self.col += 1; } \
         self.pos += 1; \
         if is_accepting_state(state) { last_accept = Some((state, self.pos, self.line, self.col)); } \
         } \
         match last_accept { \
         Some((accept_state, end, end_line, end_col)) => { \
         self.pos = end; self.line = end_line; self.col = end_col; \
         let text = &self.input[start..end]; \
         match accept_token(accept_state, text) { \
         Some(token) => Ok((token, Range { \
         start: Position { byte_offset: start, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id: self.file_id })), \
         None => Err(format!(\"{}:{}: internal error: accept state without token\", self.line + 1, self.col + 1)) \
         } } \
         None => Err(format!(\"{}:{}: unexpected character '{}'\", \
         start_line + 1, start_col + 1, self.bytes[start] as char)) \
         } }",
    );

    // next_token_for_category(category_id) — context-aware
    // Uses is_accepting_state() bitmap in inner loop; accept_token() only once after loop.
    if ambiguity_info.has_ambiguous {
        buf.push_str(
            "pub fn next_token_for_category(&mut self, category_id: u8) -> Result<(Token<'a>, Range), String> { \
             while self.pos < self.bytes.len() && is_whitespace(self.bytes[self.pos]) { \
             if self.bytes[self.pos] == b'\\n' { self.line += 1; self.col = 0; } else { self.col += 1; } \
             self.pos += 1; } \
             if self.pos >= self.bytes.len() { \
             let eof_pos = Position { byte_offset: self.pos, line: self.line, column: self.col }; \
             return Ok((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id: self.file_id })); \
             } \
             let start = self.pos; \
             let start_line = self.line; \
             let start_col = self.col; \
             let mut state: u32 = 0; \
             let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
             if is_accepting_state(0) { last_accept = Some((0, self.pos, self.line, self.col)); } \
             while self.pos < self.bytes.len() { \
             let class = CHAR_CLASS[self.bytes[self.pos] as usize]; \
             let next = dfa_next(state, class); \
             if next == u32::MAX { break; } \
             state = next; \
             if self.bytes[self.pos] == b'\\n' { self.line += 1; self.col = 0; } \
             else if self.bytes[self.pos] & 0xC0 != 0x80 { self.col += 1; } \
             self.pos += 1; \
             if is_accepting_state(state) { last_accept = Some((state, self.pos, self.line, self.col)); } \
             } \
             match last_accept { \
             Some((accept_state, end, end_line, end_col)) => { \
             self.pos = end; self.line = end_line; self.col = end_col; \
             let text = &self.input[start..end]; \
             let dispatch = composed_dispatch(category_id, accept_state); \
             if dispatch.is_empty() { \
             match accept_token(accept_state, text) { \
             Some(token) => Ok((token, Range { \
             start: Position { byte_offset: start, line: start_line, column: start_col }, \
             end: Position { byte_offset: end, line: end_line, column: end_col }, \
             file_id: self.file_id })), \
             None => Err(format!(\"{}:{}: internal error: accept state without token\", self.line + 1, self.col + 1)) \
             } \
             } else { \
             let (kind_id, _rule, _weight) = dispatch[0]; \
             match accept_token_by_kind(accept_state, text, kind_id) { \
             Some(token) => Ok((token, Range { \
             start: Position { byte_offset: start, line: start_line, column: start_col }, \
             end: Position { byte_offset: end, line: end_line, column: end_col }, \
             file_id: self.file_id })), \
             None => match accept_token(accept_state, text) { \
             Some(token) => Ok((token, Range { \
             start: Position { byte_offset: start, line: start_line, column: start_col }, \
             end: Position { byte_offset: end, line: end_line, column: end_col }, \
             file_id: self.file_id })), \
             None => Err(format!(\"{}:{}: internal error: accept state without token\", self.line + 1, self.col + 1)) \
             } } } } \
             None => Err(format!(\"{}:{}: unexpected character '{}'; expected {}\", \
             start_line + 1, start_col + 1, self.bytes[start] as char, expected_for_category(category_id))) \
             } }",
        );
    } else {
        // No ambiguous states — next_token_for_category uses same DFA as next_token
        // but still provides category-aware error messages
        buf.push_str(
            "pub fn next_token_for_category(&mut self, category_id: u8) -> Result<(Token<'a>, Range), String> { \
             match self.next_token() { \
             Ok(tok_range) => Ok(tok_range), \
             Err(msg) => Err(format!(\"{} (expected {})\", msg, expected_for_category(category_id))), \
             } }",
        );
    }

    buf.push_str("} "); // close impl Lexer

    // Emit expected_for_category() at module scope so it's accessible from both
    // Lexer methods and lazy parser functions.
    let mut expected_fn = String::from(
        "fn expected_for_category(category_id: u8) -> &'static str { match category_id { ",
    );
    for (i, cat) in category_names.iter().enumerate() {
        write!(expected_fn, "{} => EXPECTED_{}, ", i, cat.to_uppercase()).unwrap();
    }
    expected_fn.push_str("_ => \"token\" } }");
    buf.push_str(&expected_fn);

    // NOTE: lex() is already emitted by the standard lexer codegen path
    // (write_direct_coded_lexer / write_compressed_lexer). No duplicate needed.
}

/// Write the `accept_token_by_kind()` function for ambiguous states.
///
/// Given a DFA state and a target kind_id, returns the token constructed
/// as if that specific token kind was accepted. Handles the mapping from
/// kind_id back to the appropriate Token constructor.
pub fn write_accept_token_by_kind(
    buf: &mut String,
    variant_map: &TokenVariantMap,
) {

    buf.push_str(
        "fn accept_token_by_kind<'a>(state: u32, text: &'a str, kind_id: u8) -> Option<Token<'a>> {",
    );
    buf.push_str("match kind_id {");

    // Emit a match arm for each token variant
    for (name, &id) in &variant_map.name_to_id {
        write!(buf, "{} => Some(", id).unwrap();
        match name.as_str() {
            "Eof" => buf.push_str("Token::Eof"),
            "Ident" => buf.push_str("Token::Ident(text)"),
            "Integer" => buf.push_str("Token::Integer(text.parse::<i64>().expect(\"invalid integer literal\"))"),
            "Float" => buf.push_str("Token::Float(text.parse::<f64>().expect(\"invalid float literal\"))"),
            "Boolean" => {
                buf.push_str("if text == \"true\" { Token::Boolean(true) } else { Token::Boolean(false) }");
            },
            "StringLit" => buf.push_str("Token::StringLit(&text[1..text.len()-1])"),
            "Dollar" => buf.push_str("Token::Dollar(&text[1..])"),
            "DoubleDollar" => buf.push_str("Token::DoubleDollar(&text[2..text.len()-1])"),
            variant => {
                write!(buf, "Token::{}", variant).unwrap();
            },
        }
        buf.push_str("),");
    }

    buf.push_str("_ => accept_token(state, text) } }");
}

/// Write the `LexerAdapter` struct for parser-driven lexing.
///
/// Wraps a `Lexer` with a small token buffer for peek-ahead and
/// category-aware disambiguation.
///
/// Error handling: lex errors are captured and stored. When a lex error occurs,
/// the adapter stores the error message and reports EOF. The stored error can be
/// retrieved via `take_error()` for proper error propagation in the parser.
pub fn write_lexer_adapter(buf: &mut String) {
    buf.push_str(
        "pub struct LexerAdapter<'a> { \
         lexer: Lexer<'a>, \
         buf: Vec<(Token<'a>, Range)>, \
         cursor: usize, \
         category_id: u8, \
         lex_error: Option<String>, \
         } \
         impl<'a> LexerAdapter<'a> { \
         pub fn new(lexer: Lexer<'a>) -> Self { \
         LexerAdapter { lexer, buf: Vec::with_capacity(4), cursor: 0, category_id: 0, lex_error: None } \
         } \
         pub fn set_category(&mut self, id: u8) { self.category_id = id; } \
         fn ensure_buffered(&mut self, n: usize) { \
         while self.buf.len() <= self.cursor + n { \
         if self.lex_error.is_some() { \
         let pos = self.lexer.position(); \
         self.buf.push((Token::Eof, Range { start: pos, end: pos, file_id: None })); \
         break; \
         } \
         let result = if self.category_id > 0 { \
         self.lexer.next_token_for_category(self.category_id) \
         } else { \
         self.lexer.next_token() \
         }; \
         match result { \
         Ok(tok_range) => self.buf.push(tok_range), \
         Err(msg) => { \
         self.lex_error = Some(msg); \
         let pos = self.lexer.position(); \
         self.buf.push((Token::Eof, Range { start: pos, end: pos, file_id: None })); \
         break; \
         } } } } \
         pub fn peek(&mut self) -> &Token<'a> { \
         self.ensure_buffered(0); \
         &self.buf[self.cursor].0 \
         } \
         pub fn peek_range(&mut self) -> &Range { \
         self.ensure_buffered(0); \
         &self.buf[self.cursor].1 \
         } \
         pub fn peek_ahead(&mut self, n: usize) -> Option<&Token<'a>> { \
         self.ensure_buffered(n); \
         self.buf.get(self.cursor + n).map(|(t, _)| t) \
         } \
         pub fn advance(&mut self) { \
         self.ensure_buffered(0); \
         if self.cursor < self.buf.len() { self.cursor += 1; } \
         if self.cursor > 8 { \
         self.buf.drain(..self.cursor); \
         self.cursor = 0; \
         } } \
         pub fn is_eof(&mut self) -> bool { \
         matches!(self.peek(), Token::Eof) \
         } \
         pub fn take_error(&mut self) -> Option<String> { \
         self.lex_error.take() \
         } \
         pub fn pos(&self) -> usize { self.cursor } \
         pub fn set_pos(&mut self, pos: usize) { self.cursor = pos; } \
         } ",
    );
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

    // Greedy offset search with occupancy bitmap for O(1) free-slot finding.
    // The occupied bitmap tracks which slots in the check array are taken,
    // enabling faster offset searches by skipping known-occupied regions.
    let mut base = vec![0u32; num_states];
    let default = vec![u32::MAX; num_states]; // DEAD_STATE
                                              // Start with a reasonable size, will grow as needed
    let initial_capacity = num_states * 2 + num_classes;
    let mut next = vec![u32::MAX; initial_capacity];
    let mut check = vec![u32::MAX; initial_capacity]; // u32::MAX means "unoccupied"
    // Occupancy bitmap: bit i set iff check[i] != u32::MAX
    let occupied_words = (initial_capacity + 63) >> 6;
    let mut occupied: Vec<u64> = vec![0u64; occupied_words];
    let mut high_water: usize = 0;

    for (state_idx, entries) in &sparse_rows {
        if entries.is_empty() {
            base[*state_idx] = 0; // doesn't matter, will always hit DEFAULT
            continue;
        }

        // Find smallest offset d where no entries collide.
        // Use occupancy bitmap to jump past fully-occupied words.
        let first_class = entries[0].0;
        let mut d: usize = 0;
        'search: loop {
            let needed = d + num_classes;
            // Grow arrays if needed
            if needed > next.len() {
                let new_len = needed + num_classes;
                next.resize(new_len, u32::MAX);
                check.resize(new_len, u32::MAX);
                let new_occupied_words = (new_len + 63) >> 6;
                occupied.resize(new_occupied_words, 0u64);
            }

            // Quick check: if the first entry's slot is occupied, skip immediately
            let first_idx = d + first_class;
            let word_idx = first_idx >> 6;
            let bit_idx = first_idx & 63;
            if word_idx < occupied.len() && (occupied[word_idx] >> bit_idx) & 1 != 0 {
                d += 1;
                continue;
            }

            // Check for collisions on remaining entries
            let mut collides = false;
            for &(class_id, _) in entries.iter().skip(1) {
                let idx = d + class_id;
                let w = idx >> 6;
                let b = idx & 63;
                if w < occupied.len() && (occupied[w] >> b) & 1 != 0 {
                    collides = true;
                    break;
                }
            }
            if !collides {
                break 'search;
            }
            d += 1;
        }

        // Place this row at offset d and mark occupied bits
        base[*state_idx] = d as u32;
        for &(class_id, target) in entries {
            let idx = d + class_id;
            next[idx] = target;
            check[idx] = *state_idx as u32;
            // Set occupancy bit
            let w = idx >> 6;
            let b = idx & 63;
            occupied[w] |= 1u64 << b;
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
pub fn build_bitmap_tables(dfa: &Dfa) -> Result<BitmapTables, String> {
    if dfa.num_classes > 32 {
        return Err(format!(
            "bitmap compression requires num_classes <= 32, got {}",
            dfa.num_classes
        ));
    }

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

    Ok(BitmapTables { bitmaps, offsets, targets })
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
        let bitmap = build_bitmap_tables(dfa).expect("num_classes verified <= 32");
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

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // dfa_next function using comb lookup
    write!(
        buf,
        "#[inline(always)] fn dfa_next(state: u32, class: u8) -> u32 {{ \
         let idx = BASE[state as usize] as usize + class as usize; \
         if CHECK[idx] == state {{ NEXT[idx] }} else {{ DEFAULT[state as usize] }} \
         }}"
    )
    .unwrap();

    // accept_token() function
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // lex()/lex_with_file_id() via lex_core()
    write_lex_via_core(buf);

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str("fn accept_weight(state: u32) -> f64 {");
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);
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

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

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

    // accept_token() function
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa);
    buf.push('}');

    // lex()/lex_with_file_id() via lex_core()
    write_lex_via_core(buf);

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str("fn accept_weight(state: u32) -> f64 {");
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);
}


// ══════════════════════════════════════════════════════════════════════════════
// Utility functions
// ══════════════════════════════════════════════════════════════════════════════

// NOTE: The legacy quote!-based codegen API (generate_token_enum, generate_span_def,
// generate_direct_coded_lexer, generate_table_driven_lexer, generate_class_table,
// generate_accept_match_arms, generate_transition_match_arms, token_kind_to_constructor)
// was removed as part of backwards-compatibility cleanup. The string-based codegen
// (write_*) functions are the canonical implementation.

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
        let nfa = build_nfa(&terminals, &needs, &crate::LiteralPatterns::default());
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

        let tables = build_bitmap_tables(&dfa).expect("test DFA has <= 32 classes");

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

        let tables = build_bitmap_tables(&dfa).expect("test DFA has <= 32 classes");

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
    fn test_bitmap_num_classes_guard() {
        // Must return Err for num_classes > 32
        let mut dfa = Dfa::new(33);
        dfa.states[0].transitions = vec![DEAD_STATE; 33];
        let result = build_bitmap_tables(&dfa);
        assert!(result.is_err(), "build_bitmap_tables must reject num_classes > 32");
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

        let (code, _strategy, _variant_map, _ambiguity) =
            generate_lexer_string(&dfa, &partition, &token_kinds, "test");
        // If this doesn't panic, the generated code is valid Rust
        let _ts: TokenStream = code
            .parse()
            .expect("generated compressed lexer should be valid Rust");
    }

    // ══════════════════════════════════════════════════════════════════════
    // TokenVariantMap tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_variant_map_basic() {
        let kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Fixed("+".to_string()),
        ];
        let map = TokenVariantMap::from_token_kinds(&kinds);

        assert_eq!(map.count, 4); // Eof, Ident, Integer, Plus
        assert_eq!(map.get_id("Eof"), Some(0));
        assert_eq!(map.get_id("Ident"), Some(1));
        assert_eq!(map.get_id("Integer"), Some(2));
        assert_eq!(map.get_id("Plus"), Some(3));
        assert_eq!(map.get_id("Missing"), None);

        assert_eq!(map.get_name(0), Some("Eof"));
        assert_eq!(map.get_name(1), Some("Ident"));
        assert_eq!(map.get_name(2), Some("Integer"));
        assert_eq!(map.get_name(3), Some("Plus"));
        assert_eq!(map.get_name(4), None);
    }

    #[test]
    fn test_variant_map_deduplicates() {
        let kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Ident, // duplicate
            TokenKind::Integer,
            TokenKind::Integer, // duplicate
            TokenKind::True,
            TokenKind::False, // maps to same "Boolean" variant
        ];
        let map = TokenVariantMap::from_token_kinds(&kinds);

        // Eof, Ident, Integer, Boolean = 4 unique
        assert_eq!(map.count, 4);
        assert_eq!(map.get_id("Boolean"), Some(3));
    }

    #[test]
    fn test_variant_map_kind_to_id() {
        let kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Fixed("error".to_string()),
        ];
        let map = TokenVariantMap::from_token_kinds(&kinds);

        assert_eq!(map.kind_to_id(&TokenKind::Eof), Some(0));
        assert_eq!(map.kind_to_id(&TokenKind::Ident), Some(1));
        assert_eq!(
            map.kind_to_id(&TokenKind::Fixed("error".to_string())),
            Some(2)
        );
        assert_eq!(map.kind_to_id(&TokenKind::Integer), None);
    }

    // ══════════════════════════════════════════════════════════════════════
    // TokenFilter tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_token_filter_empty() {
        let f = TokenFilter::EMPTY;
        assert!(f.is_empty());
        assert_eq!(f.count(), 0);
        assert!(!f.contains(0));
        assert!(!f.contains(63));
    }

    #[test]
    fn test_token_filter_singleton() {
        let f = TokenFilter::singleton(5);
        assert!(!f.is_empty());
        assert_eq!(f.count(), 1);
        assert!(f.contains(5));
        assert!(!f.contains(0));
        assert!(!f.contains(4));
        assert!(!f.contains(6));
    }

    #[test]
    fn test_token_filter_union() {
        let f1 = TokenFilter::singleton(1);
        let f2 = TokenFilter::singleton(3);
        let f = f1.union(f2);
        assert_eq!(f.count(), 2);
        assert!(f.contains(1));
        assert!(f.contains(3));
        assert!(!f.contains(0));
        assert!(!f.contains(2));
    }

    #[test]
    fn test_token_filter_intersection() {
        let f1 = TokenFilter::singleton(1).union(TokenFilter::singleton(2));
        let f2 = TokenFilter::singleton(2).union(TokenFilter::singleton(3));
        let f = f1.intersection(f2);
        assert_eq!(f.count(), 1);
        assert!(f.contains(2));
        assert!(!f.contains(1));
        assert!(!f.contains(3));
    }

    #[test]
    fn test_token_filter_all() {
        let f = TokenFilter::ALL;
        assert!(!f.is_empty());
        assert!(f.contains(0));
        assert!(f.contains(63));
        assert_eq!(f.count(), 64);
    }

    // ══════════════════════════════════════════════════════════════════════
    // LexerAmbiguityInfo tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_ambiguity_info_no_ambiguity() {
        let terminals = vec![
            TerminalPattern {
                text: "+".to_string(),
                kind: TokenKind::Fixed("+".to_string()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds {
            ident: false,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };
        let nfa = build_nfa(&terminals, &needs, &crate::LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        let info = analyze_ambiguity(&min_dfa);
        assert!(!info.has_ambiguous);
        assert!(info.ambiguous_states.is_empty());
    }

    #[test]
    fn test_ambiguity_info_with_keyword() {
        let terminals = vec![TerminalPattern {
            text: "error".to_string(),
            kind: TokenKind::Fixed("error".to_string()),
            is_keyword: true,
        }];
        let needs = BuiltinNeeds {
            ident: true,
            integer: false,
            float: false,
            string_lit: false,
            boolean: false,
        };
        let nfa = build_nfa(&terminals, &needs, &crate::LiteralPatterns::default());
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);
        let min_dfa = minimize_dfa(&dfa);

        let info = analyze_ambiguity(&min_dfa);
        assert!(info.has_ambiguous);
        assert!(!info.ambiguous_states.is_empty());

        // Verify the ambiguous state has both kinds
        for (_, alts) in &info.ambiguous_states {
            assert!(alts.len() >= 2);
        }
    }
}
