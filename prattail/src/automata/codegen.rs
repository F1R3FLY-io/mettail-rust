//! DFA → Rust lexer code generation.
//!
//! Converts a minimized DFA with alphabet partitioning into Rust source code.
//! Three strategies are available:
//! - **Direct-coded** (default for ≤30 DFA states): each state becomes a match arm
//! - **Table-driven** (default for >30 states): transition table with row-displacement compression
//! - **Hybrid** (AL02, gated): hot states (BFS depth ≤ 2 from start) get direct-coded match
//!   arms; cold states use table-driven lookup. Activated when `optimization_gates.hybrid_lexer`
//!   is true and the DFA has > 30 states.
//!
//! ## Performance
//!
//! Code generation uses string-based construction with a single `TokenStream::parse()`
//! at the end, rather than building up `TokenStream` incrementally with `quote!`. This
//! eliminates O(states × classes) intermediate `TokenStream` allocations that dominated
//! the previous implementation (~46% of codegen time was proc_macro2 overhead).

use std::collections::HashSet;
use std::fmt::Write;

use proc_macro2::TokenStream;

use super::{partition::AlphabetPartition, semiring::TropicalWeight, Dfa, StateId, TokenKind, DEAD_STATE};
use crate::CustomTokenSpec;

/// Threshold: use direct-coded for small DFAs, table-driven for larger ones.
const DIRECT_CODED_THRESHOLD: usize = 30;

/// Default BFS depth for determining hot states in hybrid lexer mode.
const HYBRID_HOT_DEPTH: usize = 2;

// ══════════════════════════════════════════════════════════════════════════════
// AL02: Hot state classification via BFS from start state
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the set of "hot" DFA states reachable within `depth` transitions
/// from the start state via BFS.
///
/// Hot states are the most frequently visited during lexing (they process the
/// first few characters of every token). By direct-coding these states as match
/// arms while keeping cold states in compressed tables, we get the branch
/// prediction benefits of direct coding where it matters most, without the code
/// size explosion of direct-coding all states in large DFAs.
///
/// Returns a `HashSet<usize>` of state indices considered hot.
pub fn compute_hot_states(dfa: &Dfa, depth: usize) -> HashSet<usize> {
    let mut hot = HashSet::new();
    let mut frontier = vec![dfa.start as usize];
    hot.insert(dfa.start as usize);

    for _level in 0..depth {
        let mut next_frontier = Vec::new();
        for &state_idx in &frontier {
            let state = &dfa.states[state_idx];
            for &target in &state.transitions {
                let target_idx = target as usize;
                if target != DEAD_STATE && hot.insert(target_idx) {
                    next_frontier.push(target_idx);
                }
            }
        }
        frontier = next_frontier;
    }

    hot
}

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
                TokenKind::Custom(name) => name.clone(),
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
            TokenKind::Custom(name) => name.clone(),
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
/// build composed dispatch tables for resolving lexer ambiguities.
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
///
/// When `hybrid_lexer` is true and the DFA has > 30 states, AL02 hybrid
/// mode is activated: hot states (BFS depth ≤ 2) get direct-coded match
/// arms while cold states use compressed table lookup.
pub fn generate_lexer_code(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    language_name: &str,
    custom_tokens: &[CustomTokenSpec],
) -> (TokenStream, CodegenStrategy) {
    let (buf, strategy, _variant_map, _ambiguity) =
        generate_lexer_string(dfa, partition, token_kinds, language_name, custom_tokens);
    let ts = buf
        .parse::<TokenStream>()
        .expect("generated lexer code must be valid Rust");
    (ts, strategy)
}

/// Generate the complete lexer code as a TokenStream with AL02 hybrid gating.
///
/// Same as [`generate_lexer_code`] but accepts the `hybrid_lexer` optimization gate.
pub fn generate_lexer_code_hybrid(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    language_name: &str,
    hybrid_lexer: bool,
    custom_tokens: &[CustomTokenSpec],
) -> (TokenStream, CodegenStrategy) {
    let (buf, strategy, _variant_map, _ambiguity) =
        generate_lexer_string_hybrid(dfa, partition, token_kinds, language_name, hybrid_lexer, custom_tokens);
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
    custom_tokens: &[CustomTokenSpec],
) -> (String, CodegenStrategy, TokenVariantMap, LexerAmbiguityInfo) {
    generate_lexer_string_hybrid(dfa, partition, token_kinds, _language_name, false, custom_tokens)
}

/// Generate lexer code as a `String` with AL02 hybrid gating.
///
/// When `hybrid_lexer` is true and the DFA exceeds the direct-coded threshold,
/// hot states (BFS depth ≤ 2 from start) are direct-coded while cold states
/// use compressed table lookup. An I16 diagnostic is emitted when hybrid mode
/// activates.
pub fn generate_lexer_string_hybrid(
    dfa: &Dfa,
    partition: &AlphabetPartition,
    token_kinds: &[TokenKind],
    _language_name: &str,
    hybrid_lexer: bool,
    custom_tokens: &[CustomTokenSpec],
) -> (String, CodegenStrategy, TokenVariantMap, LexerAmbiguityInfo) {
    // Estimate buffer size: ~8KB for typical grammars, scales with DFA size
    let estimated_size = 4096 + dfa.states.len() * partition.num_classes * 16;
    let mut buf = String::with_capacity(estimated_size);

    write_token_enum(&mut buf, token_kinds, custom_tokens);
    write_token_display(&mut buf, token_kinds, custom_tokens);
    write_runtime_types_import(&mut buf);

    let strategy = if dfa.states.len() <= DIRECT_CODED_THRESHOLD {
        // Small DFA: all states direct-coded (existing behavior, no hybrid needed)
        write_direct_coded_lexer(&mut buf, dfa, partition, custom_tokens);
        CodegenStrategy::DirectCoded
    } else if hybrid_lexer {
        // AL02: Hybrid mode — hot states direct-coded, cold states table-driven
        let hot_states = compute_hot_states(dfa, HYBRID_HOT_DEPTH);
        let num_hot = hot_states.len();
        let num_cold = dfa.states.len() - num_hot;

        // Emit I16 diagnostic
        crate::lint::emit_diagnostic(&crate::lint::LintDiagnostic {
            id: "I16",
            name: "hybrid-lexer-active",
            severity: crate::lint::LintSeverity::Info,
            category: None,
            rule: None,
            message: format!(
                "AL02 hybrid lexer: {} hot states (direct-coded, BFS depth ≤ {}), \
                 {} cold states (table-driven), {} total",
                num_hot, HYBRID_HOT_DEPTH, num_cold, dfa.states.len()
            ),
            hint: None,
            grammar_name: None,
            source_location: None,
        });

        write_hybrid_lexer(&mut buf, dfa, partition, &hot_states, custom_tokens);
        CodegenStrategy::HybridDirectCompressed
    } else {
        write_compressed_lexer(&mut buf, dfa, partition, custom_tokens)
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
fn write_token_enum(buf: &mut String, token_kinds: &[TokenKind], custom_tokens: &[CustomTokenSpec]) {
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
            TokenKind::Custom(name) => {
                if seen.insert(name.clone()) {
                    if let Some(pt) = custom_tokens.iter()
                        .find(|s| s.name == *name)
                        .and_then(|s| s.payload_type.as_deref())
                    {
                        // Payload-carrying variant: use &'a str for str types, type directly otherwise
                        if pt == "str" {
                            write!(buf, "{}(&'a str),", name).unwrap();
                        } else {
                            write!(buf, "{}({}),", name, pt).unwrap();
                        }
                    } else {
                        write!(buf, "{},", name).unwrap();
                    }
                }
            },
        }
    }

    buf.push('}');
}

/// Write a `format_token_friendly()` function alongside the Token enum.
///
/// Produces human-readable descriptions for error messages:
/// - `Token::Eof` → `"end of input"`
/// - `Token::Ident(s)` → `` "identifier `name`" ``
/// - `Token::Integer(n)` → `` "integer `42`" ``
/// - `Token::KwFoo` → `` "`foo`" ``
/// - `Token::Plus` → `` "`+`" ``
fn write_token_display(buf: &mut String, token_kinds: &[TokenKind], custom_tokens: &[CustomTokenSpec]) {
    let mut seen = std::collections::HashSet::<String>::new();

    buf.push_str("fn format_token_friendly(token: &Token<'_>) -> String { match token {");

    // Always include Eof and Ident
    buf.push_str("Token::Eof => \"end of input\".to_string(),");
    seen.insert("Eof".to_string());

    buf.push_str("Token::Ident(s) => format!(\"identifier `{}`\", s),");
    seen.insert("Ident".to_string());

    for kind in token_kinds {
        match kind {
            TokenKind::Eof | TokenKind::Ident => {},
            TokenKind::Integer => {
                if seen.insert("Integer".to_string()) {
                    buf.push_str("Token::Integer(n) => format!(\"integer `{}`\", n),");
                }
            },
            TokenKind::Float => {
                if seen.insert("Float".to_string()) {
                    buf.push_str("Token::Float(f) => format!(\"float `{}`\", f),");
                }
            },
            TokenKind::True | TokenKind::False => {
                if seen.insert("Boolean".to_string()) {
                    buf.push_str("Token::Boolean(b) => format!(\"boolean `{}`\", b),");
                }
            },
            TokenKind::StringLit => {
                if seen.insert("StringLit".to_string()) {
                    buf.push_str("Token::StringLit(s) => format!(\"string `\\\"{}\\\"`\", s),");
                }
            },
            TokenKind::Fixed(text) => {
                let variant_name = terminal_to_variant_name(text);
                if seen.insert(variant_name.clone()) {
                    // Escape backticks in the text for the format string
                    let escaped = text.replace('\\', "\\\\").replace('"', "\\\"");
                    write!(buf, "Token::{} => \"`{}`\".to_string(),", variant_name, escaped).unwrap();
                }
            },
            TokenKind::Dollar => {
                if seen.insert("Dollar".to_string()) {
                    buf.push_str("Token::Dollar(s) => format!(\"`${}`\", s),");
                }
            },
            TokenKind::DoubleDollar => {
                if seen.insert("DoubleDollar".to_string()) {
                    buf.push_str("Token::DoubleDollar(s) => format!(\"`$${}`\", s),");
                }
            },
            TokenKind::Custom(name) => {
                if seen.insert(name.clone()) {
                    let has_payload = custom_tokens.iter()
                        .find(|s| s.name == *name)
                        .and_then(|s| s.payload_type.as_ref())
                        .is_some();
                    if has_payload {
                        write!(buf, "Token::{}(v) => format!(\"{} `{{}}`\", v),", name, name).unwrap();
                    } else {
                        write!(buf, "Token::{} => \"`{}`\".to_string(),", name, name).unwrap();
                    }
                }
            },
        }
    }

    buf.push_str("} }");
}

/// Write `use mettail_prattail::runtime_types::*;` to a string buffer.
///
/// This replaces the previously inlined Position/Range/ParseError struct definitions
/// with a single import from the runtime crate. Generated code uses the shared
/// definitions (~200 lines removed from each generated parser).
fn write_runtime_types_import(buf: &mut String) {
    buf.push_str("use std::borrow::Cow;");
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

/// Write an IS_ACCEPTING bitmap check to a string buffer.
///
/// Emits a `static IS_ACCEPTING: [u64; ceil(N/64)] = [...]` bitset where bit `i`
/// (in word `i >> 6`, bit position `i & 63`) is set iff state `i` is accepting.
/// The inner lex loop checks `(IS_ACCEPTING[state >> 6] >> (state & 63)) & 1 != 0`.
///
/// ## A-L06: Accept State Bitmap Widening
///
/// Uses a `[u64; K]` bitset for ALL DFA sizes (K = ceil(N / 64)), replacing the
/// previous split strategy (u128 for ≤128 states, `[bool; N]` for >128 states).
/// Benefits:
/// - **8× less memory** than the old `[bool; N]` path for large DFAs
/// - **No bounds check** — valid state IDs always index within the bitset
/// - **Uniform codegen** — single code path regardless of DFA size
/// - **Cache-friendly** — compact bitset fits in fewer cache lines
fn write_is_accepting_check(buf: &mut String, dfa: &Dfa) {
    let n = dfa.states.len();
    let num_words = (n + 63) / 64;

    // Build the bitset words
    let mut words = vec![0u64; num_words];
    for (i, state) in dfa.states.iter().enumerate() {
        if state.accept.is_some() {
            words[i >> 6] |= 1u64 << (i & 63);
        }
    }

    // Emit the static array
    write!(buf, "static IS_ACCEPTING: [u64; {}] = [", num_words).unwrap();
    for (i, word) in words.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "0x{:016x}", word).unwrap();
    }
    buf.push_str("];");

    // Emit the inline acceptance check function
    buf.push_str(
        "#[inline(always)] fn is_accepting_state(state: u32) -> bool { \
         (IS_ACCEPTING[(state >> 6) as usize] >> (state & 63)) & 1 != 0 \
         }",
    );
}

/// Write the accept_token match arms to a string buffer.
fn write_accept_arms(buf: &mut String, dfa: &Dfa, custom_tokens: &[CustomTokenSpec]) {
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(ref kind) = state.accept {
            write!(buf, "{}u32 => Some(", state_idx).unwrap();
            write_token_constructor(buf, kind, custom_tokens);
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
fn write_token_constructor(buf: &mut String, kind: &TokenKind, custom_tokens: &[CustomTokenSpec]) {
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
        TokenKind::Custom(name) => {
            if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
                if let Some(ref code) = spec.constructor_code {
                    write!(buf, "Token::{}({{ let text = text; {} }})", name, code).unwrap();
                } else if let Some(ref pt) = spec.payload_type {
                    // Payload variant without custom code: default constructor
                    if pt == "str" {
                        write!(buf, "Token::{}(text)", name).unwrap();
                    } else {
                        write!(buf, "Token::{}(text.parse::<{}>().expect(\"invalid {} literal\"))", name, pt, name).unwrap();
                    }
                } else {
                    write!(buf, "Token::{}", name).unwrap();
                }
            } else {
                write!(buf, "Token::{}", name).unwrap();
            }
        },
    }
}

/// Write a complete direct-coded lexer to a string buffer.
fn write_direct_coded_lexer(buf: &mut String, dfa: &Dfa, partition: &AlphabetPartition, custom_tokens: &[CustomTokenSpec]) {
    write_class_table(buf, partition);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // AL05: Detect multi-byte chains and emit chain table + try_chain function.
    let chains = detect_multi_byte_chains(dfa, partition);
    let has_chains = !chains.is_empty();
    if has_chains {
        write_chain_tables(buf, &chains);
    }

    // dfa_next() function
    buf.push_str("fn dfa_next(state: u32, class: u8) -> u32 {");
    write_transition_arms(buf, dfa);
    buf.push('}');

    // accept_token() function — returns Token<'a> borrowing from text
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa, custom_tokens);
    buf.push('}');

    // lex()/lex_with_file_id() — chain-aware if chains detected, otherwise via lex_core()
    if has_chains {
        write_lex_with_chains(buf);
    } else {
        write_lex_via_core(buf);
    }

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str(
        "fn accept_weight(state: u32) -> f64 {",
    );
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);

    // B3: Lattice-aware lexing with multi-accept alternatives
    write_accept_alternatives(buf, dfa, custom_tokens);
    write_lex_lattice_via_core(buf);
}

/// AL02: Write a hybrid direct-coded + compressed lexer to a string buffer.
///
/// Hot states (in `hot_states`) are direct-coded as match arms in `dfa_next()`.
/// Cold states fall through to compressed table lookup (best of comb/bitmap).
/// The `dfa_next()` function first checks if the state is hot (via match),
/// and if no match arm fires, delegates to the compressed table.
fn write_hybrid_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
    hot_states: &HashSet<usize>,
    custom_tokens: &[CustomTokenSpec],
) {
    let num_classes = partition.num_classes;

    write_class_table(buf, partition);
    write!(buf, "const NUM_CLASSES: usize = {};", num_classes).unwrap();

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // Build compressed tables for cold states (used by fallback path)
    let comb = compress_rows_comb(dfa, num_classes);
    let use_bitmap = num_classes <= 32 && {
        let bitmap = build_bitmap_tables(dfa).expect("num_classes verified <= 32");
        bitmap.total_bytes() <= comb.total_bytes()
    };

    if use_bitmap {
        let bitmap = build_bitmap_tables(dfa).expect("num_classes verified <= 32");
        write_bitmap_tables(buf, &bitmap);

        // Cold-state fallback function using bitmap lookup
        buf.push_str(
            "#[inline(always)] fn dfa_next_cold(state: u32, class: u8) -> u32 { \
             let bitmap = BITMAPS[state as usize]; \
             let bit = 1u32 << (class as u32); \
             if bitmap & bit == 0 { return u32::MAX; } \
             let index = (bitmap & (bit - 1)).count_ones() as usize; \
             TARGETS[OFFSETS[state as usize] as usize + index] \
             }",
        );
    } else {
        write_comb_tables(buf, &comb);

        // Cold-state fallback function using comb lookup
        buf.push_str(
            "#[inline(always)] fn dfa_next_cold(state: u32, class: u8) -> u32 { \
             let idx = BASE[state as usize] as usize + class as usize; \
             if CHECK[idx] == state { NEXT[idx] } else { DEFAULT[state as usize] } \
             }",
        );
    }

    // dfa_next() function: hot states via match arms, cold states via table fallback
    buf.push_str("#[inline(always)] fn dfa_next(state: u32, class: u8) -> u32 { match state {");
    for &state_idx in hot_states {
        let state = &dfa.states[state_idx];
        let has_transitions = state.transitions.iter().any(|&t| t != DEAD_STATE);
        if !has_transitions {
            // Hot state with no transitions → always dead
            write!(buf, "{}u32 => u32::MAX,", state_idx).unwrap();
            continue;
        }
        write!(buf, "{}u32 => match class {{", state_idx).unwrap();
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                write!(buf, "{}u8 => {}u32,", class_id, target).unwrap();
            }
        }
        buf.push_str("_ => u32::MAX },");
    }
    // Cold states: delegate to compressed table
    buf.push_str("_ => dfa_next_cold(state, class) } }");

    // accept_token() function — returns Token<'a> borrowing from text
    buf.push_str("fn accept_token<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {");
    write_accept_arms(buf, dfa, custom_tokens);
    buf.push('}');

    // lex()/lex_with_file_id() via lex_core()
    write_lex_via_core(buf);

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str("fn accept_weight(state: u32) -> f64 {");
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);

    // B3: Lattice-aware lexing with multi-accept alternatives
    write_accept_alternatives(buf, dfa, custom_tokens);
    write_lex_lattice_via_core(buf);
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

/// AL05: Write `lex()`/`lex_with_file_id()` with chain-aware inner loop.
///
/// This is a generated copy of the `lex_core()` logic with the chain fast-path
/// inserted into the inner DFA walk loop. Before performing single-byte class
/// lookup + `dfa_next()`, the loop tries `try_chain()` to advance multiple bytes
/// at once. If the chain matches, `pos` and `state` advance by the chain length.
///
/// Line/column tracking is handled correctly: each chain byte is checked for `\n`.
/// In practice, chains are almost always ASCII letters/digits (keyword paths),
/// so the newline check is a no-op.
///
/// The chain-aware lex function completely replaces `lex_core()` delegation — no
/// runtime library change is needed.
fn write_lex_with_chains(buf: &mut String) {
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }\n\
         pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) -> Result<Vec<(Token<'a>, Range)>, String> { \
         use mettail_prattail::runtime_types::{Position, Range}; \
         let bytes = input.as_bytes(); \
         let mut pos: usize = 0; \
         let mut line: usize = 0; \
         let mut col: usize = 0; \
         let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2); \
         while pos < bytes.len() { \
             while pos < bytes.len() { \
                 let b = bytes[pos]; \
                 if b == b' ' || b == b'\\t' || b == b'\\r' || b == b'\\n' { \
                     if b == b'\\n' { line += 1; col = 0; } else { col += 1; } \
                     pos += 1; \
                 } else { break; } \
             } \
             if pos >= bytes.len() { break; } \
             let start = pos; \
             let start_line = line; \
             let start_col = col; \
             let mut state: u32 = 0; \
             let mut last_accept: Option<(u32, usize, usize, usize)> = None; \
             if is_accepting_state(0) { last_accept = Some((0, pos, line, col)); } \
             while pos < bytes.len() { \
                 if let Some((end_state, chain_len)) = try_chain(state, bytes, pos) { \
                     for i in 0..chain_len { \
                         if bytes[pos + i] == b'\\n' { line += 1; col = 0; } \
                         else if bytes[pos + i] & 0xC0 != 0x80 { col += 1; } \
                     } \
                     pos += chain_len; \
                     state = end_state; \
                     if is_accepting_state(state) { last_accept = Some((state, pos, line, col)); } \
                     continue; \
                 } \
                 let class = CHAR_CLASS[bytes[pos] as usize]; \
                 let next = dfa_next(state, class); \
                 if next == u32::MAX { break; } \
                 state = next; \
                 if bytes[pos] == b'\\n' { line += 1; col = 0; } \
                 else if bytes[pos] & 0xC0 != 0x80 { col += 1; } \
                 pos += 1; \
                 if is_accepting_state(state) { last_accept = Some((state, pos, line, col)); } \
             } \
             match last_accept { \
                 Some((accept_state, end, end_line, end_col)) => { \
                     pos = end; line = end_line; col = end_col; \
                     let text = &input[start..end]; \
                     if let Some(token) = accept_token(accept_state, text) { \
                         tokens.push((token, Range { \
                             start: Position { byte_offset: start, line: start_line, column: start_col }, \
                             end: Position { byte_offset: end, line: end_line, column: end_col }, \
                             file_id, \
                         })); \
                     } \
                 } \
                 None => { \
                     let ch = bytes[start] as char; \
                     return Err(if ch.is_ascii() { \
                         format!(\"{}:{}: unexpected character '{}'\", line + 1, col + 1, ch) \
                     } else { \
                         format!(\"{}:{}: unexpected byte 0x{:02x}\", line + 1, col + 1, bytes[start]) \
                     }); \
                 } \
             } \
         } \
         let eof_pos = Position { byte_offset: pos, line, column: col }; \
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


/// B3: Write `accept_alternatives()` — returns all valid `(Token, f64)` pairs for a DFA state.
///
/// For unambiguous states, returns the single primary token with its weight.
/// For multi-accept states, returns all alternatives sorted by weight (best first).
/// Non-accepting states return an empty Vec.
///
/// Used by `lex_lattice_core()` to construct `TokenLattice` at ambiguous positions.
fn write_accept_alternatives(buf: &mut String, dfa: &Dfa, custom_tokens: &[CustomTokenSpec]) {
    use std::fmt::Write;

    buf.push_str("fn accept_alternatives<'a>(state: u32, text: &'a str) -> Vec<(Token<'a>, f64)> {");
    buf.push_str("match state {");

    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(ref primary_kind) = state.accept {
            if state.alt_accepts.is_empty() {
                // Unambiguous: single alternative
                let primary_variant = token_kind_to_constructor(primary_kind, "text", custom_tokens);
                write!(
                    buf,
                    "{}u32 => vec![({}, {:.1}_f64)],",
                    state_idx,
                    primary_variant,
                    state.weight.value()
                )
                .unwrap();
            } else {
                // Multi-accept: primary + alternatives
                write!(buf, "{}u32 => vec![", state_idx).unwrap();
                // Primary first (best weight)
                let primary_variant = token_kind_to_constructor(primary_kind, "text", custom_tokens);
                write!(buf, "({}, {:.1}_f64),", primary_variant, state.weight.value()).unwrap();
                // Alternatives
                for (alt_kind, alt_weight) in &state.alt_accepts {
                    let alt_variant = token_kind_to_constructor(alt_kind, "text", custom_tokens);
                    write!(buf, "({}, {:.1}_f64),", alt_variant, alt_weight.value()).unwrap();
                }
                buf.push_str("],");
            }
        }
    }

    buf.push_str("_ => Vec::new() } }");
}

/// Convert a TokenKind enum variant to its Rust `Token` constructor expression.
fn token_kind_to_constructor(kind: &TokenKind, text_var: &str, custom_tokens: &[CustomTokenSpec]) -> String {
    match kind {
        TokenKind::Eof => "Token::Eof".to_string(),
        TokenKind::Ident => format!("Token::Ident({})", text_var),
        TokenKind::Integer => format!(
            "Token::Integer({}.parse::<i64>().expect(\"invalid integer literal\"))",
            text_var
        ),
        TokenKind::Float => format!(
            "Token::Float({}.parse::<f64>().expect(\"invalid float literal\"))",
            text_var
        ),
        TokenKind::True => "Token::Boolean(true)".to_string(),
        TokenKind::False => "Token::Boolean(false)".to_string(),
        TokenKind::StringLit => format!("Token::StringLit(&{}[1..{}.len()-1])", text_var, text_var),
        TokenKind::Dollar => format!("Token::Dollar(&{}[1..])", text_var),
        TokenKind::DoubleDollar => format!(
            "Token::DoubleDollar(&{}[2..{}.len()-1])",
            text_var, text_var
        ),
        TokenKind::Fixed(terminal) => {
            let variant = terminal_to_variant_name(terminal);
            format!("Token::{}", variant)
        }
        TokenKind::Custom(name) => {
            if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
                if let Some(ref code) = spec.constructor_code {
                    format!("Token::{}({{ let text = {}; {} }})", name, text_var, code)
                } else if let Some(ref pt) = spec.payload_type {
                    if pt == "str" {
                        format!("Token::{}({})", name, text_var)
                    } else {
                        format!("Token::{}({}.parse::<{}>().expect(\"invalid {} literal\"))", name, text_var, pt, name)
                    }
                } else {
                    format!("Token::{}", name)
                }
            } else {
                format!("Token::{}", name)
            }
        }
    }
}

/// B3: Write `lex_lattice()`/`lex_lattice_with_file_id()` that delegate to
/// `mettail_prattail::runtime_types::lex_lattice_core()`.
///
/// Returns `TokenSource<Token, Range>` — either `Linear` (no ambiguity) or
/// `Lattice` (ambiguous positions detected). The Eof token is appended to the
/// Linear path; for the Lattice path, Eof is not added (lattice nodes represent
/// inter-token positions, not tokens themselves).
fn write_lex_lattice_via_core(buf: &mut String) {
    buf.push_str(
        "pub fn lex_lattice<'a>(input: &'a str) \
         -> Result<(mettail_prattail::lattice::TokenSource<Token<'a>, Range>, Range), String> { \
         lex_lattice_with_file_id(input, None) \
         }\n\
         pub fn lex_lattice_with_file_id<'a>(input: &'a str, file_id: Option<u32>) \
         -> Result<(mettail_prattail::lattice::TokenSource<Token<'a>, Range>, Range), String> { \
         let (source, eof_pos) = mettail_prattail::runtime_types::lex_lattice_core( \
         input, file_id, &CHAR_CLASS, dfa_next, is_accepting_state, accept_alternatives)?; \
         let eof_range = Range { start: eof_pos, end: eof_pos, file_id }; \
         match source { \
         mettail_prattail::lattice::TokenSource::Linear(mut tokens) => { \
             tokens.push((Token::Eof, eof_range)); \
             Ok((mettail_prattail::lattice::TokenSource::Linear(tokens), eof_range)) \
         } \
         lattice => Ok((lattice, eof_range)) \
         } }",
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
    /// AL02: Hybrid direct-coded + compressed lexer.
    ///
    /// Hot states (BFS depth ≤ 2 from start) get direct-coded match arms;
    /// cold states use the best compressed table (comb or bitmap).
    /// Only activated for DFAs with > 30 states when `hybrid_lexer` gate is true.
    HybridDirectCompressed,
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

// ══════════════════════════════════════════════════════════════════════════════
// AL05: Multi-byte chain transitions
// ══════════════════════════════════════════════════════════════════════════════

/// A chain of DFA states connected by single-byte transitions.
///
/// Represents a linear path `S0 -[b0]-> S1 -[b1]-> S2 -[b2]-> S3` where each
/// intermediate state has exactly one non-DEAD transition and is NOT an accept
/// state. The chain can be collapsed into a single multi-byte comparison in
/// generated code, avoiding per-byte DFA table lookups.
///
/// ## Invariants
///
/// - `bytes.len() == chain_len` (number of transitions in the chain)
/// - `chain_len >= 3` (shorter chains are not worth the overhead)
/// - `start_state` is the first state in the chain (before the first byte)
/// - `end_state` is the final state (after consuming all bytes)
/// - All intermediate states (between start and end) are non-accepting
/// - Each intermediate state has exactly one non-DEAD outgoing transition
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiByteChain {
    /// The DFA state where the chain begins.
    pub start_state: StateId,
    /// The DFA state after consuming all chain bytes.
    pub end_state: StateId,
    /// The sequence of concrete byte values consumed along the chain.
    pub bytes: Vec<u8>,
}

impl MultiByteChain {
    /// Number of transitions (bytes) in this chain.
    #[inline]
    pub fn chain_len(&self) -> usize {
        self.bytes.len()
    }
}

/// Detect linear chains of single-byte transitions in a minimized DFA.
///
/// ## Algorithm
///
/// 1. Build an inverse map from equivalence class IDs to the set of bytes that
///    map to that class. Only classes that map to a single byte (singleton classes)
///    can participate in chains, because the generated multi-byte comparison checks
///    concrete byte values.
///
/// 2. For each DFA state, determine if it is a "chain-eligible" state: it has
///    exactly one non-DEAD transition, that transition's class is a singleton class,
///    and the state is NOT an accept state.
///
/// 3. Starting from each non-chain-eligible state (potential chain root), follow
///    outgoing transitions through consecutive chain-eligible states to build
///    chains. Only chains of length >= 3 are emitted.
///
/// ## Longest-match preservation
///
/// Accept states CANNOT appear as intermediate chain states because skipping them
/// would violate the longest-match lexer semantics — the lexer must record each
/// accept state it passes through. Accept states CAN appear as the `end_state`
/// (final state after consuming all chain bytes).
///
/// ## Parameters
///
/// - `dfa`: The minimized DFA to analyze.
/// - `partition`: The alphabet partition, used to map equivalence classes back to
///   concrete byte values.
///
/// ## Returns
///
/// A vector of [`MultiByteChain`]s, each with `chain_len >= 3`. The chains are
/// non-overlapping (each intermediate state appears in at most one chain).
pub fn detect_multi_byte_chains(dfa: &Dfa, partition: &AlphabetPartition) -> Vec<MultiByteChain> {
    let num_states = dfa.states.len();
    if num_states < 4 {
        return Vec::new(); // Need at least 4 states for a chain of length 3
    }

    // Step 1: Build class → singleton byte map.
    // class_to_byte[c] = Some(byte) if exactly one byte maps to class c.
    let mut class_byte_count: Vec<(u16, u8)> = vec![(0, 0); partition.num_classes];
    for byte in 0u8..=255 {
        let class = partition.byte_to_class[byte as usize] as usize;
        if class < class_byte_count.len() {
            class_byte_count[class].0 += 1;
            class_byte_count[class].1 = byte;
        }
    }
    let class_to_singleton: Vec<Option<u8>> = class_byte_count
        .iter()
        .map(|&(count, byte)| if count == 1 { Some(byte) } else { None })
        .collect();

    // Step 2: Classify each state.
    // chain_eligible[s] = Some((singleton_byte, target_state)) if state s has
    // exactly one non-DEAD transition on a singleton class and is NOT accepting.
    let mut chain_eligible: Vec<Option<(u8, StateId)>> = Vec::with_capacity(num_states);
    for state in &dfa.states {
        if state.accept.is_some() {
            // Accept states cannot be intermediate chain states
            chain_eligible.push(None);
            continue;
        }

        let mut live_count = 0usize;
        let mut single_byte = None;
        let mut single_target = DEAD_STATE;

        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                live_count += 1;
                if live_count > 1 {
                    break;
                }
                if let Some(byte) = class_to_singleton.get(class_id).copied().flatten() {
                    single_byte = Some(byte);
                    single_target = target;
                }
            }
        }

        if live_count == 1 && single_byte.is_some() {
            chain_eligible.push(Some((single_byte.expect("checked above"), single_target)));
        } else {
            chain_eligible.push(None);
        }
    }

    // Step 3: Build chains. Track which states have been consumed as intermediates.
    let mut used_as_intermediate = vec![false; num_states];
    let mut chains: Vec<MultiByteChain> = Vec::new();

    // For every state, try to extend a chain through chain-eligible successors.
    // We start chains from transitions out of non-chain-eligible states (or the
    // start state) to avoid double-counting.
    for state_idx in 0..num_states {
        let state = &dfa.states[state_idx];
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target == DEAD_STATE {
                continue;
            }
            let target_idx = target as usize;
            if target_idx >= num_states || used_as_intermediate[target_idx] {
                continue;
            }

            // The target must be chain-eligible to start building a chain
            if chain_eligible[target_idx].is_none() {
                continue;
            }

            // Check if the first transition is on a singleton class
            let first_byte = match class_to_singleton.get(class_id).copied().flatten() {
                Some(b) => b,
                None => continue,
            };

            // Build the chain: start from state_idx, first byte transitions to target_idx,
            // then follow chain-eligible states.
            let mut bytes = vec![first_byte];
            let mut current = target_idx;

            while let Some(&Some((byte, next_target))) = chain_eligible.get(current) {
                let next_idx = next_target as usize;
                if next_idx >= num_states || used_as_intermediate[next_idx] {
                    break;
                }
                bytes.push(byte);
                // If the next target is also chain-eligible and not used, continue
                // But if the next target is NOT chain-eligible, we still add the byte
                // (the chain ends at next_target which may or may not be chain-eligible)
                current = next_idx;
                // If the new current is NOT chain-eligible, the chain ends here
                if chain_eligible.get(current).copied().flatten().is_none() {
                    break;
                }
            }

            if bytes.len() >= 3 {
                // Mark all intermediate states as used
                // Intermediate states: follow the chain from target_idx through len-1 steps
                let mut mark_state = target_idx;
                for _ in 0..bytes.len() - 1 {
                    if let Some(&Some((_, next))) = chain_eligible.get(mark_state) {
                        used_as_intermediate[mark_state] = true;
                        mark_state = next as usize;
                    } else {
                        break;
                    }
                }

                chains.push(MultiByteChain {
                    start_state: state_idx as StateId,
                    end_state: current as StateId,
                    bytes,
                });
            }
        }
    }

    chains
}

/// Compress a DFA transition table using row displacement (comb) packing.
///
/// Algorithm:
/// 1. Extract sparse rows: for each state, collect non-DEAD entries as `(class_id, target)`
/// 2. Sort rows by density (densest first) for better packing
/// 3. Greedy offset search: for each row, find smallest offset where no non-default
///    entries collide with previously placed rows
/// 4. Pad NEXT/CHECK to `max(base) + num_classes` to eliminate bounds checking
///
/// See also [`repack_comb_sparse_rows`] for a second-pass optimization (AL01).
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

/// AL01: Repack sparse rows into gaps left by the initial greedy comb compression.
///
/// After `compress_rows_comb` places rows densest-first, the NEXT/CHECK arrays may
/// contain scattered free slots where sparse rows could fit at lower offsets. This
/// second pass finds rows whose current `base` offset exceeds the high-water mark of
/// the densest rows and attempts to relocate them into earlier free slots.
///
/// The result is a smaller NEXT/CHECK array (fewer total entries), which translates
/// directly to less generated static data and better cache utilization at lex time.
///
/// ## Algorithm
///
/// 1. Build a free-slot bitmap from the existing CHECK array (slot is free iff
///    `check[i] == u32::MAX`).
/// 2. Identify "repackable" rows: states whose entries are all at offsets >= some
///    threshold, meaning they were placed late in the greedy pass and landed far
///    into the tail of the arrays.
/// 3. Sort repackable rows by sparsity (fewest entries first) so the easiest fits
///    are tried first.
/// 4. For each repackable row, scan for the earliest offset in the free-slot bitmap
///    where all its entries fit without collision.
/// 5. If a better (lower) offset is found, relocate the row: clear old slots, place
///    at new offset, update `base[state]`.
/// 6. After all relocations, truncate NEXT/CHECK to the new high-water mark + padding.
///
/// This is a pure codegen-time optimization — it does not affect runtime semantics.
/// Gated by `OptimizationGates::comb_repacking`.
pub fn repack_comb_sparse_rows(comb: &mut CombTable, num_classes: usize) {
    let table_len = comb.next.len();
    if table_len == 0 {
        return;
    }

    // Step 1: Build free-slot bitmap from CHECK array.
    let bitmap_words = (table_len + 63) >> 6;
    let mut free_bitmap: Vec<u64> = vec![!0u64; bitmap_words];
    for (i, &check_val) in comb.check.iter().enumerate() {
        if check_val != u32::MAX {
            // Slot is occupied — clear the bit
            free_bitmap[i >> 6] &= !(1u64 << (i & 63));
        }
    }

    // Step 2: Identify repackable rows — any state with at least 1 entry.
    // Collect (state_idx, entries: Vec<(class_id, target)>, current_base).
    let num_states = comb.base.len();
    let mut repackable: Vec<(usize, Vec<(usize, u32)>, u32)> = Vec::new();

    for state_idx in 0..num_states {
        let b = comb.base[state_idx] as usize;
        let mut entries: Vec<(usize, u32)> = Vec::new();
        for class_id in 0..num_classes {
            let idx = b + class_id;
            if idx < comb.check.len() && comb.check[idx] == state_idx as u32 {
                entries.push((class_id, comb.next[idx]));
            }
        }
        if !entries.is_empty() {
            repackable.push((state_idx, entries, comb.base[state_idx]));
        }
    }

    // Step 3: Sort by sparsity (fewest entries first) — sparse rows are easiest to fit.
    repackable.sort_unstable_by_key(|r| r.1.len());

    // Step 4 & 5: Try to relocate each row to a lower offset.
    let mut any_moved = false;
    for (state_idx, entries, current_base) in &repackable {
        let current_base_usize = *current_base as usize;

        // Try offsets from 0 up to (but not including) the current base.
        let first_class = entries[0].0;
        let mut best_offset: Option<usize> = None;

        'd_loop: for d in 0..current_base_usize {
            // Ensure all entries fit within the table
            let max_idx = d + num_classes;
            if max_idx > table_len {
                break;
            }

            // Quick check: first entry's slot must be free
            let first_idx = d + first_class;
            if first_idx >= table_len {
                break;
            }
            let w = first_idx >> 6;
            let b = first_idx & 63;
            if (free_bitmap[w] >> b) & 1 == 0 {
                continue;
            }

            // Check all entries for collision with occupied slots
            for &(class_id, _) in entries.iter().skip(1) {
                let idx = d + class_id;
                if idx >= table_len {
                    continue 'd_loop;
                }
                let w = idx >> 6;
                let b = idx & 63;
                if (free_bitmap[w] >> b) & 1 == 0 {
                    continue 'd_loop;
                }
            }

            best_offset = Some(d);
            break;
        }

        if let Some(new_offset) = best_offset {
            // Clear old slots in CHECK/NEXT and free bitmap
            for &(class_id, _) in entries {
                let old_idx = current_base_usize + class_id;
                comb.next[old_idx] = u32::MAX;
                comb.check[old_idx] = u32::MAX;
                // Mark old slot as free
                free_bitmap[old_idx >> 6] |= 1u64 << (old_idx & 63);
            }

            // Place at new offset
            comb.base[*state_idx] = new_offset as u32;
            for &(class_id, target) in entries {
                let new_idx = new_offset + class_id;
                comb.next[new_idx] = target;
                comb.check[new_idx] = *state_idx as u32;
                // Mark new slot as occupied
                free_bitmap[new_idx >> 6] &= !(1u64 << (new_idx & 63));
            }

            any_moved = true;
        }
    }

    // Step 6: Truncate to new high-water mark if anything moved.
    if any_moved {
        // Find actual high-water: last occupied slot
        let mut new_high_water = 0usize;
        for (i, &check_val) in comb.check.iter().enumerate() {
            if check_val != u32::MAX && i >= new_high_water {
                new_high_water = i + 1;
            }
        }

        // Pad to max(base) + num_classes for bounds-check elimination
        let max_base = comb.base.iter().copied().max().unwrap_or(0) as usize;
        let pad_to = (max_base + num_classes).max(new_high_water);

        if pad_to < comb.next.len() {
            comb.next.truncate(pad_to);
            comb.check.truncate(pad_to);
        }
    }
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
    custom_tokens: &[CustomTokenSpec],
) -> CodegenStrategy {
    let num_classes = partition.num_classes;
    let mut comb = compress_rows_comb(dfa, num_classes);

    // AL01: Repack sparse rows into gaps left by the initial greedy pass.
    // This is always beneficial (smaller tables, better cache utilization)
    // and has negligible codegen-time cost, so it is applied unconditionally.
    repack_comb_sparse_rows(&mut comb, num_classes);

    if num_classes <= 32 {
        let bitmap = build_bitmap_tables(dfa).expect("num_classes verified <= 32");
        if bitmap.total_bytes() <= comb.total_bytes() {
            write_bitmap_driven_lexer(buf, dfa, partition, &bitmap, custom_tokens);
            return CodegenStrategy::BitmapCompressed;
        }
    }

    write_comb_driven_lexer(buf, dfa, partition, &comb, custom_tokens);
    CodegenStrategy::CombCompressed
}

/// Write a complete comb-compressed lexer to a string buffer.
fn write_comb_driven_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
    comb: &CombTable,
    custom_tokens: &[CustomTokenSpec],
) {
    write_class_table(buf, partition);
    write_comb_tables(buf, comb);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // AL05: Detect multi-byte chains and emit chain table + try_chain function.
    let chains = detect_multi_byte_chains(dfa, partition);
    let has_chains = !chains.is_empty();
    if has_chains {
        write_chain_tables(buf, &chains);
    }

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
    write_accept_arms(buf, dfa, custom_tokens);
    buf.push('}');

    // lex()/lex_with_file_id() — chain-aware if chains detected, otherwise via lex_core()
    if has_chains {
        write_lex_with_chains(buf);
    } else {
        write_lex_via_core(buf);
    }

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str("fn accept_weight(state: u32) -> f64 {");
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);

    // B3: Lattice-aware lexing with multi-accept alternatives
    write_accept_alternatives(buf, dfa, custom_tokens);
    write_lex_lattice_via_core(buf);
}

/// Write a complete bitmap-compressed lexer to a string buffer.
fn write_bitmap_driven_lexer(
    buf: &mut String,
    dfa: &Dfa,
    partition: &AlphabetPartition,
    tables: &BitmapTables,
    custom_tokens: &[CustomTokenSpec],
) {
    write_class_table(buf, partition);
    write_bitmap_tables(buf, tables);

    write!(buf, "const NUM_CLASSES: usize = {};", partition.num_classes).unwrap();

    // IS_ACCEPTING bitmap for O(1) acceptance checks in the inner loop
    write_is_accepting_check(buf, dfa);

    // AL05: Detect multi-byte chains and emit chain table + try_chain function.
    let chains = detect_multi_byte_chains(dfa, partition);
    let has_chains = !chains.is_empty();
    if has_chains {
        write_chain_tables(buf, &chains);
    }

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
    write_accept_arms(buf, dfa, custom_tokens);
    buf.push('}');

    // lex()/lex_with_file_id() — chain-aware if chains detected, otherwise via lex_core()
    if has_chains {
        write_lex_with_chains(buf);
    } else {
        write_lex_via_core(buf);
    }

    // WFST weight emission: accept_weight() + lex_weighted() via lex_weighted_core()
    buf.push_str("fn accept_weight(state: u32) -> f64 {");
    write_accept_weight_arms(buf, dfa);
    buf.push('}');
    write_lex_weighted_via_core(buf);

    // B3: Lattice-aware lexing with multi-accept alternatives
    write_accept_alternatives(buf, dfa, custom_tokens);
    write_lex_lattice_via_core(buf);
}


// ══════════════════════════════════════════════════════════════════════════════
// AL05: Multi-byte chain transition codegen
// ══════════════════════════════════════════════════════════════════════════════

/// Write chain tables and a `try_chain` inline function to the output buffer.
///
/// Emits a `try_chain(state: u32, bytes: &[u8], pos: usize) -> Option<(u32, usize)>`
/// function that, for known chain-start states, checks whether the upcoming bytes
/// match the chain pattern. If so, returns `(end_state, bytes_consumed)`.
///
/// The generated function uses a match on the start state to dispatch to the
/// correct chain, then performs a slice equality check for the chain bytes.
/// This eliminates N individual DFA table lookups (one per chain byte) and
/// replaces them with a single memcmp-style comparison.
///
/// ## Generated Code Shape
///
/// ```text
/// #[inline(always)]
/// fn try_chain(state: u32, bytes: &[u8], pos: usize) -> Option<(u32, usize)> {
///     match state {
///         0u32 => {
///             if pos + 5 <= bytes.len() && bytes[pos..pos+5] == [101,114,114,111,114] {
///                 return Some((7u32, 5));
///             }
///             None
///         }
///         _ => None,
///     }
/// }
/// ```
fn write_chain_tables(buf: &mut String, chains: &[MultiByteChain]) {
    if chains.is_empty() {
        return;
    }

    buf.push_str(
        "#[inline(always)] fn try_chain(state: u32, bytes: &[u8], pos: usize) -> Option<(u32, usize)> { \
         match state {"
    );

    // Group chains by start state (a state may have multiple outgoing chains
    // via different initial bytes, though this is rare).
    let mut chains_by_start: std::collections::BTreeMap<StateId, Vec<&MultiByteChain>> =
        std::collections::BTreeMap::new();
    for chain in chains {
        chains_by_start
            .entry(chain.start_state)
            .or_default()
            .push(chain);
    }

    for (start_state, state_chains) in &chains_by_start {
        write!(buf, "{}u32 => {{", start_state).unwrap();

        // Sort chains longest-first for greedy matching (longest match wins)
        let mut sorted_chains: Vec<&&MultiByteChain> = state_chains.iter().collect();
        sorted_chains.sort_unstable_by(|a, b| b.chain_len().cmp(&a.chain_len()));

        for chain in sorted_chains {
            let len = chain.chain_len();
            write!(buf, "if pos + {} <= bytes.len() && ", len).unwrap();

            // Emit byte comparison. For short chains (3-4 bytes), use individual
            // comparisons to help the compiler optimize. For longer chains, use
            // slice equality which compiles to memcmp.
            if len <= 4 {
                for (i, &byte) in chain.bytes.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(" && ");
                    }
                    write!(buf, "bytes[pos + {}] == {}u8", i, byte).unwrap();
                }
            } else {
                write!(buf, "bytes[pos..pos + {}] == [", len).unwrap();
                for (i, &byte) in chain.bytes.iter().enumerate() {
                    if i > 0 {
                        buf.push(',');
                    }
                    write!(buf, "{}u8", byte).unwrap();
                }
                buf.push(']');
            }

            write!(buf, " {{ return Some(({}u32, {})); }}", chain.end_state, len).unwrap();
        }

        buf.push_str("None },");
    }

    buf.push_str("_ => None } }");
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

/// BP03: Write a `token_variant_id()` helper function that maps each Token variant
/// to a compact `u8` ordinal, suitable for indexing into static BP arrays.
///
/// The ordinal assignment mirrors [`TokenVariantMap::from_token_kinds`] so the
/// generated code and the compile-time analysis use the same mapping.
///
/// Generated function signature:
/// ```rust,ignore
/// fn token_variant_id(token: &Token) -> u8
/// ```
///
/// Data-carrying variants (Ident, Integer, Float, Boolean, StringLit, Dollar,
/// DoubleDollar) use wildcard patterns (e.g., `Token::Ident(_) => 1`).
/// Unit variants (Eof, Plus, Star, etc.) match directly.
pub fn write_token_variant_id(buf: &mut String, variant_map: &TokenVariantMap) {
    use std::fmt::Write as _;

    buf.push_str(
        "/// Map a Token variant to a compact ordinal for BP array indexing.\n\
         #[inline(always)]\n\
         fn token_variant_id(token: &Token) -> u8 { match token {"
    );

    /// Data-carrying token variants that need wildcard patterns.
    const DATA_VARIANTS: &[&str] = &[
        "Ident", "Integer", "Float", "Boolean", "StringLit", "Dollar", "DoubleDollar",
    ];

    for (id, name) in variant_map.id_to_name.iter().enumerate() {
        if DATA_VARIANTS.contains(&name.as_str()) {
            write!(buf, "Token::{}(_) => {},", name, id).unwrap();
        } else {
            write!(buf, "Token::{} => {},", name, id).unwrap();
        }
    }

    buf.push_str("} }");
}

// ══════════════════════════════════════════════════════════════════════════════
// AL04: Keyword recognition via minimal perfect hashing
// ══════════════════════════════════════════════════════════════════════════════

/// Generate MPH keyword lookup tables and write them into the codegen buffer.
///
/// Extracts keyword-like terminals from the terminal patterns, builds a CHD
/// minimal perfect hash table, and emits the generated Rust constants and
/// `mph_probe()` function into `buf`.
///
/// This function is gated on the `AL04_KeywordMph` optimization: callers
/// should check `OptimizationGates::keyword_mph` before invoking.
///
/// Returns `true` if MPH tables were emitted (at least one keyword found),
/// `false` otherwise.
pub fn write_mph_keyword_tables(
    buf: &mut String,
    terminals: &[super::TerminalPattern],
) -> bool {
    match super::mph::build_mph_from_terminals(terminals) {
        Some(table) => {
            super::mph::write_mph_tables(buf, &table);
            true
        }
        None => {
            // No keywords found; emit a trivial probe that always returns None
            // so downstream code can call mph_probe() unconditionally.
            let empty = super::mph::MphTable::build(&[]);
            super::mph::write_mph_tables(buf, &empty);
            false
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sprint 5: WPDS Modal Lexing — multi-mode DFA codegen with mode stack dispatch
// ══════════════════════════════════════════════════════════════════════════════

/// Write the equivalence class table with a suffixed static name.
///
/// Emits `static CHAR_CLASS_{SUFFIX}: [u8; 256] = [...]` for the given partition.
fn write_class_table_suffixed(buf: &mut String, partition: &AlphabetPartition, suffix: &str) {
    write!(buf, "static CHAR_CLASS_{}: [u8; 256] = [", suffix).unwrap();
    for (i, &class) in partition.byte_to_class.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", class).unwrap();
    }
    buf.push_str("];");
}

/// Write a suffixed IS_ACCEPTING bitmap and inline check function.
///
/// Emits:
/// - `static IS_ACCEPTING_{SUFFIX}: [u64; K] = [...]`
/// - `fn is_accepting_state_{suffix}(state: u32) -> bool`
fn write_is_accepting_suffixed(buf: &mut String, dfa: &Dfa, suffix: &str) {
    let n = dfa.states.len();
    let num_words = (n + 63) / 64;

    let mut words = vec![0u64; num_words];
    for (i, state) in dfa.states.iter().enumerate() {
        if state.accept.is_some() {
            words[i >> 6] |= 1u64 << (i & 63);
        }
    }

    write!(buf, "static IS_ACCEPTING_{}: [u64; {}] = [", suffix, num_words).unwrap();
    for (i, &w) in words.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "0x{:016x}", w).unwrap();
    }
    buf.push_str("];");

    write!(
        buf,
        "#[inline(always)] fn is_accepting_state_{}(state: u32) -> bool {{ \
         (IS_ACCEPTING_{}[(state >> 6) as usize] >> (state & 63)) & 1 != 0 \
         }}",
        suffix.to_lowercase(),
        suffix
    )
    .unwrap();
}

/// Write a suffixed `dfa_next_{suffix}` transition function.
///
/// Uses match-arm dispatch (direct-coded) for the given DFA's transitions.
fn write_dfa_next_suffixed(buf: &mut String, dfa: &Dfa, suffix: &str) {
    write!(
        buf,
        "fn dfa_next_{}(state: u32, class: u8) -> u32 {{",
        suffix.to_lowercase()
    )
    .unwrap();
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        let has_transitions = state.transitions.iter().any(|&t| t != DEAD_STATE);
        if !has_transitions {
            continue;
        }
        write!(buf, "{}u32 => match class {{", state_idx).unwrap();
        for (class_id, &target) in state.transitions.iter().enumerate() {
            if target != DEAD_STATE {
                write!(buf, "{}u8 => {}u32,", class_id, target).unwrap();
            }
        }
        buf.push_str("_ => u32::MAX },");
    }
    buf.push_str("_ => u32::MAX }");
    buf.push('}');
}

/// Write a suffixed `accept_token_{suffix}` function.
///
/// Maps accepting DFA states to `Token` constructor expressions using
/// the mode-specific custom token specs for payload resolution.
fn write_accept_token_suffixed(
    buf: &mut String,
    dfa: &Dfa,
    custom_tokens: &[CustomTokenSpec],
    suffix: &str,
) {
    write!(
        buf,
        "fn accept_token_{}<'a>(state: u32, text: &'a str) -> Option<Token<'a>> {{",
        suffix.to_lowercase()
    )
    .unwrap();
    buf.push_str("match state {");
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(ref kind) = state.accept {
            write!(buf, "{}u32 => Some(", state_idx).unwrap();
            write_token_constructor(buf, kind, custom_tokens);
            buf.push_str("),");
        }
    }
    buf.push_str("_ => None }");
    buf.push('}');
}

/// Write suffixed `push_target_{suffix}` and `should_pop_{suffix}` functions.
///
/// For each accepting DFA state with a `Custom` token kind, looks up the
/// corresponding `CustomTokenSpec` to determine push/pop mode transitions.
///
/// - `push_target_{suffix}(state) -> u8`: returns the target mode ID if this
///   accept state's custom token has `push_mode`, or `u8::MAX` if no push.
/// - `should_pop_{suffix}(state) -> bool`: returns `true` if this accept state's
///   custom token has `is_pop` set.
fn write_push_pop_tables(
    buf: &mut String,
    dfa: &Dfa,
    custom_tokens: &[CustomTokenSpec],
    mode_results: &[crate::lexer::ModeDfaResult],
    suffix: &str,
) {
    // push_target_{suffix}(state) -> u8
    write!(
        buf,
        "fn push_target_{}(state: u32) -> u8 {{ match state {{",
        suffix.to_lowercase()
    )
    .unwrap();
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(TokenKind::Custom(ref name)) = state.accept {
            if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
                if let Some(ref target_mode) = spec.push_mode {
                    let target_id = if target_mode == "default" {
                        0u8
                    } else {
                        mode_results
                            .iter()
                            .find(|m| m.name == *target_mode)
                            .map(|m| m.mode_id)
                            .unwrap_or(0)
                    };
                    write!(buf, "{}u32 => {}u8,", state_idx, target_id).unwrap();
                }
            }
        }
    }
    buf.push_str("_ => u8::MAX } }");

    // should_pop_{suffix}(state) -> bool
    write!(
        buf,
        "fn should_pop_{}(state: u32) -> bool {{ match state {{",
        suffix.to_lowercase()
    )
    .unwrap();
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(TokenKind::Custom(ref name)) = state.accept {
            if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
                if spec.is_pop {
                    write!(buf, "{}u32 => true,", state_idx).unwrap();
                }
            }
        }
    }
    buf.push_str("_ => false } }");
}

/// Write the modal lex loop: `lex()` and `lex_with_file_id()` with mode stack dispatch.
///
/// The generated code maintains a `Vec<u8>` mode stack initialized to `[0]` (MODE_DEFAULT).
/// On each token, the active mode's DFA tables are selected via a `match` on the top of
/// the mode stack. After accepting a token, push/pop actions are applied to the stack.
fn write_modal_lex_functions(
    buf: &mut String,
    mode_results: &[crate::lexer::ModeDfaResult],
) {
    // lex() delegates to lex_with_file_id()
    buf.push_str(
        "pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Range)>, String> { \
         lex_with_file_id(input, None) \
         }"
    );

    // lex_with_file_id() — main modal lexer
    buf.push_str(
        "pub fn lex_with_file_id<'a>(input: &'a str, file_id: Option<u32>) \
         -> Result<Vec<(Token<'a>, Range)>, String> {"
    );
    buf.push_str("let bytes = input.as_bytes();");
    buf.push_str("let mut pos: usize = 0;");
    buf.push_str("let mut line: usize = 0;");
    buf.push_str("let mut col: usize = 0;");
    buf.push_str("let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2);");
    buf.push_str("let mut mode_stack: Vec<u8> = vec![0u8];");

    // Main lexer loop
    buf.push_str("while pos < bytes.len() {");

    // Whitespace skip (ASCII fast path + Unicode fallback)
    buf.push_str(
        "let b = bytes[pos]; \
         if b == b' ' || b == b'\\t' || b == b'\\r' { pos += 1; col += 1; continue; } \
         if b == b'\\n' { pos += 1; line += 1; col = 0; continue; } \
         if b >= 0x80 { \
            let rest = &input[pos..]; \
            if let Some(ch) = rest.chars().next() { \
                if ch.is_whitespace() { \
                    let ch_len = ch.len_utf8(); \
                    if ch == '\\u{2028}' || ch == '\\u{2029}' { line += 1; col = 0; } \
                    else { col += 1; } \
                    pos += ch_len; continue; \
                } \
            } \
         }"
    );

    // Read current mode and set up DFA walk
    buf.push_str("let mode = *mode_stack.last().expect(\"mode stack empty\");");
    buf.push_str("let start_pos = pos; let start_line = line; let start_col = col;");
    buf.push_str("let mut state: u32 = 0;");
    buf.push_str("let mut last_accept: Option<(u32, usize, usize, usize)> = None;");

    // Check if initial state (0) is accepting for the active mode
    buf.push_str("let is_acc_init = match mode {");
    buf.push_str("0u8 => is_accepting_state_default(0),");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => is_accepting_state_{}(0),",
            mode.mode_id,
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => false };");
    buf.push_str("if is_acc_init { last_accept = Some((0, pos, line, col)); }");

    // DFA walk loop
    buf.push_str("while pos < bytes.len() {");
    buf.push_str("let b = bytes[pos];");

    // Mode-dispatched DFA transition
    buf.push_str("let next_state = match mode {");
    buf.push_str("0u8 => { let class = CHAR_CLASS_DEFAULT[b as usize]; dfa_next_default(state, class) }");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => {{ let class = CHAR_CLASS_{}[b as usize]; dfa_next_{}(state, class) }}",
            mode.mode_id,
            mode.name.to_uppercase(),
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => u32::MAX };");

    buf.push_str("if next_state == u32::MAX { break; }");
    buf.push_str("state = next_state;");

    // Line/col tracking
    buf.push_str("if b == b'\\n' { line += 1; col = 0; } else { col += 1; }");
    buf.push_str("pos += 1;");

    // Check if new state is accepting
    buf.push_str("let is_acc = match mode {");
    buf.push_str("0u8 => is_accepting_state_default(state),");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => is_accepting_state_{}(state),",
            mode.mode_id,
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => false };");
    buf.push_str("if is_acc { last_accept = Some((state, pos, line, col)); }");

    buf.push_str("}"); // end DFA walk loop

    // Process accept result
    buf.push_str("match last_accept {");
    buf.push_str("Some((accept_state, end, end_line, end_col)) => {");
    buf.push_str("pos = end; line = end_line; col = end_col;");
    buf.push_str("let text = &input[start_pos..end];");

    // Get token from mode-specific accept function
    buf.push_str("let token_opt = match mode {");
    buf.push_str("0u8 => accept_token_default(accept_state, text),");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => accept_token_{}(accept_state, text),",
            mode.mode_id,
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => None };");

    buf.push_str("if let Some(token) = token_opt {");

    // Get push/pop actions
    buf.push_str("let push_target = match mode {");
    buf.push_str("0u8 => push_target_default(accept_state),");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => push_target_{}(accept_state),",
            mode.mode_id,
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => u8::MAX };");

    buf.push_str("let do_pop = match mode {");
    buf.push_str("0u8 => should_pop_default(accept_state),");
    for mode in mode_results {
        write!(
            buf,
            "{}u8 => should_pop_{}(accept_state),",
            mode.mode_id,
            mode.name.to_lowercase()
        )
        .unwrap();
    }
    buf.push_str("_ => false };");

    // Emit token with range
    buf.push_str(
        "tokens.push((token, Range { \
         start: Position { byte_offset: start_pos, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id }));"
    );

    // Execute push/pop transitions
    buf.push_str("if push_target != u8::MAX { mode_stack.push(push_target); }");
    buf.push_str("if do_pop { mode_stack.pop(); if mode_stack.is_empty() { mode_stack.push(0u8); } }");

    buf.push_str("}"); // end if let Some(token)
    buf.push_str("}"); // end Some(...)

    // Error case: no accept found
    buf.push_str("None => {");
    buf.push_str("let rest = &input[pos..];");
    buf.push_str("let bad_char = rest.chars().next().unwrap_or('?');");
    buf.push_str(
        "return Err(format!(\"unexpected character '{}' at line {}:{}\", bad_char, line + 1, col + 1));"
    );
    buf.push_str("}"); // end None
    buf.push_str("}"); // end match last_accept

    buf.push_str("}"); // end while pos < bytes.len()

    // Eof token
    buf.push_str("let eof_pos = Position { byte_offset: pos, line, column: col };");
    buf.push_str(
        "tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }));"
    );
    buf.push_str("Ok(tokens)");
    buf.push_str("}"); // end fn lex_with_file_id
}

/// Write stream routing table for a single mode.
///
/// Emits `fn stream_id_{suffix}(state: u32) -> u8` that returns the stream index
/// for each accepting state. Stream 0 = "main" (default), 1+ = named streams.
fn write_stream_tables(
    buf: &mut String,
    dfa: &Dfa,
    custom_tokens: &[CustomTokenSpec],
    stream_names: &[String],
    suffix: &str,
) {
    write!(
        buf,
        "fn stream_id_{}(state: u32) -> u8 {{ match state {{",
        suffix.to_lowercase()
    )
    .unwrap();
    for (state_idx, state) in dfa.states.iter().enumerate() {
        if let Some(TokenKind::Custom(ref name)) = state.accept {
            if let Some(spec) = custom_tokens.iter().find(|s| s.name == *name) {
                if let Some(ref stream) = spec.stream {
                    if stream != "main" {
                        if let Some(idx) = stream_names.iter().position(|s| s == stream) {
                            write!(buf, "{}u32 => {}u8,", state_idx, idx + 1).unwrap();
                        }
                    }
                }
            }
        }
    }
    buf.push_str("_ => 0u8 } }");
}

/// Write `lex_with_streams()` / `lex_streams_with_file_id()` that return multi-stream results.
///
/// These functions are only generated when at least one custom token has a `-> stream`
/// annotation. They return the main token stream plus a `HashMap` of auxiliary streams.
/// The `lex()` function continues to return only the main stream for backward compatibility.
fn write_modal_lex_with_streams(
    buf: &mut String,
    mode_results: &[crate::lexer::ModeDfaResult],
) {
    buf.push_str("pub fn lex_with_streams<'a>(input: &'a str) -> Result<mettail_prattail::LexResult<Token<'a>>, String> { lex_streams_with_file_id(input, None) }");

    buf.push_str(
        "pub fn lex_streams_with_file_id<'a>(input: &'a str, file_id: Option<u32>) \
         -> Result<mettail_prattail::LexResult<Token<'a>>, String> {"
    );
    buf.push_str("let bytes = input.as_bytes();");
    buf.push_str("let mut pos: usize = 0;");
    buf.push_str("let mut line: usize = 0;");
    buf.push_str("let mut col: usize = 0;");
    buf.push_str("let mut tokens: Vec<(Token<'a>, Range)> = Vec::with_capacity(input.len() / 2);");
    buf.push_str("let mut streams: std::collections::HashMap<String, Vec<(Token<'a>, Range)>> = std::collections::HashMap::new();");
    buf.push_str("let mut mode_stack: Vec<u8> = vec![0u8];");

    // Same loop structure as write_modal_lex_functions but with stream routing
    buf.push_str("while pos < bytes.len() {");

    // Whitespace skip
    buf.push_str(
        "let b = bytes[pos]; \
         if b == b' ' || b == b'\\t' || b == b'\\r' { pos += 1; col += 1; continue; } \
         if b == b'\\n' { pos += 1; line += 1; col = 0; continue; } \
         if b >= 0x80 { \
            let rest = &input[pos..]; \
            if let Some(ch) = rest.chars().next() { \
                if ch.is_whitespace() { \
                    let ch_len = ch.len_utf8(); \
                    if ch == '\\u{2028}' || ch == '\\u{2029}' { line += 1; col = 0; } \
                    else { col += 1; } \
                    pos += ch_len; continue; \
                } \
            } \
         }"
    );

    buf.push_str("let mode = *mode_stack.last().expect(\"mode stack empty\");");
    buf.push_str("let start_pos = pos; let start_line = line; let start_col = col;");
    buf.push_str("let mut state: u32 = 0;");
    buf.push_str("let mut last_accept: Option<(u32, usize, usize, usize)> = None;");

    // Initial state acceptance check
    buf.push_str("let is_acc_init = match mode {");
    buf.push_str("0u8 => is_accepting_state_default(0),");
    for mode in mode_results {
        write!(buf, "{}u8 => is_accepting_state_{}(0),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => false };");
    buf.push_str("if is_acc_init { last_accept = Some((0, pos, line, col)); }");

    // DFA walk
    buf.push_str("while pos < bytes.len() {");
    buf.push_str("let b = bytes[pos];");
    buf.push_str("let next_state = match mode {");
    buf.push_str("0u8 => { let class = CHAR_CLASS_DEFAULT[b as usize]; dfa_next_default(state, class) }");
    for mode in mode_results {
        write!(buf, "{}u8 => {{ let class = CHAR_CLASS_{}[b as usize]; dfa_next_{}(state, class) }}",
               mode.mode_id, mode.name.to_uppercase(), mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => u32::MAX };");
    buf.push_str("if next_state == u32::MAX { break; }");
    buf.push_str("state = next_state;");
    buf.push_str("if b == b'\\n' { line += 1; col = 0; } else { col += 1; }");
    buf.push_str("pos += 1;");

    // Accept check
    buf.push_str("let is_acc = match mode {");
    buf.push_str("0u8 => is_accepting_state_default(state),");
    for mode in mode_results {
        write!(buf, "{}u8 => is_accepting_state_{}(state),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => false };");
    buf.push_str("if is_acc { last_accept = Some((state, pos, line, col)); }");
    buf.push_str("}"); // end DFA walk

    // Process accept
    buf.push_str("match last_accept {");
    buf.push_str("Some((accept_state, end, end_line, end_col)) => {");
    buf.push_str("pos = end; line = end_line; col = end_col;");
    buf.push_str("let text = &input[start_pos..end];");

    // Token from mode
    buf.push_str("let token_opt = match mode {");
    buf.push_str("0u8 => accept_token_default(accept_state, text),");
    for mode in mode_results {
        write!(buf, "{}u8 => accept_token_{}(accept_state, text),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => None };");

    buf.push_str("if let Some(token) = token_opt {");

    // Push/pop
    buf.push_str("let push_target = match mode {");
    buf.push_str("0u8 => push_target_default(accept_state),");
    for mode in mode_results {
        write!(buf, "{}u8 => push_target_{}(accept_state),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => u8::MAX };");

    buf.push_str("let do_pop = match mode {");
    buf.push_str("0u8 => should_pop_default(accept_state),");
    for mode in mode_results {
        write!(buf, "{}u8 => should_pop_{}(accept_state),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => false };");

    // Stream routing — the key difference from the main lex loop
    buf.push_str("let stream_id = match mode {");
    buf.push_str("0u8 => stream_id_default(accept_state),");
    for mode in mode_results {
        write!(buf, "{}u8 => stream_id_{}(accept_state),", mode.mode_id, mode.name.to_lowercase()).unwrap();
    }
    buf.push_str("_ => 0u8 };");

    buf.push_str(
        "let range = Range { \
         start: Position { byte_offset: start_pos, line: start_line, column: start_col }, \
         end: Position { byte_offset: end, line: end_line, column: end_col }, \
         file_id };"
    );
    buf.push_str(
        "if stream_id == 0 { tokens.push((token, range)); } \
         else { streams.entry(STREAM_NAMES[stream_id as usize].to_string()).or_default().push((token, range)); }"
    );

    // Execute push/pop
    buf.push_str("if push_target != u8::MAX { mode_stack.push(push_target); }");
    buf.push_str("if do_pop { mode_stack.pop(); if mode_stack.is_empty() { mode_stack.push(0u8); } }");

    buf.push_str("}"); // end if let Some(token)
    buf.push_str("}"); // end Some(...)

    // Error
    buf.push_str("None => {");
    buf.push_str("let rest = &input[pos..];");
    buf.push_str("let bad_char = rest.chars().next().unwrap_or('?');");
    buf.push_str("return Err(format!(\"unexpected character '{}' at line {}:{}\", bad_char, line + 1, col + 1));");
    buf.push_str("}");
    buf.push_str("}"); // end match

    buf.push_str("}"); // end while

    // Eof
    buf.push_str("let eof_pos = Position { byte_offset: pos, line, column: col };");
    buf.push_str("tokens.push((Token::Eof, Range { start: eof_pos, end: eof_pos, file_id }));");
    buf.push_str("Ok(mettail_prattail::LexResult { tokens, streams })");
    buf.push_str("}"); // end fn
}

/// Generate a complete modal lexer with per-mode DFA tables and mode stack dispatch.
///
/// Called when the grammar has named lexer modes (`mode name { ... }` blocks).
/// The default mode's DFA handles grammar terminals + default-mode custom tokens.
/// Each named mode gets its own DFA containing only its declared token patterns.
/// The generated lex loop maintains a `Vec<u8>` mode stack and dispatches to the
/// active mode's DFA tables.
///
/// # Generated code structure
///
/// 1. **Token enum** (shared across all modes) — merged token kinds + all custom tokens
/// 2. **Token display** — `format_token_friendly()` for merged token kinds
/// 3. **Runtime types import** — `use mettail_prattail::runtime_types::*;`
/// 4. **Mode constants** — `const MODE_DEFAULT: u8 = 0;`, etc.
/// 5. **Per-mode DFA tables** — suffixed `CHAR_CLASS_{MODE}`, `IS_ACCEPTING_{MODE}`,
///    `dfa_next_{mode}`, `accept_token_{mode}`, `is_accepting_state_{mode}`
/// 6. **Push/pop action tables** — per-mode `push_target_{mode}`, `should_pop_{mode}`
/// 7. **Modal lex loop** — mode-dispatched `lex()` / `lex_with_file_id()`
pub fn generate_modal_lexer_string(
    default_dfa: &Dfa,
    default_partition: &AlphabetPartition,
    default_token_kinds: &[TokenKind],
    mode_results: &[crate::lexer::ModeDfaResult],
    _language_name: &str,
    default_custom_tokens: &[CustomTokenSpec],
    all_custom_tokens: &[CustomTokenSpec],
) -> String {
    let estimated_size = 8192 + (mode_results.len() + 1) * 4096;
    let mut buf = String::with_capacity(estimated_size);

    // 1. Merge all token kinds for the shared Token enum.
    //    The default mode's token kinds come first, then each named mode's
    //    token kinds are appended. Deduplication is handled by write_token_enum
    //    via its internal `seen` set.
    let mut all_token_kinds = default_token_kinds.to_vec();
    for mode in mode_results {
        all_token_kinds.extend(mode.token_kinds.iter().cloned());
    }

    // 2. Write Token enum + display (shared across all modes)
    write_token_enum(&mut buf, &all_token_kinds, all_custom_tokens);
    write_token_display(&mut buf, &all_token_kinds, all_custom_tokens);
    write_runtime_types_import(&mut buf);

    // 3. Mode constants
    buf.push_str("const MODE_DEFAULT: u8 = 0;");
    for mode in mode_results {
        write!(
            buf,
            "const MODE_{}: u8 = {};",
            mode.name.to_uppercase(),
            mode.mode_id
        )
        .unwrap();
    }

    // 4. Default mode DFA tables
    write_class_table_suffixed(&mut buf, default_partition, "DEFAULT");
    write_is_accepting_suffixed(&mut buf, default_dfa, "DEFAULT");
    write_dfa_next_suffixed(&mut buf, default_dfa, "DEFAULT");
    write_accept_token_suffixed(&mut buf, default_dfa, default_custom_tokens, "DEFAULT");
    write_push_pop_tables(
        &mut buf,
        default_dfa,
        default_custom_tokens,
        mode_results,
        "DEFAULT",
    );

    // 5. Named mode DFA tables
    for mode in mode_results {
        let suffix = mode.name.to_uppercase();
        write_class_table_suffixed(&mut buf, &mode.partition, &suffix);
        write_is_accepting_suffixed(&mut buf, &mode.min_dfa, &suffix);
        write_dfa_next_suffixed(&mut buf, &mode.min_dfa, &suffix);
        write_accept_token_suffixed(&mut buf, &mode.min_dfa, &mode.custom_tokens, &suffix);
        write_push_pop_tables(
            &mut buf,
            &mode.min_dfa,
            &mode.custom_tokens,
            mode_results,
            &suffix,
        );
    }

    // 6. Check if any custom token uses stream routing (-> stream_name)
    let has_streams = all_custom_tokens.iter().any(|s| s.stream.is_some());

    if has_streams {
        // Collect unique stream names (excluding "main" which is the default)
        let mut stream_names: Vec<String> = Vec::new();
        for spec in all_custom_tokens {
            if let Some(ref stream) = spec.stream {
                if stream != "main" && !stream_names.contains(stream) {
                    stream_names.push(stream.clone());
                }
            }
        }

        // Stream ID constants (0 = main, 1+ = named streams)
        for (i, name) in stream_names.iter().enumerate() {
            write!(buf, "const STREAM_{}: u8 = {};", name.to_uppercase(), i + 1).unwrap();
        }

        // Per-mode stream routing tables
        write_stream_tables(
            &mut buf,
            default_dfa,
            default_custom_tokens,
            &stream_names,
            "DEFAULT",
        );
        for mode in mode_results {
            let suffix = mode.name.to_uppercase();
            write_stream_tables(
                &mut buf,
                &mode.min_dfa,
                &mode.custom_tokens,
                &stream_names,
                &suffix,
            );
        }

        // Generate stream name array for runtime
        write!(buf, "static STREAM_NAMES: [&str; {}] = [\"main\"", stream_names.len() + 1).unwrap();
        for name in &stream_names {
            write!(buf, ",\"{}\"", name).unwrap();
        }
        buf.push_str("];");
    }

    // 7. Modal lex functions (main stream only)
    write_modal_lex_functions(&mut buf, mode_results);

    // 8. If streams are used, add lex_with_streams()
    if has_streams {
        write_modal_lex_with_streams(&mut buf, mode_results);
    }

    buf
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

    #[test]
    fn test_write_token_variant_id() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Fixed("+".to_string()),
            TokenKind::Fixed("-".to_string()),
            TokenKind::Fixed("*".to_string()),
        ];
        let variant_map = TokenVariantMap::from_token_kinds(&token_kinds);

        let mut buf = String::new();
        write_token_variant_id(&mut buf, &variant_map);

        // Should contain the function signature
        assert!(
            buf.contains("fn token_variant_id(token: &Token) -> u8"),
            "should contain function signature, got:\n{}",
            buf
        );

        // Data-carrying variants should use wildcards
        assert!(
            buf.contains("Token::Ident(_)"),
            "Ident should use wildcard pattern, got:\n{}",
            buf
        );
        assert!(
            buf.contains("Token::Integer(_)"),
            "Integer should use wildcard pattern, got:\n{}",
            buf
        );

        // Unit variants should not have wildcards
        assert!(
            buf.contains("Token::Eof =>"),
            "Eof should be a unit pattern, got:\n{}",
            buf
        );
        assert!(
            buf.contains("Token::Plus =>"),
            "Plus should be a unit pattern, got:\n{}",
            buf
        );

        // Should have ordinals for each variant
        // Eof = 0, Ident = 1 (always first two), then sorted: Integer, Minus, Plus, Star
        assert!(
            buf.contains("Token::Eof => 0"),
            "Eof should map to ordinal 0, got:\n{}",
            buf
        );
        assert!(
            buf.contains("Token::Ident(_) => 1"),
            "Ident should map to ordinal 1, got:\n{}",
            buf
        );
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
            generate_lexer_string(&dfa, &partition, &token_kinds, "test", &[]);
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

    // ══════════════════════════════════════════════════════════════════════════
    // A-L06: Accept State Bitmap Widening tests
    // ══════════════════════════════════════════════════════════════════════════

    /// Helper: create a DFA with the given number of states and accept state indices.
    fn make_dfa_with_accepts(num_states: usize, accept_indices: &[usize]) -> Dfa {
        let num_classes = 1;
        let mut dfa = Dfa::new(num_classes);
        // The constructor already adds state 0, so add (num_states - 1) more.
        for _ in 1..num_states {
            dfa.add_state(DfaState::with_classes(num_classes));
        }
        for &idx in accept_indices {
            dfa.states[idx].accept = Some(TokenKind::Ident);
        }
        dfa
    }

    #[test]
    fn test_accept_bitmap_small_dfa() {
        // 5-state DFA, states 1 and 3 accepting
        let dfa = make_dfa_with_accepts(5, &[1, 3]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        // Should produce a single-word bitmap: [u64; 1]
        assert!(buf.contains("static IS_ACCEPTING: [u64; 1]"), "buf = {buf}");
        // Bit 1 and bit 3 set → 0b1010 = 0x000000000000000a
        assert!(buf.contains("0x000000000000000a"), "buf = {buf}");
        // Should contain the bitwise check function
        assert!(buf.contains("(IS_ACCEPTING[(state >> 6) as usize] >> (state & 63)) & 1 != 0"), "buf = {buf}");
    }

    #[test]
    fn test_accept_bitmap_no_accepts() {
        // 3-state DFA, no accepting states
        let dfa = make_dfa_with_accepts(3, &[]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        // Single word, all zeros
        assert!(buf.contains("[u64; 1]"), "buf = {buf}");
        assert!(buf.contains("0x0000000000000000"), "buf = {buf}");
    }

    #[test]
    fn test_accept_bitmap_all_accepts() {
        // 4-state DFA, all accepting
        let dfa = make_dfa_with_accepts(4, &[0, 1, 2, 3]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        // Bits 0..3 set → 0b1111 = 0x000000000000000f
        assert!(buf.contains("0x000000000000000f"), "buf = {buf}");
    }

    #[test]
    fn test_accept_bitmap_boundary_64() {
        // Exactly 64 states — should use [u64; 1]
        let dfa = make_dfa_with_accepts(64, &[0, 63]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        assert!(buf.contains("[u64; 1]"), "buf = {buf}");
        // Bit 0 and bit 63 → 0x8000000000000001
        assert!(buf.contains("0x8000000000000001"), "buf = {buf}");
    }

    #[test]
    fn test_accept_bitmap_boundary_65() {
        // 65 states — should use [u64; 2]
        let dfa = make_dfa_with_accepts(65, &[0, 64]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        assert!(buf.contains("[u64; 2]"), "buf = {buf}");
        // Word 0: bit 0 → 0x0000000000000001
        // Word 1: bit 0 (state 64) → 0x0000000000000001
        assert!(buf.contains("0x0000000000000001,0x0000000000000001"), "buf = {buf}");
    }

    #[test]
    fn test_accept_bitmap_large_dfa_200_states() {
        // 200 states — should use [u64; 4] (ceil(200/64) = 4)
        // Accept states at 0, 63, 64, 127, 128, 199
        let dfa = make_dfa_with_accepts(200, &[0, 63, 64, 127, 128, 199]);
        let mut buf = String::new();
        write_is_accepting_check(&mut buf, &dfa);

        assert!(buf.contains("[u64; 4]"), "buf = {buf}");
        // Verify we can parse the generated hex words
        // Word 0: bits 0 and 63 → 0x8000000000000001
        // Word 1: bits 0 and 63 (states 64, 127) → 0x8000000000000001
        // Word 2: bit 0 (state 128) → 0x0000000000000001
        // Word 3: bit 7 (state 192+7=199) → 0x0000000000000080
        assert!(buf.contains("0x8000000000000001,0x8000000000000001,0x0000000000000001,0x0000000000000080"), "buf = {buf}");
    }

    // ══════════════════════════════════════════════════════════════════════
    // AL02: compute_hot_states tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_compute_hot_states_depth_zero() {
        // Depth 0: only the start state is hot.
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        let _s2 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(0, 0, s1);

        let hot = compute_hot_states(&dfa, 0);
        assert_eq!(hot.len(), 1, "depth 0 should only contain start state");
        assert!(hot.contains(&0), "start state must be in hot set");
    }

    #[test]
    fn test_compute_hot_states_depth_one() {
        // Depth 1: start state + all states reachable in one transition.
        //
        //   0 --class0--> 1
        //   0 --class1--> 2
        //   1 --class0--> 3  (NOT reachable at depth 1)
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        let s2 = dfa.add_state(DfaState::with_classes(num_classes));
        let s3 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(0, 0, s1);
        dfa.set_transition(0, 1, s2);
        dfa.set_transition(s1, 0, s3);

        let hot = compute_hot_states(&dfa, 1);
        assert_eq!(hot.len(), 3, "depth 1: start + 2 direct successors");
        assert!(hot.contains(&0));
        assert!(hot.contains(&(s1 as usize)));
        assert!(hot.contains(&(s2 as usize)));
        assert!(!hot.contains(&(s3 as usize)), "s3 is at depth 2, not depth 1");
    }

    #[test]
    fn test_compute_hot_states_depth_two() {
        // Depth 2: start + depth-1 successors + depth-2 successors.
        //
        //   0 --class0--> 1 --class0--> 3
        //   0 --class1--> 2
        //   3 --class0--> 4  (NOT reachable at depth 2)
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        let s2 = dfa.add_state(DfaState::with_classes(num_classes));
        let s3 = dfa.add_state(DfaState::with_classes(num_classes));
        let s4 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(0, 0, s1);
        dfa.set_transition(0, 1, s2);
        dfa.set_transition(s1, 0, s3);
        dfa.set_transition(s3, 0, s4);

        let hot = compute_hot_states(&dfa, 2);
        assert_eq!(hot.len(), 4, "depth 2: states 0,1,2,3");
        assert!(hot.contains(&0));
        assert!(hot.contains(&(s1 as usize)));
        assert!(hot.contains(&(s2 as usize)));
        assert!(hot.contains(&(s3 as usize)));
        assert!(!hot.contains(&(s4 as usize)), "s4 is at depth 3");
    }

    #[test]
    fn test_compute_hot_states_no_duplicates_with_cycles() {
        // DFA with cycles: 0 -> 1 -> 0 (back edge). BFS should not
        // revisit states, so the hot set should be {0, 1}.
        let num_classes = 2;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        dfa.set_transition(0, 0, s1);
        dfa.set_transition(s1, 0, 0); // back edge

        let hot = compute_hot_states(&dfa, 5);
        assert_eq!(hot.len(), 2, "cyclic DFA with 2 states: hot set should be {{0, 1}}");
        assert!(hot.contains(&0));
        assert!(hot.contains(&(s1 as usize)));
    }

    #[test]
    fn test_compute_hot_states_skips_dead_state() {
        // DEAD_STATE transitions should not be followed.
        let num_classes = 4;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState::with_classes(num_classes));
        // Only class 0 has a live transition; classes 1-3 are DEAD_STATE
        dfa.set_transition(0, 0, s1);

        let hot = compute_hot_states(&dfa, 1);
        assert_eq!(hot.len(), 2, "only start and s1 should be hot");
        assert!(hot.contains(&0));
        assert!(hot.contains(&(s1 as usize)));
    }

    // ══════════════════════════════════════════════════════════════════════
    // AL02: Hybrid codegen tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_hybrid_codegen_produces_valid_tokenstream() {
        // Build a DFA with > 30 states (forces compressed path normally).
        // With hybrid_lexer=true, the hybrid path should be taken and
        // produce valid Rust code.
        let mut specs: Vec<(&str, TokenKind)> = vec![
            ("+", TokenKind::Fixed("+".to_string())),
            ("-", TokenKind::Fixed("-".to_string())),
            ("*", TokenKind::Fixed("*".to_string())),
            ("/", TokenKind::Fixed("/".to_string())),
            ("=", TokenKind::Fixed("=".to_string())),
            ("==", TokenKind::Fixed("==".to_string())),
            ("!=", TokenKind::Fixed("!=".to_string())),
            ("<=", TokenKind::Fixed("<=".to_string())),
            (">=", TokenKind::Fixed(">=".to_string())),
            ("(", TokenKind::Fixed("(".to_string())),
            (")", TokenKind::Fixed(")".to_string())),
            ("{", TokenKind::Fixed("{".to_string())),
            ("}", TokenKind::Fixed("}".to_string())),
            ("[", TokenKind::Fixed("[".to_string())),
            ("]", TokenKind::Fixed("]".to_string())),
            (",", TokenKind::Fixed(",".to_string())),
            (";", TokenKind::Fixed(";".to_string())),
            (":", TokenKind::Fixed(":".to_string())),
            (".", TokenKind::Fixed(".".to_string())),
            ("->", TokenKind::Fixed("->".to_string())),
            ("=>", TokenKind::Fixed("=>".to_string())),
            ("++", TokenKind::Fixed("++".to_string())),
            ("--", TokenKind::Fixed("--".to_string())),
            ("&&", TokenKind::Fixed("&&".to_string())),
            ("||", TokenKind::Fixed("||".to_string())),
        ];
        // Add many keywords to push past the 30-state threshold
        for kw in &[
            "if", "else", "while", "for", "return", "break", "continue",
            "fn", "let", "mut", "const", "struct", "enum", "match",
            "impl", "trait", "type", "where", "pub", "mod", "use",
        ] {
            specs.push((kw, TokenKind::Fixed(kw.to_string())));
        }

        let (dfa, partition) = build_test_dfa(
            &specs,
            BuiltinNeeds {
                ident: true,
                integer: true,
                float: true,
                string_lit: true,
                ..Default::default()
            },
        );

        // Verify we actually have > 30 states (otherwise the test is pointless)
        assert!(
            dfa.states.len() > DIRECT_CODED_THRESHOLD,
            "test DFA should have > {} states to exercise hybrid path, got {}",
            DIRECT_CODED_THRESHOLD,
            dfa.states.len()
        );

        let mut token_kinds: Vec<TokenKind> = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Float,
            TokenKind::StringLit,
        ];
        for (_text, kind) in &specs {
            token_kinds.push(kind.clone());
        }

        let (code, strategy, _variant_map, _ambiguity) =
            generate_lexer_string_hybrid(&dfa, &partition, &token_kinds, "test_hybrid", true, &[]);

        // Verify hybrid strategy was selected
        assert_eq!(
            strategy,
            CodegenStrategy::HybridDirectCompressed,
            "hybrid mode should be selected for DFA with {} states",
            dfa.states.len()
        );

        // Verify the generated code contains both direct-coded match arms
        // and compressed table arrays
        assert!(
            code.contains("dfa_next_cold"),
            "hybrid code should contain cold-state fallback function"
        );

        // Verify the generated code is valid Rust
        let _ts: TokenStream = code
            .parse()
            .expect("generated hybrid lexer should be valid Rust");
    }

    #[test]
    fn test_hybrid_skipped_for_small_dfa() {
        // For a DFA with <= 30 states, hybrid mode should not activate
        // even when hybrid_lexer=true.
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

        assert!(
            dfa.states.len() <= DIRECT_CODED_THRESHOLD,
            "test DFA should have <= {} states, got {}",
            DIRECT_CODED_THRESHOLD,
            dfa.states.len()
        );

        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Integer,
            TokenKind::Fixed("+".to_string()),
            TokenKind::Fixed("-".to_string()),
        ];

        let (_code, strategy, _variant_map, _ambiguity) =
            generate_lexer_string_hybrid(&dfa, &partition, &token_kinds, "test_small", true, &[]);

        assert_eq!(
            strategy,
            CodegenStrategy::DirectCoded,
            "small DFA should use direct-coded even with hybrid_lexer=true"
        );
    }

    // ══════════════════════════════════════════════════════════════════════
    // AL01: Comb repacking tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_repack_comb_preserves_lookup_correctness() {
        // Build a DFA with known terminals, compress, repack, and verify
        // that every (state, class) lookup still produces the correct result.
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
        let mut comb = compress_rows_comb(&dfa, num_classes);
        repack_comb_sparse_rows(&mut comb, num_classes);

        // Verify every (state, class) lookup matches the flat DFA.
        for (state_idx, state) in dfa.states.iter().enumerate() {
            for class_id in 0..num_classes {
                let flat_result = state.transitions[class_id];
                let idx = comb.base[state_idx] as usize + class_id;
                let comb_result = if idx < comb.check.len() && comb.check[idx] == state_idx as u32 {
                    comb.next[idx]
                } else {
                    comb.default[state_idx]
                };
                assert_eq!(
                    flat_result, comb_result,
                    "repack: mismatch at state={}, class={}: flat={}, comb={}",
                    state_idx, class_id, flat_result, comb_result
                );
            }
        }
    }

    #[test]
    fn test_repack_comb_reduces_or_preserves_table_size() {
        // After repacking, the table should be no larger than before.
        let num_classes = 16;
        let num_states = 20;
        let mut dfa = Dfa::new(num_classes);
        // Add states with only 1-2 live transitions each (very sparse)
        for s in 1..num_states {
            let state = dfa.add_state(DfaState::with_classes(num_classes));
            dfa.set_transition(state, 0, 0);
            if s % 3 == 0 {
                dfa.set_transition(state, 1, 0);
            }
        }

        let original = compress_rows_comb(&dfa, num_classes);
        let original_next_len = original.next.len();

        let mut repacked = compress_rows_comb(&dfa, num_classes);
        repack_comb_sparse_rows(&mut repacked, num_classes);

        assert!(
            repacked.next.len() <= original_next_len,
            "repacked NEXT ({}) should be <= original NEXT ({})",
            repacked.next.len(),
            original_next_len
        );
    }

    #[test]
    fn test_repack_comb_empty_dfa() {
        // Should not panic on empty DFA
        let dfa = Dfa::new(4);
        let mut comb = compress_rows_comb(&dfa, 4);
        repack_comb_sparse_rows(&mut comb, 4);
        assert_eq!(comb.default.len(), 1);
        assert_eq!(comb.default[0], u32::MAX);
    }

    // ══════════════════════════════════════════════════════════════════════
    // AL05: Multi-byte chain detection tests
    // ══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_chain_detection_keyword_chain() {
        // A keyword like "error" creates a chain through the DFA.
        // Not all intermediate states may form a chain (depends on whether
        // letter equivalence classes are singletons), but the detection
        // algorithm should not panic and should return valid chains.
        let (dfa, partition) = build_test_dfa(
            &[
                ("error", TokenKind::Fixed("error".to_string())),
            ],
            BuiltinNeeds {
                ident: true,
                integer: false,
                ..Default::default()
            },
        );

        let chains = detect_multi_byte_chains(&dfa, &partition);
        for chain in &chains {
            assert!(chain.chain_len() >= 3, "chain too short: {:?}", chain);
            assert_ne!(chain.start_state, chain.end_state, "chain is a self-loop: {:?}", chain);
        }
    }

    #[test]
    fn test_chain_detection_no_chains_in_tiny_dfa() {
        // A DFA with only single-char terminals should have no chains of length >= 3.
        let (dfa, partition) = build_test_dfa(
            &[
                ("+", TokenKind::Fixed("+".to_string())),
                ("-", TokenKind::Fixed("-".to_string())),
                ("*", TokenKind::Fixed("*".to_string())),
            ],
            BuiltinNeeds {
                ident: false,
                integer: false,
                ..Default::default()
            },
        );

        let chains = detect_multi_byte_chains(&dfa, &partition);
        // Single-char terminals can't form 3-byte chains
        assert!(
            chains.is_empty(),
            "expected no chains for single-char terminals, got {:?}",
            chains
        );
    }

    #[test]
    fn test_chain_detection_preserves_accept_state_semantics() {
        // Chains must not skip intermediate accept states.
        // "=", "==", "===" each has an accept state at the prefix.
        let (dfa, partition) = build_test_dfa(
            &[
                ("=", TokenKind::Fixed("=".to_string())),
                ("==", TokenKind::Fixed("==".to_string())),
                ("===", TokenKind::Fixed("===".to_string())),
            ],
            BuiltinNeeds {
                ident: false,
                integer: false,
                ..Default::default()
            },
        );

        let chains = detect_multi_byte_chains(&dfa, &partition);
        // The "=" and "==" states are accept states, so they should NOT be
        // chain intermediates. No valid 3-byte chain should exist here because
        // all intermediate states along "===" are accept states.
        for chain in &chains {
            assert!(chain.chain_len() >= 3, "chain too short: {:?}", chain);
        }
    }

    #[test]
    fn test_chain_table_codegen_valid_syntax() {
        // Verify that the generated chain table code is syntactically valid.
        let chains = vec![
            MultiByteChain {
                start_state: 0,
                end_state: 5,
                bytes: vec![b'e', b'r', b'r', b'o', b'r'],
            },
            MultiByteChain {
                start_state: 1,
                end_state: 4,
                bytes: vec![b'a', b'b', b'c'],
            },
        ];

        let mut buf = String::new();
        write_chain_tables(&mut buf, &chains);

        // The output should contain a function named try_chain
        assert!(buf.contains("fn try_chain("), "missing try_chain function: {buf}");
        // Should contain match arms for start states 0 and 1
        assert!(buf.contains("0u32 =>"), "missing start state 0: {buf}");
        assert!(buf.contains("1u32 =>"), "missing start state 1: {buf}");
        // Should reference end states
        assert!(buf.contains("5u32"), "missing end state 5: {buf}");
        assert!(buf.contains("4u32"), "missing end state 4: {buf}");
    }

    // ══════════════════════════════════════════════════════════════════════
    // Custom token codegen tests (Token enum, display, constructor)
    // ══════════════════════════════════════════════════════════════════════

    /// Helper: build a CustomTokenSpec for testing.
    fn test_custom_spec(name: &str, pattern: &str, payload_type: Option<&str>) -> crate::CustomTokenSpec {
        crate::CustomTokenSpec {
            name: name.to_string(),
            pattern: pattern.to_string(),
            category: if payload_type.is_some() { Some("Int".to_string()) } else { None },
            payload_type: payload_type.map(String::from),
            constructor_code: None,
            is_builtin_override: false,
            priority: 2,
            push_mode: None,
            is_pop: false,
            stream: None,
        }
    }

    #[test]
    fn test_write_token_enum_with_custom_unit() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Custom("MyToken".into()),
        ];
        let custom_tokens: &[crate::CustomTokenSpec] = &[];
        let mut buf = String::new();
        write_token_enum(&mut buf, &token_kinds, custom_tokens);

        assert!(
            buf.contains("MyToken,"),
            "should contain unit variant MyToken, got:\n{}",
            buf
        );
        // Unit variant should not have a payload in parens
        assert!(
            !buf.contains("MyToken("),
            "unit variant should not have payload, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_write_token_enum_with_custom_payload() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Custom("HexLit".into()),
        ];
        let custom_tokens = vec![
            test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("i64")),
        ];
        let mut buf = String::new();
        write_token_enum(&mut buf, &token_kinds, &custom_tokens);

        assert!(
            buf.contains("HexLit(i64),"),
            "should contain payload variant HexLit(i64), got:\n{}",
            buf
        );
    }

    #[test]
    fn test_write_token_enum_with_custom_str_payload() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Custom("HexLit".into()),
        ];
        let custom_tokens = vec![
            test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("str")),
        ];
        let mut buf = String::new();
        write_token_enum(&mut buf, &token_kinds, &custom_tokens);

        assert!(
            buf.contains("HexLit(&'a str),"),
            "str payload should get lifetime annotation &'a str, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_write_token_display_custom_unit() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Custom("MyToken".into()),
        ];
        let custom_tokens: &[crate::CustomTokenSpec] = &[];
        let mut buf = String::new();
        write_token_display(&mut buf, &token_kinds, custom_tokens);

        assert!(
            buf.contains("Token::MyToken => \"`MyToken`\".to_string()"),
            "unit custom token display should produce Token::MyToken => \"`MyToken`\".to_string(), got:\n{}",
            buf
        );
    }

    #[test]
    fn test_write_token_display_custom_payload() {
        let token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Custom("HexLit".into()),
        ];
        let custom_tokens = vec![
            test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("i64")),
        ];
        let mut buf = String::new();
        write_token_display(&mut buf, &token_kinds, &custom_tokens);

        // Payload variant should bind the value
        assert!(
            buf.contains("Token::HexLit(v)"),
            "payload custom token display should bind value, got:\n{}",
            buf
        );
        assert!(
            buf.contains("format!(\"HexLit `{}`\", v)"),
            "payload custom token display should format with value, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_token_kind_to_constructor_custom() {
        let custom_tokens = vec![{
            let mut spec = test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("i64"));
            spec.constructor_code = Some("i64::from_str_radix(&text[2..], 16).expect(\"bad hex\")".to_string());
            spec
        }];
        let kind = TokenKind::Custom("HexLit".into());
        let result = token_kind_to_constructor(&kind, "text", &custom_tokens);

        assert!(
            result.contains("Token::HexLit("),
            "should generate Token::HexLit constructor, got: {}",
            result
        );
        assert!(
            result.contains("i64::from_str_radix"),
            "should use custom constructor_code, got: {}",
            result
        );
    }

    #[test]
    fn test_token_kind_to_constructor_custom_no_code() {
        // Without constructor_code but with category/payload_type — should use default parse
        let custom_tokens = vec![
            test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("i64")),
        ];
        let kind = TokenKind::Custom("HexLit".into());
        let result = token_kind_to_constructor(&kind, "text", &custom_tokens);

        assert!(
            result.contains("Token::HexLit("),
            "should generate Token::HexLit constructor, got: {}",
            result
        );
        assert!(
            result.contains(".parse::<i64>()"),
            "should use default parse::<i64>() when no constructor_code, got: {}",
            result
        );
    }

    #[test]
    fn test_generate_modal_lexer_has_mode_constants() {
        use crate::automata::nfa::build_nfa_for_mode;
        use crate::lexer::ModeDfaResult;

        // Build default DFA from a simple terminal spec
        let (default_dfa, default_partition) = build_test_dfa(
            &[("+", TokenKind::Fixed("+".to_string()))],
            BuiltinNeeds { ident: true, integer: false, float: false, string_lit: false, boolean: false },
        );
        let default_token_kinds = vec![
            TokenKind::Eof,
            TokenKind::Ident,
            TokenKind::Fixed("+".to_string()),
        ];

        // Build a named mode with a custom token
        let mode_spec = test_custom_spec("HexLit", "0x[0-9a-fA-F]+", Some("i64"));
        let mode_nfa = build_nfa_for_mode(&[mode_spec.clone()]);
        let mode_partition = compute_equivalence_classes(&mode_nfa);
        let mode_dfa_raw = subset_construction(&mode_nfa, &mode_partition);
        let mode_dfa = minimize_dfa(&mode_dfa_raw);

        let mode_results = vec![ModeDfaResult {
            name: "hex".to_string(),
            mode_id: 1,
            min_dfa: mode_dfa,
            partition: mode_partition,
            token_kinds: vec![TokenKind::Custom("HexLit".into())],
            custom_tokens: vec![mode_spec.clone()],
        }];

        let output = generate_modal_lexer_string(
            &default_dfa,
            &default_partition,
            &default_token_kinds,
            &mode_results,
            "test_lang",
            &[],                // default_custom_tokens
            &[mode_spec],       // all_custom_tokens
        );

        assert!(
            output.contains("MODE_DEFAULT"),
            "should contain MODE_DEFAULT constant, got:\n{}",
            &output[..output.len().min(500)]
        );
        assert!(
            output.contains("MODE_HEX"),
            "should contain MODE_HEX constant, got:\n{}",
            &output[..output.len().min(500)]
        );
        assert!(
            output.contains("const MODE_DEFAULT: u8 = 0;"),
            "MODE_DEFAULT should be 0, got:\n{}",
            &output[..output.len().min(500)]
        );
        assert!(
            output.contains("const MODE_HEX: u8 = 1;"),
            "MODE_HEX should be 1, got:\n{}",
            &output[..output.len().min(500)]
        );
    }
}
