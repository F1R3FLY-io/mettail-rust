//! L2 (2026-04-28): lex-time ambiguity types.
//!
//! When a single byte position has multiple accepting `TokenKind`
//! interpretations (e.g., a regex like `if` matching both `Keyword("if")`
//! and `Ident`), the lexer emits a `LexEntry` carrying every alternative
//! as a `LexAlternative`. The walker then forks across alternatives and
//! uses the L1 `lex_alt_idx` to break ties.
//!
//! These types are stand-alone data carriers: they don't depend on the
//! WPDS runtime or parser — they're consumed by the lex-Fork emission
//! path (L6) and the walker's `WpdaTokenSource` extension (L4).
//!
//! ## No shipped grammar exercises lex ambiguity today
//!
//! The L-series substrate is built BEFORE any grammar declares lex
//! alternatives. Synthetic test grammars (`languages/tests/lex_*_smoke.rs`)
//! drive coverage.

use crate::automata::semiring::TropicalWeight;
use crate::automata::TokenKind;

// ══════════════════════════════════════════════════════════════════════════════
// LexAlternative
// ══════════════════════════════════════════════════════════════════════════════

/// One alternative interpretation of bytes starting at a given position.
///
/// Multiple alternatives appear when a DFA's `alt_accepts` slice contains
/// 2+ TokenKinds at the same byte position — the canonical example is a
/// keyword vs. identifier overlap (`if` matches both `Keyword("if")` and
/// `Ident`).
///
/// The `weight` field gives the alternative's priority: lower weight =
/// higher priority. For keyword-vs-identifier, the keyword form wins
/// (lower weight) when both match.
#[derive(Debug, Clone)]
pub struct LexAlternative {
    /// Token kind for this alternative.
    pub kind: TokenKind,
    /// Owned text of the matched bytes. Owned because lex-Fork branches
    /// transport these across the walker's fork boundary, where borrowed
    /// references would tie the cursor's lifetime to the outer token slice.
    pub text: String,
    /// Position after consumption. Different alternatives may consume
    /// different numbers of bytes (greedy keyword vs short identifier).
    pub end_byte: usize,
    /// Priority of this alternative. Lower = higher priority. Used by L6
    /// (walker lex-Fork) to populate the `lex_alt_idx` field of the L1
    /// `LexicographicWeight`.
    pub weight: TropicalWeight,
}

// ══════════════════════════════════════════════════════════════════════════════
// LexEntry
// ══════════════════════════════════════════════════════════════════════════════

/// All alternative interpretations of the bytes starting at `byte_start`.
///
/// A non-ambiguous position has exactly one alternative. The `alternatives`
/// vec is sorted by weight ascending (best first), so `alternatives[0]` is
/// the highest-priority interpretation.
#[derive(Debug, Clone)]
pub struct LexEntry {
    /// Byte offset where this entry begins.
    pub byte_start: usize,
    /// Alternative interpretations, sorted by weight ascending.
    pub alternatives: Vec<LexAlternative>,
}

impl LexEntry {
    /// Returns the highest-priority alternative (lowest weight, sorted
    /// first). Use this when lex disambiguation is not active and only a
    /// single interpretation is consumed.
    pub fn primary(&self) -> &LexAlternative {
        &self.alternatives[0]
    }

    /// Whether this entry has more than one alternative — i.e., this
    /// position is genuinely lex-ambiguous and the walker should fork.
    pub fn is_ambiguous(&self) -> bool {
        self.alternatives.len() > 1
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LexStream
// ══════════════════════════════════════════════════════════════════════════════

/// A stream of `LexEntry` values — replaces the flat `Vec<Token>` for
/// lex-ambiguous lex paths.
///
/// In the simple non-ambiguous case, every entry has exactly one
/// alternative; the stream is functionally equivalent to a `Vec<Token>`.
/// In the ambiguous case, entries with multiple alternatives drive lex-Fork
/// emission in the walker (L6).
#[derive(Debug, Clone, Default)]
pub struct LexStream {
    /// Lex entries in source order.
    pub entries: Vec<LexEntry>,
}

impl LexStream {
    /// Construct a new empty stream.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of entries in the stream.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the stream has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns true if any entry has multiple alternatives.
    pub fn has_ambiguity(&self) -> bool {
        self.entries.iter().any(|e| e.is_ambiguous())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LexDag — M2 (2026-05-13): DAG-shaped lex output for multi-length ambiguity
// ══════════════════════════════════════════════════════════════════════════════

/// One outgoing edge from a [`LexDagNode`].
///
/// Represents a single tokenization alternative: consuming the alt's
/// `text` advances the cursor from `self_node` (the source) to
/// `target_node` (the DAG node whose `byte_start == self.end_byte`).
///
/// Edges within a node are sorted longest-first (greatest `end_byte`)
/// to preserve maximal-munch as the canonical PRIMARY interpretation
/// (the first edge); shorter alternatives are SECONDARIES that the
/// walker may Fork over.
#[derive(Debug, Clone)]
pub struct LexDagEdge {
    /// Token kind for this alternative.
    pub kind: crate::automata::TokenKind,
    /// Owned text of the matched bytes.
    pub text: String,
    /// Byte position AFTER consuming this alt's bytes.
    pub end_byte: usize,
    /// Target node index (into [`LexDag::nodes`]).
    pub target_node: usize,
    /// Priority weight (lower = higher priority). Used by caller-forced
    /// tiebreak ordering at EOI when the walker chooses to surface a
    /// single result among ambiguous parses.
    pub weight: crate::automata::semiring::TropicalWeight,
    /// Sibling-edge ordinal at the parent node (matches the LexAlternative
    /// alt_idx convention). Used to populate `LexicographicWeight.lex_alt_idx`
    /// when a Fork branch is emitted for this alt.
    pub alt_idx: u16,
}

/// One node in a [`LexDag`] — represents a byte position (= token boundary).
#[derive(Debug, Clone)]
pub struct LexDagNode {
    /// Byte offset where this node begins (= a token boundary in the input).
    pub byte_start: usize,
    /// Outgoing edges, sorted longest-first by `end_byte` then by `weight`
    /// ascending (lowest weight = highest priority among equal-length alts).
    /// `edges[0]` is the canonical primary (maximal munch).
    pub edges: Vec<LexDagEdge>,
}

/// A DAG of token-boundary nodes connected by [`LexDagEdge`]s.
///
/// Replaces the flat `Vec<LexEntry>` for inputs with multi-LENGTH lex
/// ambiguity (e.g., `-3` lexing as both `Integer(-3)@end=2` and
/// `Minus@end=1`). Each ambiguous byte position has ≥2 outgoing edges
/// with different `end_byte`s; non-ambiguous positions are chains.
///
/// The walker's `LatticeTokenSource` (M3) wraps a `LexDag` and exposes
/// it through the `WpdaTokenSource` trait — the cursor's `pos: usize`
/// becomes a DAG node-id, and `next_pos(pos, alt_idx)` returns the
/// target node of the chosen alt. This replaces the `pending_lex_alts`
/// sidecar (commits `3290e05` / `ed53ea3`) with a WPDS-stack-pure
/// design: alt identity lives in the SHARED input structure, not in
/// per-cursor state.
#[derive(Debug, Clone, Default)]
pub struct LexDag {
    /// Nodes in the DAG, ordered by allocation (worklist FIFO pop) order.
    /// The first node always has `byte_start: 0`. The EOF sentinel (the
    /// node with `byte_start: input.len()` and empty `edges`) is
    /// **referenced by `eof_node`**, NOT by `nodes.last()` — M6c.7.1's
    /// soft-fail mechanism may allocate orphan nodes (for
    /// secondary-alt dead-ends) at indices AFTER the EOF sentinel,
    /// since dead-end byte positions are popped from the worklist
    /// later than the primary chain's terminal accept.
    pub nodes: Vec<LexDagNode>,
    /// Map from byte offset to node index. Used by `lex_dag_core` during
    /// construction (worklist scan) and by callers that need to look up
    /// nodes by byte position.
    pub byte_to_node: std::collections::BTreeMap<usize, usize>,
    /// M6c.8.1 (2026-05-14): index of the EOF sentinel node — the node
    /// at `byte_start = input.len()` with no outgoing edges. This is
    /// the canonical "end of input" position the walker must reach for
    /// a parse to be considered Accepted. May NOT equal
    /// `nodes.len() - 1` when the soft-fail logic has allocated orphan
    /// nodes for secondary-alt dead-ends after the EOF byte.
    pub eof_node: usize,
}

impl LexDag {
    /// Construct an empty DAG.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of nodes in the DAG (includes the EOF sentinel).
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the DAG has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// M6c.8.1 (2026-05-14): index of the EOF sentinel node. Use this
    /// instead of `nodes.len() - 1` — orphan nodes (M6c.7.1 soft-fail
    /// allocations for secondary-alt dead-ends) may be appended AFTER
    /// the EOF sentinel.
    pub fn eof_node(&self) -> usize {
        self.eof_node
    }

    /// Returns true if any node has ≥2 outgoing edges (multi-length
    /// lex ambiguity). Linear (chain) DAGs return false.
    pub fn has_ambiguity(&self) -> bool {
        self.nodes.iter().any(|n| n.edges.len() > 1)
    }

    /// Walk the DAG via the longest-first primary edges and return the
    /// flat (kind, text) sequence. Used by callers that want the
    /// maximal-munch tokenization without ambiguity branching (e.g.,
    /// the facade's fast-path when `!has_ambiguity()`).
    pub fn linear_path(&self) -> Vec<(crate::automata::TokenKind, String)> {
        let mut result = Vec::new();
        let mut current = 0usize;
        while let Some(node) = self.nodes.get(current) {
            let Some(edge) = node.edges.first() else {
                break;
            };
            result.push((edge.kind.clone(), edge.text.clone()));
            current = edge.target_node;
        }
        result
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// LexerConfig — driving case-insensitive matching, normalization, modes
// ══════════════════════════════════════════════════════════════════════════════

/// Per-grammar lexer configuration.
///
/// Drives case-insensitive matching (L11), unicode normalization (L11),
/// and per-mode DFA selection (L9). Codegen emits a `LEXER_CONFIG` static
/// per language; the runtime lexer reads it before each scan.
#[derive(Debug, Clone)]
pub struct LexerConfig {
    /// L11: when true, regex token-class matching folds to lowercase
    /// before comparing against the DFA. Non-ASCII case folding is not
    /// supported in v1 — synthetic grammars triggering it emit
    /// `compile_error!`.
    pub case_insensitive: bool,
    /// L11: normalize input bytes via the named Unicode form before
    /// lexing. `None` means leave bytes as-is.
    pub unicode_normalization: Option<UnicodeNormalForm>,
    /// L9: starting mode for the lexer. The mode_stack starts with this
    /// mode and pushes/pops via `ModeDirective` actions on token matches.
    pub default_mode: ModeId,
    /// L9: per-mode configuration entries. Index by `ModeId`.
    pub modes: Vec<ModeConfig>,
}

impl Default for LexerConfig {
    fn default() -> Self {
        Self {
            case_insensitive: false,
            unicode_normalization: None,
            default_mode: 0,
            modes: Vec::new(),
        }
    }
}

/// Configuration for a single lexer mode.
#[derive(Debug, Clone)]
pub struct ModeConfig {
    /// Mode identifier (matches `ModeId`).
    pub id: ModeId,
    /// Human-readable mode name (for diagnostics).
    pub name: String,
    /// Index into the codegen-emitted `Vec<Dfa>` of which DFA to scan with.
    pub dfa_index: usize,
}

/// Mode identifier. `0` is reserved for the default mode.
pub type ModeId = u16;

/// Unicode normal form for input normalization (L11).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnicodeNormalForm {
    /// Canonical Composition.
    NFC,
    /// Canonical Decomposition.
    NFD,
    /// Compatibility Composition.
    NFKC,
    /// Compatibility Decomposition.
    NFKD,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ident_alt(text: &str, end: usize, weight: f64) -> LexAlternative {
        LexAlternative {
            kind: TokenKind::Ident,
            text: text.to_string(),
            end_byte: end,
            weight: TropicalWeight::new(weight),
        }
    }

    #[test]
    fn entry_primary_returns_first_alternative() {
        let entry = LexEntry {
            byte_start: 0,
            alternatives: vec![ident_alt("if", 2, 1.0)],
        };
        assert_eq!(entry.primary().text, "if");
        assert!(!entry.is_ambiguous());
    }

    #[test]
    fn ambiguous_entry_carries_multiple_alternatives() {
        let entry = LexEntry {
            byte_start: 0,
            alternatives: vec![ident_alt("if", 2, 1.0), ident_alt("if", 2, 2.0)],
        };
        assert!(entry.is_ambiguous());
        assert_eq!(entry.alternatives.len(), 2);
    }

    #[test]
    fn stream_detects_any_ambiguity() {
        let mut stream = LexStream::new();
        stream.entries.push(LexEntry {
            byte_start: 0,
            alternatives: vec![ident_alt("a", 1, 1.0)],
        });
        assert!(!stream.has_ambiguity());
        stream.entries.push(LexEntry {
            byte_start: 1,
            alternatives: vec![ident_alt("if", 3, 1.0), ident_alt("if", 3, 2.0)],
        });
        assert!(stream.has_ambiguity());
        assert_eq!(stream.len(), 2);
    }

    #[test]
    fn lexer_config_default_is_clean() {
        let cfg = LexerConfig::default();
        assert!(!cfg.case_insensitive);
        assert!(cfg.unicode_normalization.is_none());
        assert_eq!(cfg.default_mode, 0);
        assert!(cfg.modes.is_empty());
    }
}
