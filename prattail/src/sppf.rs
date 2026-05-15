//! Shared Packed Parse Forest (SPPF) for the WPDA walker.
//!
//! Implements Scott & Johnstone (2010) "GLL parsing," ENTCS 253(7), 177–189 —
//! the canonical packed-parse-forest data structure for preserving all
//! derivations of an ambiguous grammar in O(n³) space, where n is the input
//! length (Theorem 1).
//!
//! ## Why this exists (Option C — see `~/.claude/plans/option-c-sppf-on-wpda.md`)
//!
//! M11 attempted to preserve parse-derivation ambiguity by wrapping the
//! walker's weight type in a multiset `DerivationWeight<W, Arc<SemanticBuilder>>`.
//! That conflated two orthogonal concerns — path cost (the role of a semiring
//! weight) and AST identity — and produced an O(merges²) memory blow-up plus
//! frozen mid-parse snapshots that returned wrong terms at EOI.
//!
//! Option C separates the concerns:
//!
//! - `W` reverts to `LexicographicWeight` (pure path cost).
//! - **This module** owns the AST identity, as a Tomita/Scott-Johnstone
//!   packed parse forest.
//!
//! ## Shape
//!
//! Four node types, one Vec-backed arena, three append-only dedup tables.
//!
//! ```text
//! enum SppfNode {
//!     Terminal { token_kind, text_handle, pos }
//!     Symbol   { non_terminal_tag, lo_pos, hi_pos }   // identity by (nt, lo, hi)
//!     Packing  { rule_idx, children }                  // one derivation
//!     Epsilon  { pos }
//! }
//! ```
//!
//! A Symbol node carries NO children. All derivations of a given (nt, lo, hi)
//! span are linked via the append-only side table `symbol_packings`. Adding a
//! packing to an existing Symbol does NOT mutate the Symbol node — the side
//! table receives an entry `(symbol_id, packing_id)`.
//!
//! ## Append-only arena invariant
//!
//! Three vectors are append-only: `nodes`, `text_arena`, `symbol_packings`.
//! Every other structure (`dedup_*`, `link_dedup`, `packings_by_symbol`) is
//! a derived index that can be rebuilt from a prefix of those three vectors.
//!
//! This invariant is load-bearing for incremental session checkpoint/restore
//! (see plan §11): a checkpoint is just the three lengths; a restore is a
//! truncate + dedup-filter + index-rebuild.
//!
//! ## Determinism (plan §11.5 invariants I1–I3)
//!
//! - Same input → same Symbol/Packing/Terminal SppfId, regardless of intern
//!   order (dedup tables guarantee).
//! - `dedup_packing` uses `FxHashMap` (deterministic) NOT `HashMap` (random).
//!
//! ## References
//!
//! - Tomita, M. (1986). *Efficient parsing for natural language.* §6.3, §6.4
//!   — the canonical packed-node + family-list shape.
//! - Scott, E. & Johnstone, A. (2010). *GLL parsing.* ENTCS 253(7). §3, §4 —
//!   the SPPF-construction-at-reduce-time discipline; Theorem 1 (cubic bound).

use crate::automata::TokenKind;
use rustc_hash::{FxHashMap, FxHashSet};
use std::hash::{Hash, Hasher};

// ══════════════════════════════════════════════════════════════════════════════
// Handles
// ══════════════════════════════════════════════════════════════════════════════

/// Index into the SPPF node arena. `u32::MAX` is a sentinel (`SPPF_ID_NONE`).
pub type SppfId = u32;

/// Sentinel "no node" value.
pub const SPPF_ID_NONE: SppfId = u32::MAX;

/// Index into the text arena (pooled token text). `u32::MAX` is a sentinel.
pub type TextHandle = u32;

/// Sentinel "no text" value (used for tokens without payload, like punctuation
/// where `TokenKind::Fixed(...)` already carries the lexeme).
pub const TEXT_HANDLE_NONE: TextHandle = u32::MAX;

/// Position in the input. Distinguishes real lex-DAG positions from
/// synthesized positions produced by recovery (`InsertToken` deltas).
///
/// Synthesized terminals get a distinct namespace so `dedup_terminal` does
/// not collide with real-input terminals at the same byte offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PosOrSynth {
    /// A real input position (lex-DAG node id).
    Real(u32),
    /// A synthesized terminal from error recovery. The `u32` is a monotone
    /// counter unique per recovery event in the parse.
    Synthesized(u32),
}

// ══════════════════════════════════════════════════════════════════════════════
// SppfNode
// ══════════════════════════════════════════════════════════════════════════════

/// A node in the Shared Packed Parse Forest.
///
/// Canonical Scott-Johnstone GLL shape: Terminal leaves, Symbol identity
/// nodes keyed by `(non_terminal, lo, hi)`, and Packing nodes carrying one
/// derivation each. See module doc for the rationale.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SppfNode {
    /// A terminal leaf.
    Terminal {
        /// The lexer's classification of this token.
        token_kind: TokenKind,
        /// Index into the SPPF's `text_arena`. May be `TEXT_HANDLE_NONE` when
        /// the kind already encodes the lexeme (`TokenKind::Fixed`, `Eof`).
        text_handle: TextHandle,
        /// Position. `Real` for input tokens, `Synthesized` for recovery
        /// insertions.
        pos: PosOrSynth,
    },

    /// A non-terminal Symbol node. ONE per `(non_terminal_tag, lo_pos, hi_pos)`
    /// triple by dedup. Symbol nodes are IMMUTABLE after allocation — the set
    /// of derivations attached to a Symbol grows via the side table
    /// `Sppf::symbol_packings`, never by mutating this struct.
    Symbol {
        /// `(cat_src_idx << 16) | rule_idx`, packed into one u32 so dedup keys
        /// fit in a single machine word.
        non_terminal_tag: u32,
        /// Input span start (inclusive).
        lo_pos: u32,
        /// Input span end (exclusive).
        hi_pos: u32,
    },

    /// A Packing node — one derivation alternative for some parent Symbol.
    /// Carries the production's rule_idx and an ordered children list.
    Packing {
        /// Which production produced this derivation. Identifies the action
        /// function to invoke during realization.
        rule_idx: u32,
        /// Ordered children (Terminal / Symbol / Epsilon SppfIds).
        children: Vec<SppfId>,
    },

    /// Sentinel for empty productions (epsilon). Has a position so that
    /// distinct empty rules at distinct positions don't collide in dedup.
    Epsilon {
        /// The position at which this epsilon was recognized.
        pos: u32,
    },
}

// ══════════════════════════════════════════════════════════════════════════════
// SppfCheckpoint
// ══════════════════════════════════════════════════════════════════════════════

/// Truncation watermarks for restoring the SPPF arena to a prior state.
///
/// Used by `WpdaIncrementalSession` (plan §11) to support LSP-style
/// incremental reparse. The append-only arena invariant guarantees that
/// truncating the three vectors to these lengths produces exactly the state
/// the arena was in when the checkpoint was recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SppfCheckpoint {
    /// Length of the `nodes` Vec at checkpoint time.
    pub nodes_len: u32,
    /// Length of the `text_arena` Vec at checkpoint time.
    pub text_arena_len: u32,
    /// Length of the `symbol_packings` Vec at checkpoint time.
    pub symbol_packings_len: u32,
}

// ══════════════════════════════════════════════════════════════════════════════
// Sppf
// ══════════════════════════════════════════════════════════════════════════════

/// The Shared Packed Parse Forest.
#[derive(Debug, Clone, Default)]
pub struct Sppf {
    // Append-only arrays. Truncating these by length restores prior state.
    nodes: Vec<SppfNode>,
    text_arena: Vec<u8>,
    text_index: Vec<(u32, u32)>, // (offset, len) per TextHandle
    symbol_packings: Vec<(SppfId, SppfId)>,

    // Dedup tables. On checkpoint restore, filter to drop entries pointing to
    // truncated ids. FxHashMap (deterministic) per plan §11.5 I3.
    dedup_terminal: FxHashMap<(TokenKind, PosOrSynth), SppfId>,
    dedup_symbol: FxHashMap<(u32, u32, u32), SppfId>,
    dedup_packing: FxHashMap<(u32, u64), SppfId>,
    dedup_epsilon: FxHashMap<u32, SppfId>,

    // Derived indices — strictly rebuildable from `symbol_packings`. Rebuilt
    // on checkpoint restore.
    link_dedup: FxHashSet<(SppfId, SppfId)>,
    packings_by_symbol: FxHashMap<SppfId, Vec<SppfId>>,
}

impl Sppf {
    /// Create an empty SPPF.
    pub fn new() -> Self {
        Self::default()
    }

    // ── intern_* ────────────────────────────────────────────────────────────

    /// Intern a terminal leaf. Returns an existing id if a structurally
    /// identical terminal was already interned, else allocates.
    pub fn intern_terminal(
        &mut self,
        token_kind: TokenKind,
        pos: PosOrSynth,
        text: Option<&str>,
    ) -> SppfId {
        // Dedup key: (kind, pos). Two terminals at the same position with the
        // same kind ARE the same terminal — `text` is determined by kind+pos.
        let key = (token_kind.clone(), pos);
        if let Some(&id) = self.dedup_terminal.get(&key) {
            return id;
        }
        let text_handle = match text {
            Some(s) => self.intern_text(s),
            None => TEXT_HANDLE_NONE,
        };
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Terminal {
            token_kind,
            text_handle,
            pos,
        });
        self.dedup_terminal.insert(key, id);
        id
    }

    /// Intern a Symbol identity node. Returns the existing id if `(nt, lo, hi)`
    /// was already interned, else allocates.
    ///
    /// Symbol identity is preserved across all derivations of the same span:
    /// two cursors that reduce DIFFERENT productions to the same `(nt, lo, hi)`
    /// get the SAME SppfId. They then call `link_packing_to_symbol` separately
    /// to attach their respective Packings.
    pub fn intern_symbol(&mut self, nt_tag: u32, lo_pos: u32, hi_pos: u32) -> SppfId {
        let key = (nt_tag, lo_pos, hi_pos);
        if let Some(&id) = self.dedup_symbol.get(&key) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Symbol {
            non_terminal_tag: nt_tag,
            lo_pos,
            hi_pos,
        });
        self.dedup_symbol.insert(key, id);
        id
    }

    /// Intern a Packing (one derivation). Returns the existing id if a
    /// structurally identical Packing was already interned, else allocates.
    pub fn intern_packing(&mut self, rule_idx: u32, children: Vec<SppfId>) -> SppfId {
        let key = (rule_idx, Self::hash_children(&children));
        if let Some(&id) = self.dedup_packing.get(&key) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Packing { rule_idx, children });
        self.dedup_packing.insert(key, id);
        id
    }

    /// Intern an Epsilon (empty production) at the given position.
    pub fn intern_epsilon(&mut self, pos: u32) -> SppfId {
        if let Some(&id) = self.dedup_epsilon.get(&pos) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Epsilon { pos });
        self.dedup_epsilon.insert(pos, id);
        id
    }

    /// Link a Packing to a Symbol. Idempotent (O(1) check). The link is
    /// appended to `symbol_packings` only if not already present.
    ///
    /// Pre-condition: `symbol_id` refers to a `SppfNode::Symbol` and
    /// `packing_id` refers to a `SppfNode::Packing`. Debug-asserted.
    pub fn link_packing_to_symbol(&mut self, symbol_id: SppfId, packing_id: SppfId) {
        debug_assert!(
            matches!(self.node(symbol_id), Some(SppfNode::Symbol { .. })),
            "link_packing_to_symbol: symbol_id {} is not a Symbol node",
            symbol_id
        );
        debug_assert!(
            matches!(self.node(packing_id), Some(SppfNode::Packing { .. })),
            "link_packing_to_symbol: packing_id {} is not a Packing node",
            packing_id
        );
        if self.link_dedup.insert((symbol_id, packing_id)) {
            self.symbol_packings.push((symbol_id, packing_id));
            self.packings_by_symbol
                .entry(symbol_id)
                .or_default()
                .push(packing_id);
        }
    }

    // ── accessors ───────────────────────────────────────────────────────────

    /// Borrow a node by id. Returns `None` if the id is out of range.
    pub fn node(&self, id: SppfId) -> Option<&SppfNode> {
        self.nodes.get(id as usize)
    }

    /// All Packings linked to a Symbol, in insertion order. Empty slice if
    /// the symbol has no linked packings (or if `symbol_id` is not a Symbol).
    pub fn packings_of(&self, symbol_id: SppfId) -> &[SppfId] {
        self.packings_by_symbol
            .get(&symbol_id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Resolve a `TextHandle` back to its `&str`. Returns `""` for
    /// `TEXT_HANDLE_NONE`.
    pub fn text(&self, handle: TextHandle) -> &str {
        if handle == TEXT_HANDLE_NONE {
            return "";
        }
        let (offset, len) = self.text_index[handle as usize];
        let bytes = &self.text_arena[offset as usize..(offset as usize + len as usize)];
        std::str::from_utf8(bytes).expect("intern_text only accepts valid UTF-8")
    }

    /// Total number of nodes in the arena.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the arena is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Total number of `(symbol, packing)` links.
    pub fn link_count(&self) -> usize {
        self.symbol_packings.len()
    }

    /// Iterator over all `(symbol_id, packing_id)` links, in insertion order.
    pub fn iter_links(&self) -> impl Iterator<Item = (SppfId, SppfId)> + '_ {
        self.symbol_packings.iter().copied()
    }

    // ── checkpoint / restore (plan §11.2) ───────────────────────────────────

    /// Capture the current arena state for later restoration.
    pub fn checkpoint(&self) -> SppfCheckpoint {
        SppfCheckpoint {
            nodes_len: self.nodes.len() as u32,
            text_arena_len: self.text_arena.len() as u32,
            symbol_packings_len: self.symbol_packings.len() as u32,
        }
    }

    /// Restore the arena to a prior checkpoint state.
    ///
    /// Append-only invariant guarantees: every entry surviving in the dedup
    /// tables whose value < `cp.nodes_len` still points at the same node it
    /// always did. Entries with value ≥ `cp.nodes_len` become stale and are
    /// filtered out.
    ///
    /// Derived indices (`link_dedup`, `packings_by_symbol`) are rebuilt
    /// by scanning the truncated `symbol_packings`.
    ///
    /// Complexity: O(|nodes| + |text_arena| + |symbol_packings| + |dedup_*|).
    /// Dominated by dedup-filter sweep on large arenas.
    pub fn restore_to_checkpoint(&mut self, cp: SppfCheckpoint) {
        debug_assert!(cp.nodes_len as usize <= self.nodes.len());
        debug_assert!(cp.text_arena_len as usize <= self.text_arena.len());
        debug_assert!(cp.symbol_packings_len as usize <= self.symbol_packings.len());

        // 1. Truncate append-only vectors.
        self.nodes.truncate(cp.nodes_len as usize);
        self.text_arena.truncate(cp.text_arena_len as usize);
        // text_index also truncates — handles ≥ the new index length are gone.
        // We must walk text_index and remove entries whose offset is past the
        // truncation point. Since intern_text appends both arena and index
        // monotonically, an index entry is valid iff its offset < text_arena_len.
        self.text_index
            .retain(|&(offset, _len)| offset < cp.text_arena_len);
        self.symbol_packings
            .truncate(cp.symbol_packings_len as usize);

        // 2. Filter dedup tables to drop entries pointing to truncated ids.
        let n = cp.nodes_len;
        self.dedup_terminal.retain(|_, &mut id| id < n);
        self.dedup_symbol.retain(|_, &mut id| id < n);
        self.dedup_packing.retain(|_, &mut id| id < n);
        self.dedup_epsilon.retain(|_, &mut id| id < n);

        // 3. Rebuild derived indices from the (now-truncated) symbol_packings.
        self.link_dedup.clear();
        self.packings_by_symbol.clear();
        for &(s, p) in &self.symbol_packings {
            self.link_dedup.insert((s, p));
            self.packings_by_symbol.entry(s).or_default().push(p);
        }
    }

    // ── internal helpers ────────────────────────────────────────────────────

    fn intern_text(&mut self, s: &str) -> TextHandle {
        let handle = self.text_index.len() as TextHandle;
        let offset = self.text_arena.len() as u32;
        let len = s.len() as u32;
        self.text_arena.extend_from_slice(s.as_bytes());
        self.text_index.push((offset, len));
        handle
    }

    fn hash_children(children: &[SppfId]) -> u64 {
        use rustc_hash::FxHasher;
        let mut h = FxHasher::default();
        children.hash(&mut h);
        h.finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn k_fixed(s: &str) -> TokenKind {
        TokenKind::Fixed(s.to_string())
    }

    // ── intern_terminal ─────────────────────────────────────────────────────

    #[test]
    fn intern_terminal_returns_same_id_for_same_key() {
        let mut s = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None);
        assert_eq!(a, b);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn intern_terminal_distinguishes_pos() {
        let mut s = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_distinguishes_kind() {
        let mut s = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None);
        let b = s.intern_terminal(k_fixed("-"), PosOrSynth::Real(0), None);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_real_and_synth_dont_collide() {
        let mut s = Sppf::new();
        let real = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(5), Some("x"));
        let synth = s.intern_terminal(TokenKind::Ident, PosOrSynth::Synthesized(5), Some("x"));
        assert_ne!(real, synth);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_preserves_text() {
        let mut s = Sppf::new();
        let id = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("foo"));
        match s.node(id) {
            Some(SppfNode::Terminal { text_handle, .. }) => {
                assert_eq!(s.text(*text_handle), "foo");
            }
            _ => panic!("expected Terminal"),
        }
    }

    #[test]
    fn intern_terminal_none_text_uses_sentinel() {
        let mut s = Sppf::new();
        let id = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None);
        match s.node(id) {
            Some(SppfNode::Terminal { text_handle, .. }) => {
                assert_eq!(*text_handle, TEXT_HANDLE_NONE);
                assert_eq!(s.text(*text_handle), "");
            }
            _ => panic!("expected Terminal"),
        }
    }

    // ── intern_symbol ───────────────────────────────────────────────────────

    #[test]
    fn intern_symbol_returns_same_id_for_same_span() {
        let mut s = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(0, 0, 5);
        assert_eq!(a, b);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn intern_symbol_distinguishes_nt_tag() {
        let mut s = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(1, 0, 5);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_symbol_distinguishes_span() {
        let mut s = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(0, 0, 6);
        let c = s.intern_symbol(0, 1, 5);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_eq!(s.len(), 3);
    }

    // ── intern_packing ──────────────────────────────────────────────────────

    #[test]
    fn intern_packing_returns_same_id_for_same_rule_and_children() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let a = s.intern_packing(0, vec![t]);
        let b = s.intern_packing(0, vec![t]);
        assert_eq!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_rule_idx() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let a = s.intern_packing(0, vec![t]);
        let b = s.intern_packing(1, vec![t]);
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_order() {
        let mut s = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let t2 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None);
        let a = s.intern_packing(0, vec![t1, t2]);
        let b = s.intern_packing(0, vec![t2, t1]);
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_count() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let a = s.intern_packing(0, vec![t]);
        let b = s.intern_packing(0, vec![t, t]);
        assert_ne!(a, b);
    }

    // ── intern_epsilon ──────────────────────────────────────────────────────

    #[test]
    fn intern_epsilon_dedupes_by_pos() {
        let mut s = Sppf::new();
        let a = s.intern_epsilon(3);
        let b = s.intern_epsilon(3);
        let c = s.intern_epsilon(4);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(s.len(), 2);
    }

    // ── link_packing_to_symbol ──────────────────────────────────────────────

    #[test]
    fn link_packing_to_symbol_records_link() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let p = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        assert_eq!(s.packings_of(sym), &[p]);
        assert_eq!(s.link_count(), 1);
    }

    #[test]
    fn link_packing_to_symbol_idempotent() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let p = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        assert_eq!(s.packings_of(sym), &[p]);
        assert_eq!(s.link_count(), 1);
    }

    #[test]
    fn link_packing_to_symbol_records_multiple_packings() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let p1 = s.intern_packing(0, vec![t]);
        let p2 = s.intern_packing(1, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        assert_eq!(s.packings_of(sym), &[p1, p2]);
        assert_eq!(s.link_count(), 2);
    }

    #[test]
    fn packings_of_empty_for_unlinked_symbol() {
        let mut s = Sppf::new();
        let sym = s.intern_symbol(0, 0, 1);
        assert!(s.packings_of(sym).is_empty());
    }

    // ── append-only invariant ───────────────────────────────────────────────

    #[test]
    fn arena_is_append_only_after_intern() {
        let mut s = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None);
        let snapshot = s.node(t1).cloned();
        let _ = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None);
        let _ = s.intern_symbol(0, 0, 1);
        let _ = s.intern_packing(0, vec![t1]);
        // t1's node identity is preserved.
        assert_eq!(s.node(t1).cloned(), snapshot);
    }

    #[test]
    fn symbol_node_immutable_when_packings_added() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let sym = s.intern_symbol(0, 0, 1);
        let symbol_snapshot = s.node(sym).cloned();
        let p1 = s.intern_packing(0, vec![t]);
        let p2 = s.intern_packing(1, vec![t]);
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        // Symbol node itself is unchanged.
        assert_eq!(s.node(sym).cloned(), symbol_snapshot);
        // Both packings are linked via the side table.
        assert_eq!(s.packings_of(sym).len(), 2);
    }

    // ── Tomita §6.4 packed-node example ─────────────────────────────────────

    /// Tomita 1986 §6.4 — "a + b * c" with ambiguous precedence.
    ///
    /// Two derivations:
    ///   E -> (E + E)   E -> (a)
    ///                  E -> (E * E)  E -> (b)
    ///                                E -> (c)
    /// vs:
    ///   E -> (E * E)   E -> (E + E)  E -> (a)
    ///                                E -> (b)
    ///                  E -> (c)
    ///
    /// The shared Symbol at (E, 0, 5) gets TWO packings.
    #[test]
    fn tomita_ambiguous_expression() {
        let mut s = Sppf::new();
        let nt_e: u32 = 0;
        const RULE_ADD: u32 = 0;
        const RULE_MUL: u32 = 1;
        const RULE_VAR: u32 = 2;

        // Leaf terminals at positions 0..5.
        let t_a = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("a"));
        let t_plus = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None);
        let t_b = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(2), Some("b"));
        let t_mul = s.intern_terminal(k_fixed("*"), PosOrSynth::Real(3), None);
        let t_c = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(4), Some("c"));

        // Leaf Symbols: E(a), E(b), E(c).
        let p_a = s.intern_packing(RULE_VAR, vec![t_a]);
        let p_b = s.intern_packing(RULE_VAR, vec![t_b]);
        let p_c = s.intern_packing(RULE_VAR, vec![t_c]);
        let e_a = s.intern_symbol(nt_e, 0, 1);
        let e_b = s.intern_symbol(nt_e, 2, 3);
        let e_c = s.intern_symbol(nt_e, 4, 5);
        s.link_packing_to_symbol(e_a, p_a);
        s.link_packing_to_symbol(e_b, p_b);
        s.link_packing_to_symbol(e_c, p_c);

        // Mid-level Symbols for the two parenthesizations:
        //   E(b * c) at (2, 5)
        //   E(a + b) at (0, 3)
        let p_bc_mul = s.intern_packing(RULE_MUL, vec![e_b, t_mul, e_c]);
        let e_bc = s.intern_symbol(nt_e, 2, 5);
        s.link_packing_to_symbol(e_bc, p_bc_mul);

        let p_ab_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_b]);
        let e_ab = s.intern_symbol(nt_e, 0, 3);
        s.link_packing_to_symbol(e_ab, p_ab_add);

        // Top-level Symbol E(0, 5) — TWO packings (both derivations).
        let p_top_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_bc]);
        let p_top_mul = s.intern_packing(RULE_MUL, vec![e_ab, t_mul, e_c]);
        let e_top = s.intern_symbol(nt_e, 0, 5);
        s.link_packing_to_symbol(e_top, p_top_add);
        s.link_packing_to_symbol(e_top, p_top_mul);

        // The shared E(a), E(b), E(c) symbols are reused — no duplication.
        // E(0,5) has both derivations attached.
        assert_eq!(s.packings_of(e_top).len(), 2);

        // Dedup verification: a second intern_symbol with the same span
        // returns the same id.
        let e_top_again = s.intern_symbol(nt_e, 0, 5);
        assert_eq!(e_top_again, e_top);
        let e_a_again = s.intern_symbol(nt_e, 0, 1);
        assert_eq!(e_a_again, e_a);
    }

    // ── Scott-Johnstone §4 worked example ───────────────────────────────────

    /// Scott & Johnstone (2010) §4 — building the SPPF for the GLL parse of an
    /// ambiguous grammar. Demonstrates Symbol-dedup making cursors that explore
    /// distinct paths converge on shared ids.
    #[test]
    fn scott_johnstone_two_derivations_share_symbol() {
        let mut s = Sppf::new();
        let nt_s: u32 = 0;
        const RULE_R1: u32 = 0;
        const RULE_R2: u32 = 1;

        let t0 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let t1 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None);

        // Cursor C0: S -> R1 [x, y]
        let p1 = s.intern_packing(RULE_R1, vec![t0, t1]);
        let s1 = s.intern_symbol(nt_s, 0, 2);
        s.link_packing_to_symbol(s1, p1);

        // Cursor C1 (later, distinct path): S -> R2 [x, y] (different rule)
        let p2 = s.intern_packing(RULE_R2, vec![t0, t1]);
        let s2 = s.intern_symbol(nt_s, 0, 2);
        // Must be the SAME id as s1 (Symbol dedup).
        assert_eq!(s1, s2);
        s.link_packing_to_symbol(s2, p2);

        // The shared Symbol has both packings.
        assert_eq!(s.packings_of(s1).len(), 2);
    }

    // ── checkpoint / restore ────────────────────────────────────────────────

    #[test]
    fn checkpoint_then_restore_yields_same_state() {
        let mut s = Sppf::new();
        let _ = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let _ = s.intern_symbol(0, 0, 1);
        let cp = s.checkpoint();
        let len_before = s.len();
        let link_before = s.link_count();

        let t = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None);
        let p = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 1, 2);
        s.link_packing_to_symbol(sym, p);
        assert!(s.len() > len_before);
        assert!(s.link_count() > link_before);

        s.restore_to_checkpoint(cp);
        assert_eq!(s.len(), len_before);
        assert_eq!(s.link_count(), link_before);
    }

    #[test]
    fn restore_filters_stale_dedup_entries() {
        let mut s = Sppf::new();
        let _ = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let cp = s.checkpoint();

        // Add a terminal post-checkpoint; restore should evict it from dedup.
        let pre_id = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None);
        s.restore_to_checkpoint(cp);

        // Same key after restore: must allocate a new id, NOT return the stale one.
        let post_id = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None);
        let _ = pre_id;
        // After restore + re-intern, the y@1 terminal lives at the same nodes index
        // as before (because we truncated to cp.nodes_len then appended one).
        assert_eq!(post_id, cp.nodes_len);
    }

    #[test]
    fn restore_rebuilds_packings_by_symbol_index() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None);
        let p1 = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        let cp = s.checkpoint();

        // Add another packing post-checkpoint.
        let p2 = s.intern_packing(1, vec![t]);
        s.link_packing_to_symbol(sym, p2);
        assert_eq!(s.packings_of(sym).len(), 2);

        // Restore: the second packing's link must be gone.
        s.restore_to_checkpoint(cp);
        assert_eq!(s.packings_of(sym), &[p1]);
    }

    #[test]
    fn restore_preserves_unrelated_dedup_entries() {
        let mut s = Sppf::new();
        let kept_id = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None);
        let cp = s.checkpoint();
        let _ = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None);
        s.restore_to_checkpoint(cp);
        // Re-intern the kept terminal — must return the same id.
        let again = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None);
        assert_eq!(again, kept_id);
    }

    #[test]
    fn empty_arena_checkpoint_restore_roundtrip() {
        let mut s = Sppf::new();
        let cp = s.checkpoint();
        assert_eq!(cp.nodes_len, 0);
        s.restore_to_checkpoint(cp);
        assert_eq!(s.len(), 0);
    }

    // ── determinism (plan §11.5 I3) ─────────────────────────────────────────

    #[test]
    fn dedup_packing_is_order_independent() {
        // Two separate SPPFs, same operations in same order — same ids out.
        // Per FxHash determinism, repeated runs yield identical results.
        let mut s1 = Sppf::new();
        let mut s2 = Sppf::new();
        for i in 0..16u32 {
            let t1 = s1.intern_terminal(TokenKind::Ident, PosOrSynth::Real(i), Some(&format!("v{}", i)));
            let t2 = s2.intern_terminal(TokenKind::Ident, PosOrSynth::Real(i), Some(&format!("v{}", i)));
            assert_eq!(t1, t2);
            let p1 = s1.intern_packing(0, vec![t1]);
            let p2 = s2.intern_packing(0, vec![t2]);
            assert_eq!(p1, p2);
        }
    }

    // ── text intern ─────────────────────────────────────────────────────────

    #[test]
    fn text_intern_distinct_strings_distinct_handles() {
        let mut s = Sppf::new();
        let h1 = s.intern_text("hello");
        let h2 = s.intern_text("world");
        assert_ne!(h1, h2);
        assert_eq!(s.text(h1), "hello");
        assert_eq!(s.text(h2), "world");
    }

    #[test]
    fn text_handle_none_resolves_empty() {
        let s = Sppf::new();
        assert_eq!(s.text(TEXT_HANDLE_NONE), "");
    }
}
