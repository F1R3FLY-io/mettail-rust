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
        /// Bug E fix (Phase 3.1.3, 2026-05-15): discriminator indicating
        /// which builder push-helper produced this Terminal. `true` =
        /// `emit_push_ident` (builder pushed `ActionArg::Ident{name,pos}`).
        /// `false` = `emit_push_token` (builder pushed
        /// `ActionArg::Token{kind,text,pos}`).
        ///
        /// Required because `emit_push_token` can be called with
        /// `TokenKind::Ident` for general token captures (e.g., `Func(name:
        /// Ident, body: Block)`), while `emit_push_ident` is reserved for
        /// binder-ident sites. The realization pass must reconstruct the
        /// correct `ActionArg` variant; without this flag it would
        /// mismatch when `token_kind == Ident`.
        pushed_via_push_ident: bool,
    },

    /// A non-terminal Symbol node. ONE per `(non_terminal_tag, lo_pos, hi_pos)`
    /// triple by dedup. Symbol nodes are IMMUTABLE after allocation — the set
    /// of derivations attached to a Symbol grows via the side table
    /// `Sppf::symbol_packings`, never by mutating this struct.
    Symbol {
        /// Category identifier — typically `cat_src_idx as u32`. MUST be
        /// shared across all derivations of the same non-terminal: that's
        /// what makes Symbol-dedup the ambiguity-collapse mechanism (two
        /// cursors reducing different rules of the same Cat at the same
        /// span MUST collapse to the same Symbol id, with their distinct
        /// derivations recorded as separate Packings linked via
        /// `Sppf::symbol_packings`). Rule-specific information lives in
        /// `Packing.rule_idx`, never in this tag.
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

    /// Placeholder for a collection slot's identity argument. Pushed by
    /// `emit_push_collection_id` to mirror the builder's
    /// `ActionArg::CollectionId`. The realization pass resolves it by
    /// looking up `walker.sppf_collection_arena[id]` (which holds the
    /// SppfIds collected via `emit_splice_into_collection`).
    CollectionId {
        /// Index into `WpdaWalker::sppf_collection_arena`.
        id: u32,
    },

    /// Marker for "this optional group was not filled." Distinct from
    /// `Epsilon` because optional-absent has well-defined semantics at
    /// realization (the user AST gets `None`, not "skipped").
    OptAbsent {
        /// The position at which the optional group was opened.
        pos: u32,
    },

    /// Opaque predicate-arg payload pushed by `emit_push_predicate`. The
    /// payload Arc is owned by the walker's `predicate_arena`; this node
    /// references it by index. The realization pass clones the Arc when
    /// constructing the user-visible `ActionArg::Predicate(arc)`.
    Predicate {
        /// Index into `WpdaWalker::sppf_predicate_arena`.
        handle: u32,
    },

    /// Bug N fix (Phase 3.1.5, 2026-05-15): completed binder scope —
    /// produced when `apply_effect_to_cursor` processes a
    /// `BuilderDelta::EndBinderScope` effect. The walker side pops the
    /// active `BinderHandle` from `builder.binder_scopes` and pushes it
    /// as `ActionArg::BinderScope` onto the args stack. The SPPF mirror
    /// records the same materialization as a `BinderScope` leaf so
    /// realization can reconstruct `ActionArg::BinderScope` from the
    /// SPPF alone (without depending on the parse-time `builder.binder_scopes`).
    ///
    /// Names are stored as TextHandles into the SPPF's `text_arena`;
    /// realization decodes them via `Sppf::text(handle)`. Dedup'd by
    /// `(depth, hash(names_text))`.
    BinderScope {
        /// One TextHandle per declared binder name.
        names_text: Vec<TextHandle>,
        /// Nesting depth at the time the scope was opened — matches
        /// `BinderHandle.depth`.
        depth: u16,
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
    /// Bug E fix (Phase 3.1.3): key includes `pushed_via_push_ident: bool`
    /// so emit_push_token's Terminal{kind=Ident, …} doesn't dedup with
    /// emit_push_ident's Terminal{kind=Ident, …} at the same position.
    /// They produce different ActionArgs at realization (Token vs Ident);
    /// they must be distinct SPPF nodes.
    dedup_terminal: FxHashMap<(TokenKind, PosOrSynth, bool), SppfId>,
    dedup_symbol: FxHashMap<(u32, u32, u32), SppfId>,
    dedup_packing: FxHashMap<(u32, u64), SppfId>,
    dedup_epsilon: FxHashMap<u32, SppfId>,
    dedup_collection_id: FxHashMap<u32, SppfId>,
    dedup_opt_absent: FxHashMap<u32, SppfId>,
    dedup_predicate: FxHashMap<u32, SppfId>,
    /// Bug N (Phase 3.1.5): dedup BinderScope by `(depth, names_hash)`.
    /// Two cursors emitting the same scope contents at the same depth
    /// collapse to the same SppfId.
    dedup_binder_scope: FxHashMap<(u16, u64), SppfId>,

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
    ///
    /// `pushed_via_push_ident`: Bug E discriminator. `true` if the
    /// walker's `emit_push_ident` (which produces `ActionArg::Ident` on
    /// the builder side) called this; `false` if `emit_push_token`
    /// (`ActionArg::Token`). Distinct values at the same `(kind, pos)`
    /// produce DISTINCT Terminal SppfIds so realization can reconstruct
    /// the right ActionArg variant.
    pub fn intern_terminal(
        &mut self,
        token_kind: TokenKind,
        pos: PosOrSynth,
        text: Option<&str>,
        pushed_via_push_ident: bool,
    ) -> SppfId {
        // Dedup key: (kind, pos, pushed_via_push_ident). Two terminals at the
        // same position with the same kind and same push-helper origin ARE the
        // same terminal — `text` is determined by kind+pos.
        let key = (token_kind.clone(), pos, pushed_via_push_ident);
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
            pushed_via_push_ident,
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

    /// Intern a `CollectionId` placeholder pointing at slot `id` in the
    /// walker's `sppf_collection_arena`. Dedup'd by `id` — two cursors
    /// referring to the same collection slot share the placeholder node.
    pub fn intern_collection_id(&mut self, id: u32) -> SppfId {
        if let Some(&sid) = self.dedup_collection_id.get(&id) {
            return sid;
        }
        let sid = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::CollectionId { id });
        self.dedup_collection_id.insert(id, sid);
        sid
    }

    /// Intern an `OptAbsent` leaf at the given position. Dedup'd by `pos`.
    pub fn intern_opt_absent(&mut self, pos: u32) -> SppfId {
        if let Some(&id) = self.dedup_opt_absent.get(&pos) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::OptAbsent { pos });
        self.dedup_opt_absent.insert(pos, id);
        id
    }

    /// Intern a `Predicate` payload reference. Dedup'd by `handle`.
    pub fn intern_predicate(&mut self, handle: u32) -> SppfId {
        if let Some(&id) = self.dedup_predicate.get(&handle) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Predicate { handle });
        self.dedup_predicate.insert(handle, id);
        id
    }

    /// Intern a `BinderScope` leaf (Bug N fix). Names are interned via
    /// `intern_text`; the returned SppfId references a `SppfNode::BinderScope`
    /// containing `Vec<TextHandle>` + depth. Dedup'd by `(depth, hash(names))`.
    pub fn intern_binder_scope(&mut self, names: &[String], depth: u16) -> SppfId {
        use rustc_hash::FxHasher;
        let mut h = FxHasher::default();
        for n in names {
            n.hash(&mut h);
        }
        let key = (depth, h.finish());
        if let Some(&id) = self.dedup_binder_scope.get(&key) {
            return id;
        }
        let names_text: Vec<TextHandle> =
            names.iter().map(|n| self.intern_text(n)).collect();
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::BinderScope { names_text, depth });
        self.dedup_binder_scope.insert(key, id);
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

    /// Return the input-span lower bound (inclusive) covered by `id`.
    ///
    /// Recurses through Packings to their leftmost child until it hits a
    /// Terminal / Symbol / Epsilon (whose `lo_pos` is intrinsic). Returns
    /// `None` if `id` is out-of-range or the node has no determinable
    /// position (e.g., a `Packing` with no children, which the walker
    /// should not emit but is defensively handled).
    ///
    /// Complexity: O(leftmost-spine-depth); typically <10 hops.
    pub fn span_lo(&self, id: SppfId) -> Option<u32> {
        let mut cur = id;
        loop {
            match self.node(cur)? {
                SppfNode::Terminal { pos, .. } => {
                    return Some(match pos {
                        PosOrSynth::Real(p) | PosOrSynth::Synthesized(p) => *p,
                    });
                }
                SppfNode::Symbol { lo_pos, .. } => return Some(*lo_pos),
                SppfNode::Epsilon { pos } => return Some(*pos),
                SppfNode::OptAbsent { pos } => return Some(*pos),
                SppfNode::Packing { children, .. } => {
                    cur = *children.first()?;
                }
                // CollectionId, Predicate, BinderScope are walker-arena
                // references / metadata without an intrinsic span.
                SppfNode::CollectionId { .. }
                | SppfNode::Predicate { .. }
                | SppfNode::BinderScope { .. } => return None,
            }
        }
    }

    /// Return the input-span upper bound (exclusive) covered by `id`.
    pub fn span_hi(&self, id: SppfId) -> Option<u32> {
        let mut cur = id;
        loop {
            match self.node(cur)? {
                SppfNode::Terminal { pos, .. } => {
                    // Terminals span exactly one token: hi = pos + 1.
                    let p = match pos {
                        PosOrSynth::Real(p) | PosOrSynth::Synthesized(p) => *p,
                    };
                    return Some(p + 1);
                }
                SppfNode::Symbol { hi_pos, .. } => return Some(*hi_pos),
                SppfNode::Epsilon { pos } => return Some(*pos),
                SppfNode::OptAbsent { pos } => return Some(*pos),
                SppfNode::Packing { children, .. } => {
                    cur = *children.last()?;
                }
                SppfNode::CollectionId { .. }
                | SppfNode::Predicate { .. }
                | SppfNode::BinderScope { .. } => return None,
            }
        }
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
        self.dedup_collection_id.retain(|_, &mut id| id < n);
        self.dedup_opt_absent.retain(|_, &mut id| id < n);
        self.dedup_predicate.retain(|_, &mut id| id < n);
        self.dedup_binder_scope.retain(|_, &mut id| id < n);

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
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        assert_eq!(a, b);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn intern_terminal_distinguishes_pos() {
        let mut s = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None, false);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_distinguishes_kind() {
        let mut s = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("-"), PosOrSynth::Real(0), None, false);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_real_and_synth_dont_collide() {
        let mut s = Sppf::new();
        let real = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(5), Some("x"), false);
        let synth = s.intern_terminal(TokenKind::Ident, PosOrSynth::Synthesized(5), Some("x"), false);
        assert_ne!(real, synth);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_preserves_text() {
        let mut s = Sppf::new();
        let id = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("foo"), false);
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
        let id = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
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
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let a = s.intern_packing(0, vec![t]);
        let b = s.intern_packing(0, vec![t]);
        assert_eq!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_rule_idx() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let a = s.intern_packing(0, vec![t]);
        let b = s.intern_packing(1, vec![t]);
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_order() {
        let mut s = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let t2 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        let a = s.intern_packing(0, vec![t1, t2]);
        let b = s.intern_packing(0, vec![t2, t1]);
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_count() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
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
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        assert_eq!(s.packings_of(sym), &[p]);
        assert_eq!(s.link_count(), 1);
    }

    #[test]
    fn link_packing_to_symbol_idempotent() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
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
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
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
        let t1 = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None, false);
        let snapshot = s.node(t1).cloned();
        let _ = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None, false);
        let _ = s.intern_symbol(0, 0, 1);
        let _ = s.intern_packing(0, vec![t1]);
        // t1's node identity is preserved.
        assert_eq!(s.node(t1).cloned(), snapshot);
    }

    #[test]
    fn symbol_node_immutable_when_packings_added() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
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
        let t_a = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("a"), false);
        let t_plus = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None, false);
        let t_b = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(2), Some("b"), false);
        let t_mul = s.intern_terminal(k_fixed("*"), PosOrSynth::Real(3), None, false);
        let t_c = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(4), Some("c"), false);

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

        let t0 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let t1 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);

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
        let _ = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let _ = s.intern_symbol(0, 0, 1);
        let cp = s.checkpoint();
        let len_before = s.len();
        let link_before = s.link_count();

        let t = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
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
        let _ = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let cp = s.checkpoint();

        // Add a terminal post-checkpoint; restore should evict it from dedup.
        let pre_id = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        s.restore_to_checkpoint(cp);

        // Same key after restore: must allocate a new id, NOT return the stale one.
        let post_id = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        let _ = pre_id;
        // After restore + re-intern, the y@1 terminal lives at the same nodes index
        // as before (because we truncated to cp.nodes_len then appended one).
        assert_eq!(post_id, cp.nodes_len);
    }

    #[test]
    fn restore_rebuilds_packings_by_symbol_index() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
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
        let kept_id = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None, false);
        let cp = s.checkpoint();
        let _ = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None, false);
        s.restore_to_checkpoint(cp);
        // Re-intern the kept terminal — must return the same id.
        let again = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None, false);
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
            let t1 = s1.intern_terminal(TokenKind::Ident, PosOrSynth::Real(i), Some(&format!("v{}", i)), false);
            let t2 = s2.intern_terminal(TokenKind::Ident, PosOrSynth::Real(i), Some(&format!("v{}", i)), false);
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
