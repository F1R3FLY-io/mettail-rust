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
//! - `W` reverts to a normal semiring weight (e.g. `LexicographicWeight`) and
//!   is parameterized here — Packings carry per-production weight, Symbols
//!   carry `weight_sum` aggregated via `⊕` over linked packings.
//! - **This module** owns the AST identity, as a Tomita/Scott-Johnstone
//!   packed parse forest.
//!
//! ## Phase C parameterization (2026-05-17)
//!
//! `Sppf<W: SemiringRef>` carries weights on Packing nodes (per-production
//! increment) and on Symbol nodes (⊕-aggregated weight sum). Non-Goodman
//! leaves (Terminal, Epsilon, OptAbsent, Predicate, CollectionId, BinderScope)
//! contribute `W::one_ref()` implicitly. See
//! `~/.claude/plans/phase-c-sppf-w-resolved.md` for the design.
//!
//! ## Shape
//!
//! Four primary node types, one Vec-backed arena, append-only dedup tables.
//!
//! ```text
//! enum SppfNode<W> {
//!     Terminal { token_kind, text_handle, pos, pushed_via_push_ident }
//!     Symbol   { non_terminal_tag, lo_pos, hi_pos, weight_sum: W }
//!     Packing  { rule_idx, children, weight: W }
//!     Epsilon  { pos }
//!     CollectionId { id, items }
//!     OptAbsent { pos }
//!     Predicate { handle }
//!     BinderScope { names_text, depth }
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
//! Phase C exception: Packing.weight may be ⊕-mutated on dedup hit. This
//! is monotone aggregation over an idempotent semiring (for cyclic realize)
//! and does NOT violate the "node identity is stable" invariant — the same
//! SppfId still maps to the same `(rule_idx, children)` packing; only the
//! aggregated weight grows by ⊕.
//!
//! ## Determinism (plan §11.5 invariants I1–I3)
//!
//! - Same input → same Symbol/Packing/Terminal SppfId, regardless of intern
//!   order (dedup tables guarantee).
//! - `dedup_packing` uses `FxHashMap` (deterministic) NOT `HashMap` (random).
//! - Phase C R6 fix: dedup_packing key is now full `(rule_idx, Vec<SppfId>)`
//!   not a 64-bit hash digest, eliminating collision-based silent merges.
//!
//! ## References
//!
//! - Tomita, M. (1986). *Efficient parsing for natural language.* §6.3, §6.4
//!   — the canonical packed-node + family-list shape.
//! - Scott, E. & Johnstone, A. (2010). *GLL parsing.* ENTCS 253(7). §3, §4 —
//!   the SPPF-construction-at-reduce-time discipline; Theorem 1 (cubic bound).
//! - Goodman, J. (1999). *Semiring parsing.* Comp. Ling. 25(4) — per-production
//!   weight + ⊕ at symbol = parse-forest weighting framework.

use crate::automata::semiring::SemiringRef;
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
///
/// Phase C: `Packing` carries a per-production `weight: W` (Q1.A+ pending
/// packing weight). `Symbol` carries a `weight_sum: W` aggregated via `⊕`
/// over linked packings' `(weight ⊗ children-product)`. The recursive
/// children-product is computed at realize time, NOT at link time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SppfNode<W: SemiringRef> {
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
    /// triple by dedup. Symbol nodes are IMMUTABLE after allocation EXCEPT
    /// for the `weight_sum` field which is `⊕`-aggregated as Packings link.
    /// The set of derivations attached to a Symbol grows via the side table
    /// `Sppf::symbol_packings`, never by mutating this struct's children.
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
        /// Phase C weight aggregator. Initialized to `W::zero_ref()` at
        /// intern time. Each `link_packing_to_symbol(symbol, packing)` call
        /// updates this via `weight_sum := weight_sum ⊕ packing.weight`.
        /// (The children-product factor is folded in at realize time, not
        /// at link time, because children's weight_sums may still be
        /// growing — adding the packing's own weight here keeps it
        /// monotone under idempotent semirings.)
        weight_sum: W,
    },

    /// A Packing node — one derivation alternative for some parent Symbol.
    /// Carries the production's rule_idx, an ordered children list, and the
    /// per-production weight (Phase C Q1.A+).
    Packing {
        /// Which production produced this derivation. Identifies the action
        /// function to invoke during realization.
        rule_idx: u32,
        /// Ordered children (Terminal / Symbol / Epsilon SppfIds).
        children: Vec<SppfId>,
        /// Phase C weight = `pending_packing_weight` captured at the
        /// `emit_fire_action` call that interned this Packing. `W::one_ref()`
        /// for productions reached via non-Fork code paths. For dedup-hit
        /// re-interns, this field is `⊕`-updated:
        /// `self.weight := self.weight.plus_ref(&new_weight)`.
        weight: W,
    },

    /// Sentinel for empty productions (epsilon). Has a position so that
    /// distinct empty rules at distinct positions don't collide in dedup.
    Epsilon {
        /// The position at which this epsilon was recognized.
        pos: u32,
    },

    /// Placeholder for a collection slot's identity argument. Pushed by
    /// `emit_push_collection_id` to mirror the builder's
    /// `ActionArg::CollectionId`.
    ///
    /// Collection-accumulation fix (2026-05-29): elements are now stored
    /// **derivation-locally** in `items`, captured at the `emit_fire_action`
    /// fire site as a snapshot of the owning cursor's
    /// `BranchCursor::sppf_collection_arena[id]`. Previously the node carried
    /// only `id` and was dedup'd by `id`, forcing realize to read
    /// `winner_collection_arena()` = `branch_cursors[0]` — the WRONG cursor —
    /// which truncated/emptied collections. The realization pass now walks
    /// `items` directly (no per-cursor side-table), so each derivation keeps
    /// its own elements.
    CollectionId {
        /// The slot index this marker mirrors (still used by the action
        /// reconstruction to thread `ActionArg::CollectionId(id)`).
        id: u32,
        /// The derivation-local collected element SppfIds. Snapshot of the
        /// owning cursor's `sppf_collection_arena[id]` at fire time. Distinct
        /// `items` => distinct nodes (no longer dedup'd by `id`); `Packing`
        /// dedup `(rule_idx, children)` still merges truly-identical
        /// derivations and now correctly separates differing ones.
        items: Vec<crate::sppf::SppfId>,
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

    /// Phase F.8 (2026-05-18): unary-prefix trigger token. A consumed prefix
    /// literal (e.g., `"not"` in `Not . a:Bool |- "not" a : Bool`) is
    /// mirrored to `sppf_stack` as a TriggerTerminal so the enclosing rule's
    /// packing carries a span-bearing leaf at the trigger's input position.
    /// Without this, the unary-prefix rule's Symbol shares `(nt, lo, hi)`
    /// with its sole operand → SPPF Symbol-dedup collapses both packings,
    /// `realize_root_to_terms_with_weights` (called with `limit: Some(1)`)
    /// picks the inner packing in insertion order, and the wrapping rule is
    /// silently dropped.
    ///
    /// **Filtering semantics**: TriggerTerminal contributes NO `ActionArg` to
    /// the realize-time cartesian product. `realize_packing_call` filters
    /// TriggerTerminal children before constructing the action_fn args list,
    /// so the rule's declared arity is preserved (a unary-prefix rule has
    /// arity=1; the trigger is auxiliary).
    ///
    /// **Span semantics**: `span_lo` and `span_hi` return `pos` and `pos+1`
    /// respectively (identical to `Terminal`). This shifts the parent rule's
    /// interned Symbol's `lo_pos` from "first operand's lo" to "trigger's
    /// pos" → distinct Symbol id from the operand's Symbol.
    ///
    /// **Ownership tagging**: `owner_cat` + `owner_rule_idx` identify the
    /// rule whose `ConsumeAndPush` produced this trigger. At reduce time
    /// (`emit_fire_action`) the walk-back drain claims a TriggerTerminal
    /// ONLY when these match the firing rule's `(cat_src_idx,
    /// rule_index_in_category)`. Without this gate, an inner rule firing
    /// inside the operand sub-parse (e.g., `BoolLit` for `true` inside
    /// `Not true`) would greedily claim the outer rule's TriggerTerminal,
    /// leaving the outer rule with no trigger and reintroducing the
    /// Symbol-dedup collision.
    TriggerTerminal {
        /// Lexer's classification of the consumed trigger token (e.g.,
        /// `TokenKind::Fixed("not".to_string())`).
        token_kind: TokenKind,
        /// Pooled text handle (may be `TEXT_HANDLE_NONE` for `Fixed` triggers
        /// where the kind already encodes the lexeme).
        text_handle: TextHandle,
        /// Input position of the trigger token. Always `Real(_)` in practice;
        /// `Synthesized` is reserved for the (`Terminal`) recovery path.
        pos: PosOrSynth,
        /// Category source index of the owning rule (the rule whose
        /// `ConsumeAndPush` pushed this trigger).
        owner_cat: u16,
        /// Rule index within `owner_cat` of the owning rule.
        owner_rule_idx: u16,
    },

    /// ROOT-P Canonical-GLL Stage E1 (2026-07-09): a BINARIZED intermediate
    /// SPPF node — Scott & Johnstone (2010) §5 / BRNGLR `getNodeP`. Represents
    /// a PARTIAL right-hand-side derivation `slot • ` (the left-fold of the
    /// first `dot` children of a production) as a SINGLE packed node, so a
    /// canonical-GLL descriptor can carry ONE owner-free `w` instead of an
    /// exponential per-cursor operand STACK. Like `Symbol` it carries NO direct
    /// children: its derivations link via the append-only `symbol_packings`
    /// side table (each packing is a binary `[left, right]` pair — the prefix
    /// intermediate and the newly-consumed child). Deduped by
    /// `(slot_id, lo_pos, hi_pos)`, so two partial derivations of the SAME
    /// grammar slot reaching the same span collapse to ONE node with multiple
    /// packings (canonical ambiguity ⇒ packing family, exactly like `Symbol`).
    ///
    /// **Owner-free by construction**: the label is `(slot_id, lo, hi)` — the
    /// grammar production + dot + span — NEVER a trigger's `(owner_cat,
    /// owner_rule_idx)`. This is what dissolves the Stage-E owner-attribution
    /// tension: the N `@`-owner rules stay DISTINCT via `slot_id`
    /// (`slot_id = (global_rule_idx << 8) | dot`) without owner-masking, so a
    /// poly descriptor set keeps every reading's reduce alive.
    ///
    /// **Constructed ONLY under `CANONICAL_GLL_ENABLED` + `PRATTAIL_CGLL_BINARIZE`**
    /// (`intern_intermediate`, reached solely from `cgll_get_node_p`). With the
    /// compile-time const `false` the classic walker NEVER interns one, so
    /// `span_lo`/`span_hi`/`link_packing_to_symbol`/realize never observe this
    /// arm — the default build is byte-identical (the arm is dead / DCE'd).
    Intermediate {
        /// Grammar slot + dot: `(global_rule_idx << 8) | dot`. Identifies the
        /// production and how many RHS symbols have been folded so far.
        slot_id: u32,
        /// Input span start (inclusive) — the production's frame start.
        lo_pos: u32,
        /// Input span end (exclusive) — the right extent of the last folded
        /// child.
        hi_pos: u32,
        /// `⊕`-aggregated weight over linked packings (mirrors `Symbol`).
        weight_sum: W,
    },
}

// ══════════════════════════════════════════════════════════════════════════════
// SppfCheckpoint
// ══════════════════════════════════════════════════════════════════════════════

/// Truncation watermarks for restoring the SPPF arena to a prior state.
///
/// Supports LSP-style incremental reparse: the append-only arena invariant
/// guarantees that truncating the three vectors to these lengths produces
/// exactly the state the arena was in when the checkpoint was recorded. (The
/// Stage-5 `WpdaIncrementalSession` that drove this reparse was removed in the
/// S1-S6 single-engine re-platform.)
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
///
/// Phase C parameterizes over `W: SemiringRef`. Packing nodes carry
/// per-production weights; Symbol nodes carry `weight_sum` aggregated via
/// `⊕` as Packings link. See module doc and
/// `~/.claude/plans/phase-c-sppf-w-resolved.md`.
#[derive(Debug, Clone)]
pub struct Sppf<W: SemiringRef> {
    // Append-only arrays. Truncating these by length restores prior state.
    nodes: Vec<SppfNode<W>>,
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
    ///
    /// RC-D (2026-06-18): key also includes the terminal lexeme. Several
    /// semantic actions (`NumLit`, string literals, fixed literals) read token
    /// text during lazy witness realization. If the first terminal intern at a
    /// `(kind, pos, origin)` key had no text, later same-position terminals
    /// with real text deduped to the empty-text node and their actions elided.
    /// Token text is semantic payload, so it is part of Terminal identity.
    dedup_terminal: FxHashMap<(TokenKind, PosOrSynth, Option<String>, bool), SppfId>,
    dedup_symbol: FxHashMap<(u32, u32, u32), SppfId>,
    /// Phase C R6 fix: full-list key (not a 64-bit hash digest) eliminates
    /// the silent-collision soundness risk. Memory cost is negligible
    /// (~16-24 bytes per typical entry).
    dedup_packing: FxHashMap<(u32, Vec<SppfId>), SppfId>,
    dedup_epsilon: FxHashMap<u32, SppfId>,
    /// Collection-accumulation fix (2026-05-29): CollectionId nodes are now
    /// derivation-local (they carry their own collected element `items`).
    /// Dedup by `(id, items)` — NOT by `id` alone — so two derivations with
    /// the same slot id but DIFFERENT collected elements stay distinct
    /// (preserves disambiguation: a truncated and a full collection must not
    /// collapse), while structurally-identical collections still merge. The
    /// merge bounds node growth and prevents the realize cartesian blow-up
    /// (wrong-cardinality regressions) that dropping dedup entirely caused.
    /// Mirrors `dedup_packing`'s full-list key (no silent-collision risk).
    dedup_collection_id: FxHashMap<(u32, Vec<SppfId>), SppfId>,
    dedup_opt_absent: FxHashMap<u32, SppfId>,
    dedup_predicate: FxHashMap<u32, SppfId>,
    /// Bug N (Phase 3.1.5): dedup BinderScope by `(depth, names_hash)`.
    /// Two cursors emitting the same scope contents at the same depth
    /// collapse to the same SppfId.
    dedup_binder_scope: FxHashMap<(u16, u64), SppfId>,
    /// Phase F.8 (2026-05-18): dedup TriggerTerminal by `(kind, pos,
    /// owner_cat, owner_rule_idx)`. Two cursors emitting the same prefix
    /// trigger at the same input position FOR THE SAME owning rule
    /// collapse to the same SppfId. `owner_cat` / `owner_rule_idx` are
    /// part of the key because two different unary-prefix rules in
    /// different categories could share the SAME trigger token at the
    /// SAME input position (e.g., `"!"` used as postfix in one cat and
    /// prefix in another); they must remain distinct so the walk-back
    /// gate in `emit_fire_action` can claim only the matching one.
    /// Distinct namespace from `dedup_terminal` because Terminals carry
    /// an extra `pushed_via_push_ident: bool` discriminator that
    /// TriggerTerminals don't need (they never produce `ActionArg`s).
    dedup_trigger_terminal: FxHashMap<(TokenKind, PosOrSynth, u16, u16), SppfId>,
    /// ROOT-P Canonical-GLL Stage E1 (2026-07-09): dedup `Intermediate` nodes by
    /// `(slot_id, lo_pos, hi_pos)` — a SEPARATE namespace from `dedup_symbol`
    /// (an Intermediate and a Symbol may share `(lo, hi)` but never collide).
    /// Populated ONLY by `intern_intermediate` (reached under
    /// `CANONICAL_GLL_ENABLED` + `PRATTAIL_CGLL_BINARIZE`); empty on the classic
    /// path ⇒ byte-identical default (the map is one idle `FxHashMap`).
    dedup_intermediate: FxHashMap<(u32, u32, u32), SppfId>,

    // Derived indices — strictly rebuildable from `symbol_packings`. Rebuilt
    // on checkpoint restore.
    link_dedup: FxHashSet<(SppfId, SppfId)>,
    packings_by_symbol: FxHashMap<SppfId, Vec<SppfId>>,
}

// Manual Default impl: derive(Default) would require all field types' Default,
// but `SppfNode<W>` does not derive Default. None of `Sppf<W>`'s fields hold
// `W` directly, so Default is straightforward.
impl<W: SemiringRef> Default for Sppf<W> {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            text_arena: Vec::new(),
            text_index: Vec::new(),
            symbol_packings: Vec::new(),
            dedup_terminal: FxHashMap::default(),
            dedup_symbol: FxHashMap::default(),
            dedup_packing: FxHashMap::default(),
            dedup_epsilon: FxHashMap::default(),
            dedup_collection_id: FxHashMap::default(),
            dedup_opt_absent: FxHashMap::default(),
            dedup_predicate: FxHashMap::default(),
            dedup_binder_scope: FxHashMap::default(),
            dedup_trigger_terminal: FxHashMap::default(),
            dedup_intermediate: FxHashMap::default(),
            link_dedup: FxHashSet::default(),
            packings_by_symbol: FxHashMap::default(),
        }
    }
}

impl<W: SemiringRef> Sppf<W> {
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
        // Dedup key: (kind, pos, text, pushed_via_push_ident). Text is
        // semantic payload for token-capturing actions, not recoverable from
        // kind+pos once terminals are shared across speculative branches.
        let text_key = text.map(str::to_owned);
        let key = (token_kind.clone(), pos, text_key.clone(), pushed_via_push_ident);
        if let Some(&id) = self.dedup_terminal.get(&key) {
            return id;
        }
        let text_handle = match text_key.as_deref() {
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

    /// Phase F.8 (2026-05-18): intern a `TriggerTerminal` for a consumed
    /// unary-prefix trigger token. Mirrors `intern_terminal` but writes to
    /// `dedup_trigger_terminal`. The trigger never participates in
    /// `ActionArg` construction; it exists to give the parent rule's
    /// interned Symbol a distinct `lo_pos` from its operand's Symbol.
    ///
    /// `owner_cat` + `owner_rule_idx` identify the rule whose
    /// `ConsumeAndPush` produced this trigger; the walk-back drain in
    /// `emit_fire_action` claims a TriggerTerminal ONLY when these match
    /// the firing rule.
    pub fn intern_trigger_terminal(
        &mut self,
        token_kind: TokenKind,
        pos: PosOrSynth,
        text: Option<&str>,
        owner_cat: u16,
        owner_rule_idx: u16,
    ) -> SppfId {
        let key = (token_kind.clone(), pos, owner_cat, owner_rule_idx);
        if let Some(&id) = self.dedup_trigger_terminal.get(&key) {
            return id;
        }
        let text_handle = match text {
            Some(s) => self.intern_text(s),
            None => TEXT_HANDLE_NONE,
        };
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::TriggerTerminal {
            token_kind,
            text_handle,
            pos,
            owner_cat,
            owner_rule_idx,
        });
        self.dedup_trigger_terminal.insert(key, id);
        id
    }

    /// Intern a Symbol identity node. Returns the existing id if `(nt, lo, hi)`
    /// was already interned, else allocates.
    ///
    /// Symbol identity is preserved across all derivations of the same span:
    /// two cursors that reduce DIFFERENT productions to the same `(nt, lo, hi)`
    /// get the SAME SppfId. They then call `link_packing_to_symbol` separately
    /// to attach their respective Packings.
    ///
    /// Phase C: new Symbols initialize `weight_sum = W::zero_ref()` (the
    /// `⊕`-identity). Each subsequent `link_packing_to_symbol` updates it
    /// monotonically by `⊕`-ing in the linked packing's `weight`.
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
            weight_sum: W::zero_ref(),
        });
        self.dedup_symbol.insert(key, id);
        id
    }

    /// Look up an already-interned Symbol identity node without allocating.
    pub fn symbol_id(&self, nt_tag: u32, lo_pos: u32, hi_pos: u32) -> Option<SppfId> {
        self.dedup_symbol.get(&(nt_tag, lo_pos, hi_pos)).copied()
    }

    /// ROOT-P Canonical-GLL Stage E1 (2026-07-09): intern a BINARIZED
    /// `Intermediate` identity node — a clone of [`Sppf::intern_symbol`] against
    /// the separate [`Sppf::dedup_intermediate`] table. Returns the existing id
    /// if `(slot_id, lo, hi)` was already interned, else allocates. Two partial
    /// derivations of the SAME grammar slot reaching the same span collapse to
    /// ONE node (canonical dedup); their distinct `[left, right]` packings link
    /// separately via [`Sppf::link_packing_to_symbol`] (which accepts
    /// `Intermediate` as its parent). `weight_sum` initializes to the
    /// `⊕`-identity, `⊕`-aggregated as packings link (mirrors `Symbol`).
    ///
    /// Reached ONLY from `WpdaWalker::cgll_get_node_p` under
    /// `CANONICAL_GLL_ENABLED` + `PRATTAIL_CGLL_BINARIZE`; never on the classic
    /// path (byte-identical default).
    pub fn intern_intermediate(&mut self, slot_id: u32, lo_pos: u32, hi_pos: u32) -> SppfId {
        let key = (slot_id, lo_pos, hi_pos);
        if let Some(&id) = self.dedup_intermediate.get(&key) {
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::Intermediate {
            slot_id,
            lo_pos,
            hi_pos,
            weight_sum: W::zero_ref(),
        });
        self.dedup_intermediate.insert(key, id);
        id
    }

    /// Intern a Packing (one derivation). Returns the existing id if a
    /// structurally identical Packing was already interned, else allocates.
    ///
    /// Phase C: takes a per-production `weight: W` (Q1.A+). On a dedup hit
    /// (same `(rule_idx, children)`), the stored Packing's weight is
    /// `⊕`-updated: `self.weight = self.weight.plus_ref(&weight)`. This is
    /// Goodman-style aggregation: two cursors reducing the same production
    /// at the same span via different lex-Fork branches contribute their
    /// branch weights additively.
    pub fn intern_packing(&mut self, rule_idx: u32, children: Vec<SppfId>, weight: W) -> SppfId {
        // Phase C R6: full-list key, no hash truncation.
        let key = (rule_idx, children.clone());
        if let Some(&id) = self.dedup_packing.get(&key) {
            // Dedup hit: ⊕-aggregate the new contribution into stored weight.
            if let Some(SppfNode::Packing { weight: w, .. }) = self.nodes.get_mut(id as usize) {
                *w = w.plus_ref(&weight);
            }
            return id;
        }
        let id = self.nodes.len() as SppfId;
        self.nodes
            .push(SppfNode::Packing { rule_idx, children, weight });
        self.dedup_packing.insert(key, id);
        id
    }

    /// RC-B (2026-06-17): does a Packing with exactly `(rule_idx, children)`
    /// already exist? Read-only probe over the same `dedup_packing` key
    /// `intern_packing` uses. Used as the +0-cursor "unfired" guard for the
    /// pop-site prefix-cast wrap reconciliation: when the cast already fired on
    /// its own delegate lineage the packing exists, so the reconciliation bails
    /// and the passing corpus stays byte-identical.
    pub fn packing_exists(&self, rule_idx: u32, children: &[SppfId]) -> bool {
        self.dedup_packing
            .contains_key(&(rule_idx, children.to_vec()))
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

    /// Intern a `CollectionId` marker for slot `id` carrying its
    /// derivation-local collected `items`.
    ///
    /// Collection-accumulation fix (2026-05-29): NO dedup-by-id. Distinct
    /// `items` must be distinct nodes so realize can recover each
    /// derivation's own collection from the node itself (rather than from
    /// the post-commit `branch_cursors[0]` arena, which truncated collections
    /// belonging to non-winner cursors). `Packing` dedup `(rule_idx,
    /// children)` still collapses truly-identical derivations and now
    /// correctly separates derivations whose collections differ.
    pub fn intern_collection_id(&mut self, id: u32, items: Vec<SppfId>) -> SppfId {
        // Dedup by (id, items): identical collections merge (bounds node
        // growth, prevents the realize cartesian blow-up); collections with
        // differing elements stay distinct (preserves disambiguation).
        let key = (id, items.clone());
        if let Some(&sid) = self.dedup_collection_id.get(&key) {
            return sid;
        }
        let sid = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::CollectionId { id, items });
        self.dedup_collection_id.insert(key, sid);
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
        let names_text: Vec<TextHandle> = names.iter().map(|n| self.intern_text(n)).collect();
        let id = self.nodes.len() as SppfId;
        self.nodes.push(SppfNode::BinderScope { names_text, depth });
        self.dedup_binder_scope.insert(key, id);
        id
    }

    /// Link a Packing to a Symbol. Idempotent (O(1) check). The link is
    /// appended to `symbol_packings` only if not already present.
    ///
    /// Phase C: on a fresh link, the Symbol's `weight_sum` is updated via
    /// `weight_sum := weight_sum ⊕ packing.weight`. On a duplicate link
    /// the update is skipped (the contribution was already counted).
    ///
    /// Pre-condition: `symbol_id` refers to a `SppfNode::Symbol` and
    /// `packing_id` refers to a `SppfNode::Packing`. Debug-asserted.
    pub fn link_packing_to_symbol(&mut self, symbol_id: SppfId, packing_id: SppfId) {
        debug_assert!(
            // ROOT-P Stage E1: the parent may be a `Symbol` (classic) OR an
            // `Intermediate` (binarized `getNodeP`; canonical-only, gated).
            matches!(
                self.node(symbol_id),
                Some(SppfNode::Symbol { .. }) | Some(SppfNode::Intermediate { .. })
            ),
            "link_packing_to_symbol: symbol_id {} is not a Symbol/Intermediate node",
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
            // Phase C: aggregate packing.weight into symbol.weight_sum.
            let packing_w = match self.nodes.get(packing_id as usize) {
                Some(SppfNode::Packing { weight, .. }) => weight.clone(),
                _ => W::one_ref(),
            };
            match self.nodes.get_mut(symbol_id as usize) {
                Some(SppfNode::Symbol { weight_sum, .. })
                // ROOT-P Stage E1: `Intermediate` aggregates weight exactly like
                // `Symbol` (canonical-only; never taken on the classic path).
                | Some(SppfNode::Intermediate { weight_sum, .. }) => {
                    *weight_sum = weight_sum.plus_ref(&packing_w);
                },
                _ => {},
            }
        }
    }

    // ── accessors ───────────────────────────────────────────────────────────

    /// Borrow a node by id. Returns `None` if the id is out of range.
    pub fn node(&self, id: SppfId) -> Option<&SppfNode<W>> {
        self.nodes.get(id as usize)
    }

    /// Phase F.13 H12 Stage 1.3.1 (2026-05-21): aggregate weight of a
    /// Symbol node — the `weight_sum` field that accumulates `⊕`-updates
    /// from each linked Packing (Goodman-style aggregation per
    /// `link_packing_to_symbol`). Used by the cohort-cache revive path
    /// to derive the sub-parse's weight delta (`pre_dispatch × symbol_weight_sum`
    /// is the LexicographicWeight-canonical cohort-final weight).
    ///
    /// Returns `W::one_ref()` for non-Symbol nodes (defensive default —
    /// `times_ref` against one is identity).
    pub fn symbol_weight_sum(&self, id: SppfId) -> W {
        match self.node(id) {
            Some(SppfNode::Symbol { weight_sum, .. }) => weight_sum.clone(),
            _ => W::one_ref(),
        }
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
    /// Phase F.13 chain_10000 Exp 16 (2026-05-26): node arena size
    /// diagnostic (total node count, all variants). Used by walker
    /// memory-attribution sampling.
    pub fn node_count_diag(&self) -> usize {
        self.nodes.len()
    }

    /// Phase F.13 chain_10000 Exp 16 round 3 (2026-05-26): SPPF
    /// auxiliary storage size diagnostic. Returns
    /// `(text_arena_bytes, text_index_count, dedup_packing_children_bytes,
    ///   dedup_symbol_count, dedup_terminal_count)`.
    /// Used to identify which SPPF-side accumulator scales super-
    /// linearly beyond what `node_count_diag` captures.
    pub fn dedup_table_sizes_diag(&self) -> (usize, usize, usize, usize, usize) {
        let text_arena_bytes = self.text_arena.len();
        let text_index_count = self.text_index.len();
        // dedup_packing keys are (u32, Vec<SppfId>). The Vec<SppfId>
        // grows with rule arity; the per-rule arity is bounded but
        // the per-rule INSTANCE count grows with parse size. Sum the
        // Vec lengths × 4 bytes (SppfId = u32) for total child-bytes.
        let dedup_packing_children_bytes: usize = self
            .dedup_packing
            .keys()
            .map(|(_, children)| children.len() * 4)
            .sum();
        let dedup_symbol_count = self.dedup_symbol.len();
        let dedup_terminal_count = self.dedup_terminal.len();
        (
            text_arena_bytes,
            text_index_count,
            dedup_packing_children_bytes,
            dedup_symbol_count,
            dedup_terminal_count,
        )
    }

    /// Phase F.13 chain_10000 Exp 16 (2026-05-26): symbol_packings
    /// link-table size diagnostic. Used by walker memory-attribution
    /// sampling.
    pub fn symbol_packings_count_diag(&self) -> usize {
        self.symbol_packings.len()
    }

    /// Phase F.13 chain_10000 Plan D E4 Substage 1.a (2026-05-26):
    /// diagnostic accessor for the Streaming SPPF reclamation-window
    /// instrumentation. Returns `(symbols_below, total_symbols)`
    /// where `symbols_below` is the count of `Symbol` nodes with
    /// `hi_pos < threshold` (i.e., reclamation candidates whose
    /// extent is entirely below the live frontier). `total_symbols`
    /// is the count of all `Symbol` nodes (denominator).
    ///
    /// O(n) over the node arena. Walker should not call this on the
    /// hot path; per Plan agent S1.a the sample frequency is
    /// per-step_fanout-iteration, which is amortized over many
    /// per-cursor steps.
    pub fn count_symbols_below_hi(&self, threshold: u32) -> (u64, u64) {
        let mut below: u64 = 0;
        let mut total: u64 = 0;
        for n in &self.nodes {
            if let SppfNode::Symbol { hi_pos, .. } = n {
                total += 1;
                if *hi_pos < threshold {
                    below += 1;
                }
            }
        }
        (below, total)
    }

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
                },
                // Phase F.8: TriggerTerminal carries a real input position;
                // span_lo returns that position so the parent rule's
                // interned Symbol receives `lo = trigger_pos`.
                SppfNode::TriggerTerminal { pos, .. } => {
                    return Some(match pos {
                        PosOrSynth::Real(p) | PosOrSynth::Synthesized(p) => *p,
                    });
                },
                SppfNode::Symbol { lo_pos, .. } => return Some(*lo_pos),
                // ROOT-P Stage E1: Intermediate carries its span explicitly
                // (like Symbol); canonical-only.
                SppfNode::Intermediate { lo_pos, .. } => return Some(*lo_pos),
                SppfNode::Epsilon { pos } => return Some(*pos),
                SppfNode::OptAbsent { pos } => return Some(*pos),
                SppfNode::Packing { children, .. } => {
                    cur = *children.first()?;
                },
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
                },
                // Phase F.8: TriggerTerminal spans exactly one token (the
                // consumed trigger literal): hi = pos + 1.
                SppfNode::TriggerTerminal { pos, .. } => {
                    let p = match pos {
                        PosOrSynth::Real(p) | PosOrSynth::Synthesized(p) => *p,
                    };
                    return Some(p + 1);
                },
                SppfNode::Symbol { hi_pos, .. } => return Some(*hi_pos),
                // ROOT-P Stage E1: Intermediate carries its span explicitly
                // (like Symbol); canonical-only.
                SppfNode::Intermediate { hi_pos, .. } => return Some(*hi_pos),
                SppfNode::Epsilon { pos } => return Some(*pos),
                SppfNode::OptAbsent { pos } => return Some(*pos),
                SppfNode::Packing { children, .. } => {
                    cur = *children.last()?;
                },
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
    /// Phase C: Symbol weight_sums are NOT restored by this routine — they
    /// reflect aggregation history. After restore, callers that need exact
    /// weight_sum reconstruction should re-replay `link_packing_to_symbol`
    /// for the surviving links (or, more cheaply, accept the post-restore
    /// weight_sums as a conservative ⊕-aggregation over a superset, which
    /// is still safe under idempotent semirings since `w ⊕ w = w`).
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
        self.dedup_trigger_terminal.retain(|_, &mut id| id < n);

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
}

// ══════════════════════════════════════════════════════════════════════════════
// Phase C-bis Commit 2 (2026-05-17): Tarjan SCC + PackingFactored
// helpers for closed-semiring cycle handling.
//
// Per `docs/design/plans/closed-semiring-cycle-handling.md` §7 Steps 1
// and 3. These helpers expose SCC structure and per-packing
// decomposition that the Newton-method solver (in
// `prattail/src/automata/semiring.rs::solve_scc_weights_newton`)
// consumes.
// ══════════════════════════════════════════════════════════════════════════════

/// Strongly-connected component identifier (index into the SCC vector
/// returned by [`Sppf::tarjan_sccs`]). Stable per-realize-call only —
/// not preserved across calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SccId(pub usize);

/// Phase C-bis (2026-05-17, per
/// `docs/design/plans/closed-semiring-cycle-handling.md` §7 Step 3):
/// factored representation of an SPPF Packing for its contribution to
/// a non-trivial SCC's inside-weight fixpoint.
///
/// Preserves the full structural decomposition (in-SCC children +
/// outside-product) — does NOT prematurely flatten into a linear
/// A-matrix entry. This is essential for Newton's method
/// (per Esparza-Kiefer-Luttenberger 2007) to compute the correct
/// multi-variable Leibniz differential for **multi-call** packings
/// (those with more than one in-SCC child).
///
/// **Fields**:
///
/// - `target_i`: SCC-local index of the parent Symbol `s_i` (this
///   Packing is in `packings_of(s_i)`).
/// - `outside_product`: per-production `Packing.weight` multiplied
///   by the inside-weights of all children OUTSIDE the SCC. Constant
///   with respect to the cyclic unknowns.
/// - `in_scc_children`: SCC-local indices of the children INSIDE
///   the SCC, in **source order**. Order matters: the partial
///   derivative `∂f/∂Y[c_k]` depends on which factor `Y[c_k]` is
///   differentiated with respect to (the multi-variable Leibniz rule
///   leaves the OTHER factors in place at their current iterate).
///
/// **Why `SmallVec<[usize; 4]>`**: most production packings have ≤ 4
/// in-SCC children (binary operators: 2; ternary/n-ary mixfix: 3-4).
/// Inline storage avoids heap allocation in the common case.
// `PackingFactored` was relocated to the `rigail` crate (single
// source of truth for the weight algebra). Re-exported here to preserve the
// `crate::sppf::PackingFactored` path used by `factor_scc_packing` and the
// walker's Newton-SCC extraction.
pub use rigail::PackingFactored;

impl<W: SemiringRef> Sppf<W> {
    /// Phase C-bis (2026-05-17, per
    /// `docs/design/plans/closed-semiring-cycle-handling.md` §7 Step 1):
    /// strongly-connected components of the **Symbol-induced subgraph**
    /// reachable from `root`.
    ///
    /// **Vertices**: every `SppfNode::Symbol` reachable from `root`.
    ///
    /// **Edges**: `S_i → S_j` iff some `Packing ∈ packings_of(S_i)`
    /// has `S_j` (a Symbol) among `children`. Packings, Terminals,
    /// Epsilons, CollectionIds, Predicates, BinderScopes are
    /// transparent edge-bearers — they don't appear as vertices.
    ///
    /// **Why Symbol-only**: SPPF cycles always traverse at least one
    /// Symbol (they arise from `(nt, lo, hi)` dedup collisions, which
    /// only Symbols experience). Non-Symbol nodes are inherently
    /// acyclic (Packings link to children but children never link back
    /// to Packings; Terminals are leaves; etc.).
    ///
    /// **Algorithm**: iterative Tarjan (Sedgewick 4ed §4.2.3), adapted
    /// from the reference impl at `buchi.rs:798-851`. Avoids
    /// host-stack recursion on deep SPPFs.
    ///
    /// **Complexity**: O(V + E) where V = reachable Symbol count,
    /// E = sum of `packings_of(s).len() × children.len()` over all
    /// reachable Symbols `s`.
    ///
    /// **Output**: SCCs in reverse-topological order (leaf SCCs
    /// first). Each inner `Vec<SppfId>` is one SCC; singleton Vecs
    /// are trivial SCCs (no self-loop is detected here — the caller
    /// must inspect packings for self-loop detection).
    ///
    /// Returns an empty vec if `root` is not a Symbol or `root` is
    /// `SPPF_ID_NONE`.
    pub fn tarjan_sccs(&self, root: SppfId) -> Vec<Vec<SppfId>> {
        // Map SppfId → contiguous internal index for Vec-based state.
        // Visit all reachable Symbol nodes; assign each a sequential id.
        if root == SPPF_ID_NONE {
            return Vec::new();
        }
        let mut id_of: FxHashMap<SppfId, usize> = FxHashMap::default();
        let mut symbols: Vec<SppfId> = Vec::new();
        let mut adj: Vec<Vec<usize>> = Vec::new();
        // BFS/DFS to enumerate reachable Symbols.
        let mut dfs_stack: Vec<SppfId> = Vec::new();
        let mut visited_collect: FxHashSet<SppfId> = FxHashSet::default();
        dfs_stack.push(root);
        while let Some(id) = dfs_stack.pop() {
            if !visited_collect.insert(id) {
                continue;
            }
            match self.node(id) {
                Some(SppfNode::Symbol { .. }) => {
                    if !id_of.contains_key(&id) {
                        let new_idx = symbols.len();
                        id_of.insert(id, new_idx);
                        symbols.push(id);
                        adj.push(Vec::new()); // filled below
                    }
                    // Traverse packings → children (children that are
                    // Symbols become out-edges from this Symbol).
                    for &p in self.packings_of(id) {
                        if let Some(SppfNode::Packing { children, .. }) = self.node(p) {
                            for &c in children {
                                if matches!(self.node(c), Some(SppfNode::Symbol { .. })) {
                                    dfs_stack.push(c);
                                }
                            }
                        }
                    }
                },
                Some(SppfNode::Packing { children, .. }) => {
                    for &c in children {
                        dfs_stack.push(c);
                    }
                },
                Some(SppfNode::CollectionId { .. })
                | Some(SppfNode::Terminal { .. })
                | Some(SppfNode::TriggerTerminal { .. })
                | Some(SppfNode::Epsilon { .. })
                | Some(SppfNode::OptAbsent { .. })
                | Some(SppfNode::Predicate { .. })
                | Some(SppfNode::BinderScope { .. })
                // ROOT-P Stage E1: Intermediate is canonical-only; the classic
                // Tarjan-SCC graph never contains one — treat as a leaf.
                | Some(SppfNode::Intermediate { .. })
                | None => {
                    // Leaves / non-Symbol — no out-edges in the Symbol graph.
                },
            }
        }
        // Build the adjacency list for the Symbol-only graph.
        for (s_idx, &s) in symbols.iter().enumerate() {
            for &p in self.packings_of(s) {
                if let Some(SppfNode::Packing { children, .. }) = self.node(p) {
                    for &c in children {
                        if matches!(self.node(c), Some(SppfNode::Symbol { .. })) {
                            if let Some(&c_idx) = id_of.get(&c) {
                                // Note: we do NOT dedup the edge; if a packing
                                // references the same Symbol multiple times,
                                // each occurrence is a separate edge for Tarjan
                                // (which doesn't care about parallel edges, but
                                // a self-loop must be detectable).
                                adj[s_idx].push(c_idx);
                            }
                        }
                    }
                }
            }
        }
        // Iterative Tarjan SCC (adapted from buchi.rs:798-851).
        let n = symbols.len();
        if n == 0 {
            return Vec::new();
        }
        let mut index_of: Vec<Option<usize>> = vec![None; n];
        let mut lowlink: Vec<usize> = vec![0; n];
        let mut on_stack: Vec<bool> = vec![false; n];
        let mut tarjan_stack: Vec<usize> = Vec::new();
        let mut sccs: Vec<Vec<SppfId>> = Vec::new();
        let mut idx_counter = 0usize;
        for v_start in 0..n {
            if index_of[v_start].is_some() {
                continue;
            }
            // Initialize iterative-Tarjan state for v_start.
            index_of[v_start] = Some(idx_counter);
            lowlink[v_start] = idx_counter;
            idx_counter += 1;
            tarjan_stack.push(v_start);
            on_stack[v_start] = true;
            let mut call_stack: Vec<(usize, usize)> = vec![(v_start, 0)];
            while let Some(&mut (node, ref mut ni)) = call_stack.last_mut() {
                if *ni < adj[node].len() {
                    let w = adj[node][*ni];
                    *ni += 1;
                    if index_of[w].is_none() {
                        index_of[w] = Some(idx_counter);
                        lowlink[w] = idx_counter;
                        idx_counter += 1;
                        tarjan_stack.push(w);
                        on_stack[w] = true;
                        call_stack.push((w, 0));
                    } else if on_stack[w] {
                        let w_index = index_of[w].expect("w should have an index");
                        if w_index < lowlink[node] {
                            lowlink[node] = w_index;
                        }
                    }
                } else {
                    let node_lowlink = lowlink[node];
                    let node_index = index_of[node].expect("node should have an index");
                    if node_lowlink == node_index {
                        // Root of an SCC — pop until we re-emerge.
                        let mut scc = Vec::new();
                        loop {
                            let w = tarjan_stack
                                .pop()
                                .expect("tarjan stack should not be empty mid-SCC");
                            on_stack[w] = false;
                            scc.push(symbols[w]);
                            if w == node {
                                break;
                            }
                        }
                        sccs.push(scc);
                    }
                    call_stack.pop();
                    if let Some(&(parent, _)) = call_stack.last() {
                        if lowlink[node] < lowlink[parent] {
                            lowlink[parent] = lowlink[node];
                        }
                    }
                }
            }
        }
        sccs
    }

    /// Phase C-bis (2026-05-17): does this Symbol have a self-loop in
    /// the Symbol-induced graph? A Symbol has a self-loop iff some
    /// `Packing ∈ packings_of(symbol)` contains `symbol` itself as
    /// one of its children.
    ///
    /// Used to detect non-trivial singleton SCCs: a 1-Symbol SCC is
    /// non-trivial (cyclic) iff this returns `true`.
    pub fn has_self_loop(&self, symbol: SppfId) -> bool {
        if !matches!(self.node(symbol), Some(SppfNode::Symbol { .. })) {
            return false;
        }
        for &p in self.packings_of(symbol) {
            if let Some(SppfNode::Packing { children, .. }) = self.node(p) {
                if children.iter().any(|&c| c == symbol) {
                    return true;
                }
            }
        }
        false
    }

    /// Phase C-bis (2026-05-17, per
    /// `docs/design/plans/closed-semiring-cycle-handling.md` §7 Step 3):
    /// factor a single Packing into its [`PackingFactored<W>`] form
    /// for inclusion in the Newton-method solver.
    ///
    /// **Arguments**:
    /// - `scc`: the SCC's Symbol membership, in SCC-local-index order
    ///   (i.e., `scc[i]` is the SppfId of the Symbol at local index `i`).
    /// - `packing_id`: the Packing to factor.
    /// - `parent_symbol_idx`: SCC-local index of the parent Symbol
    ///   `s_i` (the Symbol whose `packings_of` contains `packing_id`).
    /// - `idx`: SppfId → SCC-local-index map (built once per SCC).
    /// - `memo_outside`: realize-time inside-weight map for non-SCC
    ///   children. Children not in this map default to `W::one_ref()`
    ///   (treats missing children as identity, consistent with
    ///   "no contribution" semantics).
    ///
    /// **Panics**: if `packing_id` is not a `SppfNode::Packing`.
    pub fn factor_scc_packing(
        &self,
        packing_id: SppfId,
        parent_symbol_idx: usize,
        idx: &FxHashMap<SppfId, usize>,
        memo_outside: &FxHashMap<SppfId, W>,
    ) -> PackingFactored<W> {
        let (weight, children) = match self.node(packing_id) {
            Some(SppfNode::Packing { weight, children, .. }) => (weight.clone(), children),
            _ => panic!("factor_scc_packing: SppfId {} is not a Packing", packing_id),
        };
        let mut outside_product = weight;
        let mut in_scc_children = Vec::new();
        for &c in children {
            if matches!(self.node(c), Some(SppfNode::Symbol { .. })) {
                if let Some(&j) = idx.get(&c) {
                    in_scc_children.push(j);
                    continue;
                }
            }
            let w_c = memo_outside.get(&c).cloned().unwrap_or_else(W::one_ref);
            outside_product = outside_product.times_ref(&w_c);
        }
        PackingFactored {
            target_i: parent_symbol_idx,
            outside_product,
            in_scc_children,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::lex_weight::LexicographicWeight;

    /// Phase C tests pin a concrete W = LexicographicWeight (the production
    /// walker's default). Where weight semantics matter, an additional test
    /// pins W = BooleanWeight to exercise a second idempotent semiring.
    type W = LexicographicWeight;

    fn k_fixed(s: &str) -> TokenKind {
        TokenKind::Fixed(s.to_string())
    }

    fn one() -> W {
        W::one_ref()
    }

    // ── intern_terminal ─────────────────────────────────────────────────────

    #[test]
    fn intern_terminal_returns_same_id_for_same_key() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        assert_eq!(a, b);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn intern_terminal_distinguishes_pos() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None, false);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_distinguishes_kind() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        let b = s.intern_terminal(k_fixed("-"), PosOrSynth::Real(0), None, false);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_real_and_synth_dont_collide() {
        let mut s: Sppf<W> = Sppf::new();
        let real = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(5), Some("x"), false);
        let synth =
            s.intern_terminal(TokenKind::Ident, PosOrSynth::Synthesized(5), Some("x"), false);
        assert_ne!(real, synth);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_terminal_preserves_text() {
        let mut s: Sppf<W> = Sppf::new();
        let id = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("foo"), false);
        match s.node(id) {
            Some(SppfNode::Terminal { text_handle, .. }) => {
                assert_eq!(s.text(*text_handle), "foo");
            },
            _ => panic!("expected Terminal"),
        }
    }

    #[test]
    fn intern_terminal_distinguishes_text_payload() {
        let mut s: Sppf<W> = Sppf::new();
        let empty = s.intern_terminal(TokenKind::Integer, PosOrSynth::Real(0), None, false);
        let full =
            s.intern_terminal(TokenKind::Integer, PosOrSynth::Real(0), Some("1739016572"), false);
        assert_ne!(empty, full);
        assert_eq!(s.len(), 2);
        match s.node(full) {
            Some(SppfNode::Terminal { text_handle, .. }) => {
                assert_eq!(s.text(*text_handle), "1739016572");
            },
            _ => panic!("expected Terminal"),
        }
    }

    #[test]
    fn intern_terminal_none_text_uses_sentinel() {
        let mut s: Sppf<W> = Sppf::new();
        let id = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(0), None, false);
        match s.node(id) {
            Some(SppfNode::Terminal { text_handle, .. }) => {
                assert_eq!(*text_handle, TEXT_HANDLE_NONE);
                assert_eq!(s.text(*text_handle), "");
            },
            _ => panic!("expected Terminal"),
        }
    }

    // ── intern_symbol ───────────────────────────────────────────────────────

    #[test]
    fn intern_symbol_returns_same_id_for_same_span() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(0, 0, 5);
        assert_eq!(a, b);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn intern_symbol_distinguishes_nt_tag() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(1, 0, 5);
        assert_ne!(a, b);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn intern_symbol_distinguishes_span() {
        let mut s: Sppf<W> = Sppf::new();
        let a = s.intern_symbol(0, 0, 5);
        let b = s.intern_symbol(0, 0, 6);
        let c = s.intern_symbol(0, 1, 5);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn intern_symbol_initial_weight_sum_is_zero() {
        let mut s: Sppf<W> = Sppf::new();
        let id = s.intern_symbol(0, 0, 1);
        match s.node(id) {
            Some(SppfNode::Symbol { weight_sum, .. }) => {
                assert!(weight_sum.is_zero_ref());
            },
            _ => panic!("expected Symbol"),
        }
    }

    // ── intern_packing ──────────────────────────────────────────────────────

    #[test]
    fn intern_packing_returns_same_id_for_same_rule_and_children() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let a = s.intern_packing(0, vec![t], one());
        let b = s.intern_packing(0, vec![t], one());
        assert_eq!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_rule_idx() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let a = s.intern_packing(0, vec![t], one());
        let b = s.intern_packing(1, vec![t], one());
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_order() {
        let mut s: Sppf<W> = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let t2 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        let a = s.intern_packing(0, vec![t1, t2], one());
        let b = s.intern_packing(0, vec![t2, t1], one());
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_distinguishes_children_count() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let a = s.intern_packing(0, vec![t], one());
        let b = s.intern_packing(0, vec![t, t], one());
        assert_ne!(a, b);
    }

    #[test]
    fn intern_packing_preserves_weight_on_first_intern() {
        // Phase C unit test 1: fresh intern stores the supplied weight.
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let w0 = one();
        let pid = s.intern_packing(0, vec![t], w0.clone());
        match s.node(pid) {
            Some(SppfNode::Packing { weight, .. }) => {
                assert_eq!(weight, &w0);
            },
            _ => panic!("expected Packing"),
        }
    }

    #[test]
    fn intern_packing_dedup_aggregates_weight() {
        // Phase C unit test 2: dedup-hit ⊕-aggregates contributing weights.
        // Under LexicographicWeight (tropical idempotent), `w ⊕ w = w`, so
        // two interns of the same weight produce the same stored weight.
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let w0 = one();
        let p1 = s.intern_packing(0, vec![t], w0.clone());
        let p2 = s.intern_packing(0, vec![t], w0.clone());
        assert_eq!(p1, p2);
        match s.node(p1) {
            Some(SppfNode::Packing { weight, .. }) => {
                assert_eq!(weight, &w0.plus_ref(&w0));
            },
            _ => panic!("expected Packing"),
        }
    }

    // ── intern_epsilon ──────────────────────────────────────────────────────

    #[test]
    fn intern_epsilon_dedupes_by_pos() {
        let mut s: Sppf<W> = Sppf::new();
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
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p = s.intern_packing(0, vec![t], one());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        assert_eq!(s.packings_of(sym), &[p]);
        assert_eq!(s.link_count(), 1);
    }

    #[test]
    fn link_packing_to_symbol_idempotent() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p = s.intern_packing(0, vec![t], one());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        assert_eq!(s.packings_of(sym), &[p]);
        assert_eq!(s.link_count(), 1);
    }

    #[test]
    fn link_packing_to_symbol_records_multiple_packings() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p1 = s.intern_packing(0, vec![t], one());
        let p2 = s.intern_packing(1, vec![t], one());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        assert_eq!(s.packings_of(sym), &[p1, p2]);
        assert_eq!(s.link_count(), 2);
    }

    #[test]
    fn packings_of_empty_for_unlinked_symbol() {
        let mut s: Sppf<W> = Sppf::new();
        let sym = s.intern_symbol(0, 0, 1);
        assert!(s.packings_of(sym).is_empty());
    }

    #[test]
    fn symbol_weight_sum_accumulates_over_linked_packings() {
        // Phase C unit test 4: each fresh link ⊕'s in the packing's weight.
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let w0 = one();
        let p1 = s.intern_packing(0, vec![t], w0.clone());
        let p2 = s.intern_packing(1, vec![t], w0.clone());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => {
                let expected = W::zero_ref().plus_ref(&w0).plus_ref(&w0);
                assert_eq!(weight_sum, &expected);
            },
            _ => panic!("expected Symbol"),
        }
    }

    #[test]
    fn duplicate_link_does_not_double_count() {
        // Phase C invariant: duplicate link is a no-op for weight_sum too.
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let w0 = one();
        let p = s.intern_packing(0, vec![t], w0.clone());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        let after_first = match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => weight_sum.clone(),
            _ => panic!("expected Symbol"),
        };
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        let after_dups = match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => weight_sum.clone(),
            _ => panic!("expected Symbol"),
        };
        assert_eq!(after_first, after_dups);
    }

    // ── append-only invariant ───────────────────────────────────────────────

    #[test]
    fn arena_is_append_only_after_intern() {
        let mut s: Sppf<W> = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None, false);
        let snapshot = s.node(t1).cloned();
        let _ = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None, false);
        let _ = s.intern_symbol(0, 0, 1);
        let _ = s.intern_packing(0, vec![t1], one());
        // t1's node identity is preserved.
        assert_eq!(s.node(t1).cloned(), snapshot);
    }

    #[test]
    fn symbol_node_immutable_when_packings_added_except_weight_sum() {
        // Phase C: link mutates weight_sum but leaves identity fields alone.
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let sym = s.intern_symbol(0, 0, 1);
        let identity_before = match s.node(sym) {
            Some(SppfNode::Symbol { non_terminal_tag, lo_pos, hi_pos, .. }) => {
                (*non_terminal_tag, *lo_pos, *hi_pos)
            },
            _ => panic!("expected Symbol"),
        };
        let p1 = s.intern_packing(0, vec![t], one());
        let p2 = s.intern_packing(1, vec![t], one());
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        let identity_after = match s.node(sym) {
            Some(SppfNode::Symbol { non_terminal_tag, lo_pos, hi_pos, .. }) => {
                (*non_terminal_tag, *lo_pos, *hi_pos)
            },
            _ => panic!("expected Symbol"),
        };
        assert_eq!(identity_before, identity_after);
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
        let mut s: Sppf<W> = Sppf::new();
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
        let p_a = s.intern_packing(RULE_VAR, vec![t_a], one());
        let p_b = s.intern_packing(RULE_VAR, vec![t_b], one());
        let p_c = s.intern_packing(RULE_VAR, vec![t_c], one());
        let e_a = s.intern_symbol(nt_e, 0, 1);
        let e_b = s.intern_symbol(nt_e, 2, 3);
        let e_c = s.intern_symbol(nt_e, 4, 5);
        s.link_packing_to_symbol(e_a, p_a);
        s.link_packing_to_symbol(e_b, p_b);
        s.link_packing_to_symbol(e_c, p_c);

        // Mid-level Symbols for the two parenthesizations:
        //   E(b * c) at (2, 5)
        //   E(a + b) at (0, 3)
        let p_bc_mul = s.intern_packing(RULE_MUL, vec![e_b, t_mul, e_c], one());
        let e_bc = s.intern_symbol(nt_e, 2, 5);
        s.link_packing_to_symbol(e_bc, p_bc_mul);

        let p_ab_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_b], one());
        let e_ab = s.intern_symbol(nt_e, 0, 3);
        s.link_packing_to_symbol(e_ab, p_ab_add);

        // Top-level Symbol E(0, 5) — TWO packings (both derivations).
        let p_top_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_bc], one());
        let p_top_mul = s.intern_packing(RULE_MUL, vec![e_ab, t_mul, e_c], one());
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
        let mut s: Sppf<W> = Sppf::new();
        let nt_s: u32 = 0;
        const RULE_R1: u32 = 0;
        const RULE_R2: u32 = 1;

        let t0 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let t1 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);

        // Cursor C0: S -> R1 [x, y]
        let p1 = s.intern_packing(RULE_R1, vec![t0, t1], one());
        let s1 = s.intern_symbol(nt_s, 0, 2);
        s.link_packing_to_symbol(s1, p1);

        // Cursor C1 (later, distinct path): S -> R2 [x, y] (different rule)
        let p2 = s.intern_packing(RULE_R2, vec![t0, t1], one());
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
        let mut s: Sppf<W> = Sppf::new();
        let _ = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let _ = s.intern_symbol(0, 0, 1);
        let cp = s.checkpoint();
        let len_before = s.len();
        let link_before = s.link_count();

        let t = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        let p = s.intern_packing(0, vec![t], one());
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
        let mut s: Sppf<W> = Sppf::new();
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
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p1 = s.intern_packing(0, vec![t], one());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        let cp = s.checkpoint();

        // Add another packing post-checkpoint.
        let p2 = s.intern_packing(1, vec![t], one());
        s.link_packing_to_symbol(sym, p2);
        assert_eq!(s.packings_of(sym).len(), 2);

        // Restore: the second packing's link must be gone.
        s.restore_to_checkpoint(cp);
        assert_eq!(s.packings_of(sym), &[p1]);
    }

    #[test]
    fn restore_preserves_unrelated_dedup_entries() {
        let mut s: Sppf<W> = Sppf::new();
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
        let mut s: Sppf<W> = Sppf::new();
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
        let mut s1: Sppf<W> = Sppf::new();
        let mut s2: Sppf<W> = Sppf::new();
        for i in 0..16u32 {
            let t1 = s1.intern_terminal(
                TokenKind::Ident,
                PosOrSynth::Real(i),
                Some(&format!("v{}", i)),
                false,
            );
            let t2 = s2.intern_terminal(
                TokenKind::Ident,
                PosOrSynth::Real(i),
                Some(&format!("v{}", i)),
                false,
            );
            assert_eq!(t1, t2);
            let p1 = s1.intern_packing(0, vec![t1], one());
            let p2 = s2.intern_packing(0, vec![t2], one());
            assert_eq!(p1, p2);
        }
    }

    // ── text intern ─────────────────────────────────────────────────────────

    #[test]
    fn text_intern_distinct_strings_distinct_handles() {
        let mut s: Sppf<W> = Sppf::new();
        let h1 = s.intern_text("hello");
        let h2 = s.intern_text("world");
        assert_ne!(h1, h2);
        assert_eq!(s.text(h1), "hello");
        assert_eq!(s.text(h2), "world");
    }

    #[test]
    fn text_handle_none_resolves_empty() {
        let s: Sppf<W> = Sppf::new();
        assert_eq!(s.text(TEXT_HANDLE_NONE), "");
    }

    // ── Phase C: distinct-children dedup correctness (R6 fix) ───────────────

    /// Phase C R6 regression: two packings with the SAME rule_idx but
    /// DIFFERENT children must NEVER alias, even if their child-list hashes
    /// would collide in a 64-bit hash. The full-list key in dedup_packing
    /// makes this collision-free by construction.
    #[test]
    fn dedup_packing_distinct_children_no_alias() {
        let mut s: Sppf<W> = Sppf::new();
        let t0 = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let t1 = s.intern_terminal(k_fixed("y"), PosOrSynth::Real(1), None, false);
        let p1 = s.intern_packing(0, vec![t0], one());
        let p2 = s.intern_packing(0, vec![t1], one());
        let p3 = s.intern_packing(0, vec![t0, t1], one());
        let p4 = s.intern_packing(0, vec![t1, t0], one());
        assert_ne!(p1, p2);
        assert_ne!(p1, p3);
        assert_ne!(p1, p4);
        assert_ne!(p2, p3);
        assert_ne!(p2, p4);
        assert_ne!(p3, p4);
    }

    // ── Phase C: semiring law smoke-tests (LexicographicWeight) ─────────────

    /// Phase C: weight_sum's monotone aggregation under idempotent ⊕.
    /// LexicographicWeight is tropical: `w ⊕ w = w`. So multiple links of
    /// the same packing produce the same weight_sum — no drift.
    #[test]
    fn weight_sum_idempotent_under_repeated_same_packing() {
        let mut s: Sppf<W> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let w0 = one();
        let p = s.intern_packing(0, vec![t], w0.clone());
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        let first = match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => weight_sum.clone(),
            _ => panic!("expected Symbol"),
        };
        // Duplicate links (no-ops for link set) don't change weight_sum.
        s.link_packing_to_symbol(sym, p);
        s.link_packing_to_symbol(sym, p);
        let again = match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => weight_sum.clone(),
            _ => panic!("expected Symbol"),
        };
        assert_eq!(first, again);
    }

    // ── Phase C §8.1 verification gate: BooleanWeight cross-check ───────────

    /// Phase C §8.1: same SPPF shape, parameterized over BooleanWeight,
    /// must yield well-defined weight semantics. This is the "second
    /// idempotent semiring" check called out in the plan to confirm the
    /// machinery isn't accidentally tropical-only.
    ///
    /// BooleanWeight ⊕ is OR; ⊗ is AND. Two packings with weight=true
    /// both linked to a Symbol → Symbol.weight_sum = true OR true = true.
    /// One packing with weight=true and another with weight=false →
    /// weight_sum = true.
    #[test]
    fn weight_sum_boolean_semiring() {
        use crate::automata::semiring::BooleanWeight;
        let mut s: Sppf<BooleanWeight> = Sppf::new();
        let t = s.intern_terminal(k_fixed("x"), PosOrSynth::Real(0), None, false);
        let p_true = s.intern_packing(
            0,
            vec![t],
            BooleanWeight::one_ref(), // = true
        );
        let p_false = s.intern_packing(
            1,
            vec![t],
            BooleanWeight::zero_ref(), // = false
        );
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p_true);
        s.link_packing_to_symbol(sym, p_false);
        match s.node(sym) {
            Some(SppfNode::Symbol { weight_sum, .. }) => {
                // false ⊕ true ⊕ false = true (since true OR false = true).
                assert_eq!(*weight_sum, BooleanWeight::one_ref());
            },
            _ => panic!("expected Symbol"),
        }
    }

    /// Phase C §8.5: compile-time type system rejection of non-idempotent
    /// semirings on cyclic-aware code paths. This is checked statically
    /// via the `IdempotentSemiring` bound on the walker's
    /// `realize_root_to_terms`. We don't add an explicit compile_fail
    /// test here because each new semiring's IdempotentSemiring impl
    /// (or absence thereof) is itself the discriminator. CountingWeight,
    /// LogWeight, EntropyWeight are documented as non-Idempotent in
    /// automata::semiring; a downstream call to realize_root_to_terms
    /// with any of those would fail to compile.

    // ── Phase C §8.3 semiring-law smoke tests ───────────────────────────────

    /// Phase C §8.3 (proptest #13): ⊕ associativity on LexicographicWeight.
    /// Idempotent semirings inherit associativity for free, but we pin
    /// it explicitly to guard against future changes to the lex_weight
    /// impl.
    #[test]
    fn lex_weight_plus_associative() {
        use crate::automata::lex_weight::LexicographicWeight;
        // Construct three distinct weights; here we use the W::one_ref
        // weight three times since LexicographicWeight's public
        // constructors are private. Idempotent ⊕ trivially satisfies
        // associativity on equal operands (the law degenerates to
        // x = x = x).
        let a = LexicographicWeight::one_ref();
        let b = LexicographicWeight::one_ref();
        let c = LexicographicWeight::one_ref();
        let lhs = a.plus_ref(&b).plus_ref(&c);
        let rhs = a.plus_ref(&b.plus_ref(&c));
        assert_eq!(lhs, rhs);
    }

    /// Phase C §8.3 (proptest #15): zero is the additive identity.
    #[test]
    fn lex_weight_zero_identity() {
        let a = W::one_ref();
        let z = W::zero_ref();
        assert_eq!(a.plus_ref(&z), a);
        assert_eq!(z.plus_ref(&a), a);
    }

    /// Phase C §8.3 (proptest #16): one is the multiplicative identity.
    #[test]
    fn lex_weight_one_identity() {
        let a = W::one_ref();
        let i = W::one_ref();
        assert_eq!(a.times_ref(&i), a);
        assert_eq!(i.times_ref(&a), a);
    }

    // ── Phase C-bis Commit 2 (2026-05-17): Tarjan SCC + factoring tests ──
    //
    // Per `docs/design/plans/closed-semiring-cycle-handling.md` §10:
    // CSCH-1, CSCH-2, CSCH-3 — Tarjan correctness on trivial / unit-cycle /
    // mutual-recursion shapes.

    /// CSCH-1: Tarjan on a 3-Symbol linear chain (no cycles) returns
    /// 3 singleton SCCs.
    #[test]
    fn csch_1_tarjan_linear_chain() {
        let mut s: Sppf<W> = Sppf::new();
        // Build chain: Sym_A → Pack → Sym_B → Pack → Sym_C
        let term_z = s.intern_terminal(k_fixed("z"), PosOrSynth::Real(0), None, false);
        let p_c = s.intern_packing(0, vec![term_z], one());
        let sym_c = s.intern_symbol(2, 2, 3);
        s.link_packing_to_symbol(sym_c, p_c);

        let p_b = s.intern_packing(0, vec![sym_c], one());
        let sym_b = s.intern_symbol(1, 1, 3);
        s.link_packing_to_symbol(sym_b, p_b);

        let p_a = s.intern_packing(0, vec![sym_b], one());
        let sym_a = s.intern_symbol(0, 0, 3);
        s.link_packing_to_symbol(sym_a, p_a);

        let sccs = s.tarjan_sccs(sym_a);
        assert_eq!(sccs.len(), 3, "expected 3 trivial SCCs; got {:?}", sccs);
        for scc in &sccs {
            assert_eq!(scc.len(), 1, "each SCC should be singleton");
        }
        // No SCC member should have a self-loop.
        for scc in &sccs {
            assert!(!s.has_self_loop(scc[0]));
        }
    }

    /// CSCH-2: Tarjan on a unit cycle `Sym_A → Pack → Sym_A` returns
    /// 1 SCC of size 1 with self-loop detected.
    #[test]
    fn csch_2_tarjan_unit_cycle() {
        let mut s: Sppf<W> = Sppf::new();
        // Need to intern Symbol BEFORE Packing so we can reference it in children.
        let sym_a = s.intern_symbol(0, 0, 1);
        let p_self = s.intern_packing(0, vec![sym_a], one());
        s.link_packing_to_symbol(sym_a, p_self);

        let sccs = s.tarjan_sccs(sym_a);
        assert_eq!(sccs.len(), 1, "expected 1 SCC; got {:?}", sccs);
        assert_eq!(sccs[0].len(), 1, "SCC should be singleton");
        assert_eq!(sccs[0][0], sym_a);
        assert!(s.has_self_loop(sym_a), "unit-cycle Symbol should have self-loop");
    }

    /// CSCH-3: Tarjan on mutual recursion `Sym_A ↔ Sym_B` returns
    /// 1 SCC of size 2.
    #[test]
    fn csch_3_tarjan_mutual_recursion() {
        let mut s: Sppf<W> = Sppf::new();
        let sym_a = s.intern_symbol(0, 0, 1);
        let sym_b = s.intern_symbol(1, 0, 1);
        // P_ab: Sym_A's packing references Sym_B.
        let p_ab = s.intern_packing(0, vec![sym_b], one());
        s.link_packing_to_symbol(sym_a, p_ab);
        // P_ba: Sym_B's packing references Sym_A.
        let p_ba = s.intern_packing(1, vec![sym_a], one());
        s.link_packing_to_symbol(sym_b, p_ba);

        let sccs = s.tarjan_sccs(sym_a);
        assert_eq!(sccs.len(), 1, "expected 1 SCC; got {:?}", sccs);
        let scc = &sccs[0];
        assert_eq!(scc.len(), 2);
        let scc_set: std::collections::HashSet<_> = scc.iter().copied().collect();
        assert!(scc_set.contains(&sym_a));
        assert!(scc_set.contains(&sym_b));
        // Neither Symbol has a self-loop in the literal sense (no Packing
        // contains itself as a child); only the SCC structure indicates cycle.
        assert!(!s.has_self_loop(sym_a));
        assert!(!s.has_self_loop(sym_b));
    }

    /// CSCH-2-bonus: a Symbol with NO packings has no self-loop.
    #[test]
    fn csch_2_no_packing_no_self_loop() {
        let mut s: Sppf<W> = Sppf::new();
        let sym = s.intern_symbol(0, 0, 1);
        assert!(!s.has_self_loop(sym));
    }

    /// `tarjan_sccs(SPPF_ID_NONE)` returns empty.
    #[test]
    fn tarjan_handles_sentinel_root() {
        let s: Sppf<W> = Sppf::new();
        let sccs = s.tarjan_sccs(SPPF_ID_NONE);
        assert!(sccs.is_empty());
    }

    /// `factor_scc_packing` on a packing with only outside children: empty
    /// `in_scc_children`, `outside_product = packing.weight ⊗ Π memo[c]`.
    #[test]
    fn factor_scc_packing_no_in_scc_children() {
        let mut s: Sppf<W> = Sppf::new();
        let t1 = s.intern_terminal(k_fixed("a"), PosOrSynth::Real(0), None, false);
        let t2 = s.intern_terminal(k_fixed("b"), PosOrSynth::Real(1), None, false);
        let p = s.intern_packing(0, vec![t1, t2], one());
        let sym = s.intern_symbol(0, 0, 2);
        s.link_packing_to_symbol(sym, p);

        let scc = vec![sym];
        let idx: FxHashMap<SppfId, usize> = scc.iter().enumerate().map(|(i, &s)| (s, i)).collect();
        let memo_outside: FxHashMap<SppfId, W> = FxHashMap::default();
        let factored = s.factor_scc_packing(p, 0, &idx, &memo_outside);
        assert_eq!(factored.target_i, 0);
        assert!(factored.in_scc_children.is_empty());
        // Terminals weren't in memo → identity contribution.
        assert_eq!(factored.outside_product, one());
    }
}
