//! Graph-Structured Stack (GSS) for GLL/WPDS-runtime parsing.
//!
//! Generalizes the CEK continuation stack to a **graph-structured stack**
//! where multiple parse states share common continuations. Supports both:
//!
//! - Legacy GLL-style sharing via `GraphStructuredStack` (string-tagged nodes)
//! - Runtime WPDS branching via [`WpdaGss<W>`] (typed via [`StackSymbolV2`]
//!   and a generic [`Semiring`] weight)
//!
//! ## Runtime use
//!
//! Stage 3 of W7 plan v5.1 activates this module as the substrate for the
//! WPDS walker (Stage 4). [`WpdaGss<LexicographicWeight>`] is the canonical
//! instantiation; [`WpdaGss<TropicalWeight>`] and other weights remain
//! available for analysis tooling.
//!
//! Always-on; no feature gates (per plan v5.1 mandate).
//!
//! ## Architecture
//!
//! GSS nodes are `(pos, symbol)` pairs; edges are shared continuations
//! carrying weights. The WFST/WPDS selects the best parse from the GSS's
//! packed parse forest. Falls back to a deterministic single-frontier walk
//! for unambiguous grammars (zero overhead).
//!
//! All path-enumeration operations are **iterative** (no host-stack
//! recursion) to satisfy the project's PDA/trampoline mandate.
//!
//! ## References
//!
//! - Scott, E. & Johnstone, A. (2010). *GLL parsing.* ENTCS.
//! - Tomita, M. (1986). *Efficient parsing for natural language.* Kluwer.
//! - Reps, Lal & Kidd (2007). WPDS poststar/prestar saturation.

use std::collections::HashMap;

// Perf (2026-06-20): the WPDA GSS node/edge maps are looked up on every cursor
// step (get_or_create_node + edge lookup), with small integer / derived-Hash
// keys. The default `std::collections::HashMap` SipHasher is ~5-10× slower than
// `rustc_hash::FxHashMap` for such keys and showed up as `Sip13Rounds` in the
// parse profile of cross-cat-cast inputs. `FxHashMap` is a drop-in (same map
// semantics; only the hash function differs — GSS correctness is unaffected).
use rustc_hash::FxHashMap;

use crate::automata::semiring::SemiringRef;
use crate::sppf::SppfId;
use crate::wpda_runtime::StackSymbolV2;

// ══════════════════════════════════════════════════════════════════════════════
// GSS Types
// ══════════════════════════════════════════════════════════════════════════════

/// Unique identifier for a GSS node.
pub type GssNodeId = u32;

/// Stage 3.12 fix (2026-05-02): sentinel marking "cursor has no GSS node"
/// — i.e., the cursor has unwound past the entry frame. Engine.step's
/// `frontier_top = self.gss.node(cursor.node)` returns `None` for this
/// id (since `WpdaGss` cannot allocate `u32::MAX` nodes — bounded by the
/// `STRICT_PENDING_OPS_LIMIT` runaway guard), routing the cursor through
/// the `frontier_top.is_none() ⇒ Accept` engine branch. Replaces the
/// pre-Stage-3.12 `top_node: Option<GssNodeId>` semantics that the
/// cursor-side code had to encode in a single `u32` field.
pub const GSS_NODE_NONE: GssNodeId = u32::MAX;

/// Stage 3.12.6 (2026-05-02): stable identifier for a `WpdaGss` edge,
/// packed as `(source_node_u32 << 32) | edge_index_u32` where
/// `edge_index_u32` is the edge's index in the source node's
/// `Vec<WpdaGssEdge<W>>` outgoing-edge list.
///
/// **Stability invariant**: edge indices are append-only — `WpdaGss`
/// never removes edges, so an edge's index in its source's outgoing
/// list is stable for the GSS's lifetime. The dedup-via-`plus` path in
/// `add_edge` mutates an existing edge's weight in place, preserving
/// its index and thus its `GssEdgeId`.
///
/// Used by the walker's per-cursor `incoming_edge_stack` to record each
/// cursor's stack-suffix path through the GSS, restoring pop-time
/// determinism in the face of GSS structural sharing across recursive
/// rules' `(pos, symbol)` re-entries.
pub type GssEdgeId = u64;

/// Pack `(source, edge_index)` into a `GssEdgeId`.
#[inline(always)]
pub fn pack_edge_id(source: GssNodeId, edge_index: usize) -> GssEdgeId {
    debug_assert!(
        edge_index < (u32::MAX as usize),
        "GSS edge index overflow: STRICT_PENDING_OPS_LIMIT should prevent this",
    );
    ((source as u64) << 32) | (edge_index as u64)
}

/// Unpack a `GssEdgeId` into `(source, edge_index)`.
#[inline(always)]
pub fn unpack_edge_id(id: GssEdgeId) -> (GssNodeId, u32) {
    let source = (id >> 32) as GssNodeId;
    let edge_index = (id & 0xFFFF_FFFF) as u32;
    (source, edge_index)
}

/// A node in the graph-structured stack.
///
/// Each node represents a parse state at a particular input position
/// with a particular frame variant on top.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GssNode {
    /// Input position.
    pub pos: usize,
    /// Frame variant tag (e.g., "InfixRHS", "RD_Let_0").
    pub frame_tag: String,
}

/// An edge in the GSS connecting a node to its successor.
#[derive(Debug, Clone)]
pub struct GssEdge {
    /// Target node ID.
    pub target: GssNodeId,
    /// Weight of this edge (from WFST prediction).
    pub weight: f64,
}

/// Graph-Structured Stack implementation.
///
/// Supports forking (multiple stack tops sharing a common suffix)
/// for GLL-style ambiguous parsing.
#[derive(Debug, Clone)]
pub struct GraphStructuredStack {
    /// Nodes in the GSS.
    nodes: Vec<GssNode>,
    /// Edges: source node ID → list of outgoing edges.
    edges: HashMap<GssNodeId, Vec<GssEdge>>,
    /// Active frontier: stack tops currently being explored.
    frontier: Vec<GssNodeId>,
    /// Node lookup: GssNode → GssNodeId for structural sharing.
    node_index: HashMap<GssNode, GssNodeId>,
}

impl GraphStructuredStack {
    /// Create a new empty GSS.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: HashMap::new(),
            frontier: Vec::new(),
            node_index: HashMap::new(),
        }
    }

    /// Get or create a GSS node, ensuring structural sharing.
    ///
    /// If a node with the same `(pos, frame_tag)` already exists,
    /// returns its ID instead of creating a duplicate.
    pub fn get_or_create_node(&mut self, node: GssNode) -> GssNodeId {
        if let Some(&id) = self.node_index.get(&node) {
            return id;
        }
        let id = self.nodes.len() as GssNodeId;
        self.node_index.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// Add an edge from source to target with given weight.
    pub fn add_edge(&mut self, source: GssNodeId, target: GssNodeId, weight: f64) {
        self.edges
            .entry(source)
            .or_default()
            .push(GssEdge { target, weight });
    }

    /// Fork the stack: create a new frontier node sharing the
    /// current node's continuation.
    pub fn fork(&mut self, from: GssNodeId, new_node: GssNode, weight: f64) -> GssNodeId {
        let new_id = self.get_or_create_node(new_node);
        self.add_edge(new_id, from, weight);
        self.frontier.push(new_id);
        new_id
    }

    /// Push a node onto the active frontier.
    pub fn push_frontier(&mut self, node_id: GssNodeId) {
        self.frontier.push(node_id);
    }

    /// Pop a node from the active frontier.
    pub fn pop_frontier(&mut self) -> Option<GssNodeId> {
        self.frontier.pop()
    }

    /// Get the current frontier size.
    pub fn frontier_size(&self) -> usize {
        self.frontier.len()
    }

    /// Total number of nodes in the GSS.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Total number of edges in the GSS.
    pub fn edge_count(&self) -> usize {
        self.edges.values().map(|v| v.len()).sum()
    }

    /// Get a node by ID.
    pub fn node(&self, id: GssNodeId) -> Option<&GssNode> {
        self.nodes.get(id as usize)
    }

    /// Get outgoing edges from a node.
    pub fn edges_from(&self, id: GssNodeId) -> &[GssEdge] {
        self.edges.get(&id).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Check if the GSS is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Enumerate all paths from a frontier node to the root.
    ///
    /// Each path is a sequence of node IDs from the frontier to the
    /// bottom of the stack. Used for extracting parse forests.
    ///
    /// Iterative implementation (explicit work-stack) to satisfy the
    /// project's no-host-recursion mandate.
    pub fn paths_to_root(&self, start: GssNodeId) -> Vec<Vec<GssNodeId>> {
        let mut result = Vec::new();
        // Each work item carries the current node and the path taken to reach it.
        let mut work: Vec<(GssNodeId, Vec<GssNodeId>)> = vec![(start, vec![start])];
        while let Some((node, path)) = work.pop() {
            let edges = self.edges_from(node);
            if edges.is_empty() {
                result.push(path);
            } else {
                for edge in edges {
                    let mut next = path.clone();
                    next.push(edge.target);
                    work.push((edge.target, next));
                }
            }
        }
        result
    }
}

impl Default for GraphStructuredStack {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Packed Parse Forest (SPPF)
// ══════════════════════════════════════════════════════════════════════════════

/// A node in the Shared Packed Parse Forest (SPPF).
///
/// Used to represent all parse trees compactly when the grammar
/// is ambiguous. Multiple derivations share common subtrees.
#[derive(Debug, Clone)]
pub enum SppfNode {
    /// A terminal leaf.
    Terminal {
        /// Token position.
        pos: usize,
        /// Token text.
        text: String,
    },
    /// An interior node (nonterminal).
    Interior {
        /// Rule label.
        label: String,
        /// Input range [start, end).
        start: usize,
        end: usize,
        /// Children (shared across packed alternatives).
        children: Vec<SppfNodeId>,
    },
    /// A packed node representing an ambiguous derivation.
    Packed {
        /// Alternative derivations.
        alternatives: Vec<Vec<SppfNodeId>>,
    },
}

/// Unique identifier for an SPPF node.
pub type SppfNodeId = u32;

/// Shared Packed Parse Forest.
#[derive(Debug, Clone, Default)]
pub struct Sppf {
    /// All nodes in the forest.
    nodes: Vec<SppfNode>,
}

impl Sppf {
    /// Create a new empty SPPF.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a node to the forest.
    pub fn add_node(&mut self, node: SppfNode) -> SppfNodeId {
        let id = self.nodes.len() as SppfNodeId;
        self.nodes.push(node);
        id
    }

    /// Get a node by ID.
    pub fn node(&self, id: SppfNodeId) -> Option<&SppfNode> {
        self.nodes.get(id as usize)
    }

    /// Total number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the forest is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Count the number of distinct parse trees represented.
    ///
    /// Iterative: builds a memo table indexed by `SppfNodeId`, processed in
    /// creation order. Since SPPF children/alternatives may only refer to
    /// earlier IDs (a strict creation invariant), one bottom-up pass suffices.
    /// Avoids host-stack recursion on deeply nested forests.
    pub fn tree_count(&self, root: SppfNodeId) -> usize {
        let n = self.nodes.len();
        if (root as usize) >= n {
            return 0;
        }
        let mut memo: Vec<usize> = vec![0; n];
        for (id, node) in self.nodes.iter().enumerate() {
            memo[id] = match node {
                SppfNode::Terminal { .. } => 1,
                SppfNode::Interior { children, .. } => children
                    .iter()
                    .map(|&c| memo[c as usize])
                    .product::<usize>()
                    .max(1),
                SppfNode::Packed { alternatives } => alternatives
                    .iter()
                    .map(|alt| {
                        alt.iter()
                            .map(|&c| memo[c as usize])
                            .product::<usize>()
                            .max(1)
                    })
                    .sum(),
            };
        }
        memo[root as usize]
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WpdaGss — typed graph-structured stack for the WPDS-runtime walker
// ══════════════════════════════════════════════════════════════════════════════

/// A node in the typed [`WpdaGss`].
///
/// Carries an integer-indexed [`StackSymbolV2`] (no `String` allocations on
/// the hot path) plus the input position at which this stack frame was
/// created. Used for structural sharing: two parse branches reaching the
/// same `(pos, symbol)` combine into one node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WpdaGssNode {
    /// Input position when this node was created.
    pub pos: usize,
    /// The stack symbol at this frame.
    pub symbol: StackSymbolV2,
}

/// Phase F.13 H13 Step 0 (2026-05-21): semantic taxonomy of GSS edges
/// for cursor-equivalence diagnostics (and eventual merge-key
/// relaxation).
///
/// Each edge carries a `kind: EdgeKind` recording the semantic
/// reason for its creation. Two edges are STRUCTURALLY EQUIVALENT
/// if their `EdgeKind`s match under the equivalence relation `≡_E`
/// (see `crate::walker_stats`).
///
/// **Convergent** variants (no `source_id` field): edges whose
/// post-pop predecessor frame is determined by payload alone.
/// Two convergent edges of the same variant + same payload produce
/// equivalent post-pop cursor state.
///
/// **Divergent** variants (carry `source_id: GssEdgeId`): edges
/// whose post-pop predecessor depends on cursor-specific history
/// not captured in the payload. These retain GssEdgeId identity
/// strictness to preserve Stage 3.12.6's wrong-pop defense.
///
/// **Generic** is the fallback for sites not yet specifically
/// classified — strictly identity-equivalent via `source_id`.
/// Subsequent H13 iterations will refine Generic call sites into
/// specific variants as their grammar semantics are formalized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CrossCatLhsReentryOrigin {
    pub dispatch_pos: usize,
    pub key_min_bp: u8,
    pub wrap_cat: u16,
    pub wrap_rule: u16,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EdgeKind {
    /// Fallback / identity-strict — compared via GssEdgeId equality.
    /// Use when the semantic kind cannot be determined OR when the kind
    /// is divergent on pop (post-pop predecessor depends on cursor history).
    Generic,

    // ─── Convergent variants: post-pop predecessor determined by payload ───
    /// CategoryEntry root sentinel synthesis (cursor_gss_push fallback
    /// when cursor.node is GSS_NODE_NONE or 0). All such edges target
    /// the universal sentinel frame.
    CategoryEntryRoot,
    /// CategoryEntry continuation that must resume the caller's Pratt floor
    /// when the category frame is later popped. This is produced by
    /// replacement-style transparent frames, notably grouping close, where the
    /// replacement CategoryEntry is an operand continuation rather than a fresh
    /// top-level category entry.
    CategoryEntryContinuation { min_bp: u8 },
    /// Cross-cat projection branch: walker emits a push and transitions to
    /// `CrossCatDelegate` to delegate to a source-category parse. This applies
    /// to both forked and singleton fast-path emissions. Convergent: post-pop
    /// returns to the outer dispatch site whose `(source_src_idx, inner_cur_bp)`
    /// are payload.
    ///
    /// M4 (2026-05-30, re-landed): ALSO carries the WRAPPING rule's
    /// `(wrap_cat, wrap_rule)` so the resolve site
    /// (`cursor_gss_pop_via_edge`) can reconstruct the widened
    /// [`crate::dispatch_cohort::DispatchKey`] — distinct cross-cat wrap
    /// injections sharing `(pos, source, bp)` but wrapping via different rules
    /// stay distinct in the cohort cache. Making these fields part of the
    /// EdgeKind ALSO means two convergent edges that wrap via different rules
    /// are no longer `≡_E`-equivalent (their post-pop return frames genuinely
    /// differ), which is correct.
    CrossCatProjection {
        source_src_idx: u16,
        inner_cur_bp: u8,
        wrap_cat: u16,
        wrap_rule: u16,
    },
    /// Anonymous cross-category LHS delegation. Prefix dispatch pushed a
    /// `CategoryEntry(source_src_idx)` so the source category can parse the
    /// left operand before the operator is known.
    ///
    /// This edge is identity-strict: after the source LHS returns, the walker
    /// temporarily re-pushes the source category above this edge's concrete
    /// predecessor for one infix pass. The predecessor is therefore part of
    /// the semantic continuation and must not be erased by EdgeKind-only
    /// equivalence.
    CrossCatLhs { source_src_idx: u16 },
    /// One-shot continuation produced after a `CrossCatLhs` source operand
    /// has returned. Infix dispatch may use this as evidence that a
    /// category-changing operator is allowed, but popping this edge must not
    /// re-enter again.
    CrossCatLhsReentry {
        source_src_idx: u16,
        min_bp: u8,
        origin: Option<CrossCatLhsReentryOrigin>,
    },
    /// Runtime-normalized CrossCatLhs edge whose identity includes both Pratt
    /// floors involved in the handoff. `min_bp` is the delegated source
    /// category's resume floor after its prefix body has completed. This is
    /// deliberately the caller's active Pratt floor, not the source
    /// `PrefixDispatch` start floor, so a delegated RHS at high precedence
    /// cannot later consume lower-precedence source operators. `resume_bp` is
    /// the enclosing target category's floor, restored after the
    /// category-changing atom has completed.
    /// Generated code may still emit `CrossCatLhs`; the walker upgrades it
    /// before GSS insertion so edge dedup cannot merge different Pratt
    /// continuations.
    CrossCatLhsScoped {
        source_src_idx: u16,
        min_bp: u8,
        resume_bp: u8,
    },
    /// Transparent projection source continuation. A target-category wrapper
    /// such as `Expr <- Num` has produced a target Symbol, but the next
    /// lookahead operator belongs to the source category. The walker unwraps
    /// the source child, re-enters source-category InfixLoop for one
    /// continuation, and wraps the final source result back into
    /// `target_src_idx` when this edge pops.
    TransparentSourceReentry { source_src_idx: u16, target_src_idx: u16 },
    /// PrefixDispatch consumed a literal and pushed a `RuleAt` frame
    /// to begin parsing the rule's items. Payload = (cat, rule, item position).
    PrefixRuleEntry {
        cat_src: u16,
        rule_idx: u16,
        item_pos: u8,
    },
    /// InfixLoop dispatch's `ConsumeAndPush` of an InfixContinuation
    /// symbol (after matching the infix operator). Payload = (cat, rule,
    /// bp from symbol).
    InfixContinuation { cat_src: u16, rule_idx: u16, l_bp: u8 },
    /// Lex-alternative Fork branch (LexAlt family). Payload =
    /// (cat, rule). Distinguished from PrefixRuleEntry because lex-Fork
    /// is a Fork-time variant; runtime semantics are similar but
    /// emission context differs.
    LexAltLiteral { cat_src: u16, rule_idx: u16 },
    /// Optional-group `OptionalGroupAt(sub_pos)` marker. Payload =
    /// (cat, rule, sub_pos, outer_bp).
    OptionalGroupAt {
        cat_src: u16,
        rule_idx: u16,
        sub_pos: u8,
        outer_bp: u8,
    },
    /// Class-3 binder-list inner-walk marker. Payload =
    /// (cat, rule, sub_pos, outer_bp).
    BinderListLoopAt {
        cat_src: u16,
        rule_idx: u16,
        sub_pos: u8,
        outer_bp: u8,
    },

    // ─── Identity-strict variants (divergent on pop) ────────────────────────
    /// Collection-element marker push. Pop must restore the calling
    /// frame's accumulator-slot id. Comparison falls back to GssEdgeId.
    CollectionElement {
        result_src: u16,
        rule_idx: u16,
        acc_id: u8,
    },
    /// Grouping marker push. Pop restores the outer Pratt `cur_bp`.
    /// Comparison falls back to GssEdgeId.
    GroupingMarker { result_src: u16, outer_bp: u8 },
    /// Mixfix continuation marker. Comparison falls back to GssEdgeId.
    MixfixMarker {
        result_src: u16,
        rule_idx: u16,
        operands_completed: u8,
    },
    /// Return-frame push. Comparison falls back to GssEdgeId (divergent
    /// because the return frame's predecessor varies per cursor history).
    ReturnFrame { cat_src: u16, rule_idx: u16 },
}

impl EdgeKind {
    /// Derive an EdgeKind from a StackSymbolV2. Maps SymbolKind variants
    /// to the corresponding EdgeKind. Used by `cursor_gss_push_auto` to
    /// auto-tag edges at every push site.
    pub fn from_symbol(sym: &crate::wpda_runtime::StackSymbolV2) -> Self {
        use crate::wpda_runtime::SymbolKind;
        match sym.kind {
            SymbolKind::CategoryEntry => {
                // Could be CategoryEntryRoot sentinel OR CrossCatProjection;
                // callers that know it's cross-cat should construct the
                // CrossCatProjection variant explicitly.
                EdgeKind::CategoryEntryRoot
            },
            SymbolKind::RuleAt(item_pos) => EdgeKind::PrefixRuleEntry {
                cat_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                item_pos,
            },
            SymbolKind::InfixContinuation => EdgeKind::InfixContinuation {
                cat_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                l_bp: sym.bp.unwrap_or(0),
            },
            SymbolKind::CollectionMarker => EdgeKind::CollectionElement {
                result_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                acc_id: sym.bp.unwrap_or(0),
            },
            SymbolKind::GroupingMarker => EdgeKind::GroupingMarker {
                result_src: sym.category_src_idx,
                outer_bp: sym.bp.unwrap_or(0),
            },
            SymbolKind::MixfixMarker => EdgeKind::MixfixMarker {
                result_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                operands_completed: sym.bp.unwrap_or(0),
            },
            SymbolKind::OptionalGroupAt(sub_pos) => EdgeKind::OptionalGroupAt {
                cat_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                sub_pos,
                outer_bp: sym.bp.unwrap_or(0),
            },
            SymbolKind::BinderListLoopAt(sub_pos) => EdgeKind::BinderListLoopAt {
                cat_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
                sub_pos,
                outer_bp: sym.bp.unwrap_or(0),
            },
            SymbolKind::Return => EdgeKind::ReturnFrame {
                cat_src: sym.category_src_idx,
                rule_idx: sym.rule_index_in_category,
            },
        }
    }

    /// True for variants whose payload alone determines post-pop
    /// equivalence. Two convergent edges with same EdgeKind are
    /// merge-equivalent under H13's relaxed key.
    pub fn is_convergent(&self) -> bool {
        matches!(
            self,
            EdgeKind::CategoryEntryRoot
                | EdgeKind::CategoryEntryContinuation { .. }
                | EdgeKind::CrossCatProjection { .. }
                | EdgeKind::PrefixRuleEntry { .. }
                | EdgeKind::InfixContinuation { .. }
                | EdgeKind::LexAltLiteral { .. }
                | EdgeKind::OptionalGroupAt { .. }
                | EdgeKind::BinderListLoopAt { .. }
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// GSS node-identity coarsening — Plan a0ddad66 (2026-07-03)
//
// The canonical Tomita/GLL continuation-node key is `(state/return-slot,
// input position)` — derivation-agnostic + category-agnostic (see
// [[gll-invariant-configkey-overdiscrimination]]). `WpdaGssNode` currently
// keys on the FULL `StackSymbolV2`, so the two `@a` readings at a `@a<-@b`
// cross-cat dispatch (Proc-Return vs Name-CategoryEntry) fork into distinct
// GssNodeIds upstream of every merge tier — defeating top-sharing and turning
// the O(n³) frontier into 2^N.
//
// These helpers define the coarsened axes:
//   - `node_class` DEMOTES the per-derivation symbol discriminators
//     (`category_src_idx`, `rule_index_in_category`, `bp`, and the
//     `Return`-vs-`CategoryEntry` `kind` split) while KEEPING the genuine
//     continuation-shape (marker kind + `sub_pos`, `coll_dispatch_bp`,
//     `goal_src_idx`). The demoted discriminators are RELOCATED, not deleted:
//     `category_src_idx`/`rule_index_in_category` ride the SPPF packing (the
//     two readings are already distinct `Symbol(cat,lo,hi)` nodes), and the
//     `Return`/`CategoryEntry` + `bp` distinction rides the GSS edge label
//     (the `EdgeKind`, which retains cat/rule/bp on the edge).
//   - `edge_merge_key` projects a fresh per-Push `GssEdgeId` to `(edge_target,
//     EdgeKind)` for convergent edges (the merge-convergence-investigation.md
//     Lead-1 `(pred_node, EdgeKind)` projection) and keeps identity for
//     divergent edges (reconnection family — byte-identical).
//
// **T-Consist:** both helpers target the SAME equivalence — "same continuation
// position + shape, different derivation instance". `node_class` erases the
// symbol-level derivation discriminators; `edge_merge_key` erases the edge-id
// derivation instance; the discriminators they demote are exactly the ones the
// `EdgeKind` + SPPF packing retain. Pop-target soundness is preserved because
// `cursor_gss_pop_via_edge` reads the per-cursor `incoming_edge_stack` top edge
// (NOT the shared node symbol) for routing — see `T-PopTargetSound`.
//
// STAGE 0 (measure-only): these functions have ZERO behavior call sites; they
// are consulted only by the `walker-stats` shadow instrumentation
// (`PRATTAIL_COARSEN_SHADOW`). STAGE 1 wires them into `WpdaGssNode`
// Hash/Eq (Site 1), `ConfigKey` (Site 2), and `SubsumeConfigKey` (Site 3),
// gated behind [`NODE_CLASS_COARSEN_ENABLED`] + `PRATTAIL_NODE_CLASS_COARSEN`.

/// Master compile-time kill-switch for the node-identity coarsening fix.
/// `false` ⇒ every keyed site (Sites 1/2/3) behaves BYTE-IDENTICALLY to the
/// pre-fix baseline (the coarsened axes are never consulted). Runtime env
/// `PRATTAIL_NODE_CLASS_COARSEN=on` can force it ON (and `=off` force OFF)
/// once the const is flipped, mirroring `PROJ_CACHE_POS_QUOTIENT_ENABLED`.
///
/// STAGE 0/1: stays `false` (shadow measurement + OFF-byte-identical plumbing).
/// Flip to `true` only after the Stage-2 FV theorems compile zero-admission.
pub const NODE_CLASS_COARSEN_ENABLED: bool = false;

/// Runtime resolution of the coarsening switch: the const gates it OFF unless
/// explicitly overridden. Cached in a `OnceLock` so the env read happens once.
///   - const `false` (Stage 0/1): OFF unless `PRATTAIL_NODE_CLASS_COARSEN=on`.
///   - const `true` (post-flip):  ON  unless `PRATTAIL_NODE_CLASS_COARSEN=off`.
#[inline]
pub fn node_class_coarsen_active() -> bool {
    use std::sync::OnceLock;
    static GATE: OnceLock<bool> = OnceLock::new();
    *GATE.get_or_init(|| match std::env::var("PRATTAIL_NODE_CLASS_COARSEN") {
        Ok(v) if v.eq_ignore_ascii_case("on") || v == "1" => true,
        Ok(v) if v.eq_ignore_ascii_case("off") || v == "0" => false,
        _ => NODE_CLASS_COARSEN_ENABLED,
    })
}

/// Coarse continuation-shape of a [`crate::wpda_runtime::SymbolKind`]. The
/// `Return`/`CategoryEntry` (and mid-rule `RuleAt`) operand/return frames all
/// collapse into a single [`ContinuationShape::OperandOrReturn`] class — this
/// is where the two cross-cat `@a` readings re-converge. Every marker kind
/// keeps its own class (with its `sub_pos` progress payload) because those
/// frames carry genuinely-distinct continuations that must NOT be merged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ContinuationShape {
    /// `CategoryEntry`, `Return`, and mid-rule `RuleAt(_)` — the operand-entry /
    /// return-continuation family. The `RuleAt` item position is DEMOTED (the
    /// rule/position is a derivation discriminator, relocated to the edge label
    /// + SPPF packing); genuine progress is tracked by input `pos` (kept in
    /// `WpdaGssNode`) and the incoming edge.
    OperandOrReturn,
    /// `InfixContinuation` — awaiting a right-hand side after an infix operator.
    InfixContinuation,
    /// `CollectionMarker` — inside a collection-literal scope.
    CollectionMarker,
    /// `GroupingMarker` — inside a precedence-reset grouping.
    GroupingMarker,
    /// `MixfixMarker` — mixfix continuation.
    MixfixMarker,
    /// `OptionalGroupAt(sub_pos)` — the `sub_pos` IS continuation progress, KEPT.
    OptionalGroupAt(u8),
    /// `BinderListLoopAt(sub_pos)` — the `sub_pos` IS continuation progress, KEPT.
    BinderListLoopAt(u8),
}

impl ContinuationShape {
    #[inline]
    pub fn of(kind: &crate::wpda_runtime::SymbolKind) -> Self {
        use crate::wpda_runtime::SymbolKind;
        match kind {
            SymbolKind::CategoryEntry | SymbolKind::Return | SymbolKind::RuleAt(_) => {
                ContinuationShape::OperandOrReturn
            },
            SymbolKind::InfixContinuation => ContinuationShape::InfixContinuation,
            SymbolKind::CollectionMarker => ContinuationShape::CollectionMarker,
            SymbolKind::GroupingMarker => ContinuationShape::GroupingMarker,
            SymbolKind::MixfixMarker => ContinuationShape::MixfixMarker,
            SymbolKind::OptionalGroupAt(sub) => ContinuationShape::OptionalGroupAt(*sub),
            SymbolKind::BinderListLoopAt(sub) => ContinuationShape::BinderListLoopAt(*sub),
        }
    }
}

/// Derivation-agnostic node class of a stack symbol. Two symbols with equal
/// `NodeClass` at the same input position are the SAME continuation under the
/// canonical Tomita/GLL invariant — they must share one GSS node so the merge
/// tiers can fold their cursors downstream (with the derivation choice riding
/// SPPF packing + the edge label). See the module header for the T-Consist
/// argument. `coll_dispatch_bp` and `goal_src_idx` are KEPT because they bound
/// which InfixLoop candidates are admissible (genuine continuation shape).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeClass {
    pub shape: ContinuationShape,
    pub coll_dispatch_bp: Option<u8>,
    pub goal_src_idx: Option<u16>,
}

/// Compute the [`NodeClass`] of a stack symbol (Site-1 coarsening axis).
#[inline]
pub fn node_class(symbol: &crate::wpda_runtime::StackSymbolV2) -> NodeClass {
    NodeClass {
        shape: ContinuationShape::of(&symbol.kind),
        coll_dispatch_bp: symbol.coll_dispatch_bp,
        goal_src_idx: symbol.goal_src_idx,
    }
}

/// Merge-bucketing projection of an incoming GSS edge (Site-2/3 coarsening
/// axis). Convergent edges (per [`EdgeKind::is_convergent`]) project to
/// `Class(edge_target, EdgeKind)` so two structurally-identical edges from the
/// same predecessor — differing ONLY in their fresh per-Push `GssEdgeId` —
/// fold. Divergent edges (reconnection family) keep `Identity(edge_id)` so the
/// landed reconnection fixes stay byte-identical. Pop routing is unaffected:
/// the cursor's `incoming_edge_stack` retains the concrete `GssEdgeId`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EdgeMergeKey {
    /// Structural class: `(predecessor/edge_target, EdgeKind)`. Convergent edges.
    /// (Not `Copy`: `EdgeKind` is `Clone`-only.)
    Class(GssNodeId, EdgeKind),
    /// Identity fallback: the raw edge id. Divergent (reconnection) edges.
    Identity(GssEdgeId),
}

impl<W: SemiringRef> WpdaGss<W> {
    /// Project a `GssEdgeId` to its [`EdgeMergeKey`] (Site-2/3). Returns
    /// `None` iff the edge id is not in the GSS (shouldn't happen for a live
    /// cursor's incoming-edge top).
    #[inline]
    pub fn edge_merge_key(&self, edge_id: GssEdgeId) -> Option<EdgeMergeKey> {
        let kind = self.edge_kind_ref(edge_id)?;
        if kind.is_convergent() {
            let target = self.edge_target(edge_id)?;
            Some(EdgeMergeKey::Class(target, kind.clone()))
        } else {
            Some(EdgeMergeKey::Identity(edge_id))
        }
    }
}

/// An edge in the typed GSS, weighted by an arbitrary [`Semiring`].
#[derive(Debug, Clone)]
pub struct WpdaGssEdge<W: SemiringRef> {
    /// Successor node (the frame *below* on the stack).
    pub target: GssNodeId,
    /// Edge weight (e.g., [`crate::automata::lex_weight::LexicographicWeight`]).
    pub weight: W,
    /// Phase F.13 H13 Step 0 (2026-05-21): semantic taxonomy.
    /// Default is `Generic { source_id }` until the call site is
    /// specifically classified.
    pub kind: EdgeKind,
}

// ══════════════════════════════════════════════════════════════════════════════
// Canonical-GLL GSS primitives — ROOT-P redesign Stage C (2026-07-09)
//
// Scott & Johnstone (2010/2013) GLL keeps a GSS whose nodes are labelled by a
// grammar *slot* `L` and an input position `i`, whose EDGES are labelled by an
// SPPF node `w` (the left / operand part built so far at the call site), and a
// per-node *recorded-pop set* `P` of `(position, SPPF-result)` pairs. The two
// operations `create` and `pop` are symmetric and together implement the
// "create-after-pop replay" that makes GLL cubic AND complete:
//
//   • create(L, u, i, w): get-or-create the return node `v = (L, i)`, add the
//     edge `v → u` labelled `w`; if `v` has ALREADY popped (∃ (k, z) ∈ P[v]),
//     immediately synthesise the return for the *new* edge — descriptor
//     `(L, u, k, getNodeP(L, w, z))`. THIS IS THE CLASSIC BUG CLASS: an edge
//     added into a node that already popped MUST replay the recorded pop, or
//     that derivation is silently lost.
//   • pop(u, i, z): record `(i, z)` into P[u]; for EVERY edge `u → v` labelled
//     `w`, synthesise the return `(L_u, v, i, getNodeP(L_u, w, z))`.
//
// This module implements the GSS-LAYER halves of those two operations plus the
// predecessor/operand enumeration. The SPPF combine `getNodeP(L, w, z)` and the
// descriptor add-once set `U` / worklist `R` are the DRIVER's responsibility
// (Stage D, `WpdaWalker::step_canonical`); the primitives here return the raw
// materials (`GllReturn { slot, caller, at_pos, operand_w, result_w }`) from
// which the driver builds `y = getNodeP` and enqueues `(slot, caller, at_pos, y)`.
//
// ── DORMANT / zero-cost-when-OFF ─────────────────────────────────────────────
// ALL canonical state lives behind a lazily-boxed `Option<Box<CanonicalGssState>>`
// on `WpdaGss` (default `None`). The classic engine NEVER calls a `gll_*` method,
// so the box is never allocated and the field is never touched on the classic
// path — the only classic-path cost is one `None` pointer in the (single, per-
// walker) `WpdaGss` struct.
//
// ── Why a SEPARATE operand-edge store (design choice, Scott-Johnstone §4) ─────
// Canonical GSS edge identity is `(target, operand_w)`: two links to the SAME
// caller carrying DIFFERENT operands are DISTINCT edges (each records a distinct
// left-part derivation). The classic [`WpdaGss::add_edge`] dedups by `(target,
// EdgeKind)` and would MERGE two `v → u` edges carrying different `w` into one,
// silently clobbering an operand — and it carries a semiring weight the canonical
// engine does not use (canonical lex-election rides the SPPF `Packing.weight`).
// So the canonical operand edges live in their OWN adjacency map inside
// [`CanonicalGssState`], NOT the classic weighted `edges` map. Keeping the two
// stores disjoint faithfully models the §4 "edge labelled by an SPPF node" and
// ALSO guarantees the classic weighted `edges` map is byte-identical whether or
// not the canonical engine ever runs. Node identity still rides the EXISTING
// `(pos, symbol)` node index (the canonical GSS-by-slot identity is the symbol
// being slot-shaped — Stage A/D), so [`WpdaGss::get_or_create_node`] is reused
// verbatim for the node half. [`WpdaGss::gll_predecessors`] is the operand-aware
// mirror of [`WpdaGss::pop_all_predecessors`] (which enumerates the CLASSIC
// weighted edges); the classic enumerator is reused conceptually, not literally,
// because it reads the wrong (weighted, un-operand-labelled) store.

/// One canonical-GLL GSS edge: a labelled predecessor link `source → target`
/// carrying the operand SPPF node `w` the caller had built at the call site.
/// Edge identity for canonical dedup is `(target, operand_w)`. No weight:
/// canonical lex-election rides the SPPF `Packing.weight`, not a GSS edge weight.
///
/// ROOT-P Stage E (2026-07-09): the edge ALSO snapshots the caller's PERSISTENT
/// context handles at the call site — `caller_sppf_stack` (the caller's SPPF
/// working stack) and `caller_edge_stack` (its incoming-edge chain). Both are
/// `path_tree_arena::StackId` (`Copy` u32 handles into a walker-global
/// append-only path-tree ⇒ O(1) to snapshot and to restore, never clobbered).
/// The exact pop-fan (Stage E) restores THESE per-caller handles before pushing
/// the completed sub-parse result `z`, so a reduce that fans to a caller whose
/// left-context differs from the popping cursor's rebuilds THAT caller's stack
/// exactly — the n-ary realization of Scott & Johnstone's `getNodeP(L, w, z)`
/// (here the caller's whole partial SPPF working-stack IS the left part, and
/// the rule's own `emit_fire_action` packs `[…caller-context, z]` at its later
/// reduce). Edge identity stays `(target, operand_w)` (a given caller reached
/// with a given operand has ONE call-site context), so the context fields do
/// NOT widen dedup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)] // Fields read by the canonical driver (Stage D/E) + gss unit tests.
pub(crate) struct CanonicalGllEdge {
    /// Predecessor (caller) GSS node this edge returns into on pop.
    pub target: GssNodeId,
    /// Operand SPPF label `w` (the left part). May be [`crate::sppf::SPPF_ID_NONE`].
    pub operand_w: SppfId,
    /// Caller's SPPF working-stack handle at the call site (Stage E restore).
    pub caller_sppf_stack: crate::path_tree_arena::StackId,
    /// Caller's incoming-edge chain handle at the call site (Stage E restore).
    pub caller_edge_stack: crate::path_tree_arena::StackId,
}

/// One recorded pop in a node's `P` set: the input position `pos` (right extent)
/// at which the node popped and the SPPF node `result_w` (`z`) it produced.
///
/// `Eq` is deliberately NOT derived (task #10 item 3): `W` is
/// `LexicographicWeight` in production, which holds `f64` components and
/// implements only `PartialEq`. The P-set dedup compares the identity
/// fields (`pos`, `result_w`, `rule_id`) directly, never whole-struct
/// equality, so nothing needs `Eq`. `Copy`/`Clone` are conditional on `W`
/// (LexicographicWeight is `Copy`, so the production instantiation stays
/// `Copy`).
#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(dead_code)] // Fields read by the canonical driver (Stage D) + gss unit tests.
pub(crate) struct RecordedPop<W> {
    /// Right-extent input position at which this node popped.
    pub pos: usize,
    /// SPPF result node `z` produced by the completed nonterminal.
    pub result_w: SppfId,
    /// S1-FACTORING F5-2 D-3 (replay-channel identity, 2026-07-13): the
    /// POP-TIME rule identity `(cat << 16) | rule` of the popping
    /// descriptor, `u32::MAX` when the popping site carries none. The
    /// D2-class (LHS-join) create-after-pop REPLAY reconstructs the
    /// constituent's rule packing; deriving that rule from the FRAME's
    /// pushed symbol was correct only while pop identity always equalled
    /// the frame symbol — a COMMITTED mixfix-spine frame pops with the
    /// member's identity while its frame symbol keeps the spine id (the
    /// AV6/A8 doctrine: the slot label may keep SPINE, the packing/fire
    /// identity may not), so the replay must carry the recorded identity.
    pub rule_id: u32,
    /// Task #10 item 3 (ledger :884-889, the P4.b follow-up): the pop
    /// ACTION's weight, recorded so a create-after-pop REPLAY can intern a
    /// genuinely-new replay packing with the TRUE weight instead of
    /// `W::one()` (which retired the `replay_weight_drops` counter). The
    /// value is whatever the pop site charged into its own packing intern
    /// (D2: the pre-join frame weight; D1: the fire's packing weight incl.
    /// the K-B coercion completion charge; standalone collections: the pop
    /// weight; structural passthrough / bookkeeping pops: `W::one()` — no
    /// packing, no charge).
    pub pop_action_weight: W,
}

/// A return synthesised by a canonical `create`/`pop`: the raw materials for the
/// driver to build `y = getNodeP(slot, operand_w, result_w)` and enqueue the
/// descriptor `(slot, caller, at_pos, y)`. The GSS layer deliberately does NOT
/// touch the SPPF (owned by the walker) or the descriptor set `U`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)] // Consumed by the canonical driver (Stage D) + gss unit tests.
pub(crate) struct GllReturn {
    /// Return slot `L` = the label symbol of the node being resumed (the popped
    /// node in `gll_pop`; the created node `v` in a `gll_create` replay).
    pub slot: StackSymbolV2,
    /// GSS node to resume in — the caller below the edge (`u` / edge target).
    pub caller: GssNodeId,
    /// Input position to resume at (the right extent of `result_w`).
    pub at_pos: usize,
    /// Edge operand SPPF label `w` (left part).
    pub operand_w: SppfId,
    /// Completed-nonterminal SPPF node `z` (right part).
    pub result_w: SppfId,
    /// ROOT-P Stage E: caller's SPPF working-stack handle at the call site,
    /// copied from the edge so the driver can restore the caller's left-context
    /// before pushing `result_w` (the n-ary getNodeP restore).
    pub caller_sppf_stack: crate::path_tree_arena::StackId,
    /// ROOT-P Stage E: caller's incoming-edge chain handle at the call site.
    pub caller_edge_stack: crate::path_tree_arena::StackId,
    /// F5-2 D-3: the recorded pop-time rule identity (see
    /// [`RecordedPop::rule_id`]); `u32::MAX` when none was recorded.
    pub rule_id: u32,
}

/// Canonical-GLL GSS side-state: the operand-labelled edge adjacency and the
/// per-node recorded-pop set `P`. Lazily boxed on [`WpdaGss`] and allocated only
/// the first time a `gll_*` op runs (i.e. only under `canonical_gll_active()`),
/// so the classic path never allocates or touches it.
///
/// Task #10 item 3 rewrote the former "non-generic, no weight-type baggage"
/// design note: the state now carries exactly ONE `W` per recorded pop (the
/// P4.b pop-action-weight follow-up, ledger :884-889) so create-after-pop
/// replays intern with the true weight; everything else stays handle-only
/// (`u32`/`usize`).
///
/// `Default` is implemented MANUALLY (not derived): a derive would add a
/// spurious `W: Default` bound, and the fields (two maps) default
/// independently of `W`.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Populated/read by the canonical driver (Stage D) + gss unit tests.
pub(crate) struct CanonicalGssState<W> {
    /// `source node → its outgoing canonical operand edges`, deduped by
    /// `(target, operand_w)`.
    edges: FxHashMap<GssNodeId, Vec<CanonicalGllEdge>>,
    /// `node → its recorded pops P`, deduped by `(pos, result_w, rule_id)`
    /// (P is a SET over the identity triple; the weight rides the entry).
    recorded_pops: FxHashMap<GssNodeId, Vec<RecordedPop<W>>>,
}

impl<W> Default for CanonicalGssState<W> {
    fn default() -> Self {
        CanonicalGssState {
            edges: FxHashMap::default(),
            recorded_pops: FxHashMap::default(),
        }
    }
}

/// Typed graph-structured stack for the WPDS-runtime walker.
///
/// Generic over weight semiring `W`. Mirrors [`GraphStructuredStack`]'s API
/// but with typed symbols and weights, plus WPDS-specific stack operations
/// (`push_symbol`, `pop_symbol`, `replace_top`).
#[derive(Debug, Clone)]
pub struct WpdaGss<W: SemiringRef> {
    nodes: Vec<WpdaGssNode>,
    edges: FxHashMap<GssNodeId, Vec<WpdaGssEdge<W>>>,
    frontier: Vec<GssNodeId>,
    node_index: FxHashMap<WpdaGssNode, GssNodeId>,
    /// ROOT-P Stage C (2026-07-09): lazily-boxed canonical-GLL side-state
    /// (operand-labelled edges + recorded-pop set `P`). `None` on the classic
    /// path — never allocated or touched unless a `gll_*` op runs (i.e. only
    /// under `canonical_gll_active()`), so the classic GSS stays byte-identical.
    /// W-generic since task #10 item 3 (each P entry carries its pop-action
    /// weight).
    canonical: Option<Box<CanonicalGssState<W>>>,
}

impl<W: SemiringRef> WpdaGss<W> {
    /// Create an empty typed GSS.
    pub fn new() -> Self {
        WpdaGss {
            nodes: Vec::new(),
            edges: FxHashMap::default(),
            frontier: Vec::new(),
            node_index: FxHashMap::default(),
            // ROOT-P Stage C: canonical side-state stays unallocated until the
            // first `gll_*` op (canonical engine only); the classic path leaves
            // this `None` forever.
            canonical: None,
        }
    }

    /// Get or create a node, ensuring structural sharing on `(pos, symbol)`.
    pub fn get_or_create_node(&mut self, node: WpdaGssNode) -> GssNodeId {
        if let Some(&id) = self.node_index.get(&node) {
            return id;
        }
        let id = self.nodes.len() as GssNodeId;
        self.node_index.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// Add a weighted edge from `source` to `target`.
    ///
    /// **Dedup invariant (Stage 3.1, 2026-04-30):** if an edge `(source,
    /// target)` already exists, its weight is merged with the new weight
    /// via `Semiring::plus` (lex-min for `LexicographicWeight`, tropical
    /// sum for `TropicalWeight`) — no duplicate edges are appended. This
    /// is required for two reasons:
    ///
    /// 1. The Pratt walker's fanout machinery calls `add_edge` once per
    ///    cursor-step on potentially-revisited `(source, target)` pairs.
    ///    Without dedup, edge counts grow as `O(steps × cursors)`, which
    ///    on failed parses causes 73 amortized `Vec::push` reallocations
    ///    and ~805MB peak heap. Empirically reproduced and heaptrack-
    ///    validated; see `wpds-gss-unbounded-growth-2026-04-29.md`.
    /// 2. Semantically, multiple `(source, target)` edges with different
    ///    weights represent the *same* parallel-derivation relation
    ///    weighted differently — the semiring sum is the canonical
    ///    representative.
    pub fn add_edge(&mut self, source: GssNodeId, target: GssNodeId, weight: W) -> GssEdgeId {
        // Phase F.13 H13 Step 0 (2026-05-21): tag with the Generic edge kind.
        // Higher-level callers (push_symbol_with_edge_id_kind /
        // replace_top_with_edge_id_kind) should use `add_edge_kind` to
        // pass a specific EdgeKind.
        let edges = self.edges.entry(source).or_default();
        for (idx, existing) in edges.iter_mut().enumerate() {
            if existing.target == target && existing.kind == EdgeKind::Generic {
                existing.weight = existing.weight.plus_ref(&weight);
                return pack_edge_id(source, idx);
            }
        }
        let idx = edges.len();
        let edge_id = pack_edge_id(source, idx);
        edges.push(WpdaGssEdge { target, weight, kind: EdgeKind::Generic });
        edge_id
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): like `add_edge` but accepts a
    /// specific `EdgeKind` tag. Used by `push_symbol_with_edge_id_kind`
    /// and `replace_top_with_edge_id_kind` to record semantic context.
    pub fn add_edge_kind(
        &mut self,
        source: GssNodeId,
        target: GssNodeId,
        weight: W,
        kind: EdgeKind,
    ) -> GssEdgeId {
        let edges = self.edges.entry(source).or_default();
        for (idx, existing) in edges.iter_mut().enumerate() {
            if existing.target == target && existing.kind == kind {
                existing.weight = existing.weight.plus_ref(&weight);
                return pack_edge_id(source, idx);
            }
        }
        let idx = edges.len();
        let edge_id = pack_edge_id(source, idx);
        edges.push(WpdaGssEdge { target, weight, kind });
        edge_id
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): look up the `EdgeKind` of a
    /// specific edge by its `GssEdgeId`. Returns `None` if the edge
    /// does not exist.
    pub fn edge_kind(&self, edge_id: GssEdgeId) -> Option<EdgeKind> {
        let (source, idx) = unpack_edge_id(edge_id);
        self.edges
            .get(&source)
            .and_then(|edges| edges.get(idx as usize).map(|e| e.kind.clone()))
    }

    /// Borrow the `EdgeKind` of a specific edge without cloning it.
    ///
    /// Hot path scans use this when they only need to inspect edge metadata
    /// while walking a path-tree stack.
    pub fn edge_kind_ref(&self, edge_id: GssEdgeId) -> Option<&EdgeKind> {
        let (source, idx) = unpack_edge_id(edge_id);
        self.edges
            .get(&source)
            .and_then(|edges| edges.get(idx as usize).map(|e| &e.kind))
    }

    /// Stage 3.12.6 (2026-05-02): look up the target node of a specific
    /// edge by its `GssEdgeId`. Returns `None` if the edge does not exist
    /// (e.g., the source node has fewer outgoing edges than the index
    /// encoded in the id, or the source node id is invalid).
    ///
    /// Used by the walker's `cursor_gss_pop_via_edge` to follow the
    /// cursor's recorded stack-suffix path through the GSS.
    pub fn edge_target(&self, id: GssEdgeId) -> Option<GssNodeId> {
        let (source, edge_index) = unpack_edge_id(id);
        self.edges
            .get(&source)
            .and_then(|v| v.get(edge_index as usize))
            .map(|e| e.target)
    }

    /// Return the source node encoded in a concrete edge id.
    pub fn edge_source(&self, id: GssEdgeId) -> Option<GssNodeId> {
        let (source, edge_index) = unpack_edge_id(id);
        self.edges
            .get(&source)
            .and_then(|v| v.get(edge_index as usize))
            .map(|_| source)
    }

    /// Number of nodes.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges.
    pub fn edge_count(&self) -> usize {
        self.edges.values().map(|v| v.len()).sum()
    }

    /// Look up a node.
    pub fn node(&self, id: GssNodeId) -> Option<&WpdaGssNode> {
        self.nodes.get(id as usize)
    }

    /// Outgoing edges from a node (empty slice if none).
    pub fn edges_from(&self, id: GssNodeId) -> &[WpdaGssEdge<W>] {
        self.edges.get(&id).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// F1 follow-up Cluster A (2026-05-10): look up the GSS node id by its
    /// `(pos, symbol)` fingerprint via the internal `node_index`. Used by
    /// the engine's Unwinding-CategoryEntry arm to detect cross-cat
    /// grouping (where the predecessor of the just-popping CategoryEntry
    /// is a GroupingMarker), enabling the engine to preserve the inner-cat
    /// dispatch context across `)`.
    ///
    /// Returns `None` if `node` was never registered (e.g., constructed
    /// but never pushed via `get_or_create_node`).
    pub fn lookup_id(&self, node: &WpdaGssNode) -> Option<GssNodeId> {
        self.node_index.get(node).copied()
    }

    /// Whether the GSS is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Read-only view of the active frontier.
    pub fn frontier(&self) -> &[GssNodeId] {
        &self.frontier
    }

    /// Replace the entire frontier (used by the walker after a saturation step).
    pub fn replace_frontier(&mut self, new_frontier: Vec<GssNodeId>) {
        self.frontier = new_frontier;
    }

    /// Push a node onto the active frontier.
    pub fn push_frontier(&mut self, node_id: GssNodeId) {
        self.frontier.push(node_id);
    }

    /// Pop a node from the active frontier.
    pub fn pop_frontier(&mut self) -> Option<GssNodeId> {
        self.frontier.pop()
    }

    /// Current frontier size.
    pub fn frontier_size(&self) -> usize {
        self.frontier.len()
    }

    // ─── WPDS rule operations ───────────────────────────────────────────────

    /// WPDS push: emit a new frame on top of `frontier_node`.
    ///
    /// Mirrors `WpdsRule::Push` semantics. Creates a new GSS node for
    /// `(pos, symbol)`, links it to `frontier_node` with `weight`, and
    /// returns the new node's id (does NOT mutate the frontier).
    pub fn push_symbol(
        &mut self,
        frontier_node: GssNodeId,
        symbol: StackSymbolV2,
        pos: usize,
        weight: W,
    ) -> GssNodeId {
        self.push_symbol_with_edge_id(frontier_node, symbol, pos, weight)
            .0
    }

    /// Stage 3.12.6 (2026-05-02): variant of `push_symbol` that returns
    /// the new node id paired with the `GssEdgeId` of the freshly
    /// recorded `(new_id → frontier_node)` edge. Used by the walker's
    /// `cursor_gss_push` to populate the cursor's `incoming_edge_stack`.
    pub fn push_symbol_with_edge_id(
        &mut self,
        frontier_node: GssNodeId,
        symbol: StackSymbolV2,
        pos: usize,
        weight: W,
    ) -> (GssNodeId, GssEdgeId) {
        let new_id = self.get_or_create_node(WpdaGssNode { pos, symbol });
        let edge_id = self.add_edge(new_id, frontier_node, weight);
        (new_id, edge_id)
    }

    /// WPDS pop: drop the top frame, returning the predecessor node.
    ///
    /// `frontier_node` is the frame being popped. Returns `Some(target)`
    /// from the first outgoing edge, or `None` if `frontier_node` is at
    /// the GSS root (no predecessors).
    ///
    /// For ambiguous backwards traversal (multiple predecessors), use
    /// [`WpdaGss::pop_all_predecessors`].
    pub fn pop_symbol(&mut self, frontier_node: GssNodeId) -> Option<GssNodeId> {
        self.edges_from(frontier_node).first().map(|e| e.target)
    }

    /// All predecessor nodes reachable by popping `frontier_node`.
    ///
    /// Useful when the GSS has multiple parallel calling contexts to pop
    /// back into. Each returned id is paired with the edge weight that
    /// would be incurred by the pop.
    pub fn pop_all_predecessors(&self, frontier_node: GssNodeId) -> Vec<(GssNodeId, &W)> {
        self.edges_from(frontier_node)
            .iter()
            .map(|e| (e.target, &e.weight))
            .collect()
    }

    /// WPDS replace: swap the top symbol for a new one.
    ///
    /// Conceptually: pop `frontier_node`, then push `new_symbol` onto the
    /// same predecessors. Implemented by creating a new GSS node inheriting
    /// `frontier_node`'s outgoing edges (modulo the times-composition with
    /// `weight`).
    pub fn replace_top(
        &mut self,
        frontier_node: GssNodeId,
        new_symbol: StackSymbolV2,
        pos: usize,
        weight: W,
    ) -> GssNodeId {
        // Stage 3.12.7 (2026-05-02): legacy wrapper passes None for the
        // cursor's edge (returns first predecessor edge id). Walker
        // callers should use `replace_top_with_edge_id` directly with
        // the cursor's recorded incoming edge.
        self.replace_top_with_edge_id(frontier_node, new_symbol, pos, weight, None)
            .0
    }

    /// Stage 3.12.6 (2026-05-02): variant of `replace_top` that returns
    /// the new node id paired with the `GssEdgeId` of the predecessor
    /// edge that the cursor traversed (preferred) or the first
    /// predecessor edge if the cursor's edge cannot be matched.
    ///
    /// Stage 3.12.7 (2026-05-02): added `cursor_incoming_edge` parameter.
    /// When `frontier_node` has multiple predecessors (e.g., from GSS
    /// dedup of recursive `(pos, symbol)` pushes), the cursor's specific
    /// stack-suffix identity must be preserved. The function looks up
    /// the cursor's recorded edge target and returns the new edge id
    /// that points to the SAME target. Falls back to the first edge
    /// when the cursor's edge can't be resolved (shouldn't happen
    /// under correct push/pop pairing) or when frontier_node has no
    /// predecessors (terminal pop).
    ///
    /// Without this, cursors at multi-predecessor GSS nodes silently
    /// inherit the wrong predecessor on Replace — latent today (no
    /// existing test exercises Replace at a multi-pred node) but will
    /// surface in Stage 3.16+ Forks.
    pub fn replace_top_with_edge_id(
        &mut self,
        frontier_node: GssNodeId,
        new_symbol: StackSymbolV2,
        pos: usize,
        weight: W,
        cursor_incoming_edge: Option<GssEdgeId>,
    ) -> (GssNodeId, GssEdgeId) {
        let new_id = self.get_or_create_node(WpdaGssNode { pos, symbol: new_symbol });
        let preds: Vec<(GssNodeId, W)> = self
            .edges_from(frontier_node)
            .iter()
            .map(|e| (e.target, weight.times_ref(&e.weight)))
            .collect();
        let cursor_target = cursor_incoming_edge.and_then(|e| self.edge_target(e));
        let mut matching_edge_id: Option<GssEdgeId> = None;
        let mut first_edge_id: Option<GssEdgeId> = None;
        for (target, w) in preds {
            let edge_id = self.add_edge(new_id, target, w);
            if first_edge_id.is_none() {
                first_edge_id = Some(edge_id);
            }
            if cursor_target == Some(target) && matching_edge_id.is_none() {
                matching_edge_id = Some(edge_id);
            }
        }
        // Prefer the cursor's specific edge target; fall back to first
        // (single-pred case) or 0 (no preds — terminal replace).
        let edge_id = matching_edge_id.or(first_edge_id).unwrap_or(0);
        (new_id, edge_id)
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): kinded variant of
    /// `replace_top_with_edge_id`. Each new edge created from the
    /// replace operation receives the supplied `EdgeKind`.
    pub fn replace_top_with_edge_id_kind(
        &mut self,
        frontier_node: GssNodeId,
        new_symbol: StackSymbolV2,
        pos: usize,
        weight: W,
        cursor_incoming_edge: Option<GssEdgeId>,
        kind: EdgeKind,
    ) -> (GssNodeId, GssEdgeId) {
        let new_id = self.get_or_create_node(WpdaGssNode { pos, symbol: new_symbol });
        let preds: Vec<(GssNodeId, W)> = self
            .edges_from(frontier_node)
            .iter()
            .map(|e| (e.target, weight.times_ref(&e.weight)))
            .collect();
        let cursor_target = cursor_incoming_edge.and_then(|e| self.edge_target(e));
        let mut matching_edge_id: Option<GssEdgeId> = None;
        let mut first_edge_id: Option<GssEdgeId> = None;
        for (target, w) in preds {
            let edge_id = self.add_edge_kind(new_id, target, w, kind.clone());
            if first_edge_id.is_none() {
                first_edge_id = Some(edge_id);
            }
            if cursor_target == Some(target) && matching_edge_id.is_none() {
                matching_edge_id = Some(edge_id);
            }
        }
        let edge_id = matching_edge_id.or(first_edge_id).unwrap_or(0);
        (new_id, edge_id)
    }

    /// Fork the stack: create a parallel branch at `from` sharing its
    /// continuation (predecessors).
    ///
    /// Used for ambiguity fanout. `new_node` becomes a new frontier node
    /// linked to `from`'s predecessors with `weight`.
    pub fn fork(&mut self, from: GssNodeId, new_node: WpdaGssNode, weight: W) -> GssNodeId {
        let new_id = self.get_or_create_node(new_node);
        self.add_edge(new_id, from, weight);
        self.frontier.push(new_id);
        new_id
    }

    // ─── Path enumeration & cycle detection ─────────────────────────────────

    /// Enumerate all paths from `start` to a GSS root (a node with no
    /// outgoing edges).
    ///
    /// Iterative; uses an explicit work-stack to avoid host-stack recursion.
    pub fn paths_to_root(&self, start: GssNodeId) -> Vec<Vec<GssNodeId>> {
        let mut result = Vec::new();
        let mut work: Vec<(GssNodeId, Vec<GssNodeId>)> = vec![(start, vec![start])];
        while let Some((node, path)) = work.pop() {
            let edges = self.edges_from(node);
            if edges.is_empty() {
                result.push(path);
            } else {
                for edge in edges {
                    // Cycle guard: skip targets already on this path.
                    if path.contains(&edge.target) {
                        continue;
                    }
                    let mut next = path.clone();
                    next.push(edge.target);
                    work.push((edge.target, next));
                }
            }
        }
        result
    }

    /// Whether a cycle is reachable from `start` by following outgoing edges.
    ///
    /// Iterative DFS with a visit stack and a `recursion-stack` tracker
    /// (the standard back-edge cycle detection without host recursion).
    pub fn has_cycle_from(&self, start: GssNodeId) -> bool {
        // 0 = unvisited, 1 = in progress (on rec stack), 2 = done
        let mut state: HashMap<GssNodeId, u8> = HashMap::new();
        // Each work item is (node, edge_index). edge_index = next edge to try.
        let mut work: Vec<(GssNodeId, usize)> = vec![(start, 0)];
        state.insert(start, 1);
        while let Some(&(node, ref idx)) = work.last() {
            let edges = self.edges_from(node);
            let i = *idx;
            if i < edges.len() {
                // Bump the index in place.
                let last = work.last_mut().expect("work non-empty");
                last.1 += 1;
                let target = edges[i].target;
                match state.get(&target).copied().unwrap_or(0) {
                    0 => {
                        state.insert(target, 1);
                        work.push((target, 0));
                    },
                    1 => return true, // back-edge — cycle
                    _ => { /* already finished — not a back edge */ },
                }
            } else {
                state.insert(node, 2);
                work.pop();
            }
        }
        false
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Canonical-GLL GSS operations (ROOT-P Stage C) — DORMANT
//
// Reachable ONLY from the canonical descriptor-worklist driver (Stage D,
// `WpdaWalker::step_canonical`, currently `unimplemented!` and dead-code-
// eliminated while `CANONICAL_GLL_ENABLED == false`) and from the `gss` unit
// tests. Every method is `#[allow(dead_code)]`: it has no non-test caller until
// Stage D wires the driver. None is reachable on the classic parse path, so they
// add ZERO classic-path cost and cannot change classic behaviour. See the
// "Canonical-GLL GSS primitives" module section above for the create/pop
// protocol and the separate-operand-edge-store design rationale.
// ══════════════════════════════════════════════════════════════════════════════
impl<W: SemiringRef> WpdaGss<W> {
    /// Lazily obtain the mutable canonical side-state, boxing it on first use.
    /// Called only by the `gll_*` mutators, i.e. only under the canonical engine,
    /// so the classic path never triggers the allocation.
    #[allow(dead_code)]
    #[inline]
    fn canonical_mut(&mut self) -> &mut CanonicalGssState<W> {
        self.canonical
            .get_or_insert_with(|| Box::new(CanonicalGssState::default()))
    }

    /// Read-only view of the canonical side-state (`None` until the first
    /// `gll_*` mutation — the classic path always observes `None`).
    #[allow(dead_code)]
    #[inline]
    fn canonical_ref(&self) -> Option<&CanonicalGssState<W>> {
        self.canonical.as_deref()
    }

    /// Canonical GLL `create(L, u, i, w)` — GSS-layer half (Scott-Johnstone §4).
    ///
    /// Get-or-creates the return node `v = (return_slot L, at_pos i)` (via the
    /// EXISTING `(pos, symbol)` node index), then adds the operand-labelled edge
    /// `v → from_node(u)` carrying `operand_w(w)`. Edge identity is `(target,
    /// operand_w)`: re-adding an already-present edge is a no-op (idempotent) and
    /// produces NO replay.
    ///
    /// **Create-after-pop replay:** if the edge is NEW *and* `v` has already
    /// popped (`P[v]` non-empty), one [`GllReturn`] is synthesised per recorded
    /// pop `(k, z) ∈ P[v]` — `{ slot: L, caller: u, at_pos: k, operand_w: w,
    /// result_w: z }` — so the freshly-linked caller immediately receives the
    /// return it would otherwise have missed (the classic GLL bug class). The
    /// driver combines `operand_w`/`result_w` into `y = getNodeP(L, w, z)` and
    /// enqueues descriptor `(L, u, k, y)`.
    ///
    /// Returns `(v, replays)`.
    #[allow(dead_code)]
    pub(crate) fn gll_create(
        &mut self,
        from_node: GssNodeId,
        return_slot: StackSymbolV2,
        at_pos: usize,
        operand_w: SppfId,
        caller_sppf_stack: crate::path_tree_arena::StackId,
        caller_edge_stack: crate::path_tree_arena::StackId,
    ) -> (GssNodeId, Vec<GllReturn>) {
        // Node dedup rides the EXISTING (pos, symbol) index — the canonical
        // GSS-by-slot identity (Stage A/D) IS the symbol being slot-shaped.
        let v = self.get_or_create_node(WpdaGssNode { pos: at_pos, symbol: return_slot });
        let st = self.canonical_mut();
        {
            let edges = st.edges.entry(v).or_default();
            // Edge identity = (target, operand_w). Idempotent re-add ⇒ no replay.
            if edges
                .iter()
                .any(|e| e.target == from_node && e.operand_w == operand_w)
            {
                return (v, Vec::new());
            }
            edges.push(CanonicalGllEdge {
                target: from_node,
                operand_w,
                caller_sppf_stack,
                caller_edge_stack,
            });
        }
        // New edge: replay EVERY recorded pop of `v` into this fresh caller.
        let replays = st
            .recorded_pops
            .get(&v)
            .map(|pops| {
                pops.iter()
                    .map(|p| GllReturn {
                        slot: return_slot,
                        caller: from_node,
                        at_pos: p.pos,
                        operand_w,
                        result_w: p.result_w,
                        caller_sppf_stack,
                        caller_edge_stack,
                        rule_id: p.rule_id,
                    })
                    .collect()
            })
            .unwrap_or_default();
        (v, replays)
    }

    /// Canonical GLL `pop(u, i, z)` — GSS-layer half (Scott-Johnstone §4).
    ///
    /// Records `(pos i, result_w z, rule_id, pop_action_weight)` into
    /// `P[node u]` (P is a SET over the `(i, z, rule_id)` identity triple: a
    /// duplicate is ignored and yields NO returns — the returns were already
    /// produced on the first pop, and any later-added edge is handled by
    /// `gll_create`'s replay). For a genuinely-new pop, one [`GllReturn`] is
    /// produced per current outgoing edge `u → caller` labelled `w` —
    /// `{ slot: L_u, caller, at_pos: i, operand_w: w, result_w: z }` — where
    /// `L_u` is `u`'s own label symbol (the return slot).
    ///
    /// Task #10 item 3 — duplicate-pop weight policy: FIRST-WINS. A
    /// duplicate returns BEFORE any packing intern happens today (this very
    /// early-return), so the first recorded weight is the counterfactually
    /// faithful one; an ⊕-merge would mint `min(w1, w2)` — a weight no
    /// original intern ever carried (red-team amendment 5, refuting the
    /// earlier ⊕-merge rationale). With `rule_id` in the identity triple
    /// (F5-2), "duplicate" means SAME-IDENTITY duplicates only: two pops at
    /// the same `(pos, z)` under DIFFERENT rule identities are separate P
    /// entries, each carrying its own weight. The `debug_assert` below
    /// checks that same-identity duplicates carry EQUAL weights (probe P2:
    /// if it ever fires, the first-wins choice is materially lossy — stop
    /// and re-derive).
    #[allow(dead_code)]
    pub(crate) fn gll_pop(
        &mut self,
        node: GssNodeId,
        pos: usize,
        result_w: SppfId,
        rule_id: u32,
        pop_action_weight: &W,
    ) -> Vec<GllReturn> {
        // `L_u` = the popping node's label symbol. StackSymbolV2 is `Copy`, so
        // extract it BEFORE borrowing the canonical side-state (no borrow clash).
        let slot = match self.node(node) {
            Some(n) => n.symbol,
            None => return Vec::new(),
        };
        let st = self.canonical_mut();
        {
            let pops = st.recorded_pops.entry(node).or_default();
            // P is a set: skip a duplicate pop (idempotent; no double-emit and no
            // duplicate P entry that a later `gll_create` would over-replay).
            // FIRST-WINS on the stored weight (see the method doc).
            if let Some(existing) = pops
                .iter()
                .find(|p| p.pos == pos && p.result_w == result_w && p.rule_id == rule_id)
            {
                debug_assert!(
                    existing.pop_action_weight == *pop_action_weight,
                    "same-identity duplicate pop carries a DIFFERENT weight \
                     (node={node}, pos={pos}, result_w={result_w}, rule_id={rule_id:#x}) — \
                     first-wins would be lossy; re-derive the duplicate-pop policy (task #10 \
                     item 3 amendment 5 / probe P2)"
                );
                return Vec::new();
            }
            pops.push(RecordedPop {
                pos,
                result_w,
                rule_id,
                pop_action_weight: pop_action_weight.clone(),
            });
        }
        // Emit a return for EVERY current edge of `node` (edges added LATER are
        // handled by `gll_create`'s create-after-pop replay).
        st.edges
            .get(&node)
            .map(|edges| {
                edges
                    .iter()
                    .map(|e| GllReturn {
                        slot,
                        caller: e.target,
                        at_pos: pos,
                        operand_w: e.operand_w,
                        result_w,
                        caller_sppf_stack: e.caller_sppf_stack,
                        caller_edge_stack: e.caller_edge_stack,
                        rule_id,
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Enumerate a node's canonical predecessors with their operand labels —
    /// `(caller/predecessor, operand_w)` per outgoing canonical edge. The
    /// operand-aware mirror of [`WpdaGss::pop_all_predecessors`] (which
    /// enumerates the CLASSIC weighted `edges` map); this reads the
    /// operand-labelled canonical store instead. Empty if the node has no
    /// canonical edges (or no `gll_*` op has run).
    #[allow(dead_code)]
    pub(crate) fn gll_predecessors(&self, node: GssNodeId) -> Vec<(GssNodeId, SppfId)> {
        match self.canonical_ref().and_then(|st| st.edges.get(&node)) {
            Some(edges) => edges.iter().map(|e| (e.target, e.operand_w)).collect(),
            None => Vec::new(),
        }
    }

    /// Borrow a node's outgoing canonical operand edges (`&[]` if none) — a
    /// borrow-only companion to [`WpdaGss::gll_predecessors`] for the driver's
    /// hot enumerate.
    #[allow(dead_code)]
    pub(crate) fn gll_edges(&self, node: GssNodeId) -> &[CanonicalGllEdge] {
        match self.canonical_ref().and_then(|st| st.edges.get(&node)) {
            Some(edges) => edges.as_slice(),
            None => &[],
        }
    }

    /// Read a node's recorded-pop set `P` (`&[]` if none). Exposed for the driver
    /// + tests to assert pop-recording WITHOUT re-triggering emission.
    #[allow(dead_code)]
    pub(crate) fn gll_recorded_pops(&self, node: GssNodeId) -> &[RecordedPop<W>] {
        match self.canonical_ref().and_then(|st| st.recorded_pops.get(&node)) {
            Some(pops) => pops.as_slice(),
            None => &[],
        }
    }

    /// Task #10 item 3: borrow the recorded pop-action weight of the P entry
    /// with identity `(pos, result_w, rule_id)` on `node` — the identity
    /// triple a create-after-pop replay [`GllReturn`] carries (`at_pos`,
    /// `result_w`, `rule_id`), so the replay arm can intern a genuinely-new
    /// replay packing with the TRUE pop weight. A linear scan: P vecs are
    /// small and the replay arm calls this once per replayed pop.
    #[allow(dead_code)]
    pub(crate) fn gll_recorded_pop_action_weight(
        &self,
        node: GssNodeId,
        pos: usize,
        result_w: SppfId,
        rule_id: u32,
    ) -> Option<&W> {
        self.canonical_ref()
            .and_then(|st| st.recorded_pops.get(&node))
            .and_then(|pops| {
                pops.iter()
                    .find(|p| p.pos == pos && p.result_w == result_w && p.rule_id == rule_id)
                    .map(|p| &p.pop_action_weight)
            })
    }

    /// ROOT-P Stage E — every GSS node sharing a `(category, pos)` slot. The
    /// canonical `(nonterminal X, position j)` node identity, recovered by scan
    /// over the classic `(pos, symbol)` node index (poly-many nodes) WITHOUT
    /// re-keying it (which the Stage-C unit tests pin). Used by the exact pop-fan
    /// to reconnect callers spread across the `@`-cohort's rule-variant nodes.
    #[allow(dead_code)]
    pub(crate) fn nodes_with_category_pos(&self, category: u16, pos: usize) -> Vec<GssNodeId> {
        let mut out: Vec<GssNodeId> = Vec::new();
        for (id, n) in self.nodes.iter().enumerate() {
            if n.pos == pos && n.symbol.category_src_idx == category {
                out.push(id as GssNodeId);
            }
        }
        out
    }

    /// ROOT-P Stage E — SLOT-COARSENED predecessor enumeration (canonical GLL
    /// node identity fix, plan §Stage-E point #3). The canonical operand edges
    /// are stored per GSS node, and GSS nodes dedup by `(pos, symbol)` — but the
    /// `@`-send cohort's rule variants (POutputNil / POutputShort / POutputQuoted
    /// / …) each carry a DISTINCT `symbol`, so callers that descended into the
    /// SAME constituent category at the SAME position land on DIFFERENT nodes and
    /// their return edges never co-locate. Scott & Johnstone's canonical GSS node
    /// is `(nonterminal X, position j)` — ALL callers awaiting an `X` at `j` share
    /// ONE node. This enumerator recovers that identity WITHOUT re-keying the node
    /// index (which the Stage-C unit tests pin): it unions the canonical edges of
    /// every node whose `symbol.category_src_idx == category` and `pos == at_pos`.
    /// The scan is over the canonical edge map (poly-many nodes) so it stays
    /// polynomial. Returns each caller edge once (deduped by
    /// `(target, operand_w, caller_sppf_stack, caller_edge_stack)`), so the exact
    /// pop-fan can resume every awaiting caller with its own saved left-context.
    #[allow(dead_code)]
    pub(crate) fn gll_edges_by_slot(&self, category: u16, at_pos: usize) -> Vec<CanonicalGllEdge> {
        let Some(st) = self.canonical_ref() else {
            return Vec::new();
        };
        let mut out: Vec<CanonicalGllEdge> = Vec::new();
        for (node_id, edges) in st.edges.iter() {
            match self.nodes.get(*node_id as usize) {
                Some(n) if n.pos == at_pos && n.symbol.category_src_idx == category => {
                    for e in edges {
                        if !out.iter().any(|o| {
                            o.target == e.target
                                && o.operand_w == e.operand_w
                                && o.caller_sppf_stack == e.caller_sppf_stack
                                && o.caller_edge_stack == e.caller_edge_stack
                        }) {
                            out.push(*e);
                        }
                    }
                },
                _ => {},
            }
        }
        out
    }

    /// ROOT-P EXACT-FAN A1 census (2026-07-09, READ-ONLY measurement-only). For
    /// every distinct canonical slot `(category_src_idx, pos)` carrying ≥1
    /// recorded canonical operand edge, computes the DEDUPED edge count (the same
    /// `(target, operand_w, caller_sppf_stack, caller_edge_stack)` dedup as
    /// [`Self::gll_edges_by_slot`]). Returns `(n_slots, max_edges_per_slot,
    /// total_edges)`.
    ///
    /// Because canonical operand edges are recorded at DESCENT (`gll_create`),
    /// NOT at reduce, this whole-parse census tells the exact-fan A1 measurement
    /// whether a constituent's genuine callers were recorded EVEN IF its `Pop`
    /// reduce is merged away before firing under the poly return-slot key — the
    /// C-under question for `@x!(for(…){…})`. Byte-identical: `#[allow(dead_code)]`,
    /// reached only from the const-gated `step_canonical` measurement pass.
    #[allow(dead_code)]
    pub(crate) fn canonical_edge_census(&self) -> (usize, usize, usize) {
        let Some(st) = self.canonical_ref() else {
            return (0, 0, 0);
        };
        let mut by_slot: FxHashMap<(u16, usize), Vec<CanonicalGllEdge>> = FxHashMap::default();
        for (node_id, edges) in st.edges.iter() {
            let Some(n) = self.nodes.get(*node_id as usize) else {
                continue;
            };
            let slot = (n.symbol.category_src_idx, n.pos);
            let acc = by_slot.entry(slot).or_default();
            for e in edges {
                if !acc.iter().any(|o| {
                    o.target == e.target
                        && o.operand_w == e.operand_w
                        && o.caller_sppf_stack == e.caller_sppf_stack
                        && o.caller_edge_stack == e.caller_edge_stack
                }) {
                    acc.push(*e);
                }
            }
        }
        let n_slots = by_slot.len();
        let max_edges = by_slot.values().map(|v| v.len()).max().unwrap_or(0);
        let total: usize = by_slot.values().map(|v| v.len()).sum();
        (n_slots, max_edges, total)
    }
}

impl<W: SemiringRef> Default for WpdaGss<W> {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gss_create_node() {
        let mut gss = GraphStructuredStack::new();
        let node = GssNode {
            pos: 0,
            frame_tag: "InfixRHS".to_string(),
        };
        let id = gss.get_or_create_node(node.clone());
        assert_eq!(id, 0);

        // Same node should return same ID (structural sharing)
        let id2 = gss.get_or_create_node(node);
        assert_eq!(id2, 0);
        assert_eq!(gss.node_count(), 1);
    }

    #[test]
    fn test_gss_fork() {
        let mut gss = GraphStructuredStack::new();
        let root = gss.get_or_create_node(GssNode { pos: 0, frame_tag: "Root".to_string() });
        gss.push_frontier(root);

        let fork1 = gss.fork(root, GssNode { pos: 1, frame_tag: "Alt_A".to_string() }, 0.5);
        let fork2 = gss.fork(root, GssNode { pos: 1, frame_tag: "Alt_B".to_string() }, 0.7);

        assert_eq!(gss.node_count(), 3);
        assert_eq!(gss.edge_count(), 2);

        // Both forks share the root as successor
        let edges1 = gss.edges_from(fork1);
        assert_eq!(edges1.len(), 1);
        assert_eq!(edges1[0].target, root);

        let edges2 = gss.edges_from(fork2);
        assert_eq!(edges2.len(), 1);
        assert_eq!(edges2[0].target, root);
    }

    #[test]
    fn test_gss_paths_to_root() {
        let mut gss = GraphStructuredStack::new();
        let root = gss.get_or_create_node(GssNode { pos: 0, frame_tag: "Root".to_string() });
        let mid = gss.get_or_create_node(GssNode { pos: 1, frame_tag: "Mid".to_string() });
        let top = gss.get_or_create_node(GssNode { pos: 2, frame_tag: "Top".to_string() });

        gss.add_edge(mid, root, 1.0);
        gss.add_edge(top, mid, 1.0);

        let paths = gss.paths_to_root(top);
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![top, mid, root]);
    }

    #[test]
    fn test_sppf_basic() {
        let mut sppf = Sppf::new();
        let t1 = sppf.add_node(SppfNode::Terminal { pos: 0, text: "1".to_string() });
        let t2 = sppf.add_node(SppfNode::Terminal { pos: 2, text: "2".to_string() });
        let add = sppf.add_node(SppfNode::Interior {
            label: "Add".to_string(),
            start: 0,
            end: 3,
            children: vec![t1, t2],
        });

        assert_eq!(sppf.len(), 3);
        assert_eq!(sppf.tree_count(add), 1);
    }

    #[test]
    fn test_sppf_ambiguous() {
        let mut sppf = Sppf::new();
        let t1 = sppf.add_node(SppfNode::Terminal { pos: 0, text: "a".to_string() });
        let t2 = sppf.add_node(SppfNode::Terminal { pos: 1, text: "b".to_string() });
        let t3 = sppf.add_node(SppfNode::Terminal { pos: 2, text: "c".to_string() });

        // Two alternative derivations
        let packed = sppf.add_node(SppfNode::Packed {
            alternatives: vec![vec![t1, t2], vec![t2, t3]],
        });

        assert_eq!(sppf.tree_count(packed), 2);
    }

    // ─── WpdaGss tests ──────────────────────────────────────────────────────

    use crate::automata::lex_weight::LexicographicWeight;
    use crate::automata::semiring::TropicalWeight;

    fn lex(cost: f64, src: u16, rule: u16) -> LexicographicWeight {
        LexicographicWeight::from_cost(cost, src, rule)
    }

    #[test]
    fn test_wpds_gss_create_and_share() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let n = WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(3),
        };
        let id1 = g.get_or_create_node(n.clone());
        let id2 = g.get_or_create_node(n);
        assert_eq!(id1, id2, "structural sharing on (pos, symbol)");
        assert_eq!(g.node_count(), 1);
    }

    #[test]
    fn test_wpds_gss_push_symbol() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let pushed =
            g.push_symbol(root, StackSymbolV2::rule_at(0, 1, 0, Some(5)), 1, lex(2.0, 0, 1));
        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);
        let edges = g.edges_from(pushed);
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].target, root);
        assert_eq!(edges[0].weight.primary.0, 2.0);
    }

    #[test]
    fn test_wpds_gss_edge_identity_includes_edge_kind() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let target = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let source = g.get_or_create_node(WpdaGssNode {
            pos: 1,
            symbol: StackSymbolV2::rule_at(0, 1, 0, None),
        });

        let root_edge =
            g.add_edge_kind(source, target, lex(1.0, 0, 0), EdgeKind::CategoryEntryRoot);
        let lhs_kind = EdgeKind::CrossCatLhs { source_src_idx: 2 };
        let lhs_edge = g.add_edge_kind(source, target, lex(1.0, 0, 0), lhs_kind.clone());
        let lhs_reentry_kind = EdgeKind::CrossCatLhsReentry {
            source_src_idx: 2,
            min_bp: 0,
            origin: None,
        };
        let lhs_reentry_edge =
            g.add_edge_kind(source, target, lex(1.0, 0, 0), lhs_reentry_kind.clone());
        let generic_edge = g.add_edge(source, target, lex(1.0, 0, 0));
        let lhs_duplicate = g.add_edge_kind(source, target, lex(2.0, 0, 0), lhs_kind.clone());

        assert_ne!(root_edge, lhs_edge);
        assert_ne!(lhs_edge, lhs_reentry_edge);
        assert_ne!(root_edge, generic_edge);
        assert_ne!(lhs_edge, generic_edge);
        assert_ne!(lhs_reentry_edge, generic_edge);
        assert_eq!(lhs_duplicate, lhs_edge);
        assert_eq!(g.edge_count(), 4);
        assert_eq!(g.edge_kind(root_edge), Some(EdgeKind::CategoryEntryRoot));
        assert_eq!(g.edge_kind(lhs_edge), Some(lhs_kind));
        assert_eq!(g.edge_kind(lhs_reentry_edge), Some(lhs_reentry_kind));
        assert_eq!(g.edge_kind(generic_edge), Some(EdgeKind::Generic));
        assert!(matches!(g.edge_kind_ref(root_edge), Some(EdgeKind::CategoryEntryRoot)));
        assert!(matches!(
            g.edge_kind_ref(lhs_edge),
            Some(EdgeKind::CrossCatLhs { source_src_idx: 2 })
        ));
    }

    #[test]
    fn test_wpds_gss_pop_symbol() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let top = g.push_symbol(root, StackSymbolV2::rule_at(0, 0, 0, None), 1, lex(1.0, 0, 0));
        let popped = g.pop_symbol(top);
        assert_eq!(popped, Some(root));
        // Pop at root should yield None.
        assert_eq!(g.pop_symbol(root), None);
    }

    #[test]
    fn test_wpds_gss_replace_top_inherits_predecessors() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let mid = g.push_symbol(root, StackSymbolV2::rule_at(0, 0, 0, None), 1, lex(1.0, 0, 0));
        let replaced = g.replace_top(mid, StackSymbolV2::rule_at(0, 0, 1, None), 2, lex(0.5, 0, 0));
        let pred = g.pop_symbol(replaced);
        assert_eq!(pred, Some(root), "replace inherits the predecessor");
    }

    #[test]
    fn test_wpds_gss_fork_shares_continuation() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        g.push_frontier(root);
        let alt_a = g.fork(
            root,
            WpdaGssNode {
                pos: 1,
                symbol: StackSymbolV2::rule_at(0, 0, 0, None),
            },
            lex(1.0, 0, 0),
        );
        let alt_b = g.fork(
            root,
            WpdaGssNode {
                pos: 1,
                symbol: StackSymbolV2::rule_at(0, 1, 0, None),
            },
            lex(1.0, 0, 1),
        );
        assert_eq!(g.node_count(), 3);
        // Both forks point at root.
        assert_eq!(g.pop_symbol(alt_a), Some(root));
        assert_eq!(g.pop_symbol(alt_b), Some(root));
        // Both are on the frontier (plus the original root push).
        assert_eq!(g.frontier_size(), 3);
    }

    #[test]
    fn test_wpds_gss_paths_iterative_avoids_recursion() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        // Build a deep linear stack (1000 frames) — would overflow with recursive DFS.
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let mut current = root;
        for i in 1..=1000 {
            current = g.push_symbol(
                current,
                StackSymbolV2::rule_at(0, 0, (i % 250) as u8, None),
                i,
                lex(1.0, 0, 0),
            );
        }
        let paths = g.paths_to_root(current);
        assert_eq!(paths.len(), 1, "linear chain has one path");
        assert_eq!(paths[0].len(), 1001, "1000 push edges + start");
    }

    #[test]
    fn test_wpds_gss_paths_branching() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let a = g.push_symbol(root, StackSymbolV2::rule_at(0, 0, 0, None), 1, lex(1.0, 0, 0));
        let b = g.push_symbol(root, StackSymbolV2::rule_at(0, 1, 0, None), 1, lex(1.0, 0, 1));
        let merge = g.get_or_create_node(WpdaGssNode {
            pos: 2,
            symbol: StackSymbolV2::rule_at(0, 0, 1, None),
        });
        g.add_edge(merge, a, lex(1.0, 0, 0));
        g.add_edge(merge, b, lex(1.0, 0, 0));
        let paths = g.paths_to_root(merge);
        assert_eq!(paths.len(), 2, "diamond yields two paths");
        for p in &paths {
            assert_eq!(p.first(), Some(&merge));
            assert_eq!(p.last(), Some(&root));
        }
    }

    #[test]
    fn test_wpds_gss_cycle_detection_acyclic() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let mid = g.push_symbol(root, StackSymbolV2::rule_at(0, 0, 0, None), 1, lex(1.0, 0, 0));
        let top = g.push_symbol(mid, StackSymbolV2::rule_at(0, 0, 1, None), 2, lex(1.0, 0, 0));
        assert!(!g.has_cycle_from(top));
        assert!(!g.has_cycle_from(root));
    }

    #[test]
    fn test_wpds_gss_cycle_detection_self_loop() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let n = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        // Add a self-edge — pathological GSS, but cycle detection should catch.
        g.add_edge(n, n, lex(1.0, 0, 0));
        assert!(g.has_cycle_from(n));
    }

    #[test]
    fn test_wpds_gss_cycle_detection_two_node_cycle() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let a = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let b = g.get_or_create_node(WpdaGssNode {
            pos: 1,
            symbol: StackSymbolV2::rule_at(0, 0, 0, None),
        });
        g.add_edge(a, b, lex(1.0, 0, 0));
        g.add_edge(b, a, lex(1.0, 0, 0));
        assert!(g.has_cycle_from(a));
        assert!(g.has_cycle_from(b));
    }

    #[test]
    fn test_wpds_gss_pop_all_predecessors() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let r1 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let r2 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(1),
        });
        let merged = g.get_or_create_node(WpdaGssNode {
            pos: 1,
            symbol: StackSymbolV2::rule_at(0, 0, 0, None),
        });
        g.add_edge(merged, r1, lex(1.0, 0, 0));
        g.add_edge(merged, r2, lex(2.0, 1, 0));
        let preds = g.pop_all_predecessors(merged);
        assert_eq!(preds.len(), 2);
    }

    #[test]
    fn test_wpds_gss_works_with_tropical_weight() {
        // The typed GSS is generic over Semiring; make sure non-Lex weights compile.
        let mut g: WpdaGss<TropicalWeight> = WpdaGss::new();
        let n = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let _ =
            g.push_symbol(n, StackSymbolV2::rule_at(0, 0, 0, None), 1, TropicalWeight::new(0.5));
        assert_eq!(g.node_count(), 2);
    }

    #[test]
    fn test_wpds_gss_replace_top_composes_weights() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let root = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let mid = g.push_symbol(root, StackSymbolV2::rule_at(0, 0, 0, None), 1, lex(1.0, 0, 0));
        let replaced = g.replace_top(mid, StackSymbolV2::rule_at(0, 0, 1, None), 2, lex(0.5, 2, 3));
        // The replacement edge should carry the times-composition of replace weight
        // and the inherited edge weight.
        let edges = g.edges_from(replaced);
        assert_eq!(edges.len(), 1);
        // Left-projection: replace weight (0.5, 2, 3) on left ⊗ inherited (1.0, 0, 0).
        // Primary = 1.5, src/rule from left = (2, 3).
        assert!((edges[0].weight.primary.0 - 1.5).abs() < 1e-9);
        assert_eq!(edges[0].weight.src_idx, 2);
        assert_eq!(edges[0].weight.rule_idx, 3);
    }

    // ─── Canonical-GLL GSS primitives (ROOT-P Stage C) ───────────────────────
    //
    // Exercise the DORMANT canonical create/pop/enumerate primitives in
    // ISOLATION (the classic engine never calls them). `SppfId` is a plain `u32`
    // handle here — the tests use synthetic ids; the real driver (Stage D)
    // supplies interned SPPF node ids. The four test classes cover: (a) edge
    // operand-label round-trip, (b) create-after-pop replay (the classic GLL bug
    // class), (c) pop enumerates ALL predecessors with their correct operand
    // labels, (d) create idempotence / (target, operand_w) dedup.
    use crate::sppf::SppfId;

    /// A distinct return-slot symbol `L` — a mid-rule `RuleAt` frame, the
    /// slot-shaped continuation the canonical GSS keys nodes on.
    fn slot_sym(cat: u16, rule: u16, item: u8) -> StackSymbolV2 {
        StackSymbolV2::rule_at(cat, rule, item, Some(0))
    }

    #[test]
    fn test_canonical_gll_edge_label_roundtrip() {
        // (a) Attach operand `w` on create; read it back via enumerate AND at pop.
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let caller = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let w: SppfId = 42;
        let l = slot_sym(1, 0, 1);
        let (v, replays) = g.gll_create(caller, l, 3, w, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
        assert!(replays.is_empty(), "no pops recorded yet ⇒ no replay");

        // Enumerate: predecessor + operand label round-trip.
        assert_eq!(
            g.gll_predecessors(v),
            vec![(caller, w)],
            "operand label read back via enumerate"
        );
        assert_eq!(g.gll_edges(v).len(), 1);
        assert_eq!(g.gll_edges(v)[0].operand_w, w);

        // Pop: the return carries the same operand `w` plus slot/caller/pos/z.
        let z: SppfId = 99;
        let returns = g.gll_pop(v, 5, z, u32::MAX, &lex(0.0, 0, 0));
        assert_eq!(returns.len(), 1);
        let r = returns[0];
        assert_eq!(r.operand_w, w, "operand w round-trips through pop");
        assert_eq!(r.result_w, z);
        assert_eq!(r.caller, caller);
        assert_eq!(r.at_pos, 5);
        assert_eq!(r.slot, l, "return slot = the popped node's label symbol");
    }

    #[test]
    fn test_canonical_gll_create_after_pop_replay() {
        // (b) THE bug class: pop `v` (recording `z`), THEN create a NEW edge into
        // `v`; the new edge must IMMEDIATELY yield the return for `z`.
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let c1 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let c2 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(1),
        });
        let l = slot_sym(1, 0, 1);
        let (w1, w2): (SppfId, SppfId) = (10, 20);

        // 1. First caller edge, then pop → return goes to c1.
        let (v, r0) = g.gll_create(c1, l, 3, w1, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
        assert!(r0.is_empty());
        let z: SppfId = 7;
        let popret = g.gll_pop(v, 8, z, u32::MAX, &lex(0.0, 0, 0));
        assert_eq!(popret.len(), 1);
        assert_eq!(popret[0].caller, c1);
        assert_eq!(g.gll_recorded_pops(v).len(), 1, "z recorded in P[v]");

        // 2. NEW caller edge AFTER the pop ⇒ replay yields the return for z.
        let (v2, replays) = g.gll_create(c2, l, 3, w2, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
        assert_eq!(v2, v, "same (slot, pos) ⇒ same node");
        assert_eq!(replays.len(), 1, "create-after-pop replays the recorded pop");
        let r = replays[0];
        assert_eq!(r.caller, c2, "replay routes to the NEW caller");
        assert_eq!(r.result_w, z, "replayed with the recorded result z");
        assert_eq!(r.operand_w, w2, "replay carries the NEW edge's operand");
        assert_eq!(r.at_pos, 8, "replay resumes at the recorded pop position");
        assert_eq!(r.slot, l);
    }

    #[test]
    fn test_canonical_gll_pop_enumerates_all_predecessors() {
        // (c) pop enumerates ALL predecessors, each with its correct operand.
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let l = slot_sym(2, 1, 0);
        let callers: Vec<(GssNodeId, SppfId)> = (0..3u16)
            .map(|i| {
                let c = g.get_or_create_node(WpdaGssNode {
                    pos: 0,
                    symbol: StackSymbolV2::category_entry(i),
                });
                (c, 100 + i as SppfId)
            })
            .collect();
        let mut v: GssNodeId = 0;
        for &(c, w) in &callers {
            let (vv, _) = g.gll_create(c, l, 4, w, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
            v = vv;
        }
        assert_eq!(g.gll_edges(v).len(), 3, "three distinct predecessor edges");

        let z: SppfId = 555;
        let mut returns = g.gll_pop(v, 9, z, u32::MAX, &lex(0.0, 0, 0));
        assert_eq!(returns.len(), 3, "one return per predecessor edge");
        // Each return pairs the correct caller with the correct operand.
        returns.sort_by_key(|r| r.caller);
        let mut expect = callers.clone();
        expect.sort_by_key(|(c, _)| *c);
        for (r, (c, w)) in returns.iter().zip(expect.iter()) {
            assert_eq!(r.caller, *c);
            assert_eq!(r.operand_w, *w, "predecessor's operand label preserved");
            assert_eq!(r.result_w, z);
            assert_eq!(r.at_pos, 9);
            assert_eq!(r.slot, l);
        }
    }

    #[test]
    fn test_canonical_gll_create_idempotent_dedup() {
        // (d) create dedups by (target, operand_w): same edge twice = one edge;
        // a different operand into the SAME caller = a distinct edge.
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let c1 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let l = slot_sym(1, 0, 1);
        let w1: SppfId = 11;

        let (v, _) = g.gll_create(c1, l, 3, w1, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
        let (v_again, replays) = g.gll_create(c1, l, 3, w1, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT); // identical
        assert_eq!(v_again, v);
        assert!(replays.is_empty(), "idempotent re-add ⇒ no replay");
        assert_eq!(g.gll_edges(v).len(), 1, "identical edge added exactly once");

        // Different operand into the SAME caller ⇒ a distinct canonical edge.
        let w2: SppfId = 22;
        let _ = g.gll_create(c1, l, 3, w2, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT);
        assert_eq!(g.gll_edges(v).len(), 2, "distinct operand ⇒ distinct edge");

        // Re-adding an existing edge AFTER a pop must ALSO be idempotent AND must
        // NOT re-fire the replay (double-count guard — the subtle GLL bug class).
        let z: SppfId = 3;
        let _ = g.gll_pop(v, 6, z, u32::MAX, &lex(0.0, 0, 0));
        let (_, replays_after_pop) = g.gll_create(c1, l, 3, w1, crate::path_tree_arena::STACK_ID_ROOT, crate::path_tree_arena::STACK_ID_ROOT); // already present
        assert!(
            replays_after_pop.is_empty(),
            "re-adding an existing edge after a pop must NOT re-fire the replay"
        );

        // A duplicate pop is a no-op (P is a set).
        let dup = g.gll_pop(v, 6, z, u32::MAX, &lex(0.0, 0, 0));
        assert!(dup.is_empty(), "duplicate pop ⇒ no double-emit");
        assert_eq!(g.gll_recorded_pops(v).len(), 1, "P deduped by (pos, result)");
    }

    /// Task #10 item 3: P entries record the pop-action weight; the
    /// duplicate-pop policy is FIRST-WINS over the `(pos, result_w,
    /// rule_id)` identity triple (same-identity duplicates must carry
    /// EQUAL weights — the `debug_assert` in `gll_pop`; this test
    /// re-passes the SAME weight accordingly). A pop at the same
    /// `(pos, z)` under a DIFFERENT rule identity is a DISTINCT P entry
    /// carrying its own weight (the F5-2 identity-carry interaction), and
    /// a later `gll_create` replays BOTH entries.
    #[test]
    fn test_canonical_gll_pop_records_action_weight_first_wins() {
        let mut g: WpdaGss<LexicographicWeight> = WpdaGss::new();
        let c1 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(0),
        });
        let c2 = g.get_or_create_node(WpdaGssNode {
            pos: 0,
            symbol: StackSymbolV2::category_entry(1),
        });
        let l = slot_sym(1, 0, 1);
        let (v, _) = g.gll_create(
            c1,
            l,
            3,
            10,
            crate::path_tree_arena::STACK_ID_ROOT,
            crate::path_tree_arena::STACK_ID_ROOT,
        );
        let z: SppfId = 7;
        let w_rule5 = lex(0.25, 0, 5);
        let w_rule6 = lex(0.5, 0, 6);

        // First pop under rule identity 5 records its weight.
        let r1 = g.gll_pop(v, 8, z, 5, &w_rule5);
        assert_eq!(r1.len(), 1, "one return per edge on a genuinely-new pop");
        assert_eq!(
            g.gll_recorded_pop_action_weight(v, 8, z, 5),
            Some(&w_rule5),
            "the accessor returns the recorded pop-action weight"
        );

        // Same-identity duplicate (same weight per the equal-weight
        // invariant): FIRST-WINS — no returns, no new entry, stored weight
        // unchanged.
        let dup = g.gll_pop(v, 8, z, 5, &w_rule5);
        assert!(dup.is_empty(), "same-identity duplicate ⇒ no double-emit");
        assert_eq!(g.gll_recorded_pops(v).len(), 1, "no duplicate P entry");
        assert_eq!(
            g.gll_recorded_pop_action_weight(v, 8, z, 5),
            Some(&w_rule5),
            "first-wins: the stored weight is the FIRST pop's"
        );

        // DIFFERENT rule identity at the same (pos, z): a separate P entry
        // with its own weight — both weights independently retrievable.
        let r2 = g.gll_pop(v, 8, z, 6, &w_rule6);
        assert_eq!(r2.len(), 1, "distinct identity ⇒ a genuinely-new pop");
        assert_eq!(g.gll_recorded_pops(v).len(), 2, "two identity-distinct entries");
        assert_eq!(g.gll_recorded_pop_action_weight(v, 8, z, 5), Some(&w_rule5));
        assert_eq!(g.gll_recorded_pop_action_weight(v, 8, z, 6), Some(&w_rule6));
        assert_eq!(
            g.gll_recorded_pop_action_weight(v, 8, z, 7),
            None,
            "an unrecorded identity resolves to None"
        );

        // Create-after-pop: a NEW caller edge replays BOTH recorded pops,
        // each carrying its own rule identity (the weight is looked up from
        // the P entry by the replay consumer, not carried on GllReturn).
        let (v2, replays) = g.gll_create(
            c2,
            l,
            3,
            20,
            crate::path_tree_arena::STACK_ID_ROOT,
            crate::path_tree_arena::STACK_ID_ROOT,
        );
        assert_eq!(v2, v, "same (slot, pos) ⇒ same node");
        assert_eq!(replays.len(), 2, "one replay per recorded pop");
        let mut replay_rule_ids: Vec<u32> = replays.iter().map(|r| r.rule_id).collect();
        replay_rule_ids.sort_unstable();
        assert_eq!(replay_rule_ids, vec![5, 6], "replays carry the recorded identities");
    }
}
