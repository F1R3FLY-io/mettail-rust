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

use crate::automata::semiring::SemiringRef;
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    /// Fallback for sites not yet specifically classified. Always
    /// strict identity (compares by source_id).
    Generic { source_id: GssEdgeId },
    /// Cross-cat projection Fork branch: walker emits a Push to
    /// `CategoryEntry(source_src_idx)` to delegate to a sub-cat parse.
    /// Convergent: post-pop returns to the outer dispatch site whose
    /// `(source_src_idx, dest_src_idx, inner_cur_bp)` are payload.
    /// Two cursors that emit the same CrossCatProjection at the same
    /// `(pos, dest_cat, cur_bp)` produce equivalent sub-parse work AND
    /// equivalent post-pop state.
    CrossCatProjection {
        source_src_idx: u16,
        inner_cur_bp: u8,
    },
}

/// Phase F.13 H13 (2026-05-21): sentinel EdgeKind used for edges that
/// existed before the EdgeKind tagging was added, or in legacy
/// constructors that don't yet thread the parameter. Always treated
/// as identity-strict via the GssEdgeId.
impl EdgeKind {
    pub fn generic(source_id: GssEdgeId) -> Self {
        EdgeKind::Generic { source_id }
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

/// Typed graph-structured stack for the WPDS-runtime walker.
///
/// Generic over weight semiring `W`. Mirrors [`GraphStructuredStack`]'s API
/// but with typed symbols and weights, plus WPDS-specific stack operations
/// (`push_symbol`, `pop_symbol`, `replace_top`).
#[derive(Debug, Clone)]
pub struct WpdaGss<W: SemiringRef> {
    nodes: Vec<WpdaGssNode>,
    edges: HashMap<GssNodeId, Vec<WpdaGssEdge<W>>>,
    frontier: Vec<GssNodeId>,
    node_index: HashMap<WpdaGssNode, GssNodeId>,
}

impl<W: SemiringRef> WpdaGss<W> {
    /// Create an empty typed GSS.
    pub fn new() -> Self {
        WpdaGss {
            nodes: Vec::new(),
            edges: HashMap::new(),
            frontier: Vec::new(),
            node_index: HashMap::new(),
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
        // Phase F.13 H13 Step 0 (2026-05-21): tag with Generic placeholder.
        // Higher-level callers (push_symbol_with_edge_id_kind /
        // replace_top_with_edge_id_kind) should use `add_edge_kind` to
        // pass a specific EdgeKind.
        let edges = self.edges.entry(source).or_default();
        for (idx, existing) in edges.iter_mut().enumerate() {
            if existing.target == target {
                existing.weight = existing.weight.plus_ref(&weight);
                return pack_edge_id(source, idx);
            }
        }
        let idx = edges.len();
        let edge_id = pack_edge_id(source, idx);
        edges.push(WpdaGssEdge {
            target,
            weight,
            kind: EdgeKind::Generic { source_id: edge_id },
        });
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
            if existing.target == target {
                existing.weight = existing.weight.plus_ref(&weight);
                // Dedup-on-plus: keep the existing edge's kind.
                // (If the existing was Generic and new is specific,
                // it would be valid to upgrade — defer to a later
                // iteration to keep semantics simple here.)
                return pack_edge_id(source, idx);
            }
        }
        let idx = edges.len();
        let edge_id = pack_edge_id(source, idx);
        edges.push(WpdaGssEdge {
            target,
            weight,
            kind,
        });
        edge_id
    }

    /// Phase F.13 H13 Step 0 (2026-05-21): look up the `EdgeKind` of a
    /// specific edge by its `GssEdgeId`. Returns `None` if the edge
    /// does not exist.
    pub fn edge_kind(&self, edge_id: GssEdgeId) -> Option<EdgeKind> {
        let (source, idx) = unpack_edge_id(edge_id);
        self.edges.get(&source).and_then(|edges| {
            edges.get(idx as usize).map(|e| e.kind.clone())
        })
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
        self.push_symbol_with_edge_id(frontier_node, symbol, pos, weight).0
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
        self.replace_top_with_edge_id(frontier_node, new_symbol, pos, weight, None).0
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
                    }
                    1 => return true, // back-edge — cycle
                    _ => { /* already finished — not a back edge */ }
                }
            } else {
                state.insert(node, 2);
                work.pop();
            }
        }
        false
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
        let root = gss.get_or_create_node(GssNode {
            pos: 0,
            frame_tag: "Root".to_string(),
        });
        gss.push_frontier(root);

        let fork1 = gss.fork(
            root,
            GssNode {
                pos: 1,
                frame_tag: "Alt_A".to_string(),
            },
            0.5,
        );
        let fork2 = gss.fork(
            root,
            GssNode {
                pos: 1,
                frame_tag: "Alt_B".to_string(),
            },
            0.7,
        );

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
        let root = gss.get_or_create_node(GssNode {
            pos: 0,
            frame_tag: "Root".to_string(),
        });
        let mid = gss.get_or_create_node(GssNode {
            pos: 1,
            frame_tag: "Mid".to_string(),
        });
        let top = gss.get_or_create_node(GssNode {
            pos: 2,
            frame_tag: "Top".to_string(),
        });

        gss.add_edge(mid, root, 1.0);
        gss.add_edge(top, mid, 1.0);

        let paths = gss.paths_to_root(top);
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0], vec![top, mid, root]);
    }

    #[test]
    fn test_sppf_basic() {
        let mut sppf = Sppf::new();
        let t1 = sppf.add_node(SppfNode::Terminal {
            pos: 0,
            text: "1".to_string(),
        });
        let t2 = sppf.add_node(SppfNode::Terminal {
            pos: 2,
            text: "2".to_string(),
        });
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
            alternatives: vec![
                vec![t1, t2],
                vec![t2, t3],
            ],
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
        let n = WpdaGssNode { pos: 0, symbol: StackSymbolV2::category_entry(3) };
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
        let pushed = g.push_symbol(root, StackSymbolV2::rule_at(0, 1, 0, Some(5)), 1, lex(2.0, 0, 1));
        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);
        let edges = g.edges_from(pushed);
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].target, root);
        assert_eq!(edges[0].weight.primary.0, 2.0);
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
        let replaced = g.replace_top(
            mid,
            StackSymbolV2::rule_at(0, 0, 1, None),
            2,
            lex(0.5, 0, 0),
        );
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
            WpdaGssNode { pos: 1, symbol: StackSymbolV2::rule_at(0, 0, 0, None) },
            lex(1.0, 0, 0),
        );
        let alt_b = g.fork(
            root,
            WpdaGssNode { pos: 1, symbol: StackSymbolV2::rule_at(0, 1, 0, None) },
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
        let _ = g.push_symbol(
            n,
            StackSymbolV2::rule_at(0, 0, 0, None),
            1,
            TropicalWeight::new(0.5),
        );
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
        let replaced = g.replace_top(
            mid,
            StackSymbolV2::rule_at(0, 0, 1, None),
            2,
            lex(0.5, 2, 3),
        );
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
}
