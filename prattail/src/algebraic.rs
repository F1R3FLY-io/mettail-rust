//! Algebraic program analysis for MeTTaIL.
//!
//! Implements the Tarjan path-expression algorithm extended to interprocedural
//! analysis over algebraic abstractions (semirings), following:
//!
//! > Kincaid, Cyphert, Breck & Reps (2019).
//! > *Algebraic Program Analysis*.
//!
//! ## Key Idea
//!
//! Decompose a program's control flow graph (CFG) into a **path expression** —
//! a regular expression over semiring weights — then evaluate it over an
//! abstract domain.  The path expression captures all paths through the CFG,
//! and the semiring evaluation computes the abstract summary of those paths.
//!
//! ## Architecture
//!
//! ```text
//! WPDS ──→ build_cfg() ──→ ControlFlowGraph<W>
//!                                │
//!              ┌─────────────────┼─────────────────────┐
//!              │                 │                     │
//!              ▼                 ▼                     ▼
//!   tarjan_decompose()   path_expression()    all_pairs_analysis()
//!              │                 │                     │
//!              │                 ▼                     │
//!              │          evaluate() ──→ W             │
//!              │                                      │
//!              └──────────── analyze() ──→ W          │
//!                                                     │
//!                            matrix_star() ◄──────────┘
//! ```
//!
//! ## Semiring Instantiations
//!
//! | Semiring | Analysis |
//! |---|---|
//! | `BooleanWeight` | Reachability (is there any path?) |
//! | `TropicalWeight` | Shortest / minimum-cost path |
//! | `CountingWeight` | Path counting |
//!
//! ## Interprocedural Extension
//!
//! `InterproceduralCfg<W>` extends the intraprocedural CFG with call/return
//! structure.  Each procedure has its own CFG; call edges link caller nodes
//! to callee entries and callee exits to return nodes.  `interprocedural_analyze`
//! computes per-procedure summaries by analyzing each procedure and composing
//! across call boundaries.

use std::collections::HashMap;

use crate::automata::semiring::{matrix_star, Semiring, StarSemiring};
use crate::wpds::{Wpds, WpdsRule};

// ==============================================================================
// Core types
// ==============================================================================

/// A node in the control flow graph, identified by a unique index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CfgNode(pub usize);

/// A weighted directed edge in the control flow graph.
#[derive(Debug, Clone)]
pub struct CfgEdge<W: Semiring> {
    /// Source node.
    pub from: CfgNode,
    /// Target node.
    pub to: CfgNode,
    /// Edge weight in the semiring.
    pub weight: W,
}

/// A control flow graph with weighted edges over a semiring `W`.
///
/// Nodes are identified by contiguous indices `0..nodes.len()`.  The graph
/// has a designated entry and exit node for single-entry/single-exit analysis.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph<W: Semiring> {
    /// All nodes in the CFG.
    pub nodes: Vec<CfgNode>,
    /// All weighted directed edges.
    pub edges: Vec<CfgEdge<W>>,
    /// Entry node (program/procedure start).
    pub entry: CfgNode,
    /// Exit node (program/procedure end).
    pub exit: CfgNode,
}

impl<W: Semiring> ControlFlowGraph<W> {
    /// Build successor index: `successors[from] = [to, ...]` (without weights).
    fn successor_indices(&self) -> Vec<Vec<usize>> {
        let n = self.nodes.len();
        let mut succ: Vec<Vec<usize>> = Vec::with_capacity(n);
        for _ in 0..n {
            succ.push(Vec::new());
        }
        for edge in &self.edges {
            succ[edge.from.0].push(edge.to.0);
        }
        succ
    }
}

// ==============================================================================
// Path Expression (regular expression over semiring weights)
// ==============================================================================

/// A path expression: a regular expression over semiring weights.
///
/// Represents the algebraic structure of all paths through a CFG region.
/// Evaluating the expression over a `StarSemiring` yields the abstract
/// summary of the paths.
#[derive(Debug, Clone)]
pub enum PathExpr<W: Semiring> {
    /// A single edge weight (base case).
    Atom(W),
    /// Sequential composition: `a ; b` corresponds to `a ⊗ b`.
    Seq(Box<PathExpr<W>>, Box<PathExpr<W>>),
    /// Alternative paths: `a | b` corresponds to `a ⊕ b`.
    Alt(Box<PathExpr<W>>, Box<PathExpr<W>>),
    /// Loop closure (Kleene star): `a*` corresponds to `star(a)`.
    Star(Box<PathExpr<W>>),
    /// No path (additive identity).
    Zero,
    /// Empty path (multiplicative identity).
    One,
}

impl<W: Semiring> PathExpr<W> {
    /// Smart constructor for `Seq` that avoids unnecessary boxing when
    /// one operand is the identity.
    pub fn seq(a: PathExpr<W>, b: PathExpr<W>) -> PathExpr<W> {
        match (&a, &b) {
            (PathExpr::Zero, _) | (_, PathExpr::Zero) => PathExpr::Zero,
            (PathExpr::One, _) => b,
            (_, PathExpr::One) => a,
            _ => PathExpr::Seq(Box::new(a), Box::new(b)),
        }
    }

    /// Smart constructor for `Alt` that avoids unnecessary boxing when
    /// one operand is zero.
    pub fn alt(a: PathExpr<W>, b: PathExpr<W>) -> PathExpr<W> {
        match (&a, &b) {
            (PathExpr::Zero, _) => b,
            (_, PathExpr::Zero) => a,
            _ => PathExpr::Alt(Box::new(a), Box::new(b)),
        }
    }

    /// Smart constructor for `Star` that simplifies `star(Zero) = One`
    /// and `star(One) = One`.
    pub fn star(a: PathExpr<W>) -> PathExpr<W> {
        match &a {
            PathExpr::Zero | PathExpr::One => PathExpr::One,
            _ => PathExpr::Star(Box::new(a)),
        }
    }
}

// ==============================================================================
// build_cfg: extract a CFG from a WPDS
// ==============================================================================

/// Extract a control flow graph from a WPDS by flattening push/pop rules
/// to direct edges.
///
/// The WPDS stack symbols become CFG nodes.  Rule types map as follows:
///
/// | WPDS Rule | CFG Edge |
/// |---|---|
/// | `Replace(γ → γ', w)` | `γ → γ'` with weight `w` |
/// | `Pop(γ, w)` | `γ → exit` with weight `w` |
/// | `Push(γ → γ_bottom γ_top, w)` | `γ → γ_top` with weight `w` (call edge; return edge added separately) |
///
/// Push rules are flattened: the callee entry (`γ_top`) gets an edge from
/// the caller, and the return continuation (`γ_bottom`) is connected to the
/// callee entry as well (approximating the interprocedural structure within
/// a single CFG).
pub fn build_cfg<W: Semiring>(wpds: &Wpds<W>) -> ControlFlowGraph<W> {
    if wpds.stack_symbols.is_empty() {
        return ControlFlowGraph {
            nodes: vec![CfgNode(0), CfgNode(1)],
            edges: Vec::new(),
            entry: CfgNode(0),
            exit: CfgNode(1),
        };
    }

    // Map stack symbols to node indices.
    let mut symbol_to_node: HashMap<&crate::wpds::StackSymbol, usize> = HashMap::new();
    for (idx, sym) in wpds.stack_symbols.iter().enumerate() {
        symbol_to_node.insert(sym, idx);
    }

    let n = wpds.stack_symbols.len();
    // Reserve node `n` as a synthetic exit node.
    let exit_node = n;

    let mut nodes: Vec<CfgNode> = Vec::with_capacity(n + 1);
    for i in 0..=n {
        nodes.push(CfgNode(i));
    }

    let mut edges: Vec<CfgEdge<W>> = Vec::with_capacity(wpds.rules.len());

    for rule in &wpds.rules {
        match rule {
            WpdsRule::Replace {
                from_gamma,
                to_gamma,
                weight,
            } => {
                let from = symbol_to_node
                    .get(from_gamma)
                    .copied()
                    .expect("Replace: from_gamma not in symbol_index");
                let to = symbol_to_node
                    .get(to_gamma)
                    .copied()
                    .expect("Replace: to_gamma not in symbol_index");
                edges.push(CfgEdge {
                    from: CfgNode(from),
                    to: CfgNode(to),
                    weight: *weight,
                });
            }
            WpdsRule::Pop { from_gamma, weight } => {
                let from = symbol_to_node
                    .get(from_gamma)
                    .copied()
                    .expect("Pop: from_gamma not in symbol_index");
                edges.push(CfgEdge {
                    from: CfgNode(from),
                    to: CfgNode(exit_node),
                    weight: *weight,
                });
            }
            WpdsRule::Push {
                from_gamma,
                to_gamma_bottom,
                to_gamma_top,
                weight,
            } => {
                let from = symbol_to_node
                    .get(from_gamma)
                    .copied()
                    .expect("Push: from_gamma not in symbol_index");
                let callee_entry = symbol_to_node
                    .get(to_gamma_top)
                    .copied()
                    .expect("Push: to_gamma_top not in symbol_index");
                let return_site = symbol_to_node
                    .get(to_gamma_bottom)
                    .copied()
                    .expect("Push: to_gamma_bottom not in symbol_index");

                // Call edge: caller → callee entry
                edges.push(CfgEdge {
                    from: CfgNode(from),
                    to: CfgNode(callee_entry),
                    weight: *weight,
                });
                // Approximate return: callee entry → return site with identity weight.
                // This flattens the interprocedural structure into a single CFG.
                edges.push(CfgEdge {
                    from: CfgNode(callee_entry),
                    to: CfgNode(return_site),
                    weight: W::one(),
                });
            }
        }
    }

    // Determine entry: use the WPDS initial symbol.
    let entry_idx = symbol_to_node
        .get(&wpds.initial_symbol)
        .copied()
        .unwrap_or(0);

    ControlFlowGraph {
        nodes,
        edges,
        entry: CfgNode(entry_idx),
        exit: CfgNode(exit_node),
    }
}

// ==============================================================================
// Tarjan's SCC decomposition for CFGs
// ==============================================================================

/// Tarjan's strongly connected component decomposition of a CFG.
///
/// Returns SCCs in reverse topological order (sinks first), which is the
/// natural order for bottom-up path expression construction.
///
/// This is a standalone implementation (not reusing `wpds::tarjan_scc`)
/// because the CFG uses contiguous `usize` indices rather than the
/// `HashMap<usize, Vec<usize>>` adjacency format of the WPDS version.
pub fn tarjan_decompose<W: StarSemiring>(cfg: &ControlFlowGraph<W>) -> Vec<Vec<CfgNode>> {
    let n = cfg.nodes.len();
    let succ = cfg.successor_indices();

    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut indices = vec![usize::MAX; n]; // usize::MAX = not yet visited
    let mut lowlinks = vec![0usize; n];
    let mut result: Vec<Vec<CfgNode>> = Vec::new();

    // Iterative Tarjan's algorithm using an explicit work stack to avoid
    // deep recursion on large CFGs.
    //
    // Each frame records: (node, index into that node's successor list).
    // When a frame is first pushed (successor_idx == 0), we initialize
    // the node's index/lowlink and push it onto the Tarjan stack.
    // We then iterate through successors; when we encounter an unvisited
    // successor, we push a new frame for it.  When we return from a
    // successor (successor_idx advances), we update lowlink.  When all
    // successors are processed, we check if this node is an SCC root.
    struct TarjanFrame {
        node: usize,
        successor_idx: usize,
    }

    for start in 0..n {
        if indices[start] != usize::MAX {
            continue;
        }

        let mut work_stack: Vec<TarjanFrame> = vec![TarjanFrame {
            node: start,
            successor_idx: 0,
        }];

        while let Some(frame) = work_stack.last_mut() {
            let v = frame.node;

            if frame.successor_idx == 0 {
                // First visit: initialize
                indices[v] = index_counter;
                lowlinks[v] = index_counter;
                index_counter += 1;
                stack.push(v);
                on_stack[v] = true;
            }

            let successors = &succ[v];
            let mut pushed_child = false;

            while frame.successor_idx < successors.len() {
                let w = successors[frame.successor_idx];
                if indices[w] == usize::MAX {
                    // Unvisited successor: push frame for it, but first
                    // advance our own successor_idx so we resume correctly.
                    frame.successor_idx += 1;
                    work_stack.push(TarjanFrame {
                        node: w,
                        successor_idx: 0,
                    });
                    pushed_child = true;
                    break;
                } else if on_stack[w] {
                    lowlinks[v] = lowlinks[v].min(indices[w]);
                }
                frame.successor_idx += 1;
            }

            if pushed_child {
                continue;
            }

            // All successors processed.  Check for SCC root.
            if lowlinks[v] == indices[v] {
                let mut scc = Vec::new();
                loop {
                    let w = stack.pop().expect("Tarjan stack underflow");
                    on_stack[w] = false;
                    scc.push(CfgNode(w));
                    if w == v {
                        break;
                    }
                }
                result.push(scc);
            }

            // Pop this frame and propagate lowlink to parent.
            let finished_node = work_stack.pop().expect("work stack underflow").node;
            if let Some(parent_frame) = work_stack.last() {
                let parent = parent_frame.node;
                lowlinks[parent] = lowlinks[parent].min(lowlinks[finished_node]);
            }
        }
    }

    result
}

// ==============================================================================
// Path expression construction (Tarjan's algorithm)
// ==============================================================================

/// Compute the path expression from `cfg.entry` to `cfg.exit` using
/// Tarjan's path expression algorithm.
///
/// The algorithm:
/// 1. Compute SCCs of the CFG (returned in reverse topological order).
/// 2. Assign each node to its SCC.
/// 3. Process nodes in reverse postorder.  Within each SCC, internal
///    edges contribute to a loop body expression that is `star`-ed.
///    Cross-SCC edges are sequential composition.
/// 4. Build up the path expression from entry to exit by combining
///    per-SCC contributions.
///
/// For a single-SCC acyclic graph (e.g. a DAG), this reduces to
/// straightforward `Seq`/`Alt` composition without any `Star`.
pub fn path_expression<W: StarSemiring>(cfg: &ControlFlowGraph<W>) -> PathExpr<W> {
    let n = cfg.nodes.len();
    if n == 0 {
        return PathExpr::Zero;
    }

    if cfg.entry == cfg.exit {
        return PathExpr::One;
    }

    let entry = cfg.entry.0;
    let exit = cfg.exit.0;

    // Build adjacency list with combined weights for parallel edges.
    // For each (from, to), combine weights with `plus` (alternative paths).
    let mut edge_map: HashMap<(usize, usize), W> = HashMap::new();
    for edge in &cfg.edges {
        let key = (edge.from.0, edge.to.0);
        edge_map
            .entry(key)
            .and_modify(|w| *w = w.plus(&edge.weight))
            .or_insert(edge.weight);
    }

    // Compute SCCs and build SCC membership map.
    let sccs = tarjan_decompose(cfg);
    let mut scc_of: Vec<usize> = vec![0; n];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for node in scc {
            scc_of[node.0] = scc_idx;
        }
    }

    // For each node, compute the path expression from that node to `exit`.
    // We process in the order returned by tarjan_decompose (reverse topological),
    // which means we process sinks (closer to exit) before sources.
    //
    // `node_expr[v]` = path expression from node v to exit.
    let mut node_expr: Vec<Option<PathExpr<W>>> = Vec::with_capacity(n);
    for _ in 0..n {
        node_expr.push(None);
    }

    // Base case: exit node has the empty path.
    node_expr[exit] = Some(PathExpr::One);

    // Build successor list per node, but only outgoing edges.
    let mut out_edges: Vec<Vec<(usize, W)>> = Vec::with_capacity(n);
    for _ in 0..n {
        out_edges.push(Vec::new());
    }
    for (&(from, to), weight) in &edge_map {
        out_edges[from].push((to, *weight));
    }

    // Process SCCs in reverse topological order (sinks first).
    // Within each SCC, we handle internal cycles via star closure.
    for scc in &sccs {
        let _scc_id = scc_of[scc[0].0];

        if scc.len() == 1 {
            // Singleton SCC: check for self-loop.
            let v = scc[0].0;
            if node_expr[v].is_some() {
                // Already computed (exit node).
                // But check for self-loop.
                if let Some(&self_weight) = edge_map.get(&(v, v)) {
                    let self_star = PathExpr::Star(Box::new(PathExpr::Atom(self_weight)));
                    let old = node_expr[v].take().expect("just checked is_some");
                    node_expr[v] = Some(PathExpr::seq(self_star, old));
                }
                // Recompute to incorporate outgoing cross-SCC edges
                // that go to already-computed nodes (other than self-loop).
                // Actually, for singleton SCC, the outgoing edges to
                // other SCCs form alternative paths to exit.
                // We already set node_expr for exit.  For non-exit nodes,
                // we compute below.
                if v != exit {
                    // We need to compute this node's expression from its outgoing edges.
                    // Since this is a singleton SCC, the only internal edge is a self-loop.
                    let mut combined = PathExpr::Zero;
                    for &(to, w) in &out_edges[v] {
                        if to == v {
                            continue; // self-loop handled above
                        }
                        if let Some(ref to_expr) = node_expr[to] {
                            let path = PathExpr::seq(PathExpr::Atom(w), to_expr.clone());
                            combined = PathExpr::alt(combined, path);
                        }
                        // If to_expr is None, that node is unreachable to exit; skip.
                    }
                    if let Some(&self_weight) = edge_map.get(&(v, v)) {
                        // Apply star of self-loop before the outgoing paths.
                        combined = PathExpr::seq(
                            PathExpr::Star(Box::new(PathExpr::Atom(self_weight))),
                            combined,
                        );
                    }
                    if !matches!(combined, PathExpr::Zero) {
                        node_expr[v] = Some(combined);
                    }
                }
            } else {
                // Non-exit singleton: compute from outgoing edges.
                let mut combined = PathExpr::Zero;
                for &(to, w) in &out_edges[v] {
                    if to == v {
                        continue; // self-loop handled separately
                    }
                    if let Some(ref to_expr) = node_expr[to] {
                        let path = PathExpr::seq(PathExpr::Atom(w), to_expr.clone());
                        combined = PathExpr::alt(combined, path);
                    }
                }
                if let Some(&self_weight) = edge_map.get(&(v, v)) {
                    combined = PathExpr::seq(
                        PathExpr::Star(Box::new(PathExpr::Atom(self_weight))),
                        combined,
                    );
                }
                if !matches!(combined, PathExpr::Zero) {
                    node_expr[v] = Some(combined);
                }
            }
        } else {
            // Multi-node SCC: compute internal loop body and star it.
            //
            // Strategy: pick one representative node (the one with smallest index)
            // as the SCC "header".  Compute the internal path expression within the
            // SCC that forms the loop body (header → ... → header), star it, then
            // compose with outgoing edges to exit.

            let scc_nodes: Vec<usize> = scc.iter().map(|n| n.0).collect();
            let scc_set: std::collections::HashSet<usize> = scc_nodes.iter().copied().collect();

            // Choose header as the node with the smallest index in the SCC.
            let header = *scc_nodes.iter().min().expect("SCC is non-empty");

            // Step 1: Eliminate non-header nodes within the SCC using
            // path expression algebra (analogous to Gaussian elimination).
            //
            // For each non-header node in the SCC, compute its contribution
            // as a "bypass" path and fold it into the remaining edges.
            //
            // We work with an edge-weight map that we progressively simplify.
            let mut local_edges: HashMap<(usize, usize), PathExpr<W>> = HashMap::new();

            for &from in &scc_nodes {
                for &(to, w) in &out_edges[from] {
                    // Include edges within the SCC and edges leaving the SCC.
                    local_edges
                        .entry((from, to))
                        .and_modify(|e| *e = PathExpr::alt(e.clone(), PathExpr::Atom(w)))
                        .or_insert(PathExpr::Atom(w));
                }
            }

            // Eliminate non-header SCC nodes one by one.
            for &elim in &scc_nodes {
                if elim == header {
                    continue;
                }

                // Compute self-loop star for the eliminated node.
                let self_star = if let Some(self_expr) = local_edges.remove(&(elim, elim)) {
                    PathExpr::star(self_expr)
                } else {
                    PathExpr::One
                };

                // Collect predecessors and successors of elim within local_edges.
                let preds: Vec<(usize, PathExpr<W>)> = local_edges
                    .iter()
                    .filter(|&(&(_, to), _)| to == elim)
                    .map(|(&(from, _), expr)| (from, expr.clone()))
                    .collect();

                let succs: Vec<(usize, PathExpr<W>)> = local_edges
                    .iter()
                    .filter(|&(&(from, _), _)| from == elim)
                    .map(|(&(_, to), expr)| (to, expr.clone()))
                    .collect();

                // For each (pred → elim) and (elim → succ), add bypass:
                // pred → succ with weight (pred→elim) ⊗ star(elim→elim) ⊗ (elim→succ)
                for &(pred, ref pred_expr) in &preds {
                    for &(succ, ref succ_expr) in &succs {
                        let bypass = PathExpr::seq(
                            pred_expr.clone(),
                            PathExpr::seq(self_star.clone(), succ_expr.clone()),
                        );
                        local_edges
                            .entry((pred, succ))
                            .and_modify(|e| *e = PathExpr::alt(e.clone(), bypass.clone()))
                            .or_insert(bypass);
                    }
                }

                // Remove all edges involving elim.
                local_edges.retain(|&(from, to), _| from != elim && to != elim);
            }

            // After elimination, only edges involving the header remain.
            // The header self-loop gives the SCC's loop body.
            let loop_star =
                if let Some(loop_body) = local_edges.remove(&(header, header)) {
                    PathExpr::star(loop_body)
                } else {
                    PathExpr::One
                };

            // Outgoing edges from the header to non-SCC nodes.
            let mut header_combined = PathExpr::Zero;
            for (&(from, to), expr) in &local_edges {
                if from == header && !scc_set.contains(&to) {
                    if let Some(ref to_expr) = node_expr[to] {
                        let path = PathExpr::seq(expr.clone(), to_expr.clone());
                        header_combined = PathExpr::alt(header_combined, path);
                    }
                }
            }

            // header's path expression = loop_star ⊗ (outgoing alternatives)
            let header_expr = PathExpr::seq(loop_star.clone(), header_combined);
            if !matches!(header_expr, PathExpr::Zero) {
                node_expr[header] = Some(header_expr);
            }

            // For non-header SCC nodes, compute their expression as:
            // (path from node to header within SCC) ⊗ header_expr
            // We can reconstruct this from the local_edges that remain.
            for &v in &scc_nodes {
                if v == header {
                    continue;
                }
                // The node was eliminated, but we can compute its expression
                // from its outgoing edges (which were already redirected).
                // Since we eliminated these nodes, their expressions come from
                // the outgoing edges we recorded before elimination.
                let mut v_combined = PathExpr::Zero;
                for &(to, w) in &out_edges[v] {
                    if let Some(ref to_expr) = node_expr[to] {
                        let path = PathExpr::seq(PathExpr::Atom(w), to_expr.clone());
                        v_combined = PathExpr::alt(v_combined, path);
                    }
                }
                // Apply any self-loop.
                if let Some(&self_w) = edge_map.get(&(v, v)) {
                    v_combined = PathExpr::seq(
                        PathExpr::Star(Box::new(PathExpr::Atom(self_w))),
                        v_combined,
                    );
                }
                if !matches!(v_combined, PathExpr::Zero) {
                    node_expr[v] = Some(v_combined);
                }
            }
        }
    }

    // Return the path expression for the entry node.
    node_expr[entry]
        .take()
        .unwrap_or(PathExpr::Zero)
}

// ==============================================================================
// evaluate: evaluate a path expression to a semiring value
// ==============================================================================

/// Evaluate a path expression to a single semiring value.
///
/// Recursively maps the path expression algebra to semiring operations:
/// - `Atom(w)` → `w`
/// - `Seq(a, b)` → `evaluate(a) ⊗ evaluate(b)`
/// - `Alt(a, b)` → `evaluate(a) ⊕ evaluate(b)`
/// - `Star(a)` → `star(evaluate(a))`
/// - `Zero` → `W::zero()`
/// - `One` → `W::one()`
///
/// Uses an explicit stack to avoid deep recursion.
pub fn evaluate<W: StarSemiring>(expr: &PathExpr<W>) -> W {
    // Iterative evaluation using an explicit work stack.
    // We use a post-order traversal: push children first, then combine.
    enum Op<'a, W: Semiring> {
        Eval(&'a PathExpr<W>),
        CombineSeq,
        CombineAlt,
        CombineStar,
    }

    let mut work: Vec<Op<'_, W>> = vec![Op::Eval(expr)];
    let mut value_stack: Vec<W> = Vec::new();

    while let Some(op) = work.pop() {
        match op {
            Op::Eval(e) => match e {
                PathExpr::Atom(w) => value_stack.push(*w),
                PathExpr::Zero => value_stack.push(W::zero()),
                PathExpr::One => value_stack.push(W::one()),
                PathExpr::Seq(a, b) => {
                    work.push(Op::CombineSeq);
                    // Push b first so a is evaluated first (stack is LIFO).
                    work.push(Op::Eval(b));
                    work.push(Op::Eval(a));
                }
                PathExpr::Alt(a, b) => {
                    work.push(Op::CombineAlt);
                    work.push(Op::Eval(b));
                    work.push(Op::Eval(a));
                }
                PathExpr::Star(inner) => {
                    work.push(Op::CombineStar);
                    work.push(Op::Eval(inner));
                }
            },
            Op::CombineSeq => {
                let b = value_stack.pop().expect("value stack underflow (Seq rhs)");
                let a = value_stack.pop().expect("value stack underflow (Seq lhs)");
                value_stack.push(a.times(&b));
            }
            Op::CombineAlt => {
                let b = value_stack.pop().expect("value stack underflow (Alt rhs)");
                let a = value_stack.pop().expect("value stack underflow (Alt lhs)");
                value_stack.push(a.plus(&b));
            }
            Op::CombineStar => {
                let a = value_stack.pop().expect("value stack underflow (Star)");
                value_stack.push(a.star());
            }
        }
    }

    value_stack
        .pop()
        .expect("value stack should contain exactly one result")
}

// ==============================================================================
// analyze: path expression + evaluate (convenience)
// ==============================================================================

/// Full algebraic analysis: build the path expression for the CFG and evaluate it.
///
/// Returns the semiring value summarizing all paths from `cfg.entry` to `cfg.exit`.
pub fn analyze<W: StarSemiring>(cfg: &ControlFlowGraph<W>) -> W {
    let expr = path_expression(cfg);
    evaluate(&expr)
}

// ==============================================================================
// all_pairs_analysis: matrix_star-based all-pairs summary
// ==============================================================================

/// All-pairs algebraic analysis using the generalized Floyd-Warshall algorithm
/// (`matrix_star`).
///
/// Returns a matrix `result[i][j]` giving the semiring summary of all paths
/// from node `i` to node `j`.  The diagonal `result[i][i]` includes the
/// reflexive closure (identity ⊕ loop paths).
///
/// This uses the existing `crate::automata::semiring::matrix_star` which
/// implements the Floyd-Warshall algorithm over any `StarSemiring`.
pub fn all_pairs_analysis<W: StarSemiring>(cfg: &ControlFlowGraph<W>) -> Vec<Vec<W>> {
    let n = cfg.nodes.len();

    // Build the adjacency matrix.  Parallel edges are combined with `plus`.
    let mut adj: Vec<Vec<W>> = Vec::with_capacity(n);
    for _ in 0..n {
        let row = vec![W::zero(); n];
        adj.push(row);
    }

    for edge in &cfg.edges {
        let i = edge.from.0;
        let j = edge.to.0;
        adj[i][j] = adj[i][j].plus(&edge.weight);
    }

    matrix_star(&adj)
}

// ==============================================================================
// Interprocedural extension
// ==============================================================================

/// A call edge in the interprocedural CFG.
///
/// Connects a caller procedure to a callee procedure with a weight
/// representing the abstract effect of the call/return mechanism.
///
/// Procedure indices refer to positions in `InterproceduralCfg::procedures`.
#[derive(Debug, Clone)]
pub struct CallEdge<W: Semiring> {
    /// Index of the calling procedure in the `procedures` vector.
    pub caller_proc: usize,
    /// Index of the callee procedure in the `procedures` vector.
    pub callee_proc: usize,
    /// Weight of the call (abstract effect of the call/return mechanism).
    pub call_weight: W,
}

/// An interprocedural control flow graph.
///
/// Each procedure has its own `ControlFlowGraph` with local node indices.
/// Call edges link procedures by their index in the `procedures` vector.
#[derive(Debug, Clone)]
pub struct InterproceduralCfg<W: Semiring> {
    /// Per-procedure CFGs, indexed by procedure ID.
    pub procedures: Vec<ControlFlowGraph<W>>,
    /// Call edges linking procedures by index.
    pub call_edges: Vec<CallEdge<W>>,
}

/// Interprocedural algebraic analysis.
///
/// Analyzes each procedure independently to compute its entry-to-exit summary,
/// then propagates summaries across call edges.  The result is a per-procedure
/// semiring value summarizing all paths through that procedure (including
/// transitive callees).
///
/// The algorithm:
/// 1. Compute intraprocedural summaries via `analyze()` for each procedure.
/// 2. Build the procedure-level call graph and decompose into SCCs.
/// 3. Process SCCs in reverse topological order (callees before callers).
/// 4. Within each SCC, iterate to a fixed point by composing call weights
///    with callee summaries.  For recursive SCCs, apply `star()`.
pub fn interprocedural_analyze<W: StarSemiring>(icfg: &InterproceduralCfg<W>) -> Vec<W> {
    let num_procs = icfg.procedures.len();
    if num_procs == 0 {
        return Vec::new();
    }

    // Step 1: Compute intraprocedural summaries.
    let mut summaries: Vec<W> = Vec::with_capacity(num_procs);
    for proc_cfg in &icfg.procedures {
        summaries.push(analyze(proc_cfg));
    }

    if icfg.call_edges.is_empty() {
        return summaries;
    }

    // Build call graph adjacency for SCC decomposition.
    let mut call_adj: Vec<Vec<usize>> = Vec::with_capacity(num_procs);
    for _ in 0..num_procs {
        call_adj.push(Vec::new());
    }

    for ce in &icfg.call_edges {
        debug_assert!(ce.caller_proc < num_procs, "caller_proc out of range");
        debug_assert!(ce.callee_proc < num_procs, "callee_proc out of range");
        call_adj[ce.caller_proc].push(ce.callee_proc);
    }

    // SCC decomposition of the call graph (iterative Tarjan).
    let call_sccs = {
        let n = num_procs;
        let mut index_counter: usize = 0;
        let mut stack: Vec<usize> = Vec::new();
        let mut on_stack = vec![false; n];
        let mut indices = vec![usize::MAX; n];
        let mut lowlinks = vec![0usize; n];
        let mut result: Vec<Vec<usize>> = Vec::new();

        struct Frame {
            node: usize,
            succ_idx: usize,
        }

        for start in 0..n {
            if indices[start] != usize::MAX {
                continue;
            }
            let mut work: Vec<Frame> = vec![Frame {
                node: start,
                succ_idx: 0,
            }];

            while let Some(frame) = work.last_mut() {
                let v = frame.node;
                if frame.succ_idx == 0 {
                    indices[v] = index_counter;
                    lowlinks[v] = index_counter;
                    index_counter += 1;
                    stack.push(v);
                    on_stack[v] = true;
                }

                let mut pushed = false;
                while frame.succ_idx < call_adj[v].len() {
                    let w = call_adj[v][frame.succ_idx];
                    if indices[w] == usize::MAX {
                        frame.succ_idx += 1;
                        work.push(Frame {
                            node: w,
                            succ_idx: 0,
                        });
                        pushed = true;
                        break;
                    } else if on_stack[w] {
                        lowlinks[v] = lowlinks[v].min(indices[w]);
                    }
                    frame.succ_idx += 1;
                }

                if pushed {
                    continue;
                }

                if lowlinks[v] == indices[v] {
                    let mut scc = Vec::new();
                    loop {
                        let w = stack.pop().expect("call graph SCC stack underflow");
                        on_stack[w] = false;
                        scc.push(w);
                        if w == v {
                            break;
                        }
                    }
                    result.push(scc);
                }

                let done = work.pop().expect("call graph work stack underflow").node;
                if let Some(parent) = work.last() {
                    lowlinks[parent.node] = lowlinks[parent.node].min(lowlinks[done]);
                }
            }
        }

        result
    };

    // Step 2: Process SCCs in reverse topological order (the SCC list from
    // Tarjan is already in reverse topological order: sinks/callees first).
    // For each SCC, iterate until convergence.
    let epsilon = 1e-10;
    let max_iterations = 100;

    for scc in &call_sccs {
        let scc_set: std::collections::HashSet<usize> = scc.iter().copied().collect();

        for _ in 0..max_iterations {
            let old_summaries: Vec<W> = scc.iter().map(|&p| summaries[p]).collect();

            for ce in &icfg.call_edges {
                if !scc_set.contains(&ce.caller_proc) {
                    continue;
                }

                // Compose: caller_summary ⊕= call_weight ⊗ callee_summary
                let callee_contribution = ce.call_weight.times(&summaries[ce.callee_proc]);
                summaries[ce.caller_proc] =
                    summaries[ce.caller_proc].plus(&callee_contribution);
            }

            // Check convergence.
            let converged = scc
                .iter()
                .zip(old_summaries.iter())
                .all(|(&p, old)| summaries[p].approx_eq(old, epsilon));

            if converged {
                break;
            }
        }

        // For recursive SCCs (size > 1 or self-recursive), apply star closure.
        if scc.len() > 1 {
            for &p in scc {
                summaries[p] = summaries[p].star();
            }
        } else if scc.len() == 1 {
            let p = scc[0];
            // Check for self-recursion.
            if call_adj[p].contains(&p) {
                summaries[p] = summaries[p].star();
            }
        }
    }

    summaries
}

// ==============================================================================
// Pipeline bridge
// ==============================================================================

/// Pipeline-level algebraic program analysis result.
#[derive(Debug, Clone)]
pub struct AlgebraicSummary {
    /// Number of SCCs in the call graph.
    pub scc_count: usize,
    /// Number of Tarjan path expressions computed.
    pub path_expression_count: usize,
    /// Summary descriptions per SCC.
    pub scc_summaries: Vec<String>,
}

/// Run algebraic program analysis from pipeline bundle data.
///
/// Uses the call graph SCCs from the WPDS analysis to count strongly connected
/// components and generate per-SCC summaries. Each SCC with more than one
/// category represents mutual recursion; single-category SCCs with self-edges
/// represent direct recursion. The path expression count is derived from the
/// number of non-trivial SCCs (those requiring Tarjan decomposition for
/// interprocedural summarization).
///
/// # Arguments
///
/// * `wpds_analysis` — WPDS analysis result containing the call graph and cycle
///   classification.
pub fn analyze_from_bundle(
    wpds_analysis: &crate::wpds::WpdsAnalysis,
) -> AlgebraicSummary {
    let sccs = &wpds_analysis.call_graph.sccs;
    let scc_count = sccs.len();

    // Count non-trivial SCCs (size > 1 or size == 1 with a cycle) as the
    // number of path expressions that Tarjan decomposition would produce.
    // A trivial SCC (single node, no self-loop) contributes no path expression.
    let cycles = &wpds_analysis.cycles;
    let path_expression_count = cycles.len();

    // Build a human-readable summary for each SCC.
    let mut scc_summaries = Vec::with_capacity(scc_count);
    for scc in sccs {
        if scc.len() == 1 {
            // Check if this single-category SCC is a direct recursion cycle.
            let cat = &scc[0];
            let is_recursive = cycles.iter().any(|c| {
                c.kind == crate::wpds::CycleKind::Direct
                    && c.categories.len() == 1
                    && c.categories[0] == *cat
            });
            if is_recursive {
                scc_summaries.push(format!(
                    "SCC [{}]: directly recursive",
                    cat,
                ));
            } else {
                scc_summaries.push(format!(
                    "SCC [{}]: non-recursive leaf",
                    cat,
                ));
            }
        } else {
            // Mutual recursion SCC.
            let members = scc.join(", ");
            let has_left_rec = cycles.iter().any(|c| {
                c.kind == crate::wpds::CycleKind::Mutual
                    && c.is_left_recursive
                    && c.categories == *scc
            });
            if has_left_rec {
                scc_summaries.push(format!(
                    "SCC [{}]: mutually recursive (left-recursive)",
                    members,
                ));
            } else {
                scc_summaries.push(format!(
                    "SCC [{}]: mutually recursive",
                    members,
                ));
            }
        }
    }

    AlgebraicSummary {
        scc_count,
        path_expression_count,
        scc_summaries,
    }
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::{BooleanWeight, TropicalWeight};

    // Helper: create a CFG from a list of (from, to, weight) triples.
    fn make_cfg<W: Semiring>(
        num_nodes: usize,
        edges: &[(usize, usize, W)],
        entry: usize,
        exit: usize,
    ) -> ControlFlowGraph<W> {
        let nodes: Vec<CfgNode> = (0..num_nodes).map(CfgNode).collect();
        let edges: Vec<CfgEdge<W>> = edges
            .iter()
            .map(|&(from, to, weight)| CfgEdge {
                from: CfgNode(from),
                to: CfgNode(to),
                weight,
            })
            .collect();
        ControlFlowGraph {
            nodes,
            edges,
            entry: CfgNode(entry),
            exit: CfgNode(exit),
        }
    }

    // ── Linear CFG tests ─────────────────────────────────────────────────

    #[test]
    fn linear_cfg_tropical() {
        // A(0) --3.0--> B(1) --2.0--> C(2)
        // Expected: 3.0 + 2.0 = 5.0 (tropical times = addition)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(3.0)),
                (1, 2, TropicalWeight::new(2.0)),
            ],
            0,
            2,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-10),
            "linear tropical: expected 5.0, got {:?}",
            result
        );
    }

    #[test]
    fn linear_cfg_boolean() {
        // A(0) --true--> B(1) --true--> C(2)
        // Expected: true && true = true (boolean times = AND)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, BooleanWeight::new(true)),
                (1, 2, BooleanWeight::new(true)),
            ],
            0,
            2,
        );

        let result = analyze(&cfg);
        assert_eq!(result, BooleanWeight::new(true), "linear boolean: reachable");
    }

    #[test]
    fn linear_cfg_boolean_unreachable() {
        // A(0) --false--> B(1) --true--> C(2)
        // Expected: false && true = false (unreachable)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, BooleanWeight::new(false)),
                (1, 2, BooleanWeight::new(true)),
            ],
            0,
            2,
        );

        let result = analyze(&cfg);
        assert_eq!(
            result,
            BooleanWeight::new(false),
            "linear boolean: unreachable"
        );
    }

    #[test]
    fn linear_cfg_path_expression() {
        // A(0) --w1--> B(1) --w2--> C(2)
        // Path expression should be Seq(Atom(w1), Atom(w2))
        let w1 = TropicalWeight::new(3.0);
        let w2 = TropicalWeight::new(2.0);
        let cfg = make_cfg(3, &[(0, 1, w1), (1, 2, w2)], 0, 2);

        let expr = path_expression(&cfg);
        let result = evaluate(&expr);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-10),
            "path expr evaluate: expected 5.0, got {:?}",
            result
        );
    }

    // ── Diamond CFG tests ────────────────────────────────────────────────

    #[test]
    fn diamond_cfg_tropical() {
        // A(0) --1.0--> B(1) --2.0--> D(3)
        // A(0) --3.0--> C(2) --1.0--> D(3)
        // Two paths: 1+2=3 and 3+1=4.  Tropical plus = min, so result = 3.0
        let cfg = make_cfg(
            4,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (0, 2, TropicalWeight::new(3.0)),
                (1, 3, TropicalWeight::new(2.0)),
                (2, 3, TropicalWeight::new(1.0)),
            ],
            0,
            3,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "diamond tropical: expected 3.0, got {:?}",
            result
        );
    }

    #[test]
    fn diamond_cfg_boolean() {
        // A(0) --true--> B(1) --true--> D(3)
        // A(0) --true--> C(2) --true--> D(3)
        // Boolean: true (reachable via both paths)
        let cfg = make_cfg(
            4,
            &[
                (0, 1, BooleanWeight::new(true)),
                (0, 2, BooleanWeight::new(true)),
                (1, 3, BooleanWeight::new(true)),
                (2, 3, BooleanWeight::new(true)),
            ],
            0,
            3,
        );

        let result = analyze(&cfg);
        assert_eq!(result, BooleanWeight::new(true), "diamond boolean: reachable");
    }

    #[test]
    fn diamond_cfg_one_path_blocked() {
        // A(0) --true--> B(1) --false--> D(3)
        // A(0) --true--> C(2) --true--> D(3)
        // Path A→B→D is blocked, A→C→D is not.  Boolean result = true.
        let cfg = make_cfg(
            4,
            &[
                (0, 1, BooleanWeight::new(true)),
                (0, 2, BooleanWeight::new(true)),
                (1, 3, BooleanWeight::new(false)),
                (2, 3, BooleanWeight::new(true)),
            ],
            0,
            3,
        );

        let result = analyze(&cfg);
        assert_eq!(
            result,
            BooleanWeight::new(true),
            "diamond one path blocked: still reachable via other path"
        );
    }

    // ── Loop CFG tests ───────────────────────────────────────────────────

    #[test]
    fn loop_cfg_tropical() {
        // A(0) --1.0--> B(1) --2.0--> A(0) (back edge)
        // A(0) --0.5--> C(2) (exit edge)
        //
        // Loop body cost = 1.0 + 2.0 = 3.0 (tropical times = add)
        // star(3.0) = 0.0 for tropical (non-negative weight → identity)
        // Result = star(loop_body) ⊗ exit_weight = 0.0 + 0.5 = 0.5
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 0, TropicalWeight::new(2.0)),
                (0, 2, TropicalWeight::new(0.5)),
            ],
            0,
            2,
        );

        let result = analyze(&cfg);
        // The shortest path is just taking the exit directly: cost 0.5
        // (the loop can be taken 0 times since star includes identity)
        assert!(
            result.approx_eq(&TropicalWeight::new(0.5), 1e-10),
            "loop tropical: expected 0.5, got {:?}",
            result
        );
    }

    #[test]
    fn loop_cfg_boolean() {
        // A(0) --true--> B(1) --true--> A(0) (back edge)
        // A(0) --true--> C(2) (exit)
        // Boolean: reachable (star(true) = true)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, BooleanWeight::new(true)),
                (1, 0, BooleanWeight::new(true)),
                (0, 2, BooleanWeight::new(true)),
            ],
            0,
            2,
        );

        let result = analyze(&cfg);
        assert_eq!(result, BooleanWeight::new(true), "loop boolean: reachable");
    }

    #[test]
    fn self_loop_tropical() {
        // A(0) --1.0--> A(0) (self-loop)
        // A(0) --2.0--> B(1) (exit)
        //
        // star(1.0) = 0.0 for tropical.  Result = 0.0 + 2.0 = 2.0
        let cfg = make_cfg(
            2,
            &[
                (0, 0, TropicalWeight::new(1.0)),
                (0, 1, TropicalWeight::new(2.0)),
            ],
            0,
            1,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(2.0), 1e-10),
            "self-loop tropical: expected 2.0, got {:?}",
            result
        );
    }

    // ── SCC decomposition tests ──────────────────────────────────────────

    #[test]
    fn scc_linear() {
        // A(0) --> B(1) --> C(2): three singleton SCCs
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 2, TropicalWeight::new(1.0)),
            ],
            0,
            2,
        );

        let sccs = tarjan_decompose(&cfg);
        assert_eq!(sccs.len(), 3, "linear: 3 singleton SCCs");
        for scc in &sccs {
            assert_eq!(scc.len(), 1, "each SCC is singleton");
        }
    }

    #[test]
    fn scc_cycle() {
        // A(0) --> B(1) --> A(0): one SCC of size 2, plus exit node C(2)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 0, TropicalWeight::new(1.0)),
                (0, 2, TropicalWeight::new(1.0)),
            ],
            0,
            2,
        );

        let sccs = tarjan_decompose(&cfg);
        let multi_sccs: Vec<_> = sccs.iter().filter(|s| s.len() > 1).collect();
        assert_eq!(multi_sccs.len(), 1, "one multi-node SCC");
        assert_eq!(multi_sccs[0].len(), 2, "SCC has 2 nodes");
    }

    #[test]
    fn scc_self_loop() {
        // Node 0 has a self-loop.  Still a singleton SCC (but with self-edge).
        let cfg = make_cfg(
            2,
            &[
                (0, 0, TropicalWeight::new(1.0)),
                (0, 1, TropicalWeight::new(1.0)),
            ],
            0,
            1,
        );

        let sccs = tarjan_decompose(&cfg);
        assert_eq!(sccs.len(), 2, "self-loop: 2 SCCs (both singleton)");
    }

    #[test]
    fn scc_diamond_no_cycle() {
        // Diamond: A→B, A→C, B→D, C→D — no cycle, 4 singleton SCCs
        let cfg = make_cfg(
            4,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (0, 2, TropicalWeight::new(1.0)),
                (1, 3, TropicalWeight::new(1.0)),
                (2, 3, TropicalWeight::new(1.0)),
            ],
            0,
            3,
        );

        let sccs = tarjan_decompose(&cfg);
        assert_eq!(sccs.len(), 4, "diamond: 4 singleton SCCs");
    }

    #[test]
    fn scc_two_cycles() {
        // Two disjoint cycles connected linearly:
        // 0 ↔ 1 → 2 ↔ 3 → 4 (exit)
        let cfg = make_cfg(
            5,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 0, TropicalWeight::new(1.0)),
                (1, 2, TropicalWeight::new(1.0)),
                (2, 3, TropicalWeight::new(1.0)),
                (3, 2, TropicalWeight::new(1.0)),
                (3, 4, TropicalWeight::new(1.0)),
            ],
            0,
            4,
        );

        let sccs = tarjan_decompose(&cfg);
        let multi_sccs: Vec<_> = sccs.iter().filter(|s| s.len() > 1).collect();
        assert_eq!(multi_sccs.len(), 2, "two multi-node SCCs");
    }

    // ── All-pairs analysis tests ─────────────────────────────────────────

    #[test]
    fn all_pairs_matches_matrix_star() {
        // Triangle: 0→1 (3.0), 1→2 (2.0), 0→2 (10.0)
        // All-pairs should match matrix_star on the adjacency matrix.
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(3.0)),
                (1, 2, TropicalWeight::new(2.0)),
                (0, 2, TropicalWeight::new(10.0)),
            ],
            0,
            2,
        );

        let result = all_pairs_analysis(&cfg);

        // Build adjacency matrix manually and compare.
        let adj = vec![
            vec![
                TropicalWeight::zero(),
                TropicalWeight::new(3.0),
                TropicalWeight::new(10.0),
            ],
            vec![
                TropicalWeight::zero(),
                TropicalWeight::zero(),
                TropicalWeight::new(2.0),
            ],
            vec![
                TropicalWeight::zero(),
                TropicalWeight::zero(),
                TropicalWeight::zero(),
            ],
        ];
        let expected = matrix_star(&adj);

        for i in 0..3 {
            for j in 0..3 {
                assert!(
                    result[i][j].approx_eq(&expected[i][j], 1e-10),
                    "all_pairs[{}][{}]: got {:?}, expected {:?}",
                    i,
                    j,
                    result[i][j],
                    expected[i][j]
                );
            }
        }
    }

    #[test]
    fn all_pairs_with_cycle() {
        // 0 → 1 (1.0), 1 → 0 (2.0), 0 → 2 (5.0)
        let cfg = make_cfg(
            3,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 0, TropicalWeight::new(2.0)),
                (0, 2, TropicalWeight::new(5.0)),
            ],
            0,
            2,
        );

        let result = all_pairs_analysis(&cfg);

        // 0→2: direct path costs 5.0, loop 0→1→0 has star = 0 (tropical),
        // so shortest path remains 5.0.
        assert!(
            result[0][2].approx_eq(&TropicalWeight::new(5.0), 1e-10),
            "all_pairs with cycle [0][2]: expected 5.0, got {:?}",
            result[0][2]
        );

        // 1→2: must go 1→0→2 = 2.0 + 5.0 = 7.0
        assert!(
            result[1][2].approx_eq(&TropicalWeight::new(7.0), 1e-10),
            "all_pairs with cycle [1][2]: expected 7.0, got {:?}",
            result[1][2]
        );
    }

    // ── Empty and edge-case CFG tests ────────────────────────────────────

    #[test]
    fn empty_cfg() {
        let cfg: ControlFlowGraph<TropicalWeight> = ControlFlowGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
            entry: CfgNode(0),
            exit: CfgNode(0),
        };

        // path_expression should handle n=0 gracefully.
        let expr = path_expression(&cfg);
        let result = evaluate(&expr);
        // Entry == exit → should be Zero since n=0 triggers early return.
        assert!(
            result.is_zero(),
            "empty cfg: expected zero, got {:?}",
            result
        );
    }

    #[test]
    fn single_node_entry_eq_exit() {
        // Single node that is both entry and exit.
        let cfg = make_cfg::<TropicalWeight>(1, &[], 0, 0);

        let result = analyze(&cfg);
        assert!(
            result.is_one(),
            "single node (entry=exit): expected one, got {:?}",
            result
        );
    }

    #[test]
    fn single_edge_cfg() {
        // Two nodes, one edge.
        let cfg = make_cfg(2, &[(0, 1, TropicalWeight::new(7.0))], 0, 1);

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(7.0), 1e-10),
            "single edge: expected 7.0, got {:?}",
            result
        );
    }

    #[test]
    fn disconnected_cfg() {
        // Entry and exit exist but are not connected.
        let cfg = make_cfg::<TropicalWeight>(3, &[(0, 1, TropicalWeight::new(1.0))], 0, 2);

        let result = analyze(&cfg);
        assert!(
            result.is_zero(),
            "disconnected: expected zero (unreachable), got {:?}",
            result
        );
    }

    #[test]
    fn parallel_edges() {
        // Two parallel edges from 0 to 1 with different weights.
        // Tropical: min(3.0, 5.0) = 3.0
        let cfg = make_cfg(
            2,
            &[
                (0, 1, TropicalWeight::new(3.0)),
                (0, 1, TropicalWeight::new(5.0)),
            ],
            0,
            1,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "parallel edges: expected 3.0 (min), got {:?}",
            result
        );
    }

    // ── Path expression structure tests ──────────────────────────────────

    #[test]
    fn path_expr_smart_constructors() {
        // Zero is annihilator for Seq.
        let z: PathExpr<TropicalWeight> = PathExpr::Zero;
        let a = PathExpr::Atom(TropicalWeight::new(1.0));
        let seq = PathExpr::seq(z, a);
        assert!(matches!(seq, PathExpr::Zero), "Zero ⊗ a = Zero");

        // One is identity for Seq.
        let o: PathExpr<TropicalWeight> = PathExpr::One;
        let a2 = PathExpr::Atom(TropicalWeight::new(2.0));
        let seq2 = PathExpr::seq(o, a2);
        assert!(matches!(seq2, PathExpr::Atom(_)), "One ⊗ a = a");

        // Zero is identity for Alt.
        let z2: PathExpr<TropicalWeight> = PathExpr::Zero;
        let a3 = PathExpr::Atom(TropicalWeight::new(3.0));
        let alt = PathExpr::alt(z2, a3);
        assert!(matches!(alt, PathExpr::Atom(_)), "Zero ⊕ a = a");

        // Star of Zero/One = One.
        let star_z = PathExpr::star(PathExpr::<TropicalWeight>::Zero);
        assert!(matches!(star_z, PathExpr::One), "star(Zero) = One");
        let star_o = PathExpr::star(PathExpr::<TropicalWeight>::One);
        assert!(matches!(star_o, PathExpr::One), "star(One) = One");
    }

    #[test]
    fn evaluate_atom() {
        let w = TropicalWeight::new(42.0);
        let expr = PathExpr::Atom(w);
        assert_eq!(evaluate(&expr), w);
    }

    #[test]
    fn evaluate_zero_one() {
        assert_eq!(
            evaluate(&PathExpr::<TropicalWeight>::Zero),
            TropicalWeight::zero()
        );
        assert_eq!(
            evaluate(&PathExpr::<TropicalWeight>::One),
            TropicalWeight::one()
        );
    }

    #[test]
    fn evaluate_nested() {
        // Alt(Seq(Atom(1), Atom(2)), Atom(5))
        // = Alt(1 ⊗ 2, 5) = Alt(3.0, 5.0) = min(3.0, 5.0) = 3.0
        let expr = PathExpr::Alt(
            Box::new(PathExpr::Seq(
                Box::new(PathExpr::Atom(TropicalWeight::new(1.0))),
                Box::new(PathExpr::Atom(TropicalWeight::new(2.0))),
            )),
            Box::new(PathExpr::Atom(TropicalWeight::new(5.0))),
        );

        let result = evaluate(&expr);
        assert!(
            result.approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "nested evaluate: expected 3.0, got {:?}",
            result
        );
    }

    #[test]
    fn evaluate_star() {
        // Star(Atom(2.0)) for tropical: star(2.0) = 0.0 (identity, since 2.0 >= 0)
        let expr = PathExpr::Star(Box::new(PathExpr::Atom(TropicalWeight::new(2.0))));
        let result = evaluate(&expr);
        assert!(
            result.approx_eq(&TropicalWeight::one(), 1e-10),
            "star(2.0) tropical: expected 0.0, got {:?}",
            result
        );
    }

    // ── Interprocedural analysis tests ───────────────────────────────────

    #[test]
    fn interprocedural_no_calls() {
        // Two independent procedures, no call edges.
        let proc0 = make_cfg(
            2,
            &[(0, 1, TropicalWeight::new(3.0))],
            0,
            1,
        );
        let proc1 = make_cfg(
            2,
            &[(0, 1, TropicalWeight::new(5.0))],
            0,
            1,
        );

        let icfg = InterproceduralCfg {
            procedures: vec![proc0, proc1],
            call_edges: Vec::new(),
        };

        let summaries = interprocedural_analyze(&icfg);
        assert_eq!(summaries.len(), 2);
        assert!(
            summaries[0].approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "proc0: expected 3.0, got {:?}",
            summaries[0]
        );
        assert!(
            summaries[1].approx_eq(&TropicalWeight::new(5.0), 1e-10),
            "proc1: expected 5.0, got {:?}",
            summaries[1]
        );
    }

    #[test]
    fn interprocedural_single_call() {
        // Proc 0 (idx=0): 0 → 1 with weight 2.0
        // Proc 1 (idx=1): 0 → 1 with weight 3.0
        // Call edge: proc 0 calls proc 1 with call_weight 1.0
        //
        // Proc 1 summary = 3.0
        // Proc 0 summary = intraprocedural(2.0) ⊕ (1.0 ⊗ 3.0) = min(2.0, 4.0) = 2.0

        let proc0 = make_cfg(
            2,
            &[(0, 1, TropicalWeight::new(2.0))],
            0,
            1,
        );
        let proc1 = make_cfg(
            2,
            &[(0, 1, TropicalWeight::new(3.0))],
            0,
            1,
        );

        let icfg = InterproceduralCfg {
            procedures: vec![proc0, proc1],
            call_edges: vec![CallEdge {
                caller_proc: 0,
                callee_proc: 1,
                call_weight: TropicalWeight::new(1.0),
            }],
        };

        let summaries = interprocedural_analyze(&icfg);
        assert_eq!(summaries.len(), 2);
        // Proc 1 is unchanged: 3.0
        assert!(
            summaries[1].approx_eq(&TropicalWeight::new(3.0), 1e-10),
            "proc1: expected 3.0, got {:?}",
            summaries[1]
        );
        // Proc 0: min(2.0, 1.0 + 3.0) = min(2.0, 4.0) = 2.0
        assert!(
            summaries[0].approx_eq(&TropicalWeight::new(2.0), 1e-10),
            "proc0: expected 2.0, got {:?}",
            summaries[0]
        );
    }

    #[test]
    fn interprocedural_empty() {
        let icfg: InterproceduralCfg<TropicalWeight> = InterproceduralCfg {
            procedures: Vec::new(),
            call_edges: Vec::new(),
        };
        let summaries = interprocedural_analyze(&icfg);
        assert!(summaries.is_empty(), "empty icfg: no summaries");
    }

    #[test]
    fn interprocedural_boolean_reachability() {
        // Proc 0: 0 → 1 (true)
        // Proc 1: 0 → 1 (true)
        // Call: proc 0 calls proc 1 with weight true
        let proc0 = make_cfg(
            2,
            &[(0, 1, BooleanWeight::new(true))],
            0,
            1,
        );
        let proc1 = make_cfg(
            2,
            &[(0, 1, BooleanWeight::new(true))],
            0,
            1,
        );

        let icfg = InterproceduralCfg {
            procedures: vec![proc0, proc1],
            call_edges: vec![CallEdge {
                caller_proc: 0,
                callee_proc: 1,
                call_weight: BooleanWeight::new(true),
            }],
        };

        let summaries = interprocedural_analyze(&icfg);
        assert_eq!(summaries[0], BooleanWeight::new(true));
        assert_eq!(summaries[1], BooleanWeight::new(true));
    }

    // ── build_cfg tests ──────────────────────────────────────────────────

    #[test]
    fn build_cfg_empty_wpds() {
        use crate::wpds::{StackSymbol, Wpds};

        let wpds: Wpds<TropicalWeight> = Wpds {
            stack_symbols: Vec::new(),
            symbol_index: HashMap::new(),
            rules: Vec::new(),
            rules_by_source: HashMap::new(),
            initial_symbol: StackSymbol::category_entry("Main"),
            grammar_name: "empty".to_string(),
        };

        let cfg = build_cfg(&wpds);
        assert_eq!(cfg.nodes.len(), 2, "empty wpds: entry + exit");
        assert!(cfg.edges.is_empty(), "empty wpds: no edges");
    }

    #[test]
    fn build_cfg_replace_rule() {
        use crate::wpds::{StackSymbol, Wpds};

        let s0 = StackSymbol::category_entry("Expr");
        let s1 = StackSymbol::rule_position("Expr", "Add", 1);
        let mut wpds: Wpds<TropicalWeight> = Wpds {
            stack_symbols: vec![s0.clone(), s1.clone()],
            symbol_index: HashMap::new(),
            rules: Vec::new(),
            rules_by_source: HashMap::new(),
            initial_symbol: s0.clone(),
            grammar_name: "test".to_string(),
        };
        wpds.symbol_index.insert(s0.clone(), 0);
        wpds.symbol_index.insert(s1.clone(), 1);
        wpds.rules.push(WpdsRule::Replace {
            from_gamma: s0,
            to_gamma: s1,
            weight: TropicalWeight::new(2.0),
        });

        let cfg = build_cfg(&wpds);
        // 2 stack symbols + 1 exit node = 3 nodes
        assert_eq!(cfg.nodes.len(), 3);
        // 1 Replace → 1 edge
        assert_eq!(cfg.edges.len(), 1);
        assert_eq!(cfg.edges[0].from, CfgNode(0));
        assert_eq!(cfg.edges[0].to, CfgNode(1));
        assert!(cfg.edges[0].weight.approx_eq(&TropicalWeight::new(2.0), 1e-10));
    }

    // ── Multi-node SCC with exit tests ───────────────────────────────────

    #[test]
    fn triangle_cycle_tropical() {
        // 0 → 1 → 2 → 0 (cycle), 0 → 3 (exit)
        // All edges weight 1.0
        // Loop body = 1+1+1 = 3.0 (tropical times = add), star(3.0) = 0.0
        // Result = star(3.0) ⊗ 1.0 = 0.0 + 1.0 = 1.0
        let cfg = make_cfg(
            4,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 2, TropicalWeight::new(1.0)),
                (2, 0, TropicalWeight::new(1.0)),
                (0, 3, TropicalWeight::new(1.0)),
            ],
            0,
            3,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(1.0), 1e-10),
            "triangle cycle: expected 1.0, got {:?}",
            result
        );
    }

    #[test]
    fn analyze_matches_all_pairs_entry_exit() {
        // Verify that `analyze(cfg)` matches `all_pairs_analysis(cfg)[entry][exit]`.
        let cfg = make_cfg(
            4,
            &[
                (0, 1, TropicalWeight::new(2.0)),
                (0, 2, TropicalWeight::new(5.0)),
                (1, 3, TropicalWeight::new(3.0)),
                (2, 3, TropicalWeight::new(1.0)),
            ],
            0,
            3,
        );

        let single = analyze(&cfg);
        let all = all_pairs_analysis(&cfg);

        assert!(
            single.approx_eq(&all[0][3], 1e-10),
            "analyze({:?}) should match all_pairs[0][3]({:?})",
            single,
            all[0][3]
        );
    }

    #[test]
    fn all_pairs_boolean_reachability() {
        // 0 → 1 (true), 1 → 2 (true), no 0→2 direct
        let cfg = make_cfg(
            3,
            &[
                (0, 1, BooleanWeight::new(true)),
                (1, 2, BooleanWeight::new(true)),
            ],
            0,
            2,
        );

        let result = all_pairs_analysis(&cfg);
        // 0 can reach 2 transitively.
        assert_eq!(
            result[0][2],
            BooleanWeight::new(true),
            "0→2 transitively reachable"
        );
        // 2 cannot reach 0.
        assert_eq!(
            result[2][0],
            BooleanWeight::new(false),
            "2→0 not reachable"
        );
    }

    // ── Longer chain test ────────────────────────────────────────────────

    #[test]
    fn long_chain_tropical() {
        // 0 → 1 → 2 → 3 → 4 → 5, each edge weight 1.0
        // Total cost = 5.0
        let cfg = make_cfg(
            6,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (1, 2, TropicalWeight::new(1.0)),
                (2, 3, TropicalWeight::new(1.0)),
                (3, 4, TropicalWeight::new(1.0)),
                (4, 5, TropicalWeight::new(1.0)),
            ],
            0,
            5,
        );

        let result = analyze(&cfg);
        assert!(
            result.approx_eq(&TropicalWeight::new(5.0), 1e-10),
            "long chain: expected 5.0, got {:?}",
            result
        );
    }

    #[test]
    fn nested_diamonds_tropical() {
        // Nested diamond: 0→1, 0→2, 1→3, 2→3, 3→4, 3→5, 4→6, 5→6
        // First diamond: min(1+1, 2+1) = 2, second diamond: min(1+1, 2+1) = 2
        // Total: 2 + 2 = 4
        let cfg = make_cfg(
            7,
            &[
                (0, 1, TropicalWeight::new(1.0)),
                (0, 2, TropicalWeight::new(2.0)),
                (1, 3, TropicalWeight::new(1.0)),
                (2, 3, TropicalWeight::new(1.0)),
                (3, 4, TropicalWeight::new(1.0)),
                (3, 5, TropicalWeight::new(2.0)),
                (4, 6, TropicalWeight::new(1.0)),
                (5, 6, TropicalWeight::new(1.0)),
            ],
            0,
            6,
        );

        let result = analyze(&cfg);
        // First diamond: path 0→1→3 = 2.0, path 0→2→3 = 3.0, min = 2.0
        // Second diamond: path 3→4→6 = 2.0, path 3→5→6 = 3.0, min = 2.0
        // Total: 2.0 + 2.0 = 4.0
        assert!(
            result.approx_eq(&TropicalWeight::new(4.0), 1e-10),
            "nested diamonds: expected 4.0, got {:?}",
            result
        );
    }

    fn make_empty_wpds_analysis() -> crate::wpds::WpdsAnalysis {
        use std::collections::{HashMap, HashSet};
        crate::wpds::WpdsAnalysis {
            grammar_name: "test".to_string(),
            num_symbols: 0,
            num_rules: 0,
            reachable_categories: HashSet::new(),
            unreachable_rules: Vec::new(),
            category_weights: HashMap::new(),
            call_graph: crate::wpds::WpdsCallGraph {
                edges: Vec::new(),
                fan_out: HashMap::new(),
                fan_in: HashMap::new(),
                sccs: Vec::new(),
                categories: HashSet::new(),
            },
            depth_bounds: HashMap::new(),
            cycles: Vec::new(),
            calling_contexts: HashMap::new(),
            context_rule_tables: HashMap::new(),
            cross_category_bp: HashMap::new(),
            context_unambiguous: HashMap::new(),
        }
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let wpds_analysis = make_empty_wpds_analysis();
        let summary = analyze_from_bundle(&wpds_analysis);
        assert_eq!(summary.scc_count, 0, "empty call graph should have 0 SCCs");
        assert_eq!(summary.path_expression_count, 0, "no cycles means no path expressions");
    }
}
