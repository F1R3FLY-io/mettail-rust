//! Token lattice for lexical ambiguity representation.
//!
//! Provides `TokenSource` — a tagged enum that represents either a flat token
//! array (the common case with **zero overhead**) or a weighted DAG (token
//! lattice) representing multiple possible tokenizations.
//!
//! ## Design invariants
//!
//! 1. **Zero-overhead linear path**: `TokenSource::Linear` is a transparent
//!    wrapper around `Vec<(Token, Range)>`. All access methods are `#[inline]`
//!    and compile to the same code as direct Vec access. Benchmarks must show
//!    < 1% difference vs raw Vec.
//!
//! 2. **Lattice-only when needed**: The `Lattice` variant is only constructed
//!    when the lexer detects actual lexical ambiguity (e.g., `>>` could be
//!    one token or two). In current PraTTaIL grammars, this never happens.
//!
//! ## Architecture
//!
//! ```text
//!            TokenSource
//!           /          \
//!    Linear(Vec)    Lattice(TokenLattice)
//!         |               |
//!    tokens[pos]     edges from pos
//!         |          (weighted DAG)
//!    O(1) access     Viterbi best path
//! ```
//!
//! ## Derived from lling-llang
//!
//! The `TokenLattice` design is inspired by `lling-llang/src/lattice/lattice.rs`,
//! adapted for PraTTaIL's zero-copy `Token<'a>` and `Range` types.

use std::fmt;

use crate::automata::semiring::TropicalWeight;

// ══════════════════════════════════════════════════════════════════════════════
// TokenSource — the primary abstraction
// ══════════════════════════════════════════════════════════════════════════════

/// A source of tokens for the parser: either a flat array or a weighted lattice.
///
/// The parser branches on variant at entry (once), not per-token. This ensures
/// the `Linear` path has zero overhead vs direct Vec access.
///
/// **Generic over token and span types** to work with both generated `Token<'a>`
/// and `Range` types that vary per grammar.
#[derive(Debug, Clone)]
pub enum TokenSource<T, S> {
    /// Unambiguous tokenization: flat array, zero overhead.
    ///
    /// This is the common case for all current PraTTaIL grammars.
    Linear(Vec<(T, S)>),

    /// Ambiguous tokenization: weighted DAG of possible token sequences.
    ///
    /// Each node is a position in the input; edges carry a token, span, and
    /// weight. Multiple edges from the same position represent alternative
    /// tokenizations at that point.
    Lattice(TokenLattice<T, S>),
}

impl<T, S> TokenSource<T, S> {
    /// Create a linear (unambiguous) token source from a token vector.
    ///
    /// This is the zero-overhead path: no allocation beyond the Vec itself.
    #[inline]
    pub fn linear(tokens: Vec<(T, S)>) -> Self {
        TokenSource::Linear(tokens)
    }

    /// Create an empty lattice token source with the given capacity hint.
    pub fn lattice(node_capacity: usize) -> Self {
        TokenSource::Lattice(TokenLattice::with_capacity(node_capacity))
    }

    /// Whether this is the linear (unambiguous) path.
    #[inline]
    pub fn is_linear(&self) -> bool {
        matches!(self, TokenSource::Linear(_))
    }

    /// Whether this is the lattice (ambiguous) path.
    #[inline]
    pub fn is_lattice(&self) -> bool {
        matches!(self, TokenSource::Lattice(_))
    }

    /// Get the number of tokens in the linear path, or nodes in the lattice.
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            TokenSource::Linear(tokens) => tokens.len(),
            TokenSource::Lattice(lattice) => lattice.num_nodes(),
        }
    }

    /// Whether the source is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Access a token at position `pos` in the linear path.
    ///
    /// For lattice sources, returns the first (lowest-weight) edge's token.
    /// Use `edges_from(pos)` for lattice access.
    #[inline]
    pub fn token_at(&self, pos: usize) -> Option<&(T, S)> {
        match self {
            TokenSource::Linear(tokens) => tokens.get(pos),
            TokenSource::Lattice(lattice) => {
                lattice.edges_from(pos).first().map(|edge| &edge.token_span)
            },
        }
    }

    /// Get the underlying linear token slice.
    ///
    /// Returns `None` if this is a lattice source.
    #[inline]
    pub fn as_linear(&self) -> Option<&[(T, S)]> {
        match self {
            TokenSource::Linear(tokens) => Some(tokens.as_slice()),
            TokenSource::Lattice(_) => None,
        }
    }
}

impl<T: Clone, S: Clone> TokenSource<T, S> {
    /// Construct a `TokenSource` from weighted 3-tuples `(token, span, weight)`.
    ///
    /// If all tokens are unambiguous (single tokenization), returns `Linear`
    /// with the weights stripped — **zero overhead** vs direct `Vec<(T, S)>`.
    ///
    /// This is the primary constructor for `lex_weighted()` output:
    /// ```text
    /// let weighted = lex_weighted(input)?;
    /// let source = TokenSource::from_weighted(weighted);
    /// let tokens = source.resolve()?;
    /// ```
    pub fn from_weighted(tokens: Vec<(T, S, f64)>) -> Self {
        let stripped: Vec<(T, S)> = tokens.into_iter().map(|(t, s, _w)| (t, s)).collect();
        TokenSource::Linear(stripped)
    }

    /// Resolve the token source into a flat `Vec<(T, S)>`.
    ///
    /// - **Linear**: returns the inner Vec directly — zero overhead.
    /// - **Lattice**: runs Viterbi best-path extraction and returns the
    ///   minimum-weight tokenization.
    ///
    /// Returns `Err` if the lattice is empty or the final node is unreachable.
    pub fn resolve(self) -> Result<Vec<(T, S)>, String> {
        match self {
            TokenSource::Linear(tokens) => Ok(tokens),
            TokenSource::Lattice(lattice) => {
                let final_node = if lattice.num_nodes() > 0 {
                    lattice.num_nodes() - 1
                } else {
                    return Err("empty token lattice: no tokens to resolve".to_string());
                };
                match viterbi_best_path(&lattice, final_node) {
                    Some(path) => Ok(path.tokens),
                    None => Err("token lattice: final node unreachable".to_string()),
                }
            },
        }
    }

    /// Resolve with beam pruning (for WFST-enabled paths).
    ///
    /// Same as `resolve()` but applies beam pruning during Viterbi extraction
    /// on the Lattice path. The Linear path ignores the beam parameter.
    pub fn resolve_beam(self, beam_width: Option<TropicalWeight>) -> Result<Vec<(T, S)>, String> {
        match self {
            TokenSource::Linear(tokens) => Ok(tokens),
            TokenSource::Lattice(lattice) => {
                let final_node = if lattice.num_nodes() > 0 {
                    lattice.num_nodes() - 1
                } else {
                    return Err("empty token lattice: no tokens to resolve".to_string());
                };
                match viterbi_best_path_beam(&lattice, final_node, beam_width) {
                    Some(path) => Ok(path.tokens),
                    None => Err("token lattice: final node unreachable (beam may be too narrow)"
                        .to_string()),
                }
            },
        }
    }
}

impl<T: fmt::Display, S: fmt::Display> fmt::Display for TokenSource<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenSource::Linear(tokens) => write!(f, "Linear({} tokens)", tokens.len()),
            TokenSource::Lattice(lattice) => {
                write!(f, "Lattice({} nodes, {} edges)", lattice.num_nodes(), lattice.num_edges(),)
            },
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TokenLattice — weighted DAG for ambiguous tokenization
// ══════════════════════════════════════════════════════════════════════════════

/// A weighted DAG representing multiple possible tokenizations.
///
/// Nodes correspond to positions in the input string. Edges carry a token,
/// a span, and a tropical weight. An edge from node `i` to node `j` means
/// "the input from position `i` to position `j` can be tokenized as this
/// token with this weight."
///
/// Multiple edges from the same node represent **lexical ambiguity**: the
/// input at that position could be tokenized in multiple ways.
///
/// ## Example
///
/// For the input `>>` with ambiguity (one `GtGt` or two `Gt`s):
///
/// ```text
///   Node 0 --GtGt(w=0.0)--> Node 2
///   Node 0 --Gt(w=1.0)--> Node 1 --Gt(w=1.0)--> Node 2
/// ```
///
/// The Viterbi path selects the minimum-weight path (0.0 < 1.0+1.0 = 2.0).
#[derive(Debug, Clone)]
pub struct TokenLattice<T, S> {
    /// Adjacency list: `edges[node_id]` = outgoing edges from that node.
    edges: Vec<Vec<LatticeEdge<T, S>>>,
}

/// An edge in the token lattice.
#[derive(Debug, Clone)]
pub struct LatticeEdge<T, S> {
    /// The token and span for this edge.
    pub token_span: (T, S),
    /// Target node (position after consuming this token).
    pub target: usize,
    /// Tropical weight for this tokenization choice.
    pub weight: TropicalWeight,
}

impl<T, S> TokenLattice<T, S> {
    /// Create a new empty lattice.
    pub fn new() -> Self {
        TokenLattice { edges: Vec::new() }
    }

    /// Create a new lattice with pre-allocated node capacity.
    pub fn with_capacity(node_capacity: usize) -> Self {
        TokenLattice { edges: Vec::with_capacity(node_capacity) }
    }

    /// Ensure the lattice has at least `node_count` nodes.
    pub fn ensure_nodes(&mut self, node_count: usize) {
        while self.edges.len() < node_count {
            self.edges.push(Vec::new());
        }
    }

    /// Add an edge from `from_node` to `to_node` with the given token/span/weight.
    pub fn add_edge(
        &mut self,
        from_node: usize,
        to_node: usize,
        token: T,
        span: S,
        weight: TropicalWeight,
    ) {
        self.ensure_nodes(to_node + 1);
        self.edges[from_node].push(LatticeEdge {
            token_span: (token, span),
            target: to_node,
            weight,
        });
    }

    /// Get edges leaving a node.
    #[inline]
    pub fn edges_from(&self, node: usize) -> &[LatticeEdge<T, S>] {
        self.edges.get(node).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Number of nodes in the lattice.
    #[inline]
    pub fn num_nodes(&self) -> usize {
        self.edges.len()
    }

    /// Total number of edges in the lattice.
    pub fn num_edges(&self) -> usize {
        self.edges.iter().map(|e| e.len()).sum()
    }

    /// Whether the lattice is empty (no nodes).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    /// Sort edges from each node by weight (lowest first).
    ///
    /// Call after construction to ensure `edges_from(pos)[0]` is always
    /// the lowest-weight (most likely) alternative.
    pub fn sort_edges_by_weight(&mut self) {
        for edges in &mut self.edges {
            edges.sort_by_key(|e| e.weight);
        }
    }
}

impl<T, S> Default for TokenLattice<T, S> {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Viterbi best-path extraction
// ══════════════════════════════════════════════════════════════════════════════

/// Result of Viterbi best-path extraction from a token lattice.
#[derive(Debug, Clone)]
pub struct ViterbiPath<T, S> {
    /// The tokens along the best path, in order.
    pub tokens: Vec<(T, S)>,
    /// Total path weight (sum of edge weights, tropical multiplication).
    pub total_weight: TropicalWeight,
}

/// Extract the minimum-weight (Viterbi) path through a token lattice.
///
/// Uses dynamic programming: for each node, find the predecessor edge that
/// minimizes the total path weight from node 0 to that node.
///
/// Returns `None` if the lattice is empty or the final node is unreachable.
pub fn viterbi_best_path<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,
    final_node: usize,
) -> Option<ViterbiPath<T, S>> {
    viterbi_best_path_beam(lattice, final_node, None)
}

/// Extract the minimum-weight path with optional beam pruning.
///
/// When `beam_width` is `Some(w)`, edges whose accumulated weight exceeds
/// `best_known_final + w` are pruned during the forward pass. The
/// `best_known_final` is updated as paths reach the final node, enabling
/// progressive tightening of the beam.
///
/// Returns `None` if the lattice is empty or the final node is unreachable.
pub fn viterbi_best_path_beam<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,
    final_node: usize,
    beam_width: Option<TropicalWeight>,
) -> Option<ViterbiPath<T, S>> {
    use crate::automata::semiring::Semiring;

    let n = lattice.num_nodes();
    if n == 0 || final_node >= n {
        return None;
    }

    // dist[i] = minimum total weight to reach node i from node 0
    let mut dist = vec![TropicalWeight::zero(); n]; // infinity
    dist[0] = TropicalWeight::one(); // zero cost to reach start

    // pred[i] = (predecessor_node, edge_index) on the best path
    let mut pred: Vec<Option<(usize, usize)>> = vec![None; n];

    // Track best known distance to final node (for beam pruning)
    let mut best_final = TropicalWeight::zero(); // infinity

    // Forward pass: process nodes in order (DAG property guarantees correctness)
    for node in 0..n {
        if dist[node].is_zero() {
            continue; // unreachable node
        }

        // Beam pruning: skip nodes that can't improve on best known final
        if let Some(beam) = beam_width {
            if !best_final.is_zero() && dist[node].value() > best_final.value() + beam.value() {
                continue;
            }
        }

        for (edge_idx, edge) in lattice.edges_from(node).iter().enumerate() {
            let new_dist = dist[node].times(&edge.weight);

            // Beam pruning: skip edges whose cost already exceeds threshold
            if let Some(beam) = beam_width {
                if !best_final.is_zero() && new_dist.value() > best_final.value() + beam.value() {
                    continue;
                }
            }

            if new_dist < dist[edge.target] {
                dist[edge.target] = new_dist;
                pred[edge.target] = Some((node, edge_idx));

                // Update best final if we reached the final node
                if edge.target == final_node && new_dist < best_final {
                    best_final = new_dist;
                }
            }
        }
    }

    // Check if final node is reachable
    if dist[final_node].is_zero() {
        return None; // unreachable
    }

    // Backtrace: reconstruct path from final_node to node 0
    let mut path_edges: Vec<(usize, usize)> = Vec::new(); // (node, edge_idx)
    let mut current = final_node;
    while let Some((prev_node, edge_idx)) = pred[current] {
        path_edges.push((prev_node, edge_idx));
        current = prev_node;
    }
    path_edges.reverse();

    // Extract tokens from path
    let tokens: Vec<(T, S)> = path_edges
        .iter()
        .map(|&(node, edge_idx)| {
            let edge = &lattice.edges_from(node)[edge_idx];
            edge.token_span.clone()
        })
        .collect();

    Some(ViterbiPath { tokens, total_weight: dist[final_node] })
}

// ══════════════════════════════════════════════════════════════════════════════
// Linear ↔ Lattice conversion
// ══════════════════════════════════════════════════════════════════════════════

/// Convert a linear token sequence to a lattice (for testing/composition).
///
/// Creates a chain lattice: node 0 → node 1 → ... → node N, with one edge
/// per token, all at weight 0.0 (tropical one).
pub fn linear_to_lattice<T, S>(tokens: Vec<(T, S)>) -> TokenLattice<T, S> {
    use crate::automata::semiring::Semiring;

    let n = tokens.len();
    let mut lattice = TokenLattice::with_capacity(n + 1);
    lattice.ensure_nodes(n + 1);

    for (i, (token, span)) in tokens.into_iter().enumerate() {
        lattice.add_edge(i, i + 1, token, span, TropicalWeight::one());
    }

    lattice
}

// ══════════════════════════════════════════════════════════════════════════════
// N-best path extraction (feature = "wfst-log")
// ══════════════════════════════════════════════════════════════════════════════

/// Extract the N shortest (minimum-weight) paths from a token lattice.
///
/// Uses a simple heap-based approach: run Viterbi once to find the best path,
/// then enumerate alternative paths by exploring edges not on the shortest
/// path tree.
///
/// This is a simplified version of Eppstein's algorithm suitable for
/// small-to-medium lattices (typical in parser recovery scenarios).
///
/// # Arguments
///
/// * `lattice` — The token lattice to search.
/// * `final_node` — The target/sink node.
/// * `n` — Maximum number of paths to return.
///
/// # Returns
///
/// Up to `n` paths sorted by total weight (ascending).
/// Returns empty vec if the final node is unreachable.
#[cfg(feature = "wfst-log")]
pub fn n_best_paths<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,
    final_node: usize,
    n: usize,
) -> Vec<ViterbiPath<T, S>> {
    use crate::automata::semiring::Semiring;
    use std::collections::BinaryHeap;

    if n == 0 || final_node >= lattice.num_nodes() {
        return Vec::new();
    }

    let num_nodes = lattice.num_nodes();

    // State: (total_weight, current_node, path_edges)
    // path_edges stores (from_node, edge_index) for backtrace
    #[derive(Clone)]
    struct SearchState {
        weight: TropicalWeight,
        node: usize,
        path: Vec<(usize, usize)>, // (from_node, edge_index)
    }

    impl PartialEq for SearchState {
        fn eq(&self, other: &Self) -> bool {
            self.weight == other.weight
        }
    }
    impl Eq for SearchState {}
    impl PartialOrd for SearchState {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for SearchState {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            // Reverse for min-heap
            other.weight.cmp(&self.weight)
        }
    }

    let mut heap: BinaryHeap<SearchState> = BinaryHeap::new();
    let mut results: Vec<ViterbiPath<T, S>> = Vec::with_capacity(n);
    let mut count_at_final = 0;

    // Start from node 0
    heap.push(SearchState {
        weight: TropicalWeight::one(),
        node: 0,
        path: Vec::new(),
    });

    // Limit total states explored to prevent explosion
    let max_explored = n * num_nodes * 4;
    let mut explored = 0;

    while let Some(state) = heap.pop() {
        explored += 1;
        if explored > max_explored {
            break;
        }

        if state.node == final_node {
            // Reconstruct path
            let mut tokens = Vec::with_capacity(state.path.len());
            for &(from_node, edge_idx) in &state.path {
                let edge = &lattice.edges_from(from_node)[edge_idx];
                tokens.push(edge.token_span.clone());
            }
            results.push(ViterbiPath { tokens, total_weight: state.weight });
            count_at_final += 1;
            if count_at_final >= n {
                break;
            }
            continue;
        }

        // Explore outgoing edges
        for (edge_idx, edge) in lattice.edges_from(state.node).iter().enumerate() {
            let new_weight = state.weight.times(&edge.weight);
            let mut new_path = state.path.clone();
            new_path.push((state.node, edge_idx));

            heap.push(SearchState {
                weight: new_weight,
                node: edge.target,
                path: new_path,
            });
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::Semiring;

    // Use simple types for testing (avoid dependency on generated Token/Range)
    type TestToken = String;
    type TestSpan = (usize, usize);

    #[test]
    fn test_token_source_linear_zero_overhead() {
        let tokens = vec![
            ("Plus".to_string(), (0, 1)),
            ("Integer".to_string(), (2, 3)),
            ("Eof".to_string(), (3, 3)),
        ];
        let source = TokenSource::linear(tokens);

        assert!(source.is_linear());
        assert!(!source.is_lattice());
        assert_eq!(source.len(), 3);
        assert!(!source.is_empty());

        // Direct access
        let first = source.token_at(0).expect("should have token at 0");
        assert_eq!(first.0, "Plus");
        assert_eq!(first.1, (0, 1));

        // Slice access
        let slice = source.as_linear().expect("should be linear");
        assert_eq!(slice.len(), 3);
    }

    #[test]
    fn test_token_source_lattice() {
        let source: TokenSource<TestToken, TestSpan> = TokenSource::lattice(5);
        assert!(source.is_lattice());
        assert!(!source.is_linear());
        assert!(source.as_linear().is_none());
    }

    #[test]
    fn test_token_lattice_basic() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // Simple chain: 0 --Plus--> 1 --Eof--> 2
        lattice.add_edge(0, 1, "Plus".to_string(), (0, 1), TropicalWeight::one());
        lattice.add_edge(1, 2, "Eof".to_string(), (1, 1), TropicalWeight::one());

        assert_eq!(lattice.num_nodes(), 3);
        assert_eq!(lattice.num_edges(), 2);
        assert_eq!(lattice.edges_from(0).len(), 1);
        assert_eq!(lattice.edges_from(1).len(), 1);
        assert_eq!(lattice.edges_from(2).len(), 0);
    }

    #[test]
    fn test_token_lattice_ambiguous() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // Ambiguity: ">>" can be one GtGt token or two Gt tokens
        // Path 1: 0 --GtGt(w=0.0)--> 2
        // Path 2: 0 --Gt(w=1.0)--> 1 --Gt(w=1.0)--> 2
        lattice.add_edge(0, 2, "GtGt".to_string(), (0, 2), TropicalWeight::new(0.0));
        lattice.add_edge(0, 1, "Gt".to_string(), (0, 1), TropicalWeight::new(1.0));
        lattice.add_edge(1, 2, "Gt".to_string(), (1, 2), TropicalWeight::new(1.0));

        assert_eq!(lattice.num_nodes(), 3);
        assert_eq!(lattice.num_edges(), 3);
        // Node 0 has two outgoing edges (ambiguous)
        assert_eq!(lattice.edges_from(0).len(), 2);
    }

    #[test]
    fn test_viterbi_best_path_chain() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // Simple chain: 0 --a(1.0)--> 1 --b(2.0)--> 2
        lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::new(1.0));
        lattice.add_edge(1, 2, "b".to_string(), (1, 2), TropicalWeight::new(2.0));

        let path = viterbi_best_path(&lattice, 2).expect("should find path");
        assert_eq!(path.tokens.len(), 2);
        assert_eq!(path.tokens[0].0, "a");
        assert_eq!(path.tokens[1].0, "b");
        // Total weight: 0.0 (start) + 1.0 + 2.0 = 3.0
        assert_eq!(path.total_weight, TropicalWeight::new(3.0));
    }

    #[test]
    fn test_viterbi_best_path_ambiguous() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // Path 1: 0 --GtGt(0.5)--> 2 (total = 0.5)
        // Path 2: 0 --Gt(1.0)--> 1 --Gt(1.0)--> 2 (total = 2.0)
        lattice.add_edge(0, 2, "GtGt".to_string(), (0, 2), TropicalWeight::new(0.5));
        lattice.add_edge(0, 1, "Gt".to_string(), (0, 1), TropicalWeight::new(1.0));
        lattice.add_edge(1, 2, "Gt".to_string(), (1, 2), TropicalWeight::new(1.0));

        let path = viterbi_best_path(&lattice, 2).expect("should find path");
        // Should pick path 1 (weight 0.5 < 2.0)
        assert_eq!(path.tokens.len(), 1);
        assert_eq!(path.tokens[0].0, "GtGt");
        assert_eq!(path.total_weight, TropicalWeight::new(0.5));
    }

    #[test]
    fn test_viterbi_empty_lattice() {
        let lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
        assert!(viterbi_best_path(&lattice, 0).is_none());
    }

    #[test]
    fn test_viterbi_unreachable_final() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
        lattice.ensure_nodes(3);
        // 0 → 1, but 2 is unreachable
        lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::one());

        assert!(viterbi_best_path(&lattice, 2).is_none());
    }

    #[test]
    fn test_linear_to_lattice() {
        let tokens = vec![("Plus".to_string(), (0, 1)), ("Integer".to_string(), (2, 3))];

        let lattice = linear_to_lattice(tokens);
        assert_eq!(lattice.num_nodes(), 3);
        assert_eq!(lattice.num_edges(), 2);

        // Viterbi should reconstruct the original sequence
        let path = viterbi_best_path(&lattice, 2).expect("should find path");
        assert_eq!(path.tokens.len(), 2);
        assert_eq!(path.tokens[0].0, "Plus");
        assert_eq!(path.tokens[1].0, "Integer");
        assert_eq!(path.total_weight, TropicalWeight::one()); // 0.0 + 0.0 = 0.0
    }

    #[test]
    fn test_viterbi_beam_prunes_edges() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // 3 paths from 0 to 3:
        // Path 1: 0 --a(0.5)--> 1 --b(0.5)--> 3  (total = 1.0, BEST)
        // Path 2: 0 --c(1.0)--> 2 --d(1.0)--> 3  (total = 2.0, within beam=1.5)
        // Path 3: 0 --e(5.0)--> 3               (total = 5.0, beyond beam=1.5)
        lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::new(0.5));
        lattice.add_edge(1, 3, "b".to_string(), (1, 2), TropicalWeight::new(0.5));
        lattice.add_edge(0, 2, "c".to_string(), (0, 1), TropicalWeight::new(1.0));
        lattice.add_edge(2, 3, "d".to_string(), (2, 3), TropicalWeight::new(1.0));
        lattice.add_edge(0, 3, "e".to_string(), (0, 3), TropicalWeight::new(5.0));

        // Without beam: best path is 1.0
        let path = viterbi_best_path(&lattice, 3).expect("should find path");
        assert_eq!(path.total_weight, TropicalWeight::new(1.0));

        // With beam=1.5: should still find path 1 (weight 1.0), beam prunes path 3
        let path_beam = viterbi_best_path_beam(&lattice, 3, Some(TropicalWeight::new(1.5)))
            .expect("should find path with beam");
        assert_eq!(path_beam.total_weight, TropicalWeight::new(1.0));
        assert_eq!(path_beam.tokens[0].0, "a");
    }

    #[test]
    fn test_sort_edges_by_weight() {
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();

        // Add edges out of order
        lattice.add_edge(0, 1, "b".to_string(), (0, 1), TropicalWeight::new(5.0));
        lattice.add_edge(0, 2, "a".to_string(), (0, 2), TropicalWeight::new(1.0));
        lattice.add_edge(0, 3, "c".to_string(), (0, 3), TropicalWeight::new(3.0));

        lattice.sort_edges_by_weight();

        let edges = lattice.edges_from(0);
        assert_eq!(edges[0].weight, TropicalWeight::new(1.0));
        assert_eq!(edges[1].weight, TropicalWeight::new(3.0));
        assert_eq!(edges[2].weight, TropicalWeight::new(5.0));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // TokenSource::from_weighted() and resolve() tests
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_from_weighted_strips_weights() {
        let weighted = vec![
            ("Plus".to_string(), (0, 1), 0.0),
            ("Integer".to_string(), (2, 3), 8.0),
            ("Eof".to_string(), (3, 3), 0.0),
        ];
        let source = TokenSource::from_weighted(weighted);

        assert!(source.is_linear(), "from_weighted should produce Linear");
        assert_eq!(source.len(), 3);

        let first = source.token_at(0).expect("should have token at 0");
        assert_eq!(first.0, "Plus");
        assert_eq!(first.1, (0, 1));
    }

    #[test]
    fn test_resolve_linear_zero_overhead() {
        let tokens = vec![
            ("Plus".to_string(), (0, 1)),
            ("Integer".to_string(), (2, 3)),
            ("Eof".to_string(), (3, 3)),
        ];
        let source = TokenSource::linear(tokens.clone());
        let resolved = source.resolve().expect("linear resolve should succeed");
        assert_eq!(resolved, tokens);
    }

    #[test]
    fn test_resolve_lattice_viterbi() {
        // Create a lattice with two paths:
        // Path 1: "GtGt" (weight 0.5) — shorter
        // Path 2: "Gt" + "Gt" (weight 1.0 + 1.0 = 2.0) — longer
        let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
        lattice.add_edge(0, 2, "GtGt".to_string(), (0, 2), TropicalWeight::new(0.5));
        lattice.add_edge(0, 1, "Gt".to_string(), (0, 1), TropicalWeight::new(1.0));
        lattice.add_edge(1, 2, "Gt".to_string(), (1, 2), TropicalWeight::new(1.0));
        // Add EOF at node 2 → 3
        lattice.add_edge(2, 3, "Eof".to_string(), (2, 2), TropicalWeight::new(0.0));

        let source: TokenSource<TestToken, TestSpan> = TokenSource::Lattice(lattice);
        let resolved = source.resolve().expect("lattice resolve should succeed");

        // Viterbi should pick GtGt path (0.5 < 2.0)
        assert_eq!(resolved.len(), 2); // "GtGt" + "Eof"
        assert_eq!(resolved[0].0, "GtGt");
        assert_eq!(resolved[1].0, "Eof");
    }

    #[test]
    fn test_resolve_empty_lattice_returns_error() {
        let source: TokenSource<TestToken, TestSpan> = TokenSource::lattice(0);
        // The lattice variant with 0 capacity starts empty
        // But let's create a truly empty lattice
        let source2: TokenSource<TestToken, TestSpan> = TokenSource::Lattice(TokenLattice::new());
        assert!(source2.resolve().is_err(), "empty lattice should fail to resolve");
    }

    #[test]
    fn test_resolve_beam_linear_ignores_beam() {
        let tokens = vec![("a".to_string(), (0, 1))];
        let source = TokenSource::linear(tokens.clone());
        let resolved = source
            .resolve_beam(Some(TropicalWeight::new(1.0)))
            .expect("linear resolve_beam should succeed");
        assert_eq!(resolved, tokens);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // N-best path extraction (feature = "wfst-log")
    // ═══════════════════════════════════════════════════════════════════════

    #[cfg(feature = "wfst-log")]
    mod n_best_tests {
        use super::super::*;
        use crate::automata::semiring::Semiring;

        type TestToken = String;
        type TestSpan = (usize, usize);

        #[test]
        fn test_n_best_single_path() {
            // Chain: 0 →(1.0)→ 1 →(2.0)→ 2
            let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
            lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::new(1.0));
            lattice.add_edge(1, 2, "b".to_string(), (1, 2), TropicalWeight::new(2.0));

            let paths = n_best_paths(&lattice, 2, 5);
            assert_eq!(paths.len(), 1, "only 1 path exists");
            assert_eq!(paths[0].total_weight, TropicalWeight::new(3.0));
            assert_eq!(paths[0].tokens.len(), 2);
        }

        #[test]
        fn test_n_best_diamond() {
            // Diamond: 0 →(1.0)→ 1 →(0.5)→ 3  (total 1.5)
            //          0 →(2.0)→ 2 →(1.0)→ 3  (total 3.0)
            let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
            lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::new(1.0));
            lattice.add_edge(1, 3, "b".to_string(), (1, 3), TropicalWeight::new(0.5));
            lattice.add_edge(0, 2, "c".to_string(), (0, 2), TropicalWeight::new(2.0));
            lattice.add_edge(2, 3, "d".to_string(), (2, 3), TropicalWeight::new(1.0));

            let paths = n_best_paths(&lattice, 3, 5);
            assert_eq!(paths.len(), 2, "should find both paths");

            // Ordered by weight: 1.5 first, 3.0 second
            assert_eq!(paths[0].total_weight, TropicalWeight::new(1.5));
            assert_eq!(paths[1].total_weight, TropicalWeight::new(3.0));
        }

        #[test]
        fn test_n_best_many_paths() {
            // 4 parallel paths with different weights
            let mut lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
            lattice.add_edge(0, 1, "a".to_string(), (0, 1), TropicalWeight::new(1.0));
            lattice.add_edge(0, 2, "b".to_string(), (0, 2), TropicalWeight::new(3.0));
            lattice.add_edge(0, 3, "c".to_string(), (0, 3), TropicalWeight::new(2.0));
            lattice.add_edge(0, 4, "d".to_string(), (0, 4), TropicalWeight::new(5.0));
            lattice.add_edge(1, 5, "x".to_string(), (1, 5), TropicalWeight::one());
            lattice.add_edge(2, 5, "x".to_string(), (2, 5), TropicalWeight::one());
            lattice.add_edge(3, 5, "x".to_string(), (3, 5), TropicalWeight::one());
            lattice.add_edge(4, 5, "x".to_string(), (4, 5), TropicalWeight::one());

            // Request top 3 of 4 paths
            let paths = n_best_paths(&lattice, 5, 3);
            assert_eq!(paths.len(), 3);

            // Should be ordered: 1.0, 2.0, 3.0
            assert_eq!(paths[0].total_weight, TropicalWeight::new(1.0));
            assert_eq!(paths[1].total_weight, TropicalWeight::new(2.0));
            assert_eq!(paths[2].total_weight, TropicalWeight::new(3.0));
        }

        #[test]
        fn test_n_best_unreachable() {
            let lattice: TokenLattice<TestToken, TestSpan> = TokenLattice::new();
            let paths = n_best_paths(&lattice, 5, 3);
            assert!(paths.is_empty());
        }
    }
}
