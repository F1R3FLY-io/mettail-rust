# Viterbi, Forward-Backward, and N-Best Paths

## 1. Motivation

The token lattice produced by the lexer is a weighted DAG: nodes are
positions in the input string; edges are weighted tokenization hypotheses
at each position. From this DAG the parser must extract:

- **The best single parse** — the minimum-weight path (Viterbi).
- **A beam of plausible parses** — the k paths within some weight
  budget of the best (beam-pruned Viterbi).
- **The partition function** — the total weight of all paths,
  needed for normalisation in weight training and computing posteriors
  (forward-backward).
- **The top-N alternative parses** — ranked alternative paths for
  error recovery and N-best output (N-best enumeration).

Each algorithm operates generically over any `Semiring`. Under
`TropicalWeight`, "total weight" means "minimum cost path." Under
`LogWeight`, "total weight" means "log of the sum of all path
probabilities."

---

## 2. Graph Model

### 2.1 Token Lattice as a DAG

A `TokenLattice<T, S>` stores an adjacency list:

```
edges[node_id] = [ LatticeEdge { token_span, target, weight }, … ]
```

Nodes are position indices (0, 1, …, N). An edge from node `u` to
node `v` with weight `w` asserts "the input from position u to position
v can be tokenised as the given token with weight w."

The structure is a **directed acyclic graph (DAG)** by construction:
each edge always moves forward in position (`target > source`).
This DAG property is critical — it guarantees that topological order
equals node-index order, eliminating the need for an explicit topological
sort and allowing all algorithms below to process nodes in index order.

### 2.2 Types

```rust
pub enum TokenSource<T, S> {
    Linear(Vec<(T, S)>),       // common case: unambiguous, zero overhead
    Lattice(TokenLattice<T, S>),
}

pub struct TokenLattice<T, S> {
    edges: Vec<Vec<LatticeEdge<T, S>>>,
}

pub struct LatticeEdge<T, S> {
    pub token_span: (T, S),
    pub target:     usize,
    pub weight:     TropicalWeight,
}

pub struct ViterbiPath<T, S> {
    pub tokens:       Vec<(T, S)>,
    pub total_weight: TropicalWeight,
}
```

---

## 3. Viterbi Algorithm

### 3.1 Definition

The **Viterbi algorithm** finds the minimum-weight path from the start
node (0) to the final node in a semiring-weighted DAG.

It is a direct application of dynamic programming:

```
α[0]   = 1̄              (zero cost / probability 1 at start)
α[v]   = ⊕  { α[u] ⊗ w(u,v) : (u,v) ∈ E }      (forward pass)
```

Under TropicalWeight, ⊕ = min and ⊗ = addition, so:

```
α[v]   = min { α[u] + w(u,v) : (u,v) ∈ E }
```

This is exactly the relaxation step of Dijkstra's algorithm, but because
the DAG property means α[u] is already finalised when we process node u,
we need no priority queue — a single left-to-right pass suffices.

### 3.2 Backtrace

Alongside α, the algorithm records the predecessor:

```
pred[v] = argmin_{(u,v) ∈ E} α[u] ⊗ w(u,v)
```

The best path is reconstructed by following `pred` pointers from
`final_node` back to node 0, then reversing.

### 3.3 Implementation

```rust
pub fn viterbi_best_path<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,
    final_node: usize,
) -> Option<ViterbiPath<T, S>> {
    // delegates to viterbi_best_path_beam with beam_width = None
}
```

`viterbi_best_path_beam` is the canonical implementation in `lattice.rs`.
It handles both the standard and beam-pruned cases:

```rust
// Forward pass
let mut dist = vec![TropicalWeight::zero(); n];  // +∞ for all nodes
dist[0] = TropicalWeight::one();                 //  0.0 for start

for node in 0..n {
    if dist[node].is_zero() { continue; }        // skip unreachable nodes
    // [beam check here — see §4]
    for (edge_idx, edge) in lattice.edges_from(node).iter().enumerate() {
        let new_dist = dist[node].times(&edge.weight);  // ⊗ = add
        if new_dist < dist[edge.target] {
            dist[edge.target] = new_dist;
            pred[edge.target] = Some((node, edge_idx));
        }
    }
}

// Backtrace
let mut path_edges: Vec<(usize, usize)> = Vec::new();
let mut current = final_node;
while let Some((prev_node, edge_idx)) = pred[current] {
    path_edges.push((prev_node, edge_idx));
    current = prev_node;
}
path_edges.reverse();
```

Time complexity: **O(V + E)** where V = nodes, E = edges.
Space complexity: **O(V)** for dist and pred arrays.

---

## 4. Beam-Pruned Viterbi

### 4.1 Motivation

For large lattices (e.g., during error recovery where many alternative
token sequences are considered), the standard Viterbi may visit many
nodes that cannot possibly contribute to a near-optimal solution.
Beam pruning skips these nodes early.

### 4.2 Algorithm

Maintain a `best_final` running estimate of the best known cost to reach
`final_node`. Whenever we find a new path to `final_node` with lower cost,
update `best_final`. Skip any node or edge whose accumulated cost exceeds
`best_final + beam_width`:

```
if best_final ≠ +∞  and  dist[node] > best_final + beam_width:
    continue   (skip this node entirely)

if best_final ≠ +∞  and  new_dist > best_final + beam_width:
    continue   (skip this specific edge)
```

The progressive update of `best_final` tightens the beam as the search
proceeds — early paths to the final node shrink the window for later nodes.

### 4.3 Correctness

Beam pruning is an **approximation**: it can discard the optimal path if
`beam_width` is too tight. It is guaranteed to return:

- At least one path (the best path is never pruned, because when it is
  first found it sets `best_final`, and its own cost equals `best_final`).
- The optimal path is returned when `beam_width ≥ 0` (trivially). For very
  small beam_width the approximation degrades gracefully.

Callers that need exact results should pass `beam_width = None`.

---

## 5. Forward Algorithm

### 5.1 Definition

The **forward algorithm** computes the total weight of all paths from
node 0 to each node v:

```
α[0]   = 1̄
α[v]   = ⊕_{(u,v) ∈ E}  α[u] ⊗ w(u,v)
```

Under TropicalWeight this is the same as Viterbi (picks the minimum-cost
path to each node). Under LogWeight, ⊕ = log-sum-exp, so α[v] accumulates
the total probability mass reaching node v from all paths.

### 5.2 Implementation

```rust
pub fn forward_scores<W: Semiring>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
) -> Vec<W> {
    let mut alpha = vec![W::zero(); num_nodes];
    alpha[0] = W::one();

    for node in 0..num_nodes {
        if alpha[node].is_zero() { continue; }
        for &(target, ref w) in &edges[node] {
            let contribution = alpha[node].times(w);
            alpha[target] = alpha[target].plus(&contribution);
        }
    }
    alpha
}
```

The function is generic over any `Semiring W`. Swapping
`TropicalWeight` for `LogWeight` changes the semantics from
"minimum-cost path" to "sum over all paths" — the code is identical.

---

## 6. Backward Algorithm

### 6.1 Definition

The **backward algorithm** computes the total weight of all paths from
each node u to the final node:

```
β[final]  = 1̄
β[u]      = ⊕_{(u,v) ∈ E}  w(u,v) ⊗ β[v]
```

Nodes are processed in **reverse** topological order (descending index).

### 6.2 Implementation

```rust
pub fn backward_scores<W: Semiring>(
    edges: &[Vec<(usize, W)>],
    num_nodes: usize,
    final_node: usize,
) -> Vec<W> {
    let mut beta = vec![W::zero(); num_nodes];
    beta[final_node] = W::one();

    for node in (0..num_nodes).rev() {
        for &(target, ref w) in &edges[node] {
            let contribution = w.times(&beta[target]);
            beta[node] = beta[node].plus(&contribution);
        }
    }
    beta
}
```

### 6.3 Forward-Backward Identity

For a correctly constructed DAG with a single sink node:

```
α[final_node] = β[0]
```

Both equal the **total weight** (partition function) of all accepting
paths. This identity is verified in `test_forward_backward_consistency`
and `test_forward_backward_consistency_log`.

`total_weight()` extracts the partition function from the forward scores:

```rust
pub fn total_weight<W: Semiring>(forward: &[W], final_node: usize) -> W {
    forward[final_node]
}
```

---

## 7. N-Best Path Enumeration

*Requires feature `wfst-log`.*

### 7.1 Definition

N-best extraction returns the N paths with the smallest total weight,
sorted ascending. It generalises Viterbi (N = 1) to ranked alternatives,
useful for:

- Presenting multiple repair suggestions to the user.
- Seeding the parser with alternative tokenisations when the best parse fails.
- Weight training via the N-best approximation of the lattice partition function.

### 7.2 Algorithm: Heap-Based Eppstein-Style Search

PraTTaIL uses a simplified heap-based approach suitable for
small-to-medium recovery lattices (typically 5–50 nodes):

```
heap ← min-heap, initialised with state (weight=1̄, node=0, path=[])

while heap not empty and |results| < n:
    (w, u, path) ← heap.pop_min()
    if u == final_node:
        results.push(ViterbiPath { tokens: path, total_weight: w })
    else:
        for each edge (u, v, w_e):
            heap.push( (w ⊗ w_e, v, path ++ [(u, edge_idx)]) )
```

The heap is a `BinaryHeap` with `Reverse` ordering for min-heap semantics.
`SearchState` implements `Ord` with the ordering reversed so the
lowest-weight state is popped first.

### 7.3 Safety Limit

To prevent combinatorial explosion on dense lattices:

```rust
let max_explored = n * num_nodes * 4;
let mut explored = 0;
while let Some(state) = heap.pop() {
    explored += 1;
    if explored > max_explored { break; }
    // ...
}
```

This limits exploration to `n × |nodes| × 4` state expansions. In the
worst case, this means each node is visited at most `n × 4` times per
requested path, ensuring the algorithm terminates in bounded time even
when the lattice has many cycles of equal weight.

### 7.4 Complexity

- Time: **O(max_explored × log(heap_size))** ≈ O(n·V·log(n·V))
- Space: **O(n·V)** for the heap and path copies

For the typical recovery scenario (n ≤ 10, V ≤ 50), this is well
within interactive latency budgets (~100 μs).

---

## 8. Worked Example: 6-Node Repair Lattice

Consider a 6-node repair lattice representing three alternative
token sequences generated during error recovery:

```
Nodes: 0 (start), 1, 2, 3, 4, 5 (final)

Edges:
  0 ──(1.0)──► 1 ──(2.0)──► 5    (path A, total = 3.0)
  0 ──(3.0)──► 2 ──(0.5)──► 5    (path B, total = 3.5)
  0 ──(1.5)──► 3 ──(1.0)──► 4 ──(0.5)──► 5  (path C, total = 3.0)
```

Drawn with crossing arcs annotated:

```
        w=1.0         w=2.0
  0 ────────────► 1 ────────────────────────────► 5
  │                                                ▲
  │   w=3.0                         w=0.5         │
  ├────────────► 2 ─────────────────────────────► │
  │              ┊                                 │
  │   w=1.5      ┊ w=1.0         w=0.5             │
  └────────────► 3 ──────────────► 4 ─────────────┘
                 ┊
           (crossing of
            0→2 and 0→3
            arcs at ┊)
```

### 8.1 Forward Scores (TropicalWeight)

Process nodes 0 → 5 in order:

| Node | Incoming edges | α[node] = min(predecessors) |
|:----:|:--------------|:----------------------------|
| 0    | (start)        | 0.0 (= 1̄)                   |
| 1    | 0→1 (0.0+1.0)  | 1.0                          |
| 2    | 0→2 (0.0+3.0)  | 3.0                          |
| 3    | 0→3 (0.0+1.5)  | 1.5                          |
| 4    | 3→4 (1.5+1.0)  | 2.5                          |
| 5    | 1→5 (1.0+2.0)=3.0, 2→5 (3.0+0.5)=3.5, 4→5 (2.5+0.5)=3.0 → **min=3.0** | 3.0 |

**Forward score at final node = 3.0.**

### 8.2 Backward Scores (TropicalWeight)

Process nodes 5 → 0 in reverse:

| Node | Outgoing edges | β[node] = min(successors) |
|:----:|:--------------|:--------------------------|
| 5    | (final)        | 0.0 (= 1̄)                 |
| 4    | 4→5 (0.5+0.0)  | 0.5                        |
| 3    | 3→4 (1.0+0.5)  | 1.5                        |
| 2    | 2→5 (0.5+0.0)  | 0.5                        |
| 1    | 1→5 (2.0+0.0)  | 2.0                        |
| 0    | 0→1 (1.0+2.0)=3.0, 0→2 (3.0+0.5)=3.5, 0→3 (1.5+1.5)=3.0 → **min=3.0** | 3.0 |

**Backward score at start node = 3.0.** ✓ Identity α[5] = β[0] = 3.0 holds.

### 8.3 Viterbi Best Path

The forward pass records predecessors:

```
pred[1] = (0, edge 0→1)
pred[2] = (0, edge 0→2)
pred[3] = (0, edge 0→3)
pred[4] = (3, edge 3→4)
pred[5] = (1, edge 1→5)     ← tied with (4, 4→5), (1, 1→5) selected first
```

Backtrace from node 5: 5 ← 1 ← 0.

**Best path: 0 → 1 → 5, tokens = [edge(0→1), edge(1→5)], total weight = 3.0.**

(Path C via nodes 3→4 also has weight 3.0 and would be found by N-best
with N ≥ 2, but Viterbi returns whichever tied path is encountered first
in iteration order.)

### 8.4 N-Best Paths (wfst-log, N=3)

With LogWeight, the three paths have weights 3.0, 3.5, and 3.0.
The heap-based N-best returns them in order:

| Rank | Path      | Weight |
|:----:|:----------|:------:|
| 1    | 0→1→5     | 3.0    |
| 2    | 0→3→4→5   | 3.0    |
| 3    | 0→2→5     | 3.5    |

Paths of equal weight are returned in heap-pop order (determined by
insertion order when weights are tied).

---

## 9. Test Coverage

**`lattice.rs` (20 tests across two modules):**

| Test | Algorithm | What it verifies |
|:-----|:---------|:----------------|
| `test_token_source_linear_zero_overhead` | — | Linear source access |
| `test_token_source_lattice` | — | Lattice source variant |
| `test_token_lattice_basic` | — | add_edge, num_nodes, num_edges |
| `test_token_lattice_ambiguous` | — | Multiple edges from same node |
| `test_viterbi_best_path_chain` | Viterbi | Chain lattice, weight accumulation |
| `test_viterbi_best_path_ambiguous` | Viterbi | Selects min-weight path |
| `test_viterbi_empty_lattice` | Viterbi | Returns None on empty lattice |
| `test_viterbi_unreachable_final` | Viterbi | Returns None when final unreachable |
| `test_linear_to_lattice` | Viterbi | Round-trip through chain lattice |
| `test_viterbi_beam_prunes_edges` | Beam Viterbi | Beam prunes high-cost path |
| `test_sort_edges_by_weight` | — | Sort by weight for greedy access |
| `n_best_tests::test_n_best_single_path` | N-best | Single path returned once |
| `n_best_tests::test_n_best_diamond` | N-best | Diamond graph, 2 paths ordered |
| `n_best_tests::test_n_best_many_paths` | N-best | Top 3 of 4 paths returned |
| `n_best_tests::test_n_best_unreachable` | N-best | Empty on unreachable lattice |

**`forward_backward.rs` (7 tests):**

| Test | Algorithm | What it verifies |
|:-----|:---------|:----------------|
| `test_forward_scores_chain` | Forward | Chain: α[1]=2.0, α[2]=5.0 |
| `test_backward_scores_chain` | Backward | Chain: β[1]=3.0, β[0]=5.0 |
| `test_forward_scores_diamond` | Forward | Diamond: min(3.0, 4.0)=3.0 |
| `test_forward_backward_consistency` | Both | α[final] = β[start] |
| `test_forward_with_tropical` | Forward | Triangle: via 1 beats direct |
| `log_tests::test_forward_scores_diamond_log` | Forward (Log) | Log sum-over-paths |
| `log_tests::test_forward_backward_consistency_log` | Both (Log) | Identity under LogWeight |

---

## 10. Source Reference

| Symbol | Location |
|:-------|:---------|
| `TokenSource<T,S>` | `prattail/src/lattice.rs` lines 51–131 |
| `TokenLattice<T,S>` | `prattail/src/lattice.rs` lines 174–262 |
| `LatticeEdge<T,S>` | `prattail/src/lattice.rs` lines 181–188 |
| `ViterbiPath<T,S>` | `prattail/src/lattice.rs` lines 276–281 |
| `viterbi_best_path` | `prattail/src/lattice.rs` lines 289–294 |
| `viterbi_best_path_beam` | `prattail/src/lattice.rs` lines 304–390 |
| `linear_to_lattice` | `prattail/src/lattice.rs` lines 400–413 |
| `n_best_paths` (wfst-log) | `prattail/src/lattice.rs` lines 440–535 |
| `forward_scores` | `prattail/src/forward_backward.rs` lines 33–51 |
| `backward_scores` | `prattail/src/forward_backward.rs` lines 67–83 |
| `total_weight` | `prattail/src/forward_backward.rs` lines 88–91 |

---

**See also:**
- [`semirings.md`](semirings.md) — semiring axioms and the ⊕/⊗ operations used here
- [`weighted-automata.md`](weighted-automata.md) — WFST structure that produces the prediction weights fed into these algorithms
