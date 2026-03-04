# Viterbi, Forward-Backward, and N-Best Paths

## 1. Motivation

The token lattice produced by the lexer is a weighted DAG: nodes are
positions in the input string; edges are weighted tokenization hypotheses
at each position. From this DAG the parser must extract:

- **The best single parse** — the minimum-weight path (Viterbi).
  Viterbi is always available (not feature-gated).
- **A beam of plausible parses** — the k paths within some weight
  budget of the best (beam-pruned Viterbi).
- **The partition function** — the total weight of all paths,
  needed for normalisation in weight training and computing posteriors
  (forward-backward). *Requires feature `wfst-log`.*
- **The top-N alternative parses** — ranked alternative paths for
  error recovery and N-best output (N-best enumeration).
  *Requires feature `wfst-log`.*

Each algorithm operates generically over any `Semiring`. Under
`TropicalWeight`, "total weight" means "minimum cost path." Under
`LogWeight`, "total weight" means "log of the sum of all path
probabilities."

---

## 1.5 What Is Viterbi, Intuitively?

### The GPS Navigation Analogy

Viterbi is the algorithm your GPS uses. Given a road network (the
lattice) where each road segment has a travel time (the weight), Viterbi
finds the fastest route from start to destination. The lattice is the
map; edges are road segments; weights are travel times. The algorithm
sweeps left-to-right across the map, computing the fastest arrival time
at each intersection by examining all incoming roads.

Once the sweep reaches the destination, the algorithm traces back
through the recorded "came from" pointers to reconstruct the route — no
exhaustive enumeration of all possible routes is needed.

### Why Greedy Fails — A Concrete Counterexample

A greedy approach picks the cheapest token at each position without
considering downstream consequences. This can misidentify the correct
tokenization:

```
Input: ">>="

Greedy (pick cheapest token at each position):
  Position 0: GtGt (w=0.0) looks best → consumes ">>"
  Position 2: Eq (w=0.0) → consumes "="
  Result: [GtGt, Eq] — right-shift followed by equality
  But the programmer wrote >>= (ShrAssign)!

Viterbi evaluates ALL paths simultaneously:
  Path A: ShrAssign(0.0)              = 0.0  ← winner
  Path B: GtGt(0.0) + Eq(0.0)        = 0.0  (tie, but fewer tokens)
  Path C: Gt(1.0) + GtEq(0.5)        = 1.5
  Path D: Gt(1.0) + Gt(1.0) + Eq(0.0) = 2.0
```

Greedy cannot distinguish Path A from Path B because it commits to
`GtGt` before seeing `=`. Viterbi defers commitment until all paths are
scored end-to-end.

### The Wavefront Mental Model

Viterbi sweeps a "wavefront" left-to-right through the lattice. At each
position, it computes the best arrival cost by checking all incoming
edges. Once a position is processed, its cost is final — the wavefront
never revisits earlier positions.

```
Step 0:   Step 1:   Step 2:   Step 3:   Step 4:
▓░░░░     ▓▓░░░     ▓▓▓░░     ▓▓▓▓░     ▓▓▓▓▓
0 1 2 3 4 0 1 2 3 4 0 1 2 3 4 0 1 2 3 4 0 1 2 3 4
^           ^           ^           ^           ^
α[0]=0.0  α[1]=best  α[2]=best  α[3]=best  α[4]=best
            of all     of all     of all     of all
            incoming   incoming   incoming   incoming
            edges      edges      edges      edges

▓ = finalized (cost is final)    ░ = pending
```

This left-to-right single-pass property comes from the DAG constraint:
every edge moves forward in position, so when we process position *v*,
every predecessor *u* < *v* has already been finalized.

---

## 1.7 Where Viterbi Sits in the PraTTaIL Pipeline

Viterbi appears at two runtime points and is supported by several
compile-time analyses:

```
COMPILE TIME                             RUNTIME
════════════                             ═══════
LanguageSpec                             input: &str
     │                                        │
     ▼                                        ▼
run_pipeline()                           lex_weighted()
     │                                        │
     ├── FIRST/FOLLOW                         ▼
     ├── PredictionWfst              Vec<(Token, Range, f64)>
     ├── Dead-rule detection                  │
     │   (BooleanWeight)                      ▼
     ├── Ambiguity warnings          TokenSource::from_weighted()
     │   (CountingWeight)                     │
     ▼                                  ┌─────┴─────┐
Generated code                     Linear         Lattice
                                   (99%)         (ambiguous)
                                     │                │
                                  identity       ╔════╧════╗
                                     │           ║ VITERBI ║ ◄── HERE
                                     ▼           ╚════╤════╝
                                  parse_Cat()         │
                                     │                ▼
                                     │           parse_Cat()
                                     └──────┬────────┘
                                            │
                                       On error:
                                  ╔═════════╧══════════╗
                                  ║  viterbi_multi_    ║ ◄── AND HERE
                                  ║  step() on repair  ║
                                  ║  lattice           ║
                                  ╚════════════════════╝
```

**First Viterbi point (lexer → parser):** When the lexer detects lexical
ambiguity (multiple valid tokenizations at a position), it constructs a
`TokenLattice`. Viterbi extracts the minimum-weight tokenization before
parsing begins.

**Second Viterbi point (error recovery):** When the parser encounters a
syntax error, `viterbi_multi_step()` builds an implicit repair lattice
over skip/delete/insert/substitute/swap actions and finds the
minimum-cost repair sequence.

**Forward-backward (feature `wfst-log`):** Appears at a third point —
computing arc posteriors for weight training. This requires the LogWeight
semiring and is not part of the default parsing flow.

---

## 2. Graph Model

### 2.1 Token Lattice as a DAG

A `TokenLattice<T, S, W>` stores an adjacency list:

```
edges[node_id] = [ LatticeEdge { token_span, target, weight }, … ]
```

Nodes are position indices (0, 1, ..., N). An edge from node `u` to
node `v` with weight `w` asserts "the input from position u to position
v can be tokenised as the given token with weight w."

The structure is a **directed acyclic graph (DAG)** by construction:
each edge always moves forward in position (`target > source`).
This DAG property is critical — it guarantees that topological order
equals node-index order, eliminating the need for an explicit topological
sort and allowing all algorithms below to process nodes in index order.

### 2.2 Types

The lattice types are generic over the weight type `W`, defaulting to
`TropicalWeight`:

```rust
pub enum TokenSource<T, S> {
    Linear(Vec<(T, S)>),       // common case: unambiguous, zero overhead
    Lattice(TokenLattice<T, S>),
}

pub struct TokenLattice<T, S, W = TropicalWeight> {
    edges: Vec<Vec<LatticeEdge<T, S, W>>>,
}

pub struct LatticeEdge<T, S, W = TropicalWeight> {
    pub token_span: (T, S),
    pub target:     usize,
    pub weight:     W,
}

pub struct ViterbiPath<T, S, W = TropicalWeight> {
    pub tokens:       Vec<(T, S)>,
    pub total_weight: W,
}
```

The generic parameter `W` allows the same lattice infrastructure to be
used with any of PraTTaIL's ten semiring types: TropicalWeight,
CountingWeight, BooleanWeight, EditWeight, ProductWeight, LogWeight,
ContextWeight, ComplexityWeight, EntropyWeight, and NbestWeight.

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

### 3.4 Generic Viterbi

`viterbi_generic<W: Semiring + Ord>()` provides generic lattice path
extraction for any semiring that implements `Ord`. This enables Viterbi
over non-tropical lattices (e.g., EditWeight lattices for minimum-edit
path extraction, or ProductWeight lattices for multi-objective
optimization).

#### When to Use Generic Viterbi

The tropical specialization `viterbi_best_path_beam()` handles the
common case (all current grammars). Use `viterbi_generic()` when:

- **EditWeight:** Finding the minimum-edit repair path (repair lattices
  where each edge is a token-level edit operation).
- **ComplexityWeight:** Finding the least-complex derivation path (where
  complexity measures rule nesting depth or grammar recursion).
- **ProductWeight⟨T, E⟩:** Multi-objective optimization where you want
  to minimize tropical cost first, then break ties by edit distance (or
  any other secondary semiring).

#### Viterbi Compatibility Invariant

Generic Viterbi requires one critical invariant:

> **`W::zero()` must be the largest element under `Ord`.**

This ensures that unvisited nodes (initialized to `zero()`) compare as
"worse than any reachable distance," so the `new_dist < dist[target]`
comparison correctly identifies improvements. Without this invariant,
`zero()` could appear to be a valid (even optimal) distance, and the
algorithm would fail to distinguish "unreachable" from "has weight
zero()."

#### Viterbi Compatibility Table

| Semiring            |            Viterbi-Compatible?            | Reason                                                 |
|:--------------------|:-----------------------------------------:|:-------------------------------------------------------|
| TropicalWeight      |             Yes (specialized)             | `zero()` = +∞ is largest under Ord                     |
| EditWeight          |               Yes (generic)               | `zero()` = u32::MAX is largest                         |
| ComplexityWeight    |               Yes (generic)               | `zero()` = u32::MAX is largest                         |
| ProductWeight⟨T, E⟩ |               Yes (generic)               | Lexicographic; +∞ first                                |
| NbestWeight⟨N⟩      |              Not standalone               | Use via ProductWeight or dedicated N-best              |
| CountingWeight      |                  **No**                   | `zero()` = 0 is _smallest_ — breaks Viterbi invariant  |
| BooleanWeight       |           **No** (meaningless)            | Only two values; min always yields `false`             |
| ContextWeight       |            **No** (set-valued)            | Not totally ordered                                    |
| LogWeight           | Technically yes, but use forward-backward | `zero()` = +∞ is largest, but sum semantics are needed |
| EntropyWeight       |                  **No**                   | Expectation semiring; not path-valued                  |

#### Why CountingWeight Breaks Viterbi

CountingWeight counts the number of derivation paths. Its semiring
operations are ⊕ = addition (combine path counts) and ⊗ = multiplication
(sequence path counts). Critically, `zero() = 0` is the _smallest_
element under natural ordering, not the largest. This means:

- All nodes are initialized to `dist[v] = 0` (CountingWeight::zero()).
- When a real path arrives with weight > 0, the comparison
  `new_dist < dist[target]` evaluates to `false` (since any positive
  count > 0 = zero), so the relaxation never fires.
- The algorithm returns `dist[final] = 0` regardless of input.

CountingWeight should instead be used via forward-backward (to count all
paths) or via `ProductWeight<TropicalWeight, CountingWeight>` (to count
paths to the optimal solution).

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
- The optimal path is returned when `beam_width >= 0` (trivially). For very
  small beam_width the approximation degrades gracefully.

Callers that need exact results should pass `beam_width = None`.

### 4.4 Beam Pruning Walkthrough

Step-by-step walkthrough using the 6-node lattice from §8, with
`beam_width = 1.0`:

```
Forward pass with beam_width = 1.0:

Before any path reaches node 5: α_best_final = +∞ → no pruning

  Process node 0: α[0] = 0.0
    Relax: 0→1 (0.0+1.0=1.0), 0→2 (0.0+3.0=3.0), 0→3 (0.0+1.5=1.5)
    α = [0.0, 1.0, 3.0, 1.5, ∞, ∞]

  Process node 1: α[1] = 1.0
    Relax: 1→5 (1.0+2.0=3.0)
    α = [0.0, 1.0, 3.0, 1.5, ∞, 3.0]

    Path 0→1→5 reaches node 5: α_best_final = 3.0
    Beam ceiling = 3.0 + 1.0 = 4.0

  Process node 2: α[2] = 3.0
    3.0 ≤ 4.0  ✓ not pruned
    Relax: 2→5 (3.0+0.5=3.5)
    3.5 ≤ 4.0  ✓ edge accepted
    But 3.5 > 3.0 (existing α[5]), so no update.

  Process node 3: α[3] = 1.5
    1.5 ≤ 4.0  ✓ not pruned
    Relax: 3→4 (1.5+1.0=2.5)
    α = [0.0, 1.0, 3.0, 1.5, 2.5, 3.0]

  Process node 4: α[4] = 2.5
    2.5 ≤ 4.0  ✓ not pruned
    Relax: 4→5 (2.5+0.5=3.0)
    3.0 = α[5], tie → no update.

Final: α[5] = 3.0 (same as exact Viterbi)
```

Now suppose node 2 had cost 4.5 instead of 3.0:

```
  Process node 2: α[2] = 4.5
    4.5 > 4.0 (beam ceiling)  ✗ PRUNED — skip node 2 entirely
    All edges from node 2 are never examined.
```

The pruning correctly skips suboptimal nodes without affecting the
optimal path (which runs through nodes 0→1→5 or 0→3→4→5).

---

## 5. Forward Algorithm

### Intuition: Probability Flow

Before diving into the formal definitions, here is the key mental model
for forward-backward.

**Probability-flow analogy.** Imagine pouring water into the lattice at
node 0. The water splits at each branching point proportional to edge
weights and recombines at merging points. The forward algorithm measures
how much water reaches each node from the start. The backward algorithm
measures how much water would need to flow from each node to reach the
end. Together, they reveal what fraction of the total water flow passes
through each individual edge — that is the **arc posterior**.

**Why you need forward-backward.** Viterbi tells you the single best
path. But when training weights, you need to know: "if I increase this
edge's weight by ε, how much does the total path probability change?"
Forward-backward answers this by computing the marginal contribution of
each edge across _all_ paths simultaneously.

#### Worked Example: Forward-Backward under LogWeight

Consider the 3-node `>>` lattice with edges:

```
Edge A: 0→2 GtGt (w=0.0)
Edge B: 0→1 Gt   (w=1.0)
Edge C: 1→2 Gt   (w=1.0)
```

Under LogWeight (⊕ = log-sum-exp, ⊗ = addition):

```
Forward:
  α[0] = 0.0                                         (log-probability 1)
  α[1] = α[0] ⊗ w(B) = 0.0 + 1.0 = 1.0
  α[2] = logsumexp(α[0] ⊗ w(A), α[1] ⊗ w(C))
       = logsumexp(0.0 + 0.0, 1.0 + 1.0)
       = logsumexp(0.0, 2.0)
       = 0.0 + ln(1 + e⁻²) ≈ 0.127

Backward:
  β[2] = 0.0
  β[1] = w(C) ⊗ β[2] = 1.0 + 0.0 = 1.0
  β[0] = logsumexp(w(A) ⊗ β[2], w(B) ⊗ β[1])
       = logsumexp(0.0 + 0.0, 1.0 + 1.0)
       = logsumexp(0.0, 2.0) ≈ 0.127

Identity check: α[2] = β[0] ≈ 0.127  ✓

Arc posteriors (Z = α[2] ≈ 0.127):
  P(A) = exp(−(α[0] + w(A) + β[2] − Z))
       = exp(−(0.0 + 0.0 + 0.0 − 0.127))
       = exp(0.127) ≈ ... wait, let's be precise:

  Under LogWeight, the posterior is:
    P(e) = exp(−(α[u] + w(e) + β[v] − Z))

  P(A) = exp(−(0.0 + 0.0 + 0.0 − 0.127)) = exp(−(−0.127)) = exp(0.127) ≈ 1.135

  This is > 1 because LogWeight costs are negative log-probabilities.
  The correct normalization uses:
    P(A) = exp(−α[u] − w(e) − β[v] + Z)
         = exp(−0.0 − 0.0 − 0.0 + 0.127) ... which still gives the same.

  Actually, under the standard convention where lower = better:
    score(A) = α[0] + w(A) + β[2] = 0.0 + 0.0 + 0.0 = 0.0
    score(B→C) = α[0] + w(B) + β[1] = 0.0 + 1.0 + 1.0 = 2.0
                  (equivalently: α[1] + w(C) + β[2] = 1.0 + 1.0 + 0.0 = 2.0)
    Z = 0.127

  Posterior = exp(−score + Z) = exp(−score) / exp(−Z):
    P(A) = exp(−0.0) / (exp(−0.0) + exp(−2.0))
         = 1.0 / (1.0 + 0.135)
         ≈ 0.881

    P(B) = P(C) = exp(−2.0) / (exp(−0.0) + exp(−2.0))
         = 0.135 / 1.135
         ≈ 0.119

  Check: P(A) + P(B→C) ≈ 0.881 + 0.119 = 1.0  ✓
```

**Interpretation:** The `GtGt` path carries ~88% of probability mass;
the `Gt Gt` path carries ~12%. The parser strongly prefers the
single-token reading. Weight training can use these posteriors to adjust
edge weights toward the oracle parse.

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

*Forward-backward is available under feature `wfst-log`.*

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
small-to-medium recovery lattices (typically 5-50 nodes):

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

This limits exploration to `n x |nodes| x 4` state expansions. In the
worst case, this means each node is visited at most `n x 4` times per
requested path, ensuring the algorithm terminates in bounded time even
when the lattice has many cycles of equal weight.

### 7.4 Heap Expansion Walkthrough

Step-by-step heap state for the 6-node lattice from §8, with N=3:

```
Step 0: push initial
┌─────────────────────────────────────────┐
│ (w=0.0, node=0, path=[])               │
└─────────────────────────────────────────┘

Step 1: pop (0.0, node=0), expand 3 outgoing edges
┌─────────────────────────────────────────┐
│ (1.0, node=1, [0→1])                   │ ← via 0→1 (w=1.0)
│ (1.5, node=3, [0→3])                   │ ← via 0→3 (w=1.5)
│ (3.0, node=2, [0→2])                   │ ← via 0→2 (w=3.0)
└─────────────────────────────────────────┘

Step 2: pop (1.0, node=1), expand edge 1→5
┌─────────────────────────────────────────┐
│ (1.5, node=3, [0→3])                   │
│ (3.0, node=2, [0→2])                   │
│ (3.0, node=5, [0→1→5])                 │ ← RESULT 1: w=3.0
└─────────────────────────────────────────┘

Step 3: pop (1.5, node=3), expand edge 3→4
┌─────────────────────────────────────────┐
│ (2.5, node=4, [0→3→4])                 │ ← via 3→4 (w=1.0)
│ (3.0, node=2, [0→2])                   │
│ (3.0, node=5, [0→1→5])                 │
└─────────────────────────────────────────┘

Step 4: pop (2.5, node=4), expand edge 4→5
┌─────────────────────────────────────────┐
│ (3.0, node=2, [0→2])                   │
│ (3.0, node=5, [0→1→5])                 │
│ (3.0, node=5, [0→3→4→5])              │ ← RESULT 2: w=3.0
└─────────────────────────────────────────┘

Step 5: pop (3.0, node=2), expand edge 2→5
┌─────────────────────────────────────────┐
│ (3.0, node=5, [0→1→5])                 │
│ (3.0, node=5, [0→3→4→5])              │
│ (3.5, node=5, [0→2→5])                │ ← RESULT 3: w=3.5
└─────────────────────────────────────────┘

Results (N=3):
  Rank 1: 0→1→5       weight=3.0
  Rank 2: 0→3→4→5     weight=3.0
  Rank 3: 0→2→5       weight=3.5
```

Note: the heap always pops the minimum-weight entry first. Tied entries
are returned in insertion order.

### 7.5 Complexity

- Time: **O(max_explored x log(heap_size))** ~ O(n*V*log(n*V))
- Space: **O(n*V)** for the heap and path copies

For the typical recovery scenario (n <= 10, V <= 50), this is well
within interactive latency budgets (~100 us).

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

Process nodes 0 -> 5 in order:

| Node | Incoming edges                                                            | α[node] = min(predecessors) |
|:----:|:--------------------------------------------------------------------------|:----------------------------|
|  0   | (start)                                                                   | 0.0 (= 1̄)                   |
|  1   | 0->1 (0.0+1.0)                                                            | 1.0                         |
|  2   | 0->2 (0.0+3.0)                                                            | 3.0                         |
|  3   | 0->3 (0.0+1.5)                                                            | 1.5                         |
|  4   | 3->4 (1.5+1.0)                                                            | 2.5                         |
|  5   | 1->5 (1.0+2.0)=3.0, 2->5 (3.0+0.5)=3.5, 4->5 (2.5+0.5)=3.0 -> **min=3.0** | 3.0                         |

**Forward score at final node = 3.0.**

### 8.2 Backward Scores (TropicalWeight)

Process nodes 5 -> 0 in reverse:

| Node | Outgoing edges                                                            | β[node] = min(successors) |
|:----:|:--------------------------------------------------------------------------|:--------------------------|
|  5   | (final)                                                                   | 0.0 (= 1̄)                 |
|  4   | 4->5 (0.5+0.0)                                                            | 0.5                       |
|  3   | 3->4 (1.0+0.5)                                                            | 1.5                       |
|  2   | 2->5 (0.5+0.0)                                                            | 0.5                       |
|  1   | 1->5 (2.0+0.0)                                                            | 2.0                       |
|  0   | 0->1 (1.0+2.0)=3.0, 0->2 (3.0+0.5)=3.5, 0->3 (1.5+1.5)=3.0 -> **min=3.0** | 3.0                       |

**Backward score at start node = 3.0.** Identity α[5] = β[0] = 3.0 holds.

### 8.3 Viterbi Best Path

The forward pass records predecessors:

```
pred[1] = (0, edge 0→1)
pred[2] = (0, edge 0→2)
pred[3] = (0, edge 0→3)
pred[4] = (3, edge 3→4)
pred[5] = (1, edge 1→5)     ← tied with (4, 4→5), (1, 1→5) selected first
```

Backtrace from node 5: 5 <- 1 <- 0.

**Best path: 0 -> 1 -> 5, tokens = [edge(0->1), edge(1->5)], total weight = 3.0.**

(Path C via nodes 3->4 also has weight 3.0 and would be found by N-best
with N >= 2, but Viterbi returns whichever tied path is encountered first
in iteration order.)

### 8.4 N-Best Paths (wfst-log, N=3)

With LogWeight, the three paths have weights 3.0, 3.5, and 3.0.
The heap-based N-best returns them in order:

| Rank | Path       | Weight |
|:----:|:-----------|:------:|
|  1   | 0->1->5    |  3.0   |
|  2   | 0->3->4->5 |  3.0   |
|  3   | 0->2->5    |  3.5   |

Paths of equal weight are returned in heap-pop order (determined by
insertion order when weights are tied).

---

## 9. Test Coverage

**`lattice.rs` (20 tests across two modules):**

| Test                                     | Algorithm    | What it verifies                    |
|:-----------------------------------------|:-------------|:------------------------------------|
| `test_token_source_linear_zero_overhead` | —            | Linear source access                |
| `test_token_source_lattice`              | —            | Lattice source variant              |
| `test_token_lattice_basic`               | —            | add_edge, num_nodes, num_edges      |
| `test_token_lattice_ambiguous`           | —            | Multiple edges from same node       |
| `test_viterbi_best_path_chain`           | Viterbi      | Chain lattice, weight accumulation  |
| `test_viterbi_best_path_ambiguous`       | Viterbi      | Selects min-weight path             |
| `test_viterbi_empty_lattice`             | Viterbi      | Returns None on empty lattice       |
| `test_viterbi_unreachable_final`         | Viterbi      | Returns None when final unreachable |
| `test_linear_to_lattice`                 | Viterbi      | Round-trip through chain lattice    |
| `test_viterbi_beam_prunes_edges`         | Beam Viterbi | Beam prunes high-cost path          |
| `test_sort_edges_by_weight`              | —            | Sort by weight for greedy access    |
| `n_best_tests::test_n_best_single_path`  | N-best       | Single path returned once           |
| `n_best_tests::test_n_best_diamond`      | N-best       | Diamond graph, 2 paths ordered      |
| `n_best_tests::test_n_best_many_paths`   | N-best       | Top 3 of 4 paths returned           |
| `n_best_tests::test_n_best_unreachable`  | N-best       | Empty on unreachable lattice        |

**`forward_backward.rs` (7 tests, feature `wfst-log`):**

| Test                                               | Algorithm     | What it verifies             |
|:---------------------------------------------------|:--------------|:-----------------------------|
| `test_forward_scores_chain`                        | Forward       | Chain: α[1]=2.0, α[2]=5.0    |
| `test_backward_scores_chain`                       | Backward      | Chain: β[1]=3.0, β[0]=5.0    |
| `test_forward_scores_diamond`                      | Forward       | Diamond: min(3.0, 4.0)=3.0   |
| `test_forward_backward_consistency`                | Both          | α[final] = β[start]          |
| `test_forward_with_tropical`                       | Forward       | Triangle: via 1 beats direct |
| `log_tests::test_forward_scores_diamond_log`       | Forward (Log) | Log sum-over-paths           |
| `log_tests::test_forward_backward_consistency_log` | Both (Log)    | Identity under LogWeight     |

Additionally, 7 generic lattice tests verify `viterbi_generic<W>()` and
`linear_to_lattice_generic<W>()` for non-tropical weight types.

---

## 10. Source Reference

| Symbol                      | Location                                      |
|:----------------------------|:----------------------------------------------|
| `TokenSource<T,S>`          | `prattail/src/lattice.rs`                     |
| `TokenLattice<T,S,W>`       | `prattail/src/lattice.rs`                     |
| `LatticeEdge<T,S,W>`        | `prattail/src/lattice.rs`                     |
| `ViterbiPath<T,S,W>`        | `prattail/src/lattice.rs`                     |
| `viterbi_best_path`         | `prattail/src/lattice.rs`                     |
| `viterbi_best_path_beam`    | `prattail/src/lattice.rs`                     |
| `viterbi_generic`           | `prattail/src/lattice.rs`                     |
| `linear_to_lattice`         | `prattail/src/lattice.rs`                     |
| `linear_to_lattice_generic` | `prattail/src/lattice.rs`                     |
| `n_best_paths` (wfst-log)   | `prattail/src/lattice.rs`                     |
| `forward_scores`            | `prattail/src/forward_backward.rs` (wfst-log) |
| `backward_scores`           | `prattail/src/forward_backward.rs` (wfst-log) |
| `total_weight`              | `prattail/src/forward_backward.rs` (wfst-log) |

---

**See also:**
- [`semirings.md`](semirings.md) — semiring axioms and all ten concrete types
- [`weighted-automata.md`](weighted-automata.md) — WFST structure that produces the prediction weights fed into these algorithms
- [`token-lattices.md`](token-lattices.md) — formal theory of the token lattice DAG
- [`multi-step-viterbi-recovery.md`](multi-step-viterbi-recovery.md) — Viterbi on repair lattices for error recovery
- [Pipeline integration](../../architecture/wfst/pipeline-integration.md) — where WFST/Viterbi fits in the compile-time pipeline
- Per-semiring theory docs:
  - [`semirings/tropical-weight.md`](semirings/tropical-weight.md)
  - [`semirings/log-weight.md`](semirings/log-weight.md)
  - [`semirings/counting-weight.md`](semirings/counting-weight.md)
  - [`semirings/boolean-weight.md`](semirings/boolean-weight.md)
  - [`semirings/edit-weight.md`](semirings/edit-weight.md)
  - [`semirings/product-weight.md`](semirings/product-weight.md)
  - [`semirings/complexity-weight.md`](semirings/complexity-weight.md)
  - [`semirings/context-weight.md`](semirings/context-weight.md)
  - [`semirings/entropy-weight.md`](semirings/entropy-weight.md)
  - [`semirings/nbest-weight.md`](semirings/nbest-weight.md)
