# Token Lattice Design and Implementation

**Date:** 2026-03-01

This document explains *why* PraTTaIL's token lattice code is structured
the way it is — the design decisions, trade-offs, and implementation
patterns in `lattice.rs`. For formal theory, see
[theory/wfst/token-lattices.md](../../theory/wfst/token-lattices.md).
For pipeline integration, see
[architecture/wfst/token-lattices.md](../../architecture/wfst/token-lattices.md).

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [TokenSource: The Two-Path Abstraction](#2-tokensource-the-two-path-abstraction)
   - 2.1 [Design Goal](#21-design-goal)
   - 2.2 [Enum Definition](#22-enum-definition)
   - 2.3 [Zero-Overhead Inline Methods](#23-zero-overhead-inline-methods)
   - 2.4 [from_weighted()](#24-from_weighted)
   - 2.5 [resolve() and resolve_beam()](#25-resolve-and-resolve_beam)
3. [Generic Parametrization: T, S, W](#3-generic-parametrization-t-s-w)
   - 3.1 [Token Type T](#31-token-type-t)
   - 3.2 [Span Type S](#32-span-type-s)
   - 3.3 [Weight Type W](#33-weight-type-w)
   - 3.4 [Why a Default Type Parameter](#34-why-a-default-type-parameter)
4. [TokenLattice: Adjacency-List Weighted DAG](#4-tokenlattice-adjacency-list-weighted-dag)
   - 4.1 [Representation Choice](#41-representation-choice)
   - 4.2 [LatticeEdge Structure](#42-latticeedge-structure)
   - 4.3 [Lazy Node Growth](#43-lazy-node-growth)
   - 4.4 [Edge Sorting](#44-edge-sorting)
   - 4.5 [Semiring Bound on Struct](#45-semiring-bound-on-struct)
5. [Viterbi Implementation Choices](#5-viterbi-implementation-choices)
   - 5.1 [Tropical Specialization](#51-tropical-specialization)
   - 5.2 [Generic Viterbi](#52-generic-viterbi)
   - 5.3 [Why Two Functions](#53-why-two-functions)
   - 5.4 [Predecessor Tracking](#54-predecessor-tracking)
6. [Beam Pruning Design](#6-beam-pruning-design)
   - 6.1 [Two-Level Pruning](#61-two-level-pruning)
   - 6.2 [Progressive Tightening](#62-progressive-tightening)
   - 6.3 [Optional Beam Width](#63-optional-beam-width)
7. [N-Best Path Algorithm](#7-n-best-path-algorithm)
   - 7.1 [Feature Gate](#71-feature-gate)
   - 7.2 [Heap-Based Search](#72-heap-based-search)
   - 7.3 [Path Cloning Trade-Off](#73-path-cloning-trade-off)
   - 7.4 [Safety Limit](#74-safety-limit)
8. [Alternative Path Extraction](#8-alternative-path-extraction)
   - 8.1 [Feature Gate](#81-feature-gate)
   - 8.2 [Difference from N-Best](#82-difference-from-n-best)
   - 8.3 [Use Case](#83-use-case)
9. [Conversion Functions](#9-conversion-functions)
   - 9.1 [linear_to_lattice()](#91-linear_to_lattice)
   - 9.2 [linear_to_lattice_generic()](#92-linear_to_lattice_generic)
   - 9.3 [Why Free Functions](#93-why-free-functions)
10. [Feature Gating Strategy](#10-feature-gating-strategy)
11. [Design Decisions Summary](#11-design-decisions-summary)
12. [Test Coverage](#12-test-coverage)
13. [Source Reference](#13-source-reference)
14. [Cross-References](#14-cross-references)

---

## 1. Motivation

PraTTaIL needs a lattice abstraction for three reasons:

1. **Lexical ambiguity.** Some grammars produce multiple valid
   tokenizations for the same input span (e.g., `>>` as `GtGt` or
   `Gt Gt`). The lattice encodes all alternatives with weights so the
   parser can select the best one.

2. **Error recovery.** When parsing fails, the recovery system builds an
   implicit repair lattice over skip/delete/insert/substitute actions and
   runs Viterbi to find the minimum-cost repair sequence.

3. **Context-sensitive lexing.** Future context-sensitive lexers may
   produce true multi-path lattices at runtime.

The design is adapted from `lling-llang/src/lattice/lattice.rs`, with
three key changes:

- Zero-copy `Token<'a>` and `Range` types (vs. owned strings)
- Generic weight type `W` with `TropicalWeight` default (vs. fixed `f64`)
- `TokenSource` two-path enum for zero-overhead on the common case

---

## 2. TokenSource: The Two-Path Abstraction

### 2.1 Design Goal

Unambiguous tokenization (the common case for all current PraTTaIL
grammars) must have **zero runtime cost** compared to a bare
`Vec<(Token, Range)>`. The lattice machinery should add no overhead
when it is not needed.

### 2.2 Enum Definition

```rust
pub enum TokenSource<T, S> {
    /// Unambiguous tokenization: flat array, zero overhead.
    Linear(Vec<(T, S)>),
    /// Ambiguous tokenization: weighted DAG.
    Lattice(TokenLattice<T, S>),
}
```

The enum has only two variants — no `WeightedLinear` or `Hybrid` — to
keep the branch prediction profile clean. The parser branches once at
entry, not per-token.

### 2.3 Zero-Overhead Inline Methods

All `TokenSource` accessor methods are marked `#[inline]`:

```rust
#[inline]
pub fn token_at(&self, pos: usize) -> Option<&(T, S)> {
    match self {
        TokenSource::Linear(tokens) => tokens.get(pos),
        TokenSource::Lattice(lattice) => {
            lattice.edges_from(pos).first().map(|edge| &edge.token_span)
        },
    }
}
```

For the `Linear` variant, this compiles to exactly the same code as
`tokens.get(pos)` — the branch is eliminated by the optimizer when the
variant is known at the call site.

```
  TokenSource decision tree:
  ┌──────────────────────────────────────────────────────┐
  │  lex_weighted_core() produces (T, S, f64) triples    │
  │                                                      │
  │        ┌──── all unambiguous? ────┐                  │
  │        │                          │                  │
  │       YES                        NO                  │
  │        │                          │                  │
  │        ▼                          ▼                  │
  │  from_weighted()            build TokenLattice       │
  │  → strip f64               → populate edges          │
  │  → Linear(Vec<(T,S)>)      → Lattice(TokenLattice)   │
  │        │                          │                  │
  │        ▼                          ▼                  │
  │  resolve()                 resolve() / resolve_beam()│
  │  → identity                → Viterbi extraction      │
  │  → Vec<(T,S)>              → Vec<(T,S)>              │
  └──────────────────────────────────────────────────────┘
```

### 2.4 from_weighted()

```rust
pub fn from_weighted(tokens: Vec<(T, S, f64)>) -> Self {
    let stripped: Vec<(T, S)> = tokens.into_iter()
        .map(|(t, s, _w)| (t, s)).collect();
    TokenSource::Linear(stripped)
}
```

Currently, `from_weighted()` always produces `Linear` — it strips the
f64 weights and ignores ambiguity. This is correct because the current
lexer (`lex_weighted_core()`) produces at most one token per position.
When context-sensitive lexing is activated, this function will be
extended to detect multiple tokens at the same position and construct a
`Lattice` variant instead.

### 2.5 resolve() and resolve_beam()

Both methods consume `self` and return `Result<Vec<(T, S)>, String>`:

- **Linear:** Returns the inner `Vec` directly — zero allocation, zero
  Viterbi overhead.
- **Lattice:** Runs `viterbi_best_path()` (or `viterbi_best_path_beam()`
  for `resolve_beam()`) and returns the extracted token sequence.

The error case ("final node unreachable") can only occur for malformed
lattices and indicates a bug in lattice construction.

---

## 3. Generic Parametrization: T, S, W

### 3.1 Token Type T

The token type `T` is a generic parameter rather than a concrete type
because PraTTaIL generates a different `Token<'a>` enum for each grammar.
The lattice infrastructure must work with all of them.

`T: Clone` is required by Viterbi (token cloning during backtrace).
`T: fmt::Display` is required only for `Display` impls on `TokenSource`.

### 3.2 Span Type S

The span type `S` is generic for the same reason. In practice, S is
always `Range` from `runtime_types.rs`, but the genericity enables
testing with simple `(usize, usize)` tuples.

### 3.3 Weight Type W

The weight type `W: Semiring` defaults to `TropicalWeight` but can be
any semiring implementation. Use cases:

| Weight type                                 | Use case                            |
|:--------------------------------------------|:------------------------------------|
| `TropicalWeight`                            | Standard dispatch priority          |
| `EditWeight`                                | Minimum-edit recovery               |
| `ProductWeight<TropicalWeight, EditWeight>` | Joint priority + edit distance      |
| `CountingWeight`                            | Ambiguity detection (via Product)   |
| `LogWeight`                                 | Probabilistic training (`wfst-log`) |

### 3.4 Why a Default Type Parameter

The default `W = TropicalWeight` on `TokenLattice<T, S, W>` eliminates
boilerplate at every use site. Without the default, every occurrence
would need to spell out the weight type:

```rust
// Without default (verbose):
let lattice: TokenLattice<Token<'a>, Range, TropicalWeight> = ...;

// With default (clean):
let lattice: TokenLattice<Token<'a>, Range> = ...;
```

The `TokenSource` enum intentionally does NOT carry a weight parameter
because it always resolves to `Vec<(T, S)>` — weights are internal to
the lattice resolution process and are not exposed to the parser.

---

## 4. TokenLattice: Adjacency-List Weighted DAG

### 4.1 Representation Choice

The lattice stores edges as `Vec<Vec<LatticeEdge<T, S, W>>>` — an
adjacency list indexed by source node.

| Alternative      | Pros                                       | Cons                          | Why not chosen                                        |
|:-----------------|:-------------------------------------------|:------------------------------|:------------------------------------------------------|
| Adjacency list   | O(1) node lookup, cache-friendly edge scan | Wastes space for sparse nodes | **Chosen:** natural fit for sequential DAG processing |
| CSR (compressed) | Most compact, cache-optimal                | Static (no dynamic add_edge)  | Need dynamic construction                             |
| Edge list        | Compact, simple                            | O(\|E\|) per node lookup      | Viterbi needs per-node access                         |
| HashMap          | Sparse-friendly                            | Hash overhead, poor cache     | Nodes are dense 0..N                                  |

The adjacency list is the right choice because:

1. Nodes are dense (0, 1, ..., N) — no hash overhead
2. Viterbi processes nodes sequentially — excellent cache locality
3. `add_edge()` is O(1) amortized — good for dynamic construction
4. `edges_from(node)` returns a slice — zero-allocation iteration

### 4.2 LatticeEdge Structure

```rust
pub struct LatticeEdge<T, S, W: Semiring = TropicalWeight> {
    pub token_span: (T, S),   // the token and its source span
    pub target: usize,         // destination node
    pub weight: W,             // semiring weight
}
```

The token and span are stored as a tuple `(T, S)` rather than separate
fields to match the `Vec<(T, S)>` format of `TokenSource::Linear`,
making conversions between the two representations zero-copy.

### 4.3 Lazy Node Growth

```rust
pub fn ensure_nodes(&mut self, node_count: usize) {
    while self.edges.len() < node_count {
        self.edges.push(Vec::new());
    }
}
```

The `ensure_nodes()` method grows the adjacency list lazily. Combined
with `add_edge()` calling `ensure_nodes(to_node + 1)`, this means
callers never need to pre-declare the node count — the lattice grows
automatically as edges are added.

### 4.4 Edge Sorting

```rust
impl<T, S, W: Semiring + Ord> TokenLattice<T, S, W> {
    pub fn sort_edges_by_weight(&mut self) { ... }
}
```

The `sort_edges_by_weight()` method requires `W: Ord` (not just
`Semiring`) and is provided as a separate method rather than automatic
sorting on `add_edge()`. This is intentional:

- Sorting after all edges are added is O(|E| log d) where d is max
  out-degree, vs. O(|E| × d) for insertion sort on each `add_edge()`
- Many algorithms (Viterbi) don't need sorted edges
- Callers opt in when needed (e.g., for N-best extraction)

### 4.5 Semiring Bound on Struct

The `W: Semiring` bound is on the struct definition, not just on method
impls. This ensures that every `TokenLattice` carries a valid weight
type — you cannot accidentally construct a lattice with `W = String`.
The trade-off is slightly more restrictive generic bounds, but this
matches the mathematical invariant: a token lattice without a valid
weight function is meaningless.

---

## 5. Viterbi Implementation Choices

### 5.1 Tropical Specialization

```rust
pub fn viterbi_best_path_beam<T: Clone, S: Clone>(
    lattice: &TokenLattice<T, S>,      // W defaults to TropicalWeight
    final_node: usize,
    beam_width: Option<TropicalWeight>,
) -> Option<ViterbiPath<T, S>>
```

The tropical specialization uses `TropicalWeight`-specific operations:

- `is_zero()` checks for +∞ (unreachable)
- `.value()` accesses the raw `f64` for beam comparison
- Beam pruning requires float comparison semantics

This function handles the common case (all current grammars).

### 5.2 Generic Viterbi

```rust
pub fn viterbi_generic<T: Clone, S: Clone, W: Semiring + Ord>(
    lattice: &TokenLattice<T, S, W>,
    final_node: usize,
) -> Option<ViterbiPath<T, S, W>>
```

The generic version works with any semiring satisfying `Semiring + Ord`
where `zero()` is the largest element. It does NOT support beam pruning
(no raw float access).

### 5.3 Why Two Functions

A single generic function with optional beam pruning would require either:

1. An additional trait method like `can_compare_beam()` — complex
2. A `where W: BeamPrunable` bound — creates a second trait for one use
3. Runtime branching on the weight type — defeats static dispatch

The two-function approach is simpler: the tropical version handles the
99% case with full optimization; the generic version handles the
remaining cases (EditWeight, ProductWeight) without beam pruning.

### 5.4 Predecessor Tracking

The predecessor array stores `(node_index, edge_index)` pairs:

```rust
let mut pred: Vec<Option<(usize, usize)>> = vec![None; n];
```

This avoids cloning `(T, S)` data during the forward pass. Only during
backtrace are tokens cloned from the lattice's edge storage. For the
common case (small lattices with < 50 nodes), this saves significant
allocation compared to storing full token sequences in the predecessor
array.

---

## 6. Beam Pruning Design

### 6.1 Two-Level Pruning

Beam pruning operates at two levels:

1. **Node-level:** Skip entire nodes whose α[v] exceeds the beam.
   This prunes all outgoing edges at once.

2. **Edge-level:** For non-pruned nodes, skip individual edges whose
   candidate distance α[v] ⊗ w(e) exceeds the beam. This provides
   finer-grained control.

Both checks use the same threshold: `α_best_final + beam_width`.

### 6.2 Progressive Tightening

The `best_final` variable tracks the best known distance to the final
node. It starts at +∞ (no pruning) and decreases as paths reach f:

```rust
let mut best_final = TropicalWeight::zero(); // +∞

// ... during forward pass:
if edge.target == final_node && new_dist < best_final {
    best_final = new_dist;
}
```

This means early nodes are processed without pruning (exact), while
later nodes benefit from progressively tighter beams.

### 6.3 Optional Beam Width

The beam width is `Option<TropicalWeight>`:

- `None` = exact Viterbi (no pruning)
- `Some(w)` = beam pruning with width `w`

The `viterbi_best_path()` convenience function calls
`viterbi_best_path_beam(..., None)`, providing exact semantics without
requiring callers to think about beams.

---

## 7. N-Best Path Algorithm

### 7.1 Feature Gate

N-best extraction is gated under `#[cfg(feature = "wfst-log")]` because
it is primarily used for probabilistic workflows (weight training, N-best
output) that require the LogWeight semiring.

### 7.2 Heap-Based Search

The algorithm uses a `BinaryHeap<SearchState>` with reversed `Ord`
(min-heap) to explore paths in weight order:

```rust
struct SearchState {
    weight: TropicalWeight,
    node: usize,
    path: Vec<(usize, usize)>,  // (from_node, edge_index)
}

impl Ord for SearchState {
    fn cmp(&self, other: &Self) -> Ordering {
        other.weight.cmp(&self.weight)  // reversed for min-heap
    }
}
```

Each pop from the heap represents extending the shortest unexplored
partial path by one edge. When a path reaches the final node, it is
added to the results.

### 7.3 Path Cloning Trade-Off

Each `SearchState` carries a `Vec<(usize, usize)>` path history. On
each expansion, the path is cloned and extended:

```rust
let mut new_path = state.path.clone();
new_path.push((state.node, edge_idx));
```

This is O(path_length) per expansion. For large lattices, an immutable
path-tree structure would be more efficient, but for the small lattices
typical in parser recovery (< 50 nodes), path cloning is simpler and
fast enough.

### 7.4 Safety Limit

The maximum explored states is capped at:

```rust
let max_explored = n * num_nodes * 4;
```

This prevents combinatorial explosion on pathological lattices. For a
typical recovery lattice with 20 nodes and N = 5, the limit is
20 × 5 × 4 = 400 states — more than sufficient.

---

## 8. Alternative Path Extraction

### 8.1 Feature Gate

Alternative path extraction was formerly gated under the now-removed
`context-sensitive-lex` feature because it was only useful when the
lexer produced true multi-path lattices. This function has been removed
along with the feature.

### 8.2 Difference from N-Best

`alternative_paths()` differs from `n_best_paths()` in two ways:

1. **Accepts a start node:** Paths can begin at any node, not just
   node 0. This is needed for error recovery, which tries alternative
   tokenizations from the error position forward.

2. **Returns (tokens, weight) pairs:** Each result carries the actual
   token sequence and its total weight, rather than just the path as
   edge indices. This simplifies the recovery code.

### 8.3 Use Case

When parsing fails at a position that has multiple tokenizations in the
lattice, `lattice_recovery()` in `recovery.rs` calls
`alternative_paths()` to extract N alternative tokenization paths, then
runs `find_best_recovery()` on each. The cheapest successful recovery
across all tokenizations is returned.

---

## 9. Conversion Functions

### 9.1 linear_to_lattice()

```rust
pub fn linear_to_lattice<T, S>(tokens: Vec<(T, S)>) -> TokenLattice<T, S> {
    // Creates chain: 0 →(1̄)→ 1 →(1̄)→ 2 →(1̄)→ ... →(1̄)→ N
}
```

Converts a flat token vector to a chain lattice with `TropicalWeight::one()`
on every edge. The Viterbi path through the chain is the original sequence
with total weight 0.0. Used for testing and for lattice composition where
the input needs to be in lattice form.

### 9.2 linear_to_lattice_generic()

```rust
pub fn linear_to_lattice_generic<T, S, W: Semiring>(
    tokens: Vec<(T, S)>
) -> TokenLattice<T, S, W>
```

Same as `linear_to_lattice()` but uses `W::one()` for the weight,
enabling construction of lattices with non-tropical semirings (e.g.,
`EditWeight` for testing edit-distance Viterbi).

### 9.3 Why Free Functions

Both conversion functions are free functions rather than methods on
`TokenSource` or `TokenLattice`. Reasons:

1. **Ownership:** They consume a `Vec<(T, S)>` and produce a new
   `TokenLattice`, which is a different type. Method syntax would
   be awkward (`Vec::to_lattice()` doesn't exist).

2. **Symmetry:** Both functions are constructors. Placing them as
   associated functions on `TokenLattice` would require explicit
   type annotation at every call site due to the extra generic `W`.

3. **Discoverability:** Free functions in the `lattice` module are
   easy to find; methods on a generic struct can be hidden by trait
   bound constraints.

---

## 10. Feature Gating Strategy

| Function / Type               | Feature gate                          | Rationale                              |
|:------------------------------|:--------------------------------------|:---------------------------------------|
| `TokenSource`                 | always                                | Core abstraction for all parsers       |
| `TokenLattice`                | always                                | Needed by recovery (implicit lattices) |
| `LatticeEdge`                 | always                                | Part of TokenLattice                   |
| `ViterbiPath`                 | always                                | Return type of Viterbi functions       |
| `viterbi_best_path()`         | always                                | Lattice resolution                     |
| `viterbi_best_path_beam()`    | always                                | Beam-pruned lattice resolution         |
| `viterbi_generic()`           | always                                | Multi-semiring lattice analysis        |
| `linear_to_lattice()`         | always                                | Testing and composition                |
| `linear_to_lattice_generic()` | always                                | Multi-semiring testing                 |
| `sort_edges_by_weight()`      | always (needs `W: Ord`)               | Edge ordering                          |
| `n_best_paths()`              | `wfst-log`                            | Probabilistic N-best extraction        |
| `alternative_paths()`         | removed (was `context-sensitive-lex`) | Lattice-aware error recovery (removed) |

---

## 11. Design Decisions Summary

| Decision                        | Chosen                       | Alternative           | Rationale                                                    |
|:--------------------------------|:-----------------------------|:----------------------|:-------------------------------------------------------------|
| Two-path enum vs always lattice | `TokenSource` enum           | Always `TokenLattice` | Zero overhead for unambiguous case (99%+ of inputs)          |
| Adjacency list vs CSR           | `Vec<Vec<LatticeEdge>>`      | CSR                   | Dynamic construction via `add_edge()`                        |
| Two Viterbi fns vs one generic  | Specialized + generic        | Single generic        | Beam pruning requires TropicalWeight-specific float ops      |
| Predecessor as (node, idx)      | `Vec<Option<(usize,usize)>>` | Path cloning per node | Avoids allocation during forward pass                        |
| Edge sorting opt-in             | `sort_edges_by_weight()`     | Auto-sort on add_edge | O(\|E\| log d) batch vs O(\|E\| × d) incremental             |
| N-best feature gated            | `wfst-log`                   | Always available      | Only useful for probabilistic workflows; reduces binary size |

---

## 12. Test Coverage

41 tests covering all major functionality:

| Test name                                     | Category          | What it verifies                             |
|:----------------------------------------------|:------------------|:---------------------------------------------|
| `test_token_source_linear_zero_overhead`      | TokenSource       | Linear variant access, len, is_linear        |
| `test_token_source_lattice`                   | TokenSource       | Lattice variant detection                    |
| `test_token_lattice_basic`                    | TokenLattice      | Chain construction, node/edge counts         |
| `test_token_lattice_ambiguous`                | TokenLattice      | Multi-edge nodes (GtGt ambiguity)            |
| `test_viterbi_best_path_chain`                | Viterbi           | Simple chain path extraction + weight        |
| `test_viterbi_best_path_ambiguous`            | Viterbi           | Correct path selection (lower weight wins)   |
| `test_viterbi_empty_lattice`                  | Viterbi           | None on empty lattice                        |
| `test_viterbi_unreachable_final`              | Viterbi           | None when final node unreachable             |
| `test_linear_to_lattice`                      | Conversion        | Chain construction + Viterbi round-trip      |
| `test_viterbi_beam_prunes_edges`              | Beam              | High-weight path pruned, best path preserved |
| `test_sort_edges_by_weight`                   | Sorting           | Edges sorted ascending by weight             |
| `test_from_weighted_strips_weights`           | from_weighted     | f64 weights stripped, Linear produced        |
| `test_resolve_linear_zero_overhead`           | resolve           | Linear resolve returns same Vec              |
| `test_resolve_lattice_viterbi`                | resolve           | Lattice resolve picks minimum-weight path    |
| `test_resolve_empty_lattice_returns_error`    | resolve           | Error on empty lattice                       |
| `test_resolve_beam_linear_ignores_beam`       | resolve_beam      | Beam parameter ignored for Linear            |
| `test_edit_weight_lattice`                    | Generic lattice   | EditWeight Viterbi selects min-edit path     |
| `test_product_weight_lattice`                 | Generic lattice   | ProductWeight lexicographic Viterbi          |
| `test_counting_weight_not_viterbi_compatible` | Generic lattice   | CountingWeight Viterbi correctly fails       |
| `test_generic_lattice_linear_conversion`      | Generic convert   | linear_to_lattice_generic round-trip         |
| `test_generic_viterbi_unreachable`            | Generic Viterbi   | None for unreachable final node              |
| `test_generic_viterbi_empty`                  | Generic Viterbi   | None for empty lattice                       |
| `test_n_best_single_path`                     | N-best (wfst-log) | Single path returns 1 result                 |
| `test_n_best_diamond`                         | N-best (wfst-log) | Diamond yields 2 paths, ordered by weight    |
| `test_n_best_many_paths`                      | N-best (wfst-log) | Top-3 from 4 parallel paths                  |
| `test_n_best_unreachable`                     | N-best (wfst-log) | Empty vec for unreachable final              |
| `test_alternative_paths_single_path`          | Alt paths (csl)   | Single chain yields 1 result                 |
| `test_alternative_paths_diamond`              | Alt paths (csl)   | Diamond yields 2 paths, weight-sorted        |
| `test_alternative_paths_from_midpoint`        | Alt paths (csl)   | Start from non-zero node                     |
| `test_alternative_paths_empty`                | Alt paths (csl)   | Empty lattice yields no paths                |
| `test_alternative_paths_n_limit`              | Alt paths (csl)   | Respects N-limit                             |

Plus 10 additional semiring-related tests exercised through lattice
operations (EditWeight, ProductWeight, CountingWeight lattice creation
and Viterbi extraction).

---

## 13. Source Reference

| Type / Function                | File             | Lines   |
|:-------------------------------|:-----------------|:--------|
| `TokenSource<T, S>`            | `src/lattice.rs` | 51–205  |
| `TokenSource::linear()`        | `src/lattice.rs` | 70–72   |
| `TokenSource::from_weighted()` | `src/lattice.rs` | 144–147 |
| `TokenSource::resolve()`       | `src/lattice.rs` | 156–171 |
| `TokenSource::resolve_beam()`  | `src/lattice.rs` | 177–193 |
| `TokenLattice<T, S, W>`        | `src/lattice.rs` | 240–331 |
| `LatticeEdge<T, S, W>`         | `src/lattice.rs` | 247–254 |
| `ViterbiPath<T, S, W>`         | `src/lattice.rs` | 343–348 |
| `viterbi_best_path()`          | `src/lattice.rs` | 356–361 |
| `viterbi_best_path_beam()`     | `src/lattice.rs` | 371–449 |
| `viterbi_generic()`            | `src/lattice.rs` | 484–536 |
| `linear_to_lattice()`          | `src/lattice.rs` | 546–556 |
| `linear_to_lattice_generic()`  | `src/lattice.rs` | 562–572 |
| `n_best_paths()`               | `src/lattice.rs` | 598–689 |
| `alternative_paths()`          | `src/lattice.rs` | 708–785 |

---

## 14. Cross-References

- [Token Lattice Theory](../../theory/wfst/token-lattices.md) — Formal definitions, proofs, complexity
- [Token Lattice Architecture](../../architecture/wfst/token-lattices.md) — Pipeline integration points
- [Error Recovery Design](error-recovery.md) — Repair lattices, viterbi_multi_step, lattice_recovery
- [Semirings Overview](../../theory/wfst/semirings.md) — Semiring axioms, all ten concrete types
- [Per-Semiring Theory](../../theory/wfst/semirings/) — Detailed theory for each weight type
- [Per-Semiring Design](semirings/) — Implementation details for each weight type
- [Viterbi and Forward-Backward](../../theory/wfst/viterbi-and-forward-backward.md) — Algorithm details
- [Weighted Automata](../../theory/wfst/weighted-automata.md) — WFST formal definition
- [Stream-to-Lattice — Theory](../../theory/wfst/stream-to-lattice.md) — Pedagogical guide to all conversion points
- [Stream-to-Lattice — Architecture](../../architecture/wfst/stream-to-lattice.md) — Code-path walkthrough with source-line references
