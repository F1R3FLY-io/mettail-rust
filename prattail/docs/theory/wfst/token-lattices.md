# Token Lattices: Formal Theory

**Date:** 2026-03-01

A token lattice is a weighted directed acyclic graph (DAG) that
represents all possible tokenizations of an input string. This document
establishes the mathematical foundations: formal definitions, key
properties, algorithm correctness proofs, and connections to classical
NLP lattice models. It serves as the theoretical companion to the
[design](../../design/wfst/token-lattices.md) and
[architecture](../../architecture/wfst/token-lattices.md) documents.

---

## Table of Contents

1. [Motivation](#1-motivation)
2. [Definitions and Notation](#2-definitions-and-notation)
   - 2.1 [Semiring Recap](#21-semiring-recap)
   - 2.2 [Token Alphabet and Span Type](#22-token-alphabet-and-span-type)
   - 2.3 [Formal Definition](#23-formal-definition)
3. [Properties of Token Lattices](#3-properties-of-token-lattices)
   - 3.1 [Topological Ordering](#31-topological-ordering)
   - 3.2 [Paths and Path Weight](#32-paths-and-path-weight)
   - 3.3 [Lattice Weight](#33-lattice-weight)
4. [The Linear Degenerate Case](#4-the-linear-degenerate-case)
   - 4.1 [Definition](#41-definition)
   - 4.2 [Zero-Overhead Principle](#42-zero-overhead-principle)
5. [Viterbi Algorithm on Lattice DAGs](#5-viterbi-algorithm-on-lattice-dags)
   - 5.1 [Problem Statement](#51-problem-statement)
   - 5.2 [DP Recurrence](#52-dp-recurrence)
   - 5.3 [Correctness Theorem](#53-correctness-theorem)
   - 5.4 [Backtrace](#54-backtrace)
   - 5.5 [Worked Example](#55-worked-example)
   - 5.6 [Generic Viterbi](#56-generic-viterbi)
6. [Beam-Pruned Viterbi](#6-beam-pruned-viterbi)
   - 6.1 [Motivation](#61-motivation)
   - 6.2 [Algorithm](#62-algorithm)
   - 6.3 [Progressive Tightening](#63-progressive-tightening)
   - 6.4 [Soundness Theorem](#64-soundness-theorem)
7. [N-Best Path Extraction](#7-n-best-path-extraction)
   - 7.1 [Problem Statement](#71-problem-statement)
   - 7.2 [Heap-Based Algorithm](#72-heap-based-algorithm)
   - 7.3 [Safety Bound](#73-safety-bound)
   - 7.4 [Complexity](#74-complexity)
8. [Forward-Backward on Lattices](#8-forward-backward-on-lattices)
   - 8.1 [Forward Scores](#81-forward-scores)
   - 8.2 [Backward Scores](#82-backward-scores)
   - 8.3 [Arc Posterior](#83-arc-posterior)
9. [Relationship to Classical NLP Lattices](#9-relationship-to-classical-nlp-lattices)
   - 9.1 [Speech Recognition Word Lattices](#91-speech-recognition-word-lattices)
   - 9.2 [Chinese Word Segmentation Lattices](#92-chinese-word-segmentation-lattices)
   - 9.3 [Morphological Analysis Lattices](#93-morphological-analysis-lattices)
   - 9.4 [Disambiguation of Terminology](#94-disambiguation-of-terminology)
10. [References](#10-references)
11. [Source Reference](#11-source-reference)
12. [Cross-References](#12-cross-references)

---

## 1. Motivation

Most programming language lexers are deterministic: given an input
string, there is exactly one token sequence. But some grammars exhibit
**lexical ambiguity** — the same character sequence admits multiple
valid tokenizations. A canonical example:

```
Input:   > >
         ───
Could be:  GtGt   (one token, right-shift operator)
       or: Gt Gt  (two tokens, two comparisons)
```

The parser cannot resolve this ambiguity without syntactic context (e.g.,
`Vec<Vec<i32>>` needs `>>` as two `Gt` tokens, while `x >> 2` needs one
`GtGt`). A token lattice encodes **all** tokenizations simultaneously as
a weighted DAG, deferring resolution to the parser.

Parsing over a token lattice reduces to a shortest-path problem: assign
weights encoding tokenization preference (via a semiring), then extract
the minimum-weight path. The semiring abstraction (cross-ref
[semirings.md](semirings.md)) makes this generic — switching from
`TropicalWeight` (best single parse) to `LogWeight` (all-paths sum)
changes *what is optimized* without changing the algorithm.

---

## 1.5 What Is a Token Lattice, Intuitively?

### The Subway Map Analogy

A token lattice is like a subway map between two stations (start and end
of input). Each route represents a different tokenization of the input
string. Some routes are express (fewer stops = fewer tokens, e.g.,
`ShrAssign` as one token) and some are local (more stops = more tokens,
e.g., `Gt Gt Eq` as three). Each route has a travel time (weight).
Viterbi finds the fastest route.

### Core Insight

A token lattice represents **all possible readings** of an input string
simultaneously in a single data structure. Instead of trying each
tokenization sequentially (which could be exponential in the number of
ambiguous positions), the lattice encodes them all at once and lets
Viterbi extract the winner in a single O(V + E) pass.

### Subway Map for `>>=`

```
Station 0         Station 1         Station 2         Station 3
(before >)        (between > >)     (between > =)     (after =)
    ●─── Gt(1.0) ───●─── Gt(1.0) ───●─── Eq(0.0) ───●
    │               │               ▲               │
    │               └── GtEq(0.5) ──┘               │
    │                                               │
    ├──── GtGt(0.0) ─── ● ╌╌╌ Eq(0.0) ╌╌╌╌╌╌╌╌╌╌╌╌╌─┤
    │                   2                           │
    │                                               │
    └───────────── ShrAssign(0.0) ──────────────────┘

Express:  ShrAssign          (1 token, cost 0.0)
Local:    Gt + Gt + Eq       (3 tokens, cost 2.0)
Mixed:    GtGt + Eq          (2 tokens, cost 0.0)
Mixed:    Gt + GtEq          (2 tokens, cost 1.5)
```

Four different tokenizations are encoded simultaneously. Viterbi
processes stations 0 through 3 left-to-right, computing the cheapest
arrival at each. The express route `ShrAssign` (cost 0.0) ties with
`GtGt + Eq` (cost 0.0); both win over the local routes. The parser
receives whichever tied path is encountered first in edge iteration
order.

---

## 2. Definitions and Notation

### 2.1 Semiring Recap

A semiring **S = (K, ⊕, ⊗, 0̄, 1̄)** is a carrier set K with two
operations satisfying the standard axioms. See [semirings.md](semirings.md)
§2 for the full definition. The key operations in this document:

| Operation | Symbol | TropicalWeight         | Meaning                 |
|:----------|:------:|:-----------------------|:------------------------|
| Plus      | ⊕      | min(a, b)              | Combine parallel paths  |
| Times     | ⊗      | a + b                  | Sequence path segments  |
| Zero      | 0̄      | +∞                     | Unreachable             |
| One       | 1̄      | 0.0                    | Zero cost               |

### 2.2 Token Alphabet and Span Type

Let **T** denote the token alphabet — the set of all token variants
produced by the lexer (e.g., `{Gt, GtGt, Plus, Integer, Eof, ...}`).
In PraTTaIL, T is the generated `Token<'a>` enum.

Let **S** denote the span type — a range in the source text. In
PraTTaIL, S is the `Range` struct from `runtime_types.rs`, carrying
start/end `Position` values and an optional file ID.

### 2.3 Formal Definition

A **token lattice** over semiring S = (K, ⊕, ⊗, 0̄, 1̄) is a 5-tuple:

```
L = (V, E, s, f, w)
```

where:

| Symbol | Type           | Description                       |
|:------:|:---------------|:----------------------------------|
|   V    | {0, 1, ..., N} | Node set = positions in the input |
|   E    | V × V × T × S  | Directed edges (arcs)             |
|   s    | 0              | Start node                        |
|   f    | N              | Final node                        |
|   w    | E → K          | Weight function                   |

Each edge e = (u, v, t, σ) ∈ E with u < v asserts: "the input from
position u to position v can be tokenized as token t covering span σ
with weight w(e)."

**DAG constraint:** For every edge (u, v, t, σ) ∈ E, we require v > u.
This ensures L is acyclic.

**Example:** The `>>` ambiguity produces the following 3-node lattice:

```
                 GtGt (w = 0.0)
    ┌───────────────────────────────┐
    │                               ▼
  ┌───┐    Gt (w = 1.0)    ┌───┐   Gt (w = 1.0)     ┌───┐
  │ 0 │ ──────────────────►│ 1 │ ──────────────────►│ 2 │
  └───┘                    └───┘                    └───┘
    s                                                 f
```

Node 0 is the start (position before `>`), node 1 is the position
between the two `>` characters, and node 2 is the final position. The
direct edge 0 → 2 represents the `GtGt` tokenization; the two-hop path
0 → 1 → 2 represents the `Gt Gt` tokenization.

---

## 3. Properties of Token Lattices

### 3.1 Topological Ordering

**Theorem (Topological ordering by construction):** The node index
ordering 0, 1, ..., N is a valid topological order for L.

*Proof.* Let (u, v, t, σ) be any edge in E. By the DAG constraint,
v > u. Therefore u precedes v in the natural index ordering. Since this
holds for every edge, the index ordering is a topological order. □

This property is critical: it allows all DP algorithms (Viterbi,
forward-backward) to process nodes in index order without computing an
explicit topological sort, reducing overhead by O(|V| + |E|).

### 3.2 Paths and Path Weight

A **path** π = (e₁, e₂, ..., eₖ) in L is a sequence of edges where
the target of eᵢ equals the source of eᵢ₊₁. The **path weight** is:

```
w(π) = w(e₁) ⊗ w(e₂) ⊗ ··· ⊗ w(eₖ)
```

Under TropicalWeight, this is ordinary addition:

```
w(π) = w(e₁) + w(e₂) + ··· + w(eₖ)
```

A path from s to f represents one complete tokenization of the input.

### 3.3 Lattice Weight

The **lattice weight** (or string weight) ‖L‖ is the ⊕-combination of
all s→f path weights:

```
‖L‖ = ⊕ { w(π) : π is an s→f path in L }
```

Under TropicalWeight, ‖L‖ is the minimum-cost tokenization. Under
LogWeight, ‖L‖ is the total probability of all tokenizations (the
partition function). This corresponds to the WFST string weight
‖M‖(x) from [weighted-automata.md](weighted-automata.md) §2.2, where
the lattice is viewed as a single-string WFST accepting one input string
with multiple transduction paths.

---

## 4. The Linear Degenerate Case

### 4.1 Definition

A token lattice L is **linear** (or **degenerate**) if every node has at
most one outgoing edge:

```
∀ v ∈ V : |{ e ∈ E : source(e) = v }| ≤ 1
```

In a linear lattice, there is exactly one s→f path (or no path if f is
unreachable). The lattice degenerates to a chain:

```
  ┌───┐  t₁  ┌───┐  t₂  ┌───┐       tₙ  ┌───┐
  │ 0 │ ────►│ 1 │ ────►│ 2 │ ··· ────►│ N │
  └───┘      └───┘      └───┘          └───┘
```

### 4.2 Zero-Overhead Principle

The overwhelming majority of programming language inputs have
unambiguous tokenization. PraTTaIL encodes this via `TokenSource::Linear`,
which stores a flat `Vec<(T, S)>` with no DAG overhead. The lattice
data structure is only allocated when actual lexical ambiguity is detected.

This maps to the formal observation: if the lattice is linear, path
extraction is trivial (the unique path IS the token vector), Viterbi
reduces to identity, and the path weight is just the ⊗-product of all
edge weights — which is 1̄ when all edges carry unit weight.

### 4.3 Relationship to TokenSource

In PraTTaIL's type system:

| Formal condition   | Runtime type           | Overhead |
|:-------------------|:-----------------------|:---------|
| Linear lattice     | `TokenSource::Linear`  | Zero     |
| Non-linear lattice | `TokenSource::Lattice` | O(\|E\|) |

The `resolve()` method branches once on the variant, not per-token.

---

## 5. Viterbi Algorithm on Lattice DAGs

### 5.1 Problem Statement

Given a token lattice L = (V, E, s, f, w) over an idempotent semiring
S, find the minimum-weight path from s to f:

```
π* = argmin { w(π) : π is an s→f path in L }
          π
```

Under TropicalWeight, this is the classical shortest-path problem on a
DAG.

### 5.2 DP Recurrence

Define the **forward distance** α[v] as the minimum weight of any path
from s to v:

```
α[s] = 1̄
α[v] = ⊕ { α[u] ⊗ w(u, v) : (u, v) ∈ E }    for v ≠ s
```

Under TropicalWeight:

```
α[0] = 0.0
α[v] = min { α[u] + w(u, v) : (u, v) ∈ E }
```

The optimal path weight is α[f].

### 5.3 Correctness Theorem

**Theorem (Viterbi correctness on DAGs):** A single left-to-right pass
over the nodes of L, processing each node v in index order and relaxing
all outgoing edges of v, correctly computes α[v] for all v ∈ V.

*Proof.* We show by induction on v that α[v] is correctly computed when
node v is processed.

**Base case:** v = 0 = s. We initialize α[0] = 1̄, which is correct
since the zero-length path from s to s has weight 1̄ (the multiplicative
identity).

**Inductive step:** Assume α[u] is correctly computed for all u < v.
When we process node v, we compute:

```
α[v] = ⊕ { α[u] ⊗ w(u, v) : (u, v) ∈ E }
```

By the DAG constraint, every edge (u, v) ∈ E has u < v, so α[u] is
already finalized by the inductive hypothesis. The ⊕-combination of all
predecessor contributions gives the correct forward distance for v.

**Complexity:** Each node is visited exactly once and each edge is
relaxed exactly once, giving O(|V| + |E|) time. The distance and
predecessor arrays occupy O(|V|) space. □

### 5.4 Backtrace

To reconstruct the optimal path (not just its weight), we maintain a
**predecessor array** pred[v] = (u*, idx*), where u* is the node and
idx* is the edge index that achieved the minimum:

```
pred[v] = argmin { α[u] ⊗ w(u, v) }
           (u, idx)
```

After the forward pass, we trace back from f:

```
path = []
current = f
while pred[current] is not None:
    (u, idx) = pred[current]
    path.prepend(edges[u][idx])
    current = u
```

This stores `(node, edge_index)` pairs rather than cloning token/span
data, avoiding allocation during the forward pass.

### 5.5 Worked Example

Consider a 5-node lattice for the arithmetic expression `1 + 2`:

```
       Int(w=0.0)     Plus(w=0.0)     Int(w=0.0)     Eof(w=0.0)
  ┌───┐ ──────────►┌───┐ ──────────►┌───┐ ──────────►┌───┐ ──────────►┌───┐
  │ 0 │            │ 1 │            │ 2 │            │ 3 │            │ 4 │
  └───┘            └───┘            └───┘            └───┘            └───┘
    │                                  ▲
    │          Num12(w=2.0)            │
    └──────────────────────────────────┘
```

The alternative edge 0 → 2 with token `Num12` (weight 2.0) represents a
hypothetical tokenization where "1+" is a single numeric literal. Viterbi
traces:

| Step | Node | α[v] | pred[v] | Note                              |
|:----:|:----:|:----:|:-------:|:----------------------------------|
|  0   |  0   | 0.0  |    —    | Start                             |
|  1   |  1   | 0.0  | (0, 0)  | via Int(0.0): 0.0 + 0.0 = 0.0     |
|  2   |  2   | 0.0  | (1, 0)  | via Plus(0.0): 0.0 + 0.0 = 0.0    |
|      |      |      |         | Num12 path: 0.0 + 2.0 = 2.0 > 0.0 |
|  3   |  3   | 0.0  | (2, 0)  | via Int(0.0): 0.0 + 0.0 = 0.0     |
|  4   |  4   | 0.0  | (3, 0)  | via Eof(0.0): 0.0 + 0.0 = 0.0     |

**Result:** α[4] = 0.0. Backtrace: 4←3←2←1←0, yielding
`[Int, Plus, Int, Eof]` with total weight 0.0.

The Num12 alternative (weight 2.0) is correctly rejected because the
canonical tokenization has lower total weight.

#### Wavefront Propagation Visual

The same computation visualized as a left-to-right wavefront:

```
Step 0:       Step 1:       Step 2:       Step 3:       Step 4:
▓░░░░         ▓▓░░░         ▓▓▓░░         ▓▓▓▓░         ▓▓▓▓▓
0 1 2 3 4     0 1 2 3 4     0 1 2 3 4     0 1 2 3 4     0 1 2 3 4
^               ^               ^               ^               ^
α[0]=0.0      α[1]=0.0      α[2]=0.0      α[3]=0.0      α[4]=0.0
              Int(0.0)      Plus(0.0)     Int(0.0)      Eof(0.0)
                            Num12: 2.0
                            rejected!

▓ = finalized    ░ = pending
```

At step 2, node 2 receives two contributions: the canonical path
(0→1→2 via Int+Plus, cost 0.0) and the alternative (0→2 via Num12,
cost 2.0). The ⊕ = min operation selects 0.0, finalizing node 2 and
effectively discarding the Num12 hypothesis.

### 5.6 Generic Viterbi

PraTTaIL provides `viterbi_generic<W: Semiring + Ord>()`, which runs
the same DP algorithm for any semiring satisfying:

1. **W: Semiring** — provides `zero()`, `one()`, `plus()`, `times()`
2. **W: Ord** — needed for the `new_dist < dist[target]` comparison
3. **`zero()` is the largest element under Ord** — so unvisited nodes
   compare as "worse" than any reachable distance

This holds for `TropicalWeight` (+∞), `EditWeight` (u32::MAX), and
`ProductWeight<TropicalWeight, EditWeight>` (lexicographic with +∞
first). It does **not** hold for `CountingWeight` (zero = 0 is the
smallest), because CountingWeight's zero() is the smallest element
under Ord, making the algorithm unable to distinguish "unreachable"
from "zero derivations." CountingWeight should be used via
`ProductWeight` composition or forward-backward, not standalone Viterbi.

---

## 6. Beam-Pruned Viterbi

### 6.1 Motivation

Error recovery can produce large lattices with many repair alternatives.
Full Viterbi processes every node and edge, which is wasteful when most
paths are far from optimal. Beam pruning skips provably suboptimal
nodes and edges during the forward pass.

### 6.2 Algorithm

Given a beam width B (a TropicalWeight value), the beam-pruned Viterbi
modifies the forward pass with two pruning rules:

**Node-level pruning:** Skip node v if:

```
α[v] > α_best_final + B
```

where α_best_final is the best distance to f found so far (or +∞ if f
is not yet reached).

**Edge-level pruning:** For edge (v, u) with candidate distance d =
α[v] ⊗ w(v, u), skip if:

```
d > α_best_final + B
```

Both checks are no-ops when α_best_final = +∞ (no path to f yet), so
the algorithm starts as exact Viterbi and progressively tightens.

### 6.3 Progressive Tightening

As the forward pass proceeds, any path reaching f updates α_best_final:

```
if target == f and new_dist < α_best_final:
    α_best_final = new_dist
```

This means:

1. **Early in the pass:** α_best_final = +∞, no pruning occurs.
2. **After first path reaches f:** α_best_final = w(π₁), enabling pruning.
3. **As better paths arrive:** α_best_final decreases, beam tightens.

```
  ┌─────────────────────────────────────────────────────┐
  │  Weight axis                                        │
  │                                                     │
  │  ─ ─ ─ ─ ─ ─ α_best_final + B ─ ─ ─ ─ ─ ─ beam      │
  │                    ┌─────────────────────┐ ceiling  │
  │                    │   PRUNED REGION     │          │
  │  ══════════════════╪═════════════════════╪════════  │
  │                    │   EXPLORED REGION   │          │
  │  ──────────────────┘─────────────────────┘────────  │
  │  α_best_final                                       │
  │                                                     │
  │  Node axis:   0    1    2    ...   f                │
  └─────────────────────────────────────────────────────┘
```

Nodes and edges above the beam ceiling are never processed.

### 6.4 Soundness Theorem

**Theorem (Beam soundness):** Beam pruning never discards the optimal
path. That is, if π* is the minimum-weight s→f path in L, then
beam-pruned Viterbi returns π* (assuming it exists).

*Proof.* Let w* = w(π*) be the optimal path weight. We show that no
node or edge on π* is ever pruned.

Consider any node v on the optimal path. Since v lies on π*, the
partial weight from s to v along π* is α*[v] ≤ w* (partial weight
cannot exceed total path weight under TropicalWeight where all weights
are non-negative).

At any point during the algorithm, α_best_final ≥ w* (the best known
final distance is at least as large as the true optimum, since we may
not have found the optimal path yet, or we have found it exactly).

Therefore:

```
α[v] ≤ α*[v] ≤ w* ≤ α_best_final ≤ α_best_final + B
```

The node-level pruning condition α[v] > α_best_final + B is not
satisfied, so v is not pruned. The same argument applies edge-by-edge
along π*. □

**Corollary:** Setting B = None (no beam) yields exact Viterbi. Setting
B = 0 yields greedy search (only the single best path explored). The
default B = 3.0 provides a good trade-off for error recovery lattices.

---

## 7. N-Best Path Extraction

### 7.1 Problem Statement

Given a token lattice L and an integer N ≥ 1, find the N minimum-weight
s→f paths, sorted by ascending weight:

```
π₁, π₂, ..., πN    where w(π₁) ≤ w(π₂) ≤ ··· ≤ w(πN)
```

This is useful for error recovery (try multiple tokenizations) and
N-best output (return ranked alternatives to the user).

### 7.2 Heap-Based Algorithm

PraTTaIL uses a simplified heap-based approach (a specialization of
Eppstein's k-shortest-paths algorithm for DAGs):

```
HEAP ← min-heap ordered by weight
push (weight=1̄, node=s, path=[]) onto HEAP
results ← []

while HEAP is not empty and |results| < N:
    (w, v, path) ← pop minimum from HEAP
    if v == f:
        results.append((path, w))
        continue
    for each edge (v, u, t, σ) in edges_from(v):
        push (w ⊗ w(e), u, path ++ [(v, edge_idx)]) onto HEAP

return results
```

The heap expansion tree for the `>>` lattice with N=3:

```
  pop(0.0, node=0, [])
  ├── push(0.0, node=2, [(0,0)])  ← GtGt edge
  └── push(1.0, node=1, [(0,1)])  ← Gt edge
       │
  pop(0.0, node=2, [(0,0)])  → RESULT 1: [GtGt], w=0.0
       │
  pop(1.0, node=1, [(0,1)])
  └── push(2.0, node=2, [(0,1),(1,0)])  ← Gt edge
       │
  pop(2.0, node=2, [(0,1),(1,0)])  → RESULT 2: [Gt,Gt], w=2.0
```

### 7.3 Safety Bound

To prevent combinatorial explosion on pathological lattices, PraTTaIL
imposes a maximum number of explored states:

```
max_explored = N × |V| × 4
```

This bounds the total work. If the limit is reached, the algorithm
returns whatever results have been collected so far.

### 7.4 Complexity

In the worst case, the heap may contain O(N × |E|) entries. Each
heap operation takes O(log(N × |E|)) time. The overall complexity is:

```
O(N × |E| × log(N × |E|))
```

For typical parser recovery lattices (|V| < 50, |E| < 100, N ≤ 10),
this is negligible.

---

## 8. Forward-Backward on Lattices

The forward-backward algorithm computes the total probability of each
edge, enabling weight training. It operates under the LogWeight semiring
(feature `wfst-log`). See [viterbi-and-forward-backward.md](viterbi-and-forward-backward.md)
§§5–7 for the full treatment; this section summarizes the lattice-specific
aspects.

### 8.1 Forward Scores

The forward score α[v] is the log-sum-exp of all path weights from s
to v:

```
α[s] = 1̄ = 0.0                   (log-probability 1)
α[v] = ⊕ { α[u] ⊗ w(u, v) }    (⊕ = log-sum-exp, ⊗ = addition)
```

Computed in a single left-to-right pass (same DAG ordering as Viterbi).

### 8.2 Backward Scores

The backward score β[u] is the log-sum-exp of all path weights from u
to f:

```
β[f] = 1̄ = 0.0
β[u] = ⊕ { w(u, v) ⊗ β[v] }    (computed right-to-left)
```

### 8.3 Arc Posterior

The posterior probability of edge e = (u, v) is:

```
P(e) = exp(−(α[u] ⊗ w(e) ⊗ β[v] − Z))
```

where Z = α[f] is the partition function (total log-probability of all
s→f paths). Edges with high posterior are important for the final parse;
edges with low posterior can be pruned or down-weighted during training.

#### Worked Example: Arc Posteriors for the `>>` Lattice

Consider the 3-node lattice from §2.3:

```
Edges:
  A: 0→2 GtGt (w=0.0)
  B: 0→1 Gt   (w=1.0)
  C: 1→2 Gt   (w=1.0)
```

Under LogWeight (⊕ = log-sum-exp, ⊗ = addition):

```
Forward scores:
  α[0] = 0.0
  α[1] = α[0] + w(B) = 0.0 + 1.0 = 1.0
  α[2] = logsumexp(α[0] + w(A), α[1] + w(C))
       = logsumexp(0.0, 2.0)
       = −ln(e⁻⁰·⁰ + e⁻²·⁰)
       = −ln(1.0 + 0.135)
       ≈ −ln(1.135) ≈ −0.127

  (Using the convention where logsumexp(a,b) = −ln(e⁻ᵃ + e⁻ᵇ).)
  So α[2] ≈ −0.127.

Backward scores:
  β[2] = 0.0
  β[1] = w(C) + β[2] = 1.0 + 0.0 = 1.0
  β[0] = logsumexp(w(A) + β[2], w(B) + β[1])
       = logsumexp(0.0, 2.0) ≈ −0.127

Identity check: α[2] = β[0] ≈ −0.127  ✓

Partition function: Z = α[2] ≈ −0.127

Edge scores (α[u] + w(e) + β[v]):
  score(A) = α[0] + w(A) + β[2] = 0.0 + 0.0 + 0.0 = 0.0
  score(B) = α[0] + w(B) + β[1] = 0.0 + 1.0 + 1.0 = 2.0
  score(C) = α[1] + w(C) + β[2] = 1.0 + 1.0 + 0.0 = 2.0

Arc posteriors:
  P(A) = exp(−score(A)) / exp(−Z)
       = exp(−0.0) / exp(0.127)
       = 1.0 / 1.135
       ≈ 0.881

  P(B) = exp(−2.0) / exp(0.127)
       = 0.135 / 1.135
       ≈ 0.119

  P(C) = exp(−2.0) / exp(0.127) ≈ 0.119

Check: paths GtGt and Gt+Gt partition the probability:
  P(path GtGt) = P(A)    ≈ 0.881
  P(path Gt+Gt) = P(B) = P(C) ≈ 0.119
  Total ≈ 1.0  ✓
```

**Interpretation:** The `GtGt` path carries ~88% of probability mass;
the `Gt Gt` path carries ~12%. The parser strongly prefers the
single-token reading. During weight training, gradient updates would
reinforce whichever reading matches the oracle parse.

---

## 9. Relationship to Classical NLP Lattices

### 9.1 Speech Recognition Word Lattices

Speech recognizers produce **word lattices** (Murveit et al. 1993) where
nodes are time points in the audio signal and edges are word hypotheses
with acoustic + language model scores. PraTTaIL's token lattice is the
text analogue: nodes are character positions and edges are token
hypotheses with lexer-priority weights.

The algorithmic infrastructure is identical: Viterbi for best-path
decoding, forward-backward for posterior computation, and beam pruning
for efficiency. The semiring framework unifies both domains.

### 9.2 Chinese Word Segmentation Lattices

Chinese text has no whitespace between words, making segmentation
ambiguous. Zhang & Clark (2011) represent all possible segmentations as
a lattice and use Viterbi decoding with a learned model. PraTTaIL's
token lattice solves an analogous problem for programming languages where
operator tokenization is ambiguous (e.g., `>>`, `->>`).

### 9.3 Morphological Analysis Lattices

Goldberg & Tsarfaty (2008) propose a single lattice framework for joint
word segmentation and POS tagging in morphologically rich languages
(Hebrew, Arabic). Their lattice edges carry both a word hypothesis and a
POS tag. PraTTaIL's lattice edges carry both a token variant and a span,
with the semiring weight encoding preference strength.

### 9.4 Feature Comparison Table

| Feature             |  PraTTaIL Lattice  | Speech Word Lattice | Chinese Segmentation |     Morphological      |
|:--------------------|:------------------:|:-------------------:|:--------------------:|:----------------------:|
| Nodes               |   char positions   |     time points     |    char positions    |     char positions     |
| Edges               |  token hypotheses  |   word hypotheses   |   word hypotheses    |     morpheme + POS     |
| Weight              | dispatch priority  |    acoustic + LM    |    learned model     |   joint probability    |
| Typical size        |     5–50 nodes     |    100–10K nodes    |     10–200 nodes     |      10–100 nodes      |
| Ambiguity source    |  operator overlap  | acoustic confusion  |    no whitespace     | morphological richness |
| Resolution          | Viterbi (tropical) | Viterbi (tropical)  |  Viterbi (learned)   |       joint CRF        |
| Semirings available |      10 types      |    typically 1–2    |          1           |           1            |
| Training            | wfst-log (planned) | EM / discriminative |    discriminative    |          CRF           |

PraTTaIL's lattice is distinguished by its multi-semiring framework:
the same lattice structure supports ten different semiring types, each
providing a different optimization objective. Speech and NLP lattices
typically use one or two fixed weight types.

### 9.5 Disambiguation of Terminology

The word "lattice" in this document refers to a **graph-theoretic
lattice** — a weighted directed acyclic graph with a designated start
and final node. This is **unrelated** to the order-theoretic concept of
a lattice (a partially ordered set with meet and join operations).

The graph-theoretic usage originates from the speech recognition
community (Murveit et al. 1993) and has become standard in NLP. PraTTaIL
follows this convention. If order-theoretic lattices are needed elsewhere
in the codebase (e.g., for type inference), they should be given a
distinct name (e.g., `PartialOrderLattice`) to avoid confusion.

For the formal order-theoretic treatment of lattices (partial orders, meet,
join, bounded distributive lattices), see
[Mathematical Foundations: Order Theory](../foundations/01-order-theory.md).

---

## 10. References

1. **Mohri, M.** (2002). Semiring frameworks and algorithms for
   shortest-distance problems. *Journal of Automata, Languages and
   Combinatorics*, 7(3), 321–350.

2. **Mohri, M., Pereira, F., & Riley, M.** (2008). Speech recognition
   with weighted finite-state transducers. In *Springer Handbook of
   Speech Processing* (pp. 559–584). Springer.

3. **Murveit, H., Butzberger, J., Digalakis, V., & Weintraub, M.**
   (1993). Large-vocabulary dictation using SRI's DECIPHER speech
   recognition system: Progressive search techniques. *ICASSP-93*.

4. **Goldberg, Y., & Tsarfaty, R.** (2008). A single generative model
   for joint morphological segmentation and syntactic parsing.
   *ACL 2008*, 371–379.

5. **Zhang, Y., & Clark, S.** (2011). Syntactic processing using the
   generalized perceptron and beam search. *Computational Linguistics*,
   37(1), 105–151.

6. **Eppstein, D.** (1998). Finding the k shortest paths. *SIAM Journal
   on Computing*, 28(2), 652–673.

---

## 11. Source Reference

| Concept                    | File                       | Lines/Function                           |
|:---------------------------|:---------------------------|:-----------------------------------------|
| TokenSource enum           | `src/lattice.rs`           | `TokenSource<T, S>` (line 51)            |
| TokenLattice struct        | `src/lattice.rs`           | `TokenLattice<T, S, W>` (line 240)       |
| LatticeEdge struct         | `src/lattice.rs`           | `LatticeEdge<T, S, W>` (line 247)        |
| ViterbiPath struct         | `src/lattice.rs`           | `ViterbiPath<T, S, W>` (line 343)        |
| Viterbi (tropical, beam)   | `src/lattice.rs`           | `viterbi_best_path_beam()` (line 371)    |
| Viterbi (generic semiring) | `src/lattice.rs`           | `viterbi_generic()` (line 484)           |
| Linear→Lattice conversion  | `src/lattice.rs`           | `linear_to_lattice()` (line 546)         |
| Generic conversion         | `src/lattice.rs`           | `linear_to_lattice_generic()` (line 562) |
| N-best paths               | `src/lattice.rs`           | `n_best_paths()` (line 598)              |
| Alternative paths          | `src/lattice.rs`           | `alternative_paths()` (line 708)         |
| Semiring trait             | `src/automata/semiring.rs` | `Semiring` (line 36)                     |
| TropicalWeight             | `src/automata/semiring.rs` | `TropicalWeight` (line 68)               |

---

## 12. Cross-References

- [Semirings](semirings.md) — Semiring axioms, all ten concrete types
- [Weighted Automata](weighted-automata.md) — WFST structure, string weight
- [Viterbi and Forward-Backward](viterbi-and-forward-backward.md) — Full algorithm details
- [Token Lattice Design](../../design/wfst/token-lattices.md) — Implementation decisions
- [Token Lattice Architecture](../../architecture/wfst/token-lattices.md) — Pipeline integration
- [Error Recovery](../../design/wfst/error-recovery.md) — Recovery WFST and lattice recovery
- [Per-semiring documents](semirings/) — Detailed theory for each semiring type
- [Stream-to-Lattice Conversion](stream-to-lattice.md) — Pedagogical guide to all seven conversion points and five implicit lattice structures
