# Bottleneck Semiring: ComplexityWeight

> **Date**: 2026-03-01
> **Source**: `prattail/src/automata/semiring.rs`, lines 760--888
> **Carrier**: `ComplexityWeight(u32)` -- discrete lookahead depth / parsing effort

---

## Table of Contents

1. [Intuition & Motivation](#1-intuition--motivation)
2. [Formal Definition](#2-formal-definition)
3. [Semiring Axiom Verification](#3-semiring-axiom-verification)
4. [Key Properties](#4-key-properties)
5. [Connection to Bottleneck Path Problems](#5-connection-to-bottleneck-path-problems)
6. [Interpretation for Parsing](#6-interpretation-for-parsing)
7. [Worked Example: Dispatch Graph](#7-worked-example-dispatch-graph)
8. [Product Composition: Tropical x Complexity](#8-product-composition-tropical-x-complexity)
9. [Complexity Analysis](#9-complexity-analysis)
10. [Rust Implementation](#10-rust-implementation)
11. [Integration into PraTTaIL](#11-integration-into-prattail)
12. [Source Reference & See Also](#12-source-reference--see-also)

---

## 1. Intuition & Motivation

The bottleneck semiring answers the question: *what is the hardest
decision point on the easiest path?*

In a weighted parser, each dispatch point has a complexity: a
deterministic dispatch (unique FIRST-set token) requires zero
lookahead, a single-token ambiguity requires one token of lookahead,
and a deeply ambiguous point may require multiple tokens of lookahead
or full backtracking. When choosing among alternative parse paths,
the parser wants the path whose *worst decision point* is as simple
as possible.

This is the classical **bottleneck path** problem from graph theory,
and the algebraic structure that solves it is the bottleneck semiring
-- also known as the min-max semiring. The two operations map
directly to parsing decisions:

- **Selecting among alternatives** (parallel paths) uses `min` --
  the best alternative is the one whose bottleneck is least complex.
- **Chaining sequential segments** (a path through multiple arcs)
  uses `max` -- the bottleneck of a path is its most complex segment.

```
lower complexity  =  more deterministic  =  preferred
```

A deterministic dispatch point (complexity 0) is preferred over a
single-token lookahead (complexity 1), which is preferred over a
3-token lookahead (complexity 3). An unreachable path carries
complexity infinity and is never selected.

Unlike TropicalWeight, where costs *accumulate* along a path (a path
through two weight-2.0 arcs costs 4.0), ComplexityWeight *bottlenecks*
-- a path through two complexity-2 arcs has complexity 2, not 4. This
captures the real-world semantics: a parser that must perform 3-token
lookahead at one point and 1-token lookahead at another point needs a
lookahead budget of 3, not 4.

### Bottleneck Pipe Metaphor

Think of a parse path as a sequence of pipe segments with varying widths,
where the width represents how deterministic each dispatch point is.
Overall throughput (parsing ease) is limited by the narrowest segment:

```
  ComplexityWeight: throughput = narrowest pipe = max(complexity)

    ╔════════╗   ╔══╗   ╔══════╗   ╔═══════════════╗
    ║ wide   ║───║  ║───║ med  ║───║    wide       ║
    ║ (c=0)  ║   ║  ║   ║(c=1) ║   ║   (c=0)      ║
    ╚════════╝   ║  ║   ╚══════╝   ╚═══════════════╝
                 ║  ║ ← bottleneck! (c=3)
                 ╚══╝

    Path complexity = max(0, 3, 1, 0) = 3
    Lookahead budget needed: 3 tokens

  Contrast with TropicalWeight: cost = sum of all segments

    ╔════════╗   ╔══╗   ╔══════╗   ╔═══════════════╗
    ║  1.0   ║───║  ║───║ 0.5  ║───║     2.0       ║
    ╚════════╝   ║  ║   ╚══════╝   ╚═══════════════╝
                 ║  ║
                 ╚══╝ 3.0

    Path cost = 1.0 + 3.0 + 0.5 + 2.0 = 6.5   (costs accumulate)
```

The bottleneck semantics mean that adding a trivially deterministic segment
(complexity 0) to a path never increases its overall complexity — the
narrowest pipe stays the same. This is the correct model for lookahead
budget: a parser needs enough buffer for its hardest decision, and easy
decisions consume no additional budget.

---

## 2. Formal Definition

The bottleneck semiring is the algebraic structure

```
B  =  ( N ∪ {∞},  min,  max,  ∞,  0 )
```

where:

| Component        | Symbol | Concrete value      | Meaning                                 |
|------------------|--------|---------------------|-----------------------------------------|
| Carrier set      | K      | N ∪ {∞}             | Non-negative integers plus infinity     |
| Addition (⊕)     | min    | min(a, b)           | Select least-complex alternative        |
| Multiplication (⊗)| max   | max(a, b)           | Bottleneck: path complexity = worst segment |
| Additive identity (0̄) | ∞ | `u32::MAX`          | Unreachable path (identity for min)     |
| Multiplicative identity (1̄) | 0 | `0_u32`       | Zero complexity (identity for max)      |

The name "bottleneck" comes from the max operation along a path: the
overall path complexity is determined by its most complex (highest)
segment, just as the throughput of a pipeline is determined by its
narrowest bottleneck.

---

## 3. Semiring Axiom Verification

We verify all nine properties (eight semiring axioms plus
idempotency) with concrete numerical examples. Let a = 2, b = 5,
c = 7.

### (A1) Associativity of ⊕

```
(a ⊕ b) ⊕ c  =  min(min(2, 5), 7)  =  min(2, 7)  =  2
a ⊕ (b ⊕ c)  =  min(2, min(5, 7))  =  min(2, 5)  =  2   ✓
```

**General proof.** For all x, y, z in N ∪ {∞}, consider cases on
the relative ordering. Without loss of generality, assume x ≤ y ≤ z
(the total order on N ∪ {∞} is well-defined). Then:

```
min(min(x, y), z)  =  min(x, z)  =  x
min(x, min(y, z))  =  min(x, y)  =  x
```

Both reduce to the minimum element. Since this holds for all
permutations of the ordering, min is associative over any totally
ordered set.   ∎

### (A2) Commutativity of ⊕

```
a ⊕ b  =  min(2, 5)  =  2
b ⊕ a  =  min(5, 2)  =  2   ✓
```

**General proof.** For all x, y in N ∪ {∞}: min(x, y) = min(y, x)
because the minimum of two elements does not depend on the order in
which they are presented. Formally, min(x, y) = x if x ≤ y and
min(x, y) = y if y < x; in both cases the result is the same
regardless of argument order.   ∎

### (A3) ⊕ Identity

```
0̄ ⊕ a  =  min(∞, 2)  =  2  =  a   ✓
a ⊕ 0̄  =  min(2, ∞)  =  2  =  a   ✓
```

**General proof.** For all x in N ∪ {∞}: x ≤ ∞ (since ∞ is the
maximum element of the carrier set), so min(∞, x) = min(x, ∞) = x.
Therefore ∞ is the two-sided identity for min.   ∎

### (M1) Associativity of ⊗

```
(a ⊗ b) ⊗ c  =  max(max(2, 5), 7)  =  max(5, 7)  =  7
a ⊗ (b ⊗ c)  =  max(2, max(5, 7))  =  max(2, 7)  =  7   ✓
```

**General proof.** Symmetric to (A1). For all x, y, z in N ∪ {∞},
assume without loss of generality x ≤ y ≤ z. Then:

```
max(max(x, y), z)  =  max(y, z)  =  z
max(x, max(y, z))  =  max(x, z)  =  z
```

Both reduce to the maximum element. Since this holds for all
orderings, max is associative over any totally ordered set.   ∎

### (M2) ⊗ Identity

```
1̄ ⊗ a  =  max(0, 2)  =  2  =  a   ✓
a ⊗ 1̄  =  max(2, 0)  =  2  =  a   ✓
```

**General proof.** For all x in N ∪ {∞}: x ≥ 0 (since 0 is the
minimum element of N ∪ {∞}), so max(0, x) = max(x, 0) = x.
Therefore 0 is the two-sided identity for max.   ∎

### (D1) Left Distributivity: ⊗ distributes over ⊕ from the left

```
a ⊗ (b ⊕ c)  =  max(2, min(5, 7))  =  max(2, 5)  =  5
(a ⊗ b) ⊕ (a ⊗ c)  =  min(max(2, 5), max(2, 7))  =  min(5, 7)  =  5   ✓
```

**General proof.** We must show that for all x, y, z in N ∪ {∞}:

```
max(x, min(y, z))  =  min(max(x, y), max(x, z))
```

This is the **lattice distributivity law**: in any totally ordered
set, max distributes over min (and vice versa). The proof proceeds
by case analysis.

*Case 1: x ≤ y ≤ z.*
- LHS: max(x, min(y, z)) = max(x, y) = y
- RHS: min(max(x, y), max(x, z)) = min(y, z) = y   ✓

*Case 2: y ≤ x ≤ z.*
- LHS: max(x, min(y, z)) = max(x, y) = x
- RHS: min(max(x, y), max(x, z)) = min(x, z) = x   ✓

*Case 3: y ≤ z ≤ x.*
- LHS: max(x, min(y, z)) = max(x, y) = x
- RHS: min(max(x, y), max(x, z)) = min(x, x) = x   ✓

*Case 4: x ≤ z ≤ y.*
- LHS: max(x, min(y, z)) = max(x, z) = z
- RHS: min(max(x, y), max(x, z)) = min(y, z) = z   ✓

*Case 5: z ≤ x ≤ y.*
- LHS: max(x, min(y, z)) = max(x, z) = x
- RHS: min(max(x, y), max(x, z)) = min(y, x) = x   ✓

*Case 6: z ≤ y ≤ x.*
- LHS: max(x, min(y, z)) = max(x, z) = x
- RHS: min(max(x, y), max(x, z)) = min(x, x) = x   ✓

All six orderings satisfy the identity.   ∎

### (D2) Right Distributivity: ⊗ distributes over ⊕ from the right

```
(a ⊕ b) ⊗ c  =  max(min(2, 5), 7)  =  max(2, 7)  =  7
(a ⊗ c) ⊕ (b ⊗ c)  =  min(max(2, 7), max(5, 7))  =  min(7, 7)  =  7   ✓
```

**General proof.** We must show:

```
max(min(x, y), z)  =  min(max(x, z), max(y, z))
```

By commutativity of max, this reduces to:

```
max(z, min(x, y))  =  min(max(z, x), max(z, y))
```

which is precisely left distributivity (D1) with the variables
relabeled (z for x, x for y, y for z). Since D1 holds for all
elements, D2 holds as well.   ∎

### (Z) Zero Annihilation

```
0̄ ⊗ a  =  max(∞, 2)  =  ∞  =  0̄   ✓
a ⊗ 0̄  =  max(2, ∞)  =  ∞  =  0̄   ✓
```

**General proof.** For all x in N ∪ {∞}: ∞ ≥ x (since ∞ is the
maximum element of the carrier set), so max(∞, x) = max(x, ∞) = ∞.
Therefore ∞ annihilates under max. An unreachable segment (complexity
∞) makes the entire path unreachable.   ∎

### (I) Idempotence of ⊕

```
a ⊕ a  =  min(2, 2)  =  2  =  a   ✓
```

**General proof.** For all x in N ∪ {∞}: min(x, x) = x. The
minimum of any value with itself is that value.   ∎

All eight semiring axioms and idempotence are satisfied. B is a valid
idempotent semiring.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Commutativity of ⊗

**Claim**: The bottleneck semiring is commutative (⊗ is commutative).

**Proof**: For all a, b in N ∪ {∞}:

```
a ⊗ b  =  max(a, b)  =  max(b, a)  =  b ⊗ a
```

The max function is symmetric.   ∎

Commutativity means path complexity is independent of traversal
direction -- the bottleneck of A then B equals the bottleneck of
B then A.

### 4.2 Idempotency of ⊗

**Claim**: The ⊗ operation is also idempotent.

**Proof**: For all a in N ∪ {∞}:

```
a ⊗ a  =  max(a, a)  =  a
```

The maximum of any value with itself is that value.   ∎

Both operations are idempotent, making this a **doubly idempotent
semiring** (also called a *bounded distributive lattice*). This
distinguishes ComplexityWeight from TropicalWeight (where ⊗ = + is
not idempotent: 2 + 2 = 4 /= 2) and from CountingWeight (where ⊕ = +
is not idempotent: 3 + 3 = 6 /= 3).

### 4.3 Lattice Structure

**Claim**: (N ∪ {∞}, min, max) forms a bounded distributive lattice.

**Proof**: We have already verified:

1. **Both operations are associative** (axioms A1, M1).
2. **Both operations are commutative** (axiom A2 and section 4.1).
3. **Both operations are idempotent** (axiom I and section 4.2).
4. **Distributivity holds in both directions** (axioms D1, D2).
5. **The absorption laws hold.** For all a, b in N ∪ {∞}:
   - min(a, max(a, b)) = a. If a ≤ b then max(a, b) = b and
     min(a, b) = a. If a > b then max(a, b) = a and min(a, a) = a.
   - max(a, min(a, b)) = a. If a ≤ b then min(a, b) = a and
     max(a, a) = a. If a > b then min(a, b) = b and max(a, b) = a.
6. **Bounded**: 0 is the bottom (0 ≤ x for all x) and ∞ is the top
   (x ≤ ∞ for all x).

Therefore (N ∪ {∞}, min, max, ∞, 0) is a bounded distributive
lattice, and equivalently a doubly idempotent semiring.   ∎

### 4.4 Total Ordering and Viterbi Compatibility

ComplexityWeight implements `Ord` via the natural ordering on `u32`:

```
0 < 1 < 2 < ... < u32::MAX
```

The zero element `∞` = `u32::MAX` is the *largest* element under
`Ord`. This satisfies the Viterbi invariant:

> `W::zero()` must be the largest element under `Ord`, so that
> unvisited nodes compare as "worse" than any reachable distance.

Therefore ComplexityWeight is Viterbi-compatible: `viterbi_generic`
correctly skips unreachable nodes and selects minimum-complexity
paths.

---

## 5. Connection to Bottleneck Path Problems

### 5.1 Classical Definition

The **bottleneck shortest path problem** (also called the
**minimax path problem** or **widest path problem** in its dual
form) asks: given a weighted directed graph G = (V, E, w) with
non-negative edge weights, find the path from source s to target t
that minimizes the maximum edge weight along the path.

Formally, for a path P = (e₁, e₂, ..., eₖ) where eᵢ in E:

```
bottleneck(P)  =  max(w(e₁), w(e₂), ..., w(eₖ))

optimal path  =  argmin   bottleneck(P)
                  P: s→t
```

This is exactly the optimization problem that the bottleneck semiring
solves: ⊗ = max computes the bottleneck of a path, and ⊕ = min
selects the best (least-bottlenecked) alternative.

### 5.2 Relationship to Other Path Problems

| Problem              | Semiring        | ⊕    | ⊗   | Semantics                     |
|----------------------|-----------------|------|-----|-------------------------------|
| Shortest path        | Tropical        | min  | +   | Minimize total cost           |
| Bottleneck path      | Bottleneck      | min  | max | Minimize worst edge           |
| Widest path          | Max-min         | max  | min | Maximize narrowest edge       |
| Most reliable path   | Probability     | max  | ×   | Maximize product reliability  |
| Counting paths       | Counting        | +    | ×   | Count distinct paths          |

The bottleneck semiring is the *dual* of the widest-path (max-min)
semiring obtained by swapping ⊕ and ⊗. In network routing, the
widest-path problem finds the path with maximum bandwidth
(bottleneck = minimum capacity edge). In parsing, we solve the
dual: find the path with minimum complexity (bottleneck = maximum
lookahead depth edge).

### 5.3 Algorithmic Complexity

The bottleneck shortest path on a DAG can be solved in O(|V| + |E|)
time by a single topological-order relaxation pass -- the same
complexity as Dijkstra on a DAG, and the same Viterbi algorithm
used for TropicalWeight. The key property enabling this is that both
operations (min and max) are monotone and the carrier set is totally
ordered.

---

## 6. Interpretation for Parsing

### 6.1 Complexity Scale

The ComplexityWeight value represents the estimated **lookahead
depth** or **parsing effort** required at a dispatch point:

| Value    | Constant               | Interpretation                                |
|----------|------------------------|-----------------------------------------------|
| 0        | `deterministic()`      | Deterministic dispatch -- no lookahead needed |
| 1        | `single_lookahead()`   | Single-token lookahead resolves ambiguity     |
| n        | `multi_lookahead(n)`   | n-token lookahead required                    |
| ∞ (MAX)  | `infinite()`           | Unreachable path -- no valid derivation       |

### 6.2 Semantic Mapping

Each dispatch point in PraTTaIL's generated parser carries an
implicit complexity level:

| Dispatch Scenario                   | Complexity | Rationale                            |
|-------------------------------------|------------|--------------------------------------|
| Unique token in FIRST set           | 0          | No ambiguity, direct dispatch        |
| Two alternatives, distinct 2nd token | 1         | One lookahead disambiguates          |
| Three alternatives, shared prefix    | 2         | Two lookaheads needed                |
| Cross-category with shared FIRST    | 1--3       | Depends on overlap depth             |
| Unreachable category/token pair     | ∞          | No derivation exists                 |

### 6.3 Applications

**Lookahead budget allocation.** The ComplexityWeight of a dispatch
path tells the parser how much lookahead to allocate. A path with
bottleneck complexity 3 needs at most 3 tokens of lookahead buffer.
Paths with complexity 0 need no buffer at all. This enables
*selective* lookahead: the parser only maintains a lookahead buffer
for the categories that need it.

**Backtrack depth bounding.** When the NFA disambiguation engine
spills alternatives for parallel exploration, the ComplexityWeight
bounds the maximum backtrack depth. A path with bottleneck complexity
n will require at most n tokens of speculative parsing before the
ambiguity is resolved. The parser can set a hard backtrack limit
based on this value.

**B1 selection.** The "B1" strategy in composed dispatch selects the
single best alternative by tropical weight. ComplexityWeight
augments this decision: among alternatives with equal tropical
weight, prefer the one with lower complexity (fewer lookahead
tokens needed). This is achieved via
`ProductWeight<TropicalWeight, ComplexityWeight>`.

---

## 7. Worked Example: Dispatch Graph

Consider a grammar for category `Expr` with three dispatch paths
upon seeing token `Ident`:

```
Path 1 (variable):           q₀ ──0── q₁ ──0── q₃     (deterministic)
Path 2 (function call):      q₀ ──1── q₂ ──2── q₃     (needs lookahead for `(`)
Path 3 (cross-cat from Int): q₀ ──3── q₄ ──1── q₃     (3-token prefix shared)
```

### 7.1 Dispatch Graph Diagram

```
       ┌──────┐    0      ┌──────┐    0      ┌──────────┐
       │      │──────────▶│      │──────────▶│          │
       │      │           │  q₁  │           │          │
       │      │           └──────┘           │          │
       │      │                              │          │
       │  q₀  │    1      ┌──────┐    2      │   q₃     │
       │      │──────────▶│      │──────────▶│ (accept) │
       │      │           │  q₂  │           │          │
       │      │           └──────┘           │          │
       │      │                              │          │
       │      │    3      ┌──────┐    1      │          │
       │      │──────────▶│      │──────────▶│          │
       └──────┘           │  q₄  │           └──────────┘
                          └──────┘
```

### 7.2 Path Bottleneck Computation

**Path 1** (variable reference -- fully deterministic):

```
w₁  =  0 ⊗ 0  =  max(0, 0)  =  0
```

**Path 2** (function call -- needs 2-token lookahead at q₂):

```
w₂  =  1 ⊗ 2  =  max(1, 2)  =  2
```

**Path 3** (cross-category from Int -- 3-token shared prefix):

```
w₃  =  3 ⊗ 1  =  max(3, 1)  =  3
```

### 7.3 Selecting the Best Alternative

```
w*  =  w₁ ⊕ w₂ ⊕ w₃
    =  min(0, min(2, 3))
    =  min(0, 2)
    =  0
```

The parser selects Path 1 (variable reference) because its
bottleneck complexity is 0 -- it is fully deterministic. No
lookahead is needed. Note that unlike TropicalWeight, the
complexity of Path 2 is 2 (its worst segment), not 3 (the sum
of its segments). The bottleneck operation correctly identifies
that Path 2's hardest decision point requires 2-token lookahead,
regardless of how many easy decision points precede it.

### 7.4 Lookahead Budget

If the parser must explore all three paths (e.g., for error
recovery), the required lookahead budget is:

```
budget  =  w₁ ⊕ w₂ ⊕ w₃  =  0    (best path needs 0)
```

But if Path 1 fails and the parser falls back to alternatives:

```
budget  =  w₂ ⊕ w₃  =  min(2, 3)  =  2
```

The parser needs at most 2 tokens of lookahead buffer for the
remaining alternatives.

---

## 8. Product Composition: Tropical x Complexity

### 8.1 Motivation

TropicalWeight alone tells the parser which path has the lowest
accumulated cost but not how much lookahead the path requires.
ComplexityWeight alone tells the parser the maximum lookahead depth
but not the path priority. The product
`ProductWeight<TropicalWeight, ComplexityWeight>` captures both
simultaneously.

### 8.2 Structure

```
ProductWeight<TropicalWeight, ComplexityWeight>
  =  ( (R⁺ ∪ {+∞}) × (N ∪ {∞}),  ⊕,  ⊗,  0,  1 )

where:
  ⊕  :  (a₁, a₂) ⊕ (b₁, b₂)  =  (min(a₁, b₁),  min(a₂, b₂))
  ⊗  :  (a₁, a₂) ⊗ (b₁, b₂)  =  (a₁ + b₁,       max(a₂, b₂))
  0  =  (+∞, ∞)
  1  =  (0.0, 0)
```

The tropical component accumulates path cost via addition; the
complexity component bottlenecks via max. When selecting alternatives,
both components use min independently.

### 8.3 Worked Example

Consider two dispatch paths for token `Ident` in category `Proc`:

```
Path A: cross-category cast (priority 0.5, 2-token lookahead)
    weight: (0.5, 2)

Path B: own-category variable (priority 2.0, deterministic)
    weight: (2.0, 0)
```

**Selecting the best alternative (⊕):**

```
(0.5, 2) ⊕ (2.0, 0)
  = (min(0.5, 2.0), min(2, 0))
  = (0.5, 0)
```

Under component-wise ⊕, the result says: the best priority is 0.5
and the least complexity is 0. Note that ⊕ selects independently
in each component -- it does not indicate which single path achieves
both.

**Sequencing two segments (⊗):**

```
(0.5, 2) ⊗ (1.0, 1)
  = (0.5 + 1.0, max(2, 1))
  = (1.5, 2)
```

The accumulated tropical cost is 1.5; the bottleneck complexity
remains 2 (the harder of the two segments).

### 8.4 Lexicographic Ordering for Viterbi

The `Ord` implementation on `ProductWeight` uses lexicographic
ordering: compare the tropical (left) component first, break ties
with the complexity (right) component.

```
(0.5, 2) < (2.0, 0)     because 0.5 < 2.0 (tropical dominates)
(1.0, 2) < (1.0, 5)     because 1.0 = 1.0, then 2 < 5
```

This means Viterbi selects the lowest-cost path first; among
equal-cost paths, it prefers the one with lower complexity
(fewer lookahead tokens needed).

### 8.5 Viterbi Compatibility

The zero element is (+∞, u32::MAX), which is the largest element
under lexicographic ordering (since +∞ is the largest f64 and
u32::MAX is the largest u32). The Viterbi invariant is satisfied.

---

## 9. Complexity Analysis

All ComplexityWeight operations are O(1) integer operations:

| Operation           | Implementation         | Cost   |
|---------------------|------------------------|--------|
| `plus(a, b)`        | `u32::min(a, b)`       | O(1)   |
| `times(a, b)`       | `u32::max(a, b)`       | O(1)   |
| `is_zero(a)`        | `a == u32::MAX`        | O(1)   |
| `is_one(a)`         | `a == 0`               | O(1)   |
| `cmp(a, b)`         | `u32::cmp(a, b)`       | O(1)   |

Both `min` and `max` on `u32` compile to a single conditional-move
instruction (`cmov`) on x86-64, making them branch-free. There is
no floating-point arithmetic, no saturation concern (u32 suffices
for any realistic lookahead depth), and no overflow risk.

**Space**: 4 bytes per weight (one `u32`). Half the size of
TropicalWeight (8 bytes, one `f64`) and a quarter of
ProductWeight<TropicalWeight, ComplexityWeight> (12 bytes).

---

## 10. Rust Implementation

The following is the complete `ComplexityWeight` implementation from
`prattail/src/automata/semiring.rs`.

```rust
/// Bottleneck semiring for parsing complexity measurement.
///
/// **Semiring:** `(N union {inf}, min, max, inf, 0)`
///
/// - `plus` = min (take least-complex alternative)
/// - `times` = max (bottleneck: path complexity = most complex segment)
/// - `zero` = inf (u32::MAX -- identity for min)
/// - `one` = 0 (identity for max)
///
/// **Applications:**
/// - Lookahead budget allocation (only extend WFST where complexity warrants)
/// - Backtrack depth bounding (NFA try-all max depth proportional to ComplexityWeight)
/// - Selective application of multi-token lookahead (B1)
///
/// **Interpretation:** The value represents the estimated lookahead depth
/// or parsing effort required for a dispatch path. Lower values indicate
/// simpler, more deterministic paths.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ComplexityWeight(u32);

impl ComplexityWeight {
    /// Create a ComplexityWeight from a raw complexity value.
    #[inline]
    pub const fn new(value: u32) -> Self {
        ComplexityWeight(value)
    }

    /// Return the complexity value.
    #[inline]
    pub const fn value(&self) -> u32 {
        self.0
    }

    /// Complexity for a deterministic (unambiguous) dispatch point.
    #[inline]
    pub const fn deterministic() -> Self {
        ComplexityWeight(0)
    }

    /// Complexity for a dispatch point requiring single-token lookahead.
    #[inline]
    pub const fn single_lookahead() -> Self {
        ComplexityWeight(1)
    }

    /// Complexity for a dispatch point requiring multi-token lookahead.
    #[inline]
    pub const fn multi_lookahead(depth: u32) -> Self {
        ComplexityWeight(depth)
    }

    /// Infinite complexity (unreachable path).
    #[inline]
    pub const fn infinite() -> Self {
        ComplexityWeight(u32::MAX)
    }
}

impl Semiring for ComplexityWeight {
    /// Zero = inf (identity for min -- no reachable path).
    #[inline]
    fn zero() -> Self {
        ComplexityWeight(u32::MAX)
    }

    /// One = 0 (identity for max -- zero complexity).
    #[inline]
    fn one() -> Self {
        ComplexityWeight(0)
    }

    /// Plus = min: take the least-complex alternative.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ComplexityWeight(self.0.min(other.0))
    }

    /// Times = max: bottleneck complexity is the worst segment.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        ComplexityWeight(self.0.max(other.0))
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == u32::MAX
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd for ComplexityWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Natural ordering: lower complexity = lower (better).
impl Ord for ComplexityWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for ComplexityWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == u32::MAX {
            write!(f, "∞")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl Default for ComplexityWeight {
    fn default() -> Self {
        Self::one()
    }
}
```

### Implementation Notes

- **Derived traits**: `Debug`, `PartialEq`, `Eq`, `Hash` are derived
  automatically. Unlike TropicalWeight (which wraps `f64` and needs
  custom impls for NaN handling), `u32` has well-behaved derived
  implementations.

- **Custom `PartialOrd`/`Ord`**: While `u32` has derived ordering,
  the explicit impl is provided for clarity and to match the pattern
  of other semiring types. The natural u32 ordering places `u32::MAX`
  (= ∞ = zero element) at the top, satisfying the Viterbi invariant.

- **`approx_eq` ignores epsilon**: Since ComplexityWeight wraps an
  integer, there is no floating-point imprecision. The `epsilon`
  parameter (required by the `Semiring` trait) is ignored; exact
  equality is used.

- **`Display` shows ∞**: The `u32::MAX` sentinel is displayed as the
  unicode symbol `∞` rather than `4294967295`, improving readability
  in diagnostic output.

- **`Default = one()`**: Consistent with all other PraTTaIL semirings
  -- a newly created weight represents zero complexity (the
  multiplicative identity), not infinite complexity (the additive
  identity / unreachable).

---

## 11. Integration into PraTTaIL

### 11.1 Lookahead Budget in Dispatch Codegen

During pipeline codegen, the ComplexityWeight of each dispatch path
informs how much lookahead buffer to allocate in the generated parser.
Categories where all dispatch paths have complexity 0 generate simple
direct-match code with no lookahead buffer. Categories with
complexity > 0 generate lookahead-aware code with a buffer sized to
the maximum bottleneck complexity:

```
// Generated code for category Expr (max complexity = 2):
let lookahead_buf: [Token; 2] = peek_tokens(input, 2);
match lookahead_buf[0] {
    Token::Ident => match lookahead_buf[1] {
        Token::LParen => parse_function_call(input),
        _             => parse_variable(input),
    },
    Token::Integer => parse_num_lit(input),
    ...
}
```

### 11.2 NFA Disambiguation Depth Bounding

The NFA disambiguation engine uses ComplexityWeight to bound the
number of alternatives that are explored in parallel. When spilling
alternatives for forced-prefix replay, the maximum replay depth
is bounded by the ComplexityWeight of the dispatch point:

```
if complexity.value() <= beam_threshold {
    // Explore all alternatives (cheap dispatch point)
} else {
    // Limit to top-k alternatives by tropical weight
}
```

### 11.3 Product Composition for B1 Selection

The composed dispatch table annotates each entry with
`ProductWeight<TropicalWeight, ComplexityWeight>`. The B1 selection
strategy picks the single best alternative:

```rust
// Sort by product weight: lowest tropical first, then lowest complexity
dispatch_arms.sort_by_key(|arm| arm.product_weight);
let winner = dispatch_arms[0]; // B1: take the best
```

Among alternatives with equal tropical weight (e.g., two cross-category
casts both at weight 0.5), the one with lower complexity is preferred
-- it requires less lookahead to confirm.

---

## 12. Source Reference & See Also

### Source Location

- **File**: `prattail/src/automata/semiring.rs`, lines 760--888
- **Struct**: `ComplexityWeight(u32)` (line 781)
- **Trait impl**: `impl Semiring for ComplexityWeight` (lines 821--859)
- **Ordering**: `impl Ord for ComplexityWeight` (lines 868--872)
- **Display**: `impl Display for ComplexityWeight` (lines 874--882)
- **Tests**: `test_complexity_weight_*` (lines 1612--1717)

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom
  definitions, classification, and comparison of all semirings
- [Tropical Weight Theory](tropical-weight.md) -- The tropical
  semiring for shortest-path dispatch ordering; shares the same ⊕ = min
  but uses ⊗ = + (cost accumulation) instead of ⊗ = max (bottleneck)
- [Edit Weight Theory](edit-weight.md) -- The edit-distance semiring;
  also uses ⊕ = min but with ⊗ = + (edit count accumulation)
- [Counting Weight Theory](counting-weight.md) -- The counting
  semiring for ambiguity detection; uses ⊕ = + (sum) and ⊗ = ×
  (product), neither of which is idempotent
- [Product Weight Theory](product-weight.md) -- The product semiring
  construction for composing TropicalWeight with ComplexityWeight
- [Dispatch Codegen](../../../src/dispatch.rs) -- Weight-ordered match
  arm emission using tropical and complexity weights
- [NFA Disambiguation](../../../src/nfa.rs) -- Forced-prefix replay
  depth bounded by ComplexityWeight
- [PredictionWfst](../../../src/wfst.rs) -- WFST prediction using
  weighted actions

### References

- Mohri, M. (2002). "Semiring Frameworks and Algorithms for
  Shortest-Distance Problems." *Journal of Automata, Languages and
  Combinatorics*, 7(3), 321--350. Section 3.4: Bottleneck semiring.
- Gondran, M. & Minoux, M. (2008). *Graphs, Dioids and Semirings:
  New Models and Algorithms*. Springer. Chapter 4: Bottleneck paths
  and min-max algebras.
- Pollack, M. (1960). "The Maximum Capacity Through a Network."
  *Operations Research*, 8(5), 733--736. Original bottleneck path
  formulation.
