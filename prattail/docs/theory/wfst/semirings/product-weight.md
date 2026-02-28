# Product Semiring: Multi-Objective Weighted Parsing

## 1. Intuition & Motivation

A parser often needs to optimize multiple criteria simultaneously. For example:

- **"What is the best parse, and is it unique?"** requires tracking both path
  cost (TropicalWeight) and derivation count (CountingWeight).
- **"What is the best parse with the fewest error corrections?"** requires
  tracking both priority (TropicalWeight) and edit distance (EditWeight).

No single semiring captures both objectives. The TropicalWeight semiring selects
the minimum-cost path but discards information about how many alternatives
existed. The CountingWeight semiring tallies derivations but cannot rank them
by quality. A parser that needs both must compose semirings.

The **product semiring** S1 x S2 solves this by computing two weights in
parallel. Every path carries a pair (w1, w2), and all semiring operations
apply component-wise. The result is a semiring that jointly tracks both
metrics with zero additional algorithmic complexity -- the same Viterbi,
forward-backward, and beam-pruning algorithms work unchanged.

```
                     ┌─────────────────────────┐
  "1 + 2 * 3"  ───> │   Lattice Construction   │
                     └─────────┬───────────────┘
                               │ edges carry (TropicalWeight, CountingWeight)
                               v
                     ┌─────────────────────────┐
                     │   Viterbi / Forward-     │
                     │   Backward (generic)     │
                     └─────────┬───────────────┘
                               │
                  ┌────────────┴────────────┐
                  v                          v
          best path weight            derivation count
          (tropical: 2.5)              (counting: 3)
```

---

## 2. Formal Construction

### 2.1 Component Semirings

Let S1 = (K1, ⊕1, ⊗1, 01, 11) and S2 = (K2, ⊕2, ⊗2, 02, 12) be semirings.

### 2.2 Product Definition

The product semiring **S1 x S2** = (K1 x K2, ⊕, ⊗, 0, 1) is defined by:

```
Carrier set:     K  = K1 x K2  =  { (a, b) | a in K1, b in K2 }

Addition:        (a1, a2) ⊕ (b1, b2)  =  (a1 ⊕1 b1,  a2 ⊕2 b2)

Multiplication:  (a1, a2) ⊗ (b1, b2)  =  (a1 ⊗1 b1,  a2 ⊗2 b2)

Additive identity:        0  =  (01, 02)

Multiplicative identity:  1  =  (11, 12)
```

Each operation decomposes into the corresponding operation on each component.
The two semirings evolve independently -- there is no interaction between
components at the algebraic level.

### 2.3 is_zero and is_one Predicates

```
is_zero((a, b))  =  is_zero1(a)  OR   is_zero2(b)

is_one((a, b))   =  is_one1(a)   AND  is_one2(b)
```

The `is_zero` predicate uses disjunction (see Section 7 for rationale).
The `is_one` predicate uses conjunction: only the pair of identities is itself
an identity.

---

## 3. Semiring Axiom Verification

We verify that S1 x S2 satisfies all semiring axioms, assuming S1 and S2 each
do. Every proof proceeds by decomposing the product operation into its
components and applying the corresponding axiom of S1 or S2.

### 3.1 (A1) Associativity of ⊕

```
((a1,a2) ⊕ (b1,b2)) ⊕ (c1,c2)
  = (a1 ⊕1 b1, a2 ⊕2 b2) ⊕ (c1, c2)
  = ((a1 ⊕1 b1) ⊕1 c1, (a2 ⊕2 b2) ⊕2 c2)
  = (a1 ⊕1 (b1 ⊕1 c1), a2 ⊕2 (b2 ⊕2 c2))     [by (A1) in S1, S2]
  = (a1, a2) ⊕ (b1 ⊕1 c1, b2 ⊕2 c2)
  = (a1, a2) ⊕ ((b1,b2) ⊕ (c1,c2))              QED
```

### 3.2 (A2) Commutativity of ⊕

```
(a1, a2) ⊕ (b1, b2)
  = (a1 ⊕1 b1, a2 ⊕2 b2)
  = (b1 ⊕1 a1, b2 ⊕2 a2)     [by (A2) in S1, S2]
  = (b1, b2) ⊕ (a1, a2)       QED
```

### 3.3 (A3) Additive Identity

```
0 ⊕ (a1, a2)
  = (01, 02) ⊕ (a1, a2)
  = (01 ⊕1 a1, 02 ⊕2 a2)
  = (a1, a2)                   [by (A3) in S1, S2]    QED
```

### 3.4 (M1) Associativity of ⊗

```
((a1,a2) ⊗ (b1,b2)) ⊗ (c1,c2)
  = (a1 ⊗1 b1, a2 ⊗2 b2) ⊗ (c1, c2)
  = ((a1 ⊗1 b1) ⊗1 c1, (a2 ⊗2 b2) ⊗2 c2)
  = (a1 ⊗1 (b1 ⊗1 c1), a2 ⊗2 (b2 ⊗2 c2))     [by (M1) in S1, S2]
  = (a1, a2) ⊗ ((b1,b2) ⊗ (c1,c2))              QED
```

### 3.5 (M2) Multiplicative Identity

```
1 ⊗ (a1, a2)
  = (11, 12) ⊗ (a1, a2)
  = (11 ⊗1 a1, 12 ⊗2 a2)
  = (a1, a2)                   [by (M2) in S1, S2]    QED
```

### 3.6 (D1, D2) Distributivity

Left-distributivity (D1):

```
(a1,a2) ⊗ ((b1,b2) ⊕ (c1,c2))
  = (a1,a2) ⊗ (b1 ⊕1 c1, b2 ⊕2 c2)
  = (a1 ⊗1 (b1 ⊕1 c1), a2 ⊗2 (b2 ⊕2 c2))
  = ((a1 ⊗1 b1) ⊕1 (a1 ⊗1 c1), (a2 ⊗2 b2) ⊕2 (a2 ⊗2 c2))    [by (D1) in S1, S2]
  = (a1 ⊗1 b1, a2 ⊗2 b2) ⊕ (a1 ⊗1 c1, a2 ⊗2 c2)
  = ((a1,a2) ⊗ (b1,b2)) ⊕ ((a1,a2) ⊗ (c1,c2))                  QED
```

Right-distributivity (D2) follows symmetrically.

### 3.7 (Z) Zero Annihilation

```
0 ⊗ (a1, a2)
  = (01, 02) ⊗ (a1, a2)
  = (01 ⊗1 a1, 02 ⊗2 a2)
  = (01, 02)                   [by (Z) in S1, S2]
  = 0                          QED
```

The symmetric case (a1, a2) ⊗ 0 = 0 follows identically.

---

## 4. Key Properties

### 4.1 Commutativity

The product semiring is **commutative** if and only if both S1 and S2 are
commutative.

**Proof.** (a1,a2) ⊗ (b1,b2) = (a1 ⊗1 b1, a2 ⊗2 b2). This equals
(b1 ⊗1 a1, b2 ⊗2 a2) = (b1,b2) ⊗ (a1,a2) iff a1 ⊗1 b1 = b1 ⊗1 a1
and a2 ⊗2 b2 = b2 ⊗2 a2, which holds iff S1 and S2 are commutative. QED

All PraTTaIL semirings (Tropical, Counting, Boolean, Edit) are commutative,
so all product combinations are commutative.

### 4.2 Idempotency

The product semiring is **idempotent** if and only if both S1 and S2 are
idempotent.

**Proof.** (a1,a2) ⊕ (a1,a2) = (a1 ⊕1 a1, a2 ⊕2 a2). This equals (a1,a2)
iff a1 ⊕1 a1 = a1 and a2 ⊕2 a2 = a2, which holds iff S1 and S2 are
idempotent. QED

**Consequence:** `ProductWeight<TropicalWeight, EditWeight>` is idempotent
(both components use min). `ProductWeight<TropicalWeight, CountingWeight>` is
**not** idempotent (CountingWeight uses addition: 3 + 3 = 6 != 3).

### 4.3 Lexicographic Ordering

PraTTaIL's `ProductWeight` implements `Ord` with **lexicographic ordering**:
compare the left component first; if equal, break ties with the right component.

```
(a1, a2) < (b1, b2)   iff   a1 < b1   OR  (a1 = b1  AND  a2 < b2)
```

This ordering determines which path Viterbi considers "better." With
`ProductWeight<TropicalWeight, EditWeight>`, the parser prefers the lowest
tropical weight (highest priority) first; among equally-prioritized parses,
it prefers the fewest edits.

**This is NOT the same as component-wise ⊕.** The semiring ⊕ (component-wise
min/add) and the Ord (lexicographic) are distinct operations. The ⊕ is used
for path combination in forward-backward; the Ord is used for Viterbi
comparison. This distinction is critical (see Section 9).

---

## 5. Application: Tropical x Counting

### 5.1 Disambiguation with Confidence

Consider a grammar with three rules that all accept the token `Ident`:

| Rule      | Tropical Weight | Description             |
|-----------|-----------------|-------------------------|
| Variable  | 2.0             | Variable reference      |
| TypeName  | 3.0             | Type constructor        |
| ModName   | 5.0             | Module qualifier        |

Under TropicalWeight alone, the parser selects Variable (weight 2.0) without
knowing whether the choice was unique. With
`ProductWeight<TropicalWeight, CountingWeight>`, each rule contributes both
a cost and a count of 1:

| Rule     | Product Weight      |
|----------|---------------------|
| Variable | (2.0, 1)            |
| TypeName | (3.0, 1)            |
| ModName  | (5.0, 1)            |

### 5.2 Worked Example

The semiring ⊕ (component-wise) combines all three:

```
Step 1:  (2.0, 1) ⊕ (3.0, 1)
       = (min(2.0, 3.0), 1 + 1)
       = (2.0, 2)

Step 2:  (2.0, 2) ⊕ (5.0, 1)
       = (min(2.0, 5.0), 2 + 1)
       = (2.0, 3)
```

**Result:** (2.0, 3) -- the best weight is 2.0 (Variable wins) but there are
3 competing derivations. A count > 1 signals ambiguity, enabling a
compile-time warning or runtime disambiguation strategy.

### 5.3 Path Sequencing (⊗)

When combining weights along a path (e.g., tokenize then parse), ⊗ operates:

```
(2.0, 3) ⊗ (1.5, 2) = (2.0 + 1.5,  3 * 2) = (3.5, 6)
```

The tropical component accumulates cost; the counting component multiplies
segment counts (two segments with 3 and 2 derivations respectively produce
3 x 2 = 6 combined derivations).

---

## 6. Application: Tropical x Edit

### 6.1 Error-Tolerant Parsing

When parsing erroneous input, the recovery engine generates multiple repair
paths. Each repair has a priority (how natural the repair is) and an edit
distance (how many tokens were inserted/deleted/substituted).

`ProductWeight<TropicalWeight, EditWeight>` optimizes both simultaneously.

### 6.2 Worked Example

Consider the erroneous input `1 + * 2` with three repair strategies:

```
  Path A: Skip '*'       ──> (1.0, 1)    [priority 1.0, skip cost 1]
  Path B: Insert '0'     ──> (2.0, 2)    [priority 2.0, insert cost 2]
  Path C: Substitute '1' ──> (1.5, 2)    [priority 1.5, substitute cost 2]
```

The Viterbi algorithm over ProductWeight selects the path with the smallest
lexicographic pair:

```
  Candidates under lexicographic Ord:
    (1.0, 1)  <  (1.5, 2)  <  (2.0, 2)

  Winner: Path A -- (1.0, 1) -- skip the unexpected '*'
```

### 6.3 Diagram: Recovery Lattice

```
  Input:   1    +    *    2
           │    │    │    │
  Pos:     0    1    2    3

  ┌───┐  1.0   ┌───┐  1.0   ┌───┐
  │ 0 │───────>│ 1 │───────>│ 3 │   Path A: skip '*', (1.0, 1)
  └───┘        └───┘        └─┬─┘
    │                     1.0  │
    │           ┌───┐ ────────>│   Path B: insert '0' before '*',
    │    2.0    │ 2 │──────────┘     then parse '*' as Mul, (2.0, 2)
    └──────────>└───┘
    │
    │    1.5    ┌───┐  1.0   ┌───┐
    └──────────>│ 2'│───────>│ 3 │   Path C: substitute '1' for '*', (1.5, 2)
                └───┘        └───┘

  Product ⊗ along each path:
    A: (1.0, 1) ⊗ (0.0, 0) = (1.0, 1)
    B: (2.0, 2)
    C: (1.5, 2)

  Viterbi best (lexicographic): A = (1.0, 1)
```

---

## 7. is_zero Semantics

The `is_zero` predicate for ProductWeight uses **disjunction**:

```
is_zero((a, b))  =  is_zero(a)  OR  is_zero(b)
```

**Rationale.** In weighted parsing, a path's product weight is computed by
sequencing edge weights with ⊗. If either component reaches zero (unreachable),
the entire path is unreachable -- there is no meaningful interpretation of a
parse that is simultaneously "impossible in dimension 1 but possible in
dimension 2."

Formally, the zero-annihilation axiom (Z) guarantees:

```
(01, x) ⊗ (a, b) = (01 ⊗1 a, x ⊗2 b) = (01, x ⊗2 b)
```

Since 01 is zero in S1, the first component can never leave zero regardless
of subsequent multiplications. Any path through this weight contributes
nothing to the overall computation.

The OR semantics also ensures that Viterbi's "skip unvisited nodes" optimization
works correctly: if `dist[node].is_zero()`, the node is provably unreachable
from the start, and outgoing edges need not be relaxed.

---

## 8. Composability

Product semirings compose recursively. To track three objectives simultaneously:

```
ProductWeight<ProductWeight<TropicalWeight, CountingWeight>, EditWeight>
```

This yields triples (tropical_cost, derivation_count, edit_distance) with
all operations applying component-wise through the nested structure.

### 8.1 Nested Structure

```
type TripleWeight = ProductWeight<ProductWeight<TropicalWeight, CountingWeight>, EditWeight>;

let w = TripleWeight::new(
    ProductWeight::new(TropicalWeight::new(2.0), CountingWeight::new(3)),
    EditWeight::new(1),
);
```

### 8.2 Axiom Preservation

Since ProductWeight<A, B> is a semiring whenever A and B are semirings, and
ProductWeight<ProductWeight<A, B>, C> is a product of two semirings
(ProductWeight<A, B> and C), it is also a semiring by the construction in
Section 3. No additional verification is needed -- the proof composes.

### 8.3 Lexicographic Ord Nesting

With nested products, the lexicographic ordering nests naturally:

```
((a1, a2), a3) < ((b1, b2), b3)
  iff  (a1, a2) < (b1, b2)          [outer comparison]
  iff  a1 < b1                       [inner comparison, left first]
       OR (a1 = b1 AND a2 < b2)      [inner comparison, tie-break]
  OR   ((a1, a2) = (b1, b2) AND a3 < b3)  [outer tie-break]
```

The effective priority order is: tropical > counting > edit distance.

---

## 9. Viterbi Compatibility

### 9.1 The Problem with CountingWeight

Viterbi shortest-path algorithms require a key invariant:

> **Invariant.** `W::zero()` must be the **largest** element under `Ord`,
> so that unvisited nodes compare as "worse" than any reachable distance.

This holds for:
- `TropicalWeight`: zero = +inf, which is the largest f64
- `EditWeight`: zero = u32::MAX, which is the largest u32
- `ProductWeight<TropicalWeight, EditWeight>`: zero = (+inf, u32::MAX), largest lexicographically

It does **not** hold for:
- `CountingWeight`: zero = 0, which is the **smallest** u64

When `viterbi_generic` initializes `dist[node] = W::zero()` for all nodes
and then checks `if dist[node].is_zero() { continue }`, it correctly skips
unreachable nodes for Tropical/Edit but produces incorrect results for
CountingWeight because zero (0) is indistinguishable from "0 derivations
found so far" and is the smallest value under Ord.

### 9.2 The Solution via ProductWeight

CountingWeight works correctly inside a ProductWeight when the **left**
component drives the Ord:

```
ProductWeight<TropicalWeight, CountingWeight>

zero() = (+inf, 0)     -- largest under lexicographic Ord (because +inf is largest)
one()  = (0.0, 1)      -- one path with zero cost
```

Since lexicographic comparison examines the TropicalWeight first, the Viterbi
invariant is satisfied: zero = (+inf, 0) > any reachable weight (finite, n).
The CountingWeight rides along in the second component, accumulating counts
without disrupting the path-selection logic.

### 9.3 Summary Table

| Semiring                                  | Viterbi Compatible | Reason              |
|-------------------------------------------|--------------------|---------------------|
| TropicalWeight                            | Yes                | zero = +inf (max)   |
| EditWeight                                | Yes                | zero = MAX (max)    |
| CountingWeight                            | **No**             | zero = 0 (min)      |
| ProductWeight\<Tropical, Counting\>       | Yes                | Tropical drives Ord |
| ProductWeight\<Tropical, Edit\>           | Yes                | Both max under Ord  |
| ProductWeight\<Edit, Counting\>           | Yes                | Edit drives Ord     |

---

## 10. Generic Viterbi

PraTTaIL provides `viterbi_generic<W: Semiring + Ord>()` in `lattice.rs` for
running Viterbi over any compatible product semiring.

### 10.1 Algorithm

```
FUNCTION viterbi_generic(lattice, final_node) -> Option<ViterbiPath>
  n := lattice.num_nodes()
  IF n = 0 OR final_node >= n THEN RETURN None

  dist := [W::zero(); n]        // Initialize all nodes as unreachable
  dist[0] := W::one()           // Start node has identity weight
  pred := [None; n]              // Predecessor tracking for path reconstruction

  FOR node IN 0..n DO
    IF dist[node].is_zero() THEN CONTINUE    // Skip unreachable nodes
    FOR (edge_idx, edge) IN lattice.edges_from(node) DO
      new_dist := dist[node] ⊗ edge.weight   // Extend path
      IF new_dist < dist[edge.target] THEN    // Better path found (Ord comparison)
        dist[edge.target] := new_dist
        pred[edge.target] := Some((node, edge_idx))

  IF dist[final_node].is_zero() THEN RETURN None
  RETURN reconstruct_path(pred, final_node, dist[final_node])
```

### 10.2 Key Observation

The comparison `new_dist < dist[edge.target]` uses the `Ord` implementation
(lexicographic), not the semiring ⊕. This is intentional:

- **Semiring ⊕** (component-wise) is used in forward-backward to combine
  all paths' contributions.
- **Ord** (lexicographic) is used in Viterbi to select the single best path.

For idempotent semirings (Tropical, Edit), ⊕ and min agree. For
non-idempotent components (Counting), only the Ord comparison is used in
Viterbi; the ⊕ is used separately in forward-backward.

---

## 11. Comparison Table

| Property                  | Tropical | Counting | Edit     | Product\<S1,S2\>        |
|---------------------------|----------|----------|----------|--------------------------|
| Carrier set               | R+ u {+inf} | N    | N u {inf} | S1 x S2                |
| ⊕ (plus)                  | min      | +        | min      | component-wise ⊕        |
| ⊗ (times)                 | +        | x        | +        | component-wise ⊗        |
| 0 (zero)                  | +inf     | 0        | u32::MAX | (01, 02)               |
| 1 (one)                   | 0.0      | 1        | 0        | (11, 12)               |
| Commutative               | Yes      | Yes      | Yes      | iff both components     |
| Idempotent                | Yes      | No       | Yes      | iff both components     |
| Viterbi compatible        | Yes      | No       | Yes      | iff left drives Ord     |
| Forward-backward capable  | Limited  | No       | Limited  | depends on components   |

---

## 12. Rust Implementation

The full implementation from `prattail/src/automata/semiring.rs`:

```rust
/// Product semiring `(S1 x S2)` -- computes two metrics simultaneously.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ProductWeight<S1: Semiring, S2: Semiring> {
    pub left: S1,
    pub right: S2,
}

impl<S1: Semiring, S2: Semiring> ProductWeight<S1, S2> {
    #[inline]
    pub const fn new(left: S1, right: S2) -> Self {
        ProductWeight { left, right }
    }
}

impl<S1: Semiring + Eq + Hash, S2: Semiring + Eq + Hash> Semiring
    for ProductWeight<S1, S2>
{
    #[inline]
    fn zero() -> Self {
        ProductWeight { left: S1::zero(), right: S2::zero() }
    }

    #[inline]
    fn one() -> Self {
        ProductWeight { left: S1::one(), right: S2::one() }
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ProductWeight {
            left: self.left.plus(&other.left),
            right: self.right.plus(&other.right),
        }
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        ProductWeight {
            left: self.left.times(&other.left),
            right: self.right.times(&other.right),
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.left.is_zero() || self.right.is_zero()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.left.is_one() && self.right.is_one()
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        self.left.approx_eq(&other.left, epsilon)
            && self.right.approx_eq(&other.right, epsilon)
    }
}

/// Lexicographic ordering: compare left component first, then right.
impl<S1: Semiring + Ord, S2: Semiring + Ord> Ord for ProductWeight<S1, S2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.left.cmp(&other.left).then_with(|| self.right.cmp(&other.right))
    }
}

impl<S1: Semiring, S2: Semiring> Default for ProductWeight<S1, S2> {
    fn default() -> Self {
        ProductWeight { left: S1::one(), right: S2::one() }
    }
}

impl<S1: Semiring + Display, S2: Semiring + Display> Display for ProductWeight<S1, S2> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.left, self.right)
    }
}
```

### 12.1 Design Notes

- **Trait bounds.** The `Semiring` impl requires `Eq + Hash` on both components
  to support use as keys in hash maps (e.g., for visited-state tracking in
  composition algorithms).

- **Default = one().** The `Default` implementation returns the multiplicative
  identity, matching Rust's convention that `Default::default()` represents the
  "no-op" or "neutral" value.

- **Display.** The `({left}, {right})` format mirrors tuple notation and nests
  cleanly for `ProductWeight<ProductWeight<A,B>, C>` as `((a, b), c)`.

---

## 13. Integration into PraTTaIL

### 13.1 Lattice Parameterization

The token lattice is generic over the weight type:

```rust
pub struct TokenLattice<T, S, W = TropicalWeight> { ... }
pub struct LatticeEdge<T, S, W = TropicalWeight> { ... }
pub struct ViterbiPath<T, S, W = TropicalWeight> { ... }
```

The default `W = TropicalWeight` preserves backward compatibility. A product
lattice is constructed by specifying the type parameter:

```rust
type PW = ProductWeight<TropicalWeight, EditWeight>;
let mut lattice: TokenLattice<Token, Span, PW> = TokenLattice::new();
lattice.add_edge(0, 1, token, span, PW::new(
    TropicalWeight::new(1.0),
    EditWeight::new(2),
));
```

### 13.2 Joint Optimization via viterbi_generic

```rust
use prattail::lattice::viterbi_generic;

let path = viterbi_generic(&product_lattice, final_node)
    .expect("reachable final node");

// Decompose the result:
let priority = path.total_weight.left;    // TropicalWeight
let edit_dist = path.total_weight.right;  // EditWeight
```

### 13.3 Ambiguity Detection via predict_with_confidence

The `PredictionWfst::predict_with_confidence()` method annotates each dispatch
action with a `CountingWeight` recording how many alternatives exist:

```rust
let annotated = wfst.predict_with_confidence("Ident");
for (action, count) in &annotated {
    if count.count() > 1 {
        // Ambiguous dispatch -- emit compile-time warning
    }
}
```

This is the runtime analog of the ProductWeight<Tropical, Counting>
composition: the tropical component selects the winner, and the counting
component flags whether the choice was unique.

---

## 14. Source Reference & See Also

### Source

- `prattail/src/automata/semiring.rs` -- `ProductWeight` definition (lines 512-620)
- `prattail/src/lattice.rs` -- `viterbi_generic()`, `TokenLattice<T, S, W>`

### Related Theory Documents

- [Semiring Algebra for Weighted Parsing](../semirings.md)
  -- the Semiring trait, TropicalWeight, and axiom definitions
- [Log Semiring Theory](./log-weight.md) -- LogWeight, forward-backward, training
- [Viterbi, Forward-Backward, and N-Best Paths](../viterbi-and-forward-backward.md)
  -- algorithms that operate over ProductWeight via generic dispatch
- [Error Recovery Design](../../../design/wfst/error-recovery.md)
  -- how EditWeight + ProductWeight compose for recovery path selection
- [Prediction Engine](../../../design/prediction-engine.md)
  -- WFST dispatch using weighted actions

### References

- Kuich, W. & Salomaa, A. (1986). *Semirings, Automata, Languages*.
  Springer. Chapter 2: Product semirings.
- Mohri, M. (2009). "Weighted Automata Algorithms." In *Handbook of Weighted
  Automata*. Springer. Section 2.3: Semiring products.
