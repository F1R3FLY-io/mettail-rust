# RelationalWeight -- Design & Pipeline Integration

> **Date:** 2026-03-08

Most semirings in PraTTaIL use numeric weights: costs, counts, probabilities.
RelationalWeight is different -- its elements are **sets of pairs**. Each pair
`(a, b)` says "if we start in state `a`, we can reach state `b`." Combining
two relations by composition answers: "if we apply transformation R1 and then
R2, which state pairs are reachable end-to-end?" This is the mathematical
foundation of interprocedural program analysis via weighted pushdown systems.

---

## Table of Contents

1. [Intuition](#1-intuition)
2. [Mathematical Definition](#2-mathematical-definition)
3. [Data Structure](#3-data-structure)
4. [HeapSemiring Trait](#4-heapsemiring-trait)
5. [Semiring Operations](#5-semiring-operations)
6. [Projections and Queries](#6-projections-and-queries)
7. [Connection to SLAM/BLAST](#7-connection-to-slamblast)
8. [Pipeline Integration](#8-pipeline-integration)
9. [Rust API](#9-rust-api)
10. [Test Coverage](#10-test-coverage)
11. [Source References](#11-source-references)
12. [Cross-References](#12-cross-references)

---

## 1. Intuition

Imagine a parser with three internal states: `{idle, parsing, recovering}`.
Each grammar rule transforms the parser's state. Rule A might map `idle`
to `parsing`. Rule B might map `parsing` to `recovering`. The relational
weight captures this as a set of pairs:

```
Rule A weight:  { (idle, parsing) }
Rule B weight:  { (parsing, recovering) }
```

Composing A followed by B (via `times`) yields:

```
A ; B  =  { (idle, recovering) }
```

"If we start idle and apply A then B, we end up recovering."

Taking the union of two rule weights (via `plus`) combines their
reachability:

```
A ∪ B  =  { (idle, parsing), (parsing, recovering) }
```

"From idle we can reach parsing (via A), and from parsing we can reach
recovering (via B)."

This representation is powerful because it tracks **all possible state
transitions**, not just the cheapest or most probable one. It is the
weight domain of choice for Boolean program analysis and WPDS-based
verification.

---

## 2. Mathematical Definition

The relational semiring over a finite ground set G is:

```
(2^{G x G},  ∪,  ;,  empty,  id_G)
```

where:

- **Carrier set**: `2^{G x G}` -- all binary relations on G (subsets of
  the Cartesian product G x G).

- **Plus** (⊕ = ∪): Set union. Combines reachability from two
  independent analyses:
  ```
  R₁ ⊕ R₂  =  R₁ ∪ R₂  =  { (a,b) | (a,b) ∈ R₁ or (a,b) ∈ R₂ }
  ```

- **Times** (⊗ = ;): Relational composition. Sequences two state
  transformations:
  ```
  R₁ ⊗ R₂  =  R₁ ; R₂  =  { (a,c) | ∃b : (a,b) ∈ R₁ and (b,c) ∈ R₂ }
  ```

- **Zero** (0 = empty): The empty relation -- no state pairs are
  reachable. This is the additive identity because `R ∪ empty = R`.

- **One** (1 = id_G): The identity relation `{ (g,g) | g ∈ G }` -- every
  state maps to itself. This is the multiplicative identity because
  `R ; id_G = id_G ; R = R`.

### Size

For a ground set of size n = |G|, the carrier has `2^{n^2}` elements.
This is manageable for small abstract domains (n <= 10 or so) but
grows rapidly. In practice, most analysis domains have fewer than 8
abstract states (e.g., 2^3 = 8 valuations for 3 Boolean variables).

### Semiring axioms

| Axiom                  | Formula                              | Status     |
|------------------------|--------------------------------------|------------|
| Additive identity      | R ∪ empty = R                        | Holds      |
| Additive commutativity | R₁ ∪ R₂ = R₂ ∪ R₁                    | Holds      |
| Additive associativity | (R₁ ∪ R₂) ∪ R₃ = R₁ ∪ (R₂ ∪ R₃)      | Holds      |
| Multiplicative identity| R ; id = id ; R = R                  | Holds      |
| Multiplicative assoc.  | (R₁ ; R₂) ; R₃ = R₁ ; (R₂ ; R₃)      | Holds      |
| Left distributivity    | R₁ ; (R₂ ∪ R₃) = (R₁;R₂) ∪ (R₁;R₃)  | Holds      |
| Zero annihilation      | R ; empty = empty ; R = empty        | Holds      |

All seven axioms are verified by unit tests in `relational.rs`.

### Non-commutativity of times

Unlike most PraTTaIL semirings, relational composition is **not**
commutative in general. `R₁ ; R₂ != R₂ ; R₁`. This is expected:
the order of state transformations matters.

---

## 3. Data Structure

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalWeight<G: Clone + Eq + Hash + Debug + Send + Sync + 'static> {
    /// Set of (source, target) state pairs.
    pub pairs: HashSet<(G, G)>,
    /// The full universe of G values (needed for identity relation).
    universe: Vec<G>,
}
```

**Type parameter G**: The ground set element type. Must be `Clone + Eq + Hash`
for `HashSet` membership, `Debug` for diagnostics, `Ord` for canonical display
ordering, and `Send + Sync + 'static` for thread safety. Typical instantiation:
`RelationalWeight<u8>` for small finite domains.

**Universe field**: Stored so that `identity()` can construct the correct
identity relation `{ (g,g) | g ∈ G }` without requiring the caller to pass
the universe repeatedly. The universe is the larger of the two operands'
universes after any binary operation.

**Memory layout**: Heap-allocated via `HashSet`. The average element size is
`2 * size_of::<G>()` per pair, plus hash table overhead. For `G = u8` and
n = |universe|, the HashSet stores up to n^2 pairs.

---

## 4. HeapSemiring Trait

The standard `Semiring` trait in PraTTaIL requires `Copy`. Since
`RelationalWeight` contains a `HashSet` (heap-allocated), it cannot be
`Copy`. The `HeapSemiring` trait mirrors `Semiring` without the `Copy` bound:

```rust
pub trait HeapSemiring: Clone + Debug + PartialEq + Send + Sync + 'static {
    fn zero() -> Self;
    fn one() -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}
```

`HeapSemiring` is also used by `ProvenanceWeight` and the `HeapWpds<W>`
infrastructure. The `HeapWpds` type mirrors the standard `Wpds<W>` but
accepts `HeapSemiring`-bounded weights, enabling relational and provenance
WPDS analysis.

### Trait caveat: context-free `zero()` and `one()`

The `HeapSemiring` trait requires `zero()` and `one()` to be constructable
without arguments. For `RelationalWeight`, this means the trait-level
`zero()` returns an empty relation with an empty universe, and `one()`
returns an empty relation with an empty universe (since the identity
relation on an empty set is empty). **Callers should use the explicit
constructors** `RelationalWeight::empty(universe)` and
`RelationalWeight::identity(universe)` when universe context is available.

---

## 5. Semiring Operations

### 5a. Plus (set union)

```rust
fn plus(&self, other: &Self) -> Self {
    let pairs: HashSet<(G, G)> = self.pairs.union(&other.pairs).cloned().collect();
    let universe = if self.universe.len() >= other.universe.len() {
        self.universe.clone()
    } else {
        other.universe.clone()
    };
    RelationalWeight { pairs, universe }
}
```

**Complexity**: O(|R₁| + |R₂|) for the union operation.

**Example**:

```
R₁ = { (0,1) }
R₂ = { (1,2) }
R₁ ⊕ R₂ = { (0,1), (1,2) }
```

### 5b. Times (relational composition)

```rust
fn times(&self, other: &Self) -> Self {
    let mut pairs = HashSet::new();
    for (a, b) in &self.pairs {
        for (b2, c) in &other.pairs {
            if b == b2 {
                pairs.insert((a.clone(), c.clone()));
            }
        }
    }
    // ...
}
```

**Complexity**: O(|R₁| * |R₂|) in the worst case. For sparse relations
(typical in program analysis), the number of matching `b == b2` pairs is
much smaller.

**Example**:

```
R₁ = { (0,1), (0,2) }
R₂ = { (1,2), (2,0) }

R₁ ; R₂:
  (0,1) matches (1,2) via b=1  -->  (0,2)
  (0,2) matches (2,0) via b=2  -->  (0,0)

R₁ ; R₂ = { (0,2), (0,0) }
```

### 5c. is_zero and is_one

```
is_zero():  pairs.is_empty()                    // no reachable state pairs
is_one():   pairs == { (g,g) | g in universe }  // identity relation
```

The `is_one` check verifies both that `|pairs| == |universe|` and that
every pair is a diagonal entry `(g, g)`.

### 5d. approx_eq

For discrete relational weights, approximate equality reduces to exact
equality:

```rust
fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
    self.pairs == other.pairs
}
```

The `epsilon` parameter is ignored because binary relations are exact
(no floating-point imprecision).

---

## 6. Projections and Queries

RelationalWeight provides four projection/query methods:

| Method         | Return Type  | Semantics                                |
|----------------|-------------|------------------------------------------|
| `domain()`     | `HashSet<G>` | `{ a | exists b: (a,b) ∈ R }`            |
| `range()`      | `HashSet<G>` | `{ b | exists a: (a,b) ∈ R }`            |
| `image(a)`     | `HashSet<G>` | `{ b | (a,b) ∈ R }` (forward reach)      |
| `preimage(b)`  | `HashSet<G>` | `{ a | (a,b) ∈ R }` (backward reach)     |

### Example

```
R = { (0,1), (0,2), (1,2) }

domain(R)     = { 0, 1 }
range(R)      = { 1, 2 }
image(R, 0)   = { 1, 2 }
preimage(R, 2)= { 0, 1 }
```

These projections are useful for extracting reachability information
from WPDS saturation results. After `poststar`, `image(initial_state)`
gives the set of reachable target states. After `prestar`,
`preimage(error_state)` gives the set of states from which the error
is reachable.

---

## 7. Connection to SLAM/BLAST

The relational weight domain is the foundation of SLAM-style and
BLAST-style Boolean program analysis, as described in:

> T. Reps, A. Lal, and N. Kidd. "Program Analysis Using Weighted
> Pushdown Systems." In Proceedings of the 27th Conference on
> Foundations of Software Technology and Theoretical Computer Science
> (FSTTCS), 2007.

In these analyses:

1. **Ground set G** = the set of Boolean variable valuations (e.g., for
   3 Boolean variables, G = {000, 001, 010, ..., 111}, |G| = 8).

2. **Each program statement** is modeled as a WPDS rule weighted by the
   binary relation describing its state transformation. For example, the
   assignment `x := true` maps every valuation with `x=false` to the
   corresponding valuation with `x=true`, and leaves `x=true` valuations
   unchanged.

3. **Interprocedural analysis** composes these relations along call
   chains. WPDS `poststar` computes the net relation from all initial
   configurations to all reachable configurations. WPDS `prestar`
   computes the relation from all configurations that can reach a
   target set.

4. **MOVP(S, T)** (Meet Over Valid Paths) reduces to semiring path
   combination in the relational domain. The union of all path-wise
   compositions gives the exact set of reachable state pairs.

In PraTTaIL, this framework applies to grammar analysis: each grammar
rule is a "statement" that transforms the parser's abstract state, and
WPDS composition tracks which parser states are reachable after
sequences of rule applications.

---

## 8. Pipeline Integration

### 8a. HeapWpds infrastructure

`relational.rs` defines `HeapWpds<W>` and `HeapWpdsRule<W>`, which
mirror the standard `Wpds<W>` and `WpdsRule<W>` types but accept
`HeapSemiring`-bounded weights:

```
┌───────────────────────┐     ┌───────────────────────┐
│  Wpds<TropicalWeight> │     │  HeapWpds<Relational>  │
│  (Copy semirings)     │     │  (Heap semirings)      │
│                       │     │                        │
│  WpdsRule::Pop        │     │  HeapWpdsRule::Pop     │
│  WpdsRule::Replace    │     │  HeapWpdsRule::Replace │
│  WpdsRule::Push       │     │  HeapWpdsRule::Push    │
└───────────────────────┘     └────────────────────────┘
```

Both expose the same `from_gamma()` and `weight()` accessors, enabling
uniform treatment in saturation algorithms that are generic over the
weight domain.

### 8b. Rule types

Each `HeapWpdsRule<W>` variant models a PDS configuration transition:

| Variant   | Notation                     | Stack Effect      |
|-----------|------------------------------|-------------------|
| `Pop`     | `<p, gamma> -> <p', epsilon>` | Stack shrinks by 1 |
| `Replace` | `<p, gamma> -> <p', gamma'>` | Top symbol changes |
| `Push`    | `<p, gamma> -> <p', gamma' gamma''>` | Stack grows by 1 |

### 8c. Use cases

| Use Case                    | How RelationalWeight Is Used                     |
|-----------------------------|--------------------------------------------------|
| **ARA weight domain**       | Alternating register automata use relational weights for state-pair reachability |
| **WPDS relational analysis**| HeapWpds with RelationalWeight tracks parser state transformations |
| **Safety verification**     | Prestar on RelationalWeight confirms which initial states can reach error states |
| **Boolean program modeling**| Grammar operational semantics as state-pair transformations |

---

## 9. Rust API

### Creating relational weights

```rust
use prattail::relational::RelationalWeight;
use std::collections::HashSet;

let universe = vec![0u8, 1, 2];

// Empty relation (zero)
let empty = RelationalWeight::empty(universe.clone());
assert!(empty.is_zero());

// Identity relation (one)
let id = RelationalWeight::identity(universe.clone());
assert!(id.is_one());
assert_eq!(id.size(), 3);  // {(0,0), (1,1), (2,2)}

// Singleton relation
let r = RelationalWeight::singleton(0, 1, universe.clone());
assert_eq!(r.size(), 1);
assert!(r.contains(&0, &1));
```

### Semiring operations

```rust
use prattail::relational::HeapSemiring;

let r1 = RelationalWeight::singleton(0u8, 1, universe.clone());
let r2 = RelationalWeight::singleton(1u8, 2, universe.clone());

// Union (plus): {(0,1)} U {(1,2)} = {(0,1), (1,2)}
let union = r1.plus(&r2);
assert_eq!(union.size(), 2);

// Composition (times): {(0,1)} ; {(1,2)} = {(0,2)}
let comp = r1.times(&r2);
assert_eq!(comp.size(), 1);
assert!(comp.contains(&0, &2));

// Zero annihilation
let z = RelationalWeight::empty(universe.clone());
assert!(r1.times(&z).is_zero());

// Identity neutrality
let id = RelationalWeight::identity(universe.clone());
assert_eq!(r1.times(&id).pairs, r1.pairs);
```

### Projections

```rust
let mut pairs = HashSet::new();
pairs.insert((0u8, 1u8));
pairs.insert((0, 2));
pairs.insert((1, 2));
let r = RelationalWeight::new(pairs, universe.clone());

// Domain and range
assert_eq!(r.domain().len(), 2);   // {0, 1}
assert_eq!(r.range().len(), 2);    // {1, 2}

// Image and preimage
assert_eq!(r.image(&0).len(), 2);     // {1, 2}
assert_eq!(r.preimage(&2).len(), 2);  // {0, 1}
```

### HeapWpds construction

```rust
use prattail::relational::{HeapWpds, HeapWpdsRule};
use prattail::wpds::StackSymbol;

let rule = HeapWpdsRule::Replace {
    from_gamma: StackSymbol::Category("Expr".into()),
    to_gamma: StackSymbol::Category("Int".into()),
    weight: RelationalWeight::singleton(0u8, 1, vec![0, 1, 2]),
};

assert_eq!(
    *rule.from_gamma(),
    StackSymbol::Category("Expr".into())
);
assert_eq!(rule.weight().size(), 1);
```

---

## 10. Test Coverage

Thirteen tests in `relational.rs` cover the full API:

| #  | Test                          | What It Verifies                                     |
|----|-------------------------------|------------------------------------------------------|
| 1  | `test_empty_is_zero`          | Empty relation satisfies is_zero                     |
| 2  | `test_identity_is_one`        | Identity relation satisfies is_one, has |G| pairs    |
| 3  | `test_union_plus`             | Plus = set union, size = sum of inputs               |
| 4  | `test_composition_times`      | {(0,1)} ; {(1,2)} = {(0,2)}                         |
| 5  | `test_zero_annihilates`       | R ; empty = empty ; R = empty                        |
| 6  | `test_identity_is_neutral`    | R ; id = id ; R = R                                  |
| 7  | `test_plus_is_commutative`    | R1 U R2 = R2 U R1                                    |
| 8  | `test_times_is_associative`   | (R1 ; R2) ; R3 = R1 ; (R2 ; R3)                      |
| 9  | `test_distributive`           | R1 ; (R2 U R3) = (R1;R2) U (R1;R3)                  |
| 10 | `test_domain_and_range`       | domain and range projection correctness              |
| 11 | `test_image_and_preimage`     | Forward and backward reachability queries            |
| 12 | `test_display`                | Display format includes pair notation                |
| 13 | `test_approx_eq`              | Discrete equality (exact match, epsilon ignored)     |

---

## 11. Source References

| Component                   | File             | Lines     |
|-----------------------------|------------------|-----------|
| Module documentation        | `relational.rs`  | 1-24      |
| `HeapSemiring` trait        | `relational.rs`  | 29-48     |
| `RelationalWeight` struct   | `relational.rs`  | 50-132    |
| `HeapSemiring` impl         | `relational.rs`  | 134-198   |
| `Display` impl              | `relational.rs`  | 200-217   |
| `HeapWpds` struct            | `relational.rs`  | 219-237   |
| `HeapWpdsRule` enum          | `relational.rs`  | 239-280   |
| Tests (13)                  | `relational.rs`  | 282-407   |

---

## 12. Cross-References

- **Theory**: Reps, Lal & Kidd (2007), "Program Analysis Using Weighted Pushdown Systems" -- foundational paper for relational WPDS analysis (Definition 7: relational weight domain)
- **WPDS core**: `wpds.rs` -- standard WPDS with Copy-bounded semirings; RelationalWeight uses HeapWpds instead
- **ProvenanceWeight**: `provenance-weight.md` -- another HeapSemiring weight; shares the HeapSemiring trait
- **TensorWeight**: `tensor-weight.md` -- models interaction between analyses; can compose with RelationalWeight via TensorWeight if both are projected to Copy semirings first
- **Safety verification**: `verify.rs` -- uses prestar with relational domains for parser safety properties
- **ARA**: `ara.rs` -- alternating register automata that use relational weights for state-pair tracking
- **CEGAR**: `cegar.rs` -- counterexample-guided abstraction refinement uses relational weights for abstract state tracking
