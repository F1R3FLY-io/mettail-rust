# Relational Semiring: RelationalWeight

## 1. Intuition & Motivation

The relational semiring provides a *state-pair reachability algebra*
for tracking which parser states can reach which other states through
sequences of grammar rule applications. Its carrier set consists of
binary relations over a finite ground set G, and its two operations
correspond directly to program analysis composition:

- **Combining independent analyses** (parallel paths) uses set union
  -- if either analysis can reach a state pair, the combined analysis
  can reach it.
- **Sequencing transformations** (a path through multiple rules) uses
  relational composition -- if transformation R_1 maps state a to
  state b, and R_2 maps state b to state c, then the sequence maps
  a to c.

Within PraTTaIL, relational weights model the operational semantics
of grammar rules as state transformations:

```
rule application  =  state-pair relation  =  who can reach whom
```

A Boolean weight tells you whether *any* state can reach *any* other.
A relational weight tells you *exactly which* source states can reach
*exactly which* target states. This precision is essential for
interprocedural analysis, where the calling context determines which
state transitions are valid.

---

## 2. Formal Definition

The relational semiring over a finite ground set G is the algebraic
structure:

```
R  =  ( 2^{G x G},  ∪,  ;,  emptyset,  id_G )
```

where:

| Component                   | Symbol    | Concrete value                    | Meaning                          |
|-----------------------------|-----------|-----------------------------------|----------------------------------|
| Carrier set                 | K         | 2^{G x G}                        | All binary relations on G        |
| Addition (⊕)                | ∪         | set union                         | Combine reachability             |
| Multiplication (⊗)          | ;         | relational composition            | Sequence transformations         |
| Additive identity (0)       | emptyset  | empty relation `{}`               | No state pairs reachable         |
| Multiplicative identity (1) | id_G      | `{(g,g) | g in G}`               | Identity transformation          |

Binary relation composition is defined as:

```
R_1 ; R_2  =  { (a, c) | exists b in G : (a, b) in R_1 and (b, c) in R_2 }
```

For a ground set of size n = |G|, the carrier has `2^{n^2}` elements.
This is manageable for small abstract domains (n <= 10) but grows
rapidly.

---

## 3. Semiring Axiom Verification

We verify all eight semiring axioms with concrete examples. Let
G = {0, 1, 2}, R_1 = {(0, 1)}, R_2 = {(1, 2)}, R_3 = {(2, 0)}.

### (A1) Associativity of ⊕

```
(R_1 ⊕ R_2) ⊕ R_3
  = ({(0,1)} ∪ {(1,2)}) ∪ {(2,0)}
  = {(0,1), (1,2)} ∪ {(2,0)}
  = {(0,1), (1,2), (2,0)}

R_1 ⊕ (R_2 ⊕ R_3)
  = {(0,1)} ∪ ({(1,2)} ∪ {(2,0)})
  = {(0,1)} ∪ {(1,2), (2,0)}
  = {(0,1), (1,2), (2,0)}   ✓
```

Holds because set union is associative.

### (A2) Commutativity of ⊕

```
R_1 ⊕ R_2  = {(0,1)} ∪ {(1,2)} = {(0,1), (1,2)}
R_2 ⊕ R_1  = {(1,2)} ∪ {(0,1)} = {(0,1), (1,2)}   ✓
```

Holds because set union is commutative.

### (A3) ⊕ Identity

```
emptyset ⊕ R_1  = {} ∪ {(0,1)} = {(0,1)} = R_1   ✓
R_1 ⊕ emptyset  = {(0,1)} ∪ {} = {(0,1)} = R_1   ✓
```

The empty relation is the identity for union because adding no pairs
leaves the relation unchanged.

### (M1) Associativity of ⊗

```
(R_1 ⊗ R_2) ⊗ R_3
  = ({(0,1)} ; {(1,2)}) ; {(2,0)}
  = {(0,2)} ; {(2,0)}
  = {(0,0)}

R_1 ⊗ (R_2 ⊗ R_3)
  = {(0,1)} ; ({(1,2)} ; {(2,0)})
  = {(0,1)} ; {(1,0)}
  = {(0,0)}   ✓
```

Step-by-step for `(R_1 ⊗ R_2)`:
  (0,1) matches (1,2) via b=1 --> (0,2). Result: {(0,2)}.

Step-by-step for `{(0,2)} ; {(2,0)}`:
  (0,2) matches (2,0) via b=2 --> (0,0). Result: {(0,0)}.

Step-by-step for `(R_2 ⊗ R_3)`:
  (1,2) matches (2,0) via b=2 --> (1,0). Result: {(1,0)}.

Step-by-step for `{(0,1)} ; {(1,0)}`:
  (0,1) matches (1,0) via b=1 --> (0,0). Result: {(0,0)}.

Both sides yield {(0,0)}. Holds because relational composition is
associative (a standard result in relation algebra).

### (M2) ⊗ Identity

```
id_G ⊗ R_1  = {(0,0),(1,1),(2,2)} ; {(0,1)} = {(0,1)} = R_1   ✓
R_1 ⊗ id_G  = {(0,1)} ; {(0,0),(1,1),(2,2)} = {(0,1)} = R_1   ✓
```

Step-by-step for `id_G ; R_1`:
  (0,0) matches (0,1) via b=0 --> (0,1).
  (1,1): no match (need (1,x) in R_1, but R_1 = {(0,1)}).
  (2,2): no match.
  Result: {(0,1)}.

Step-by-step for `R_1 ; id_G`:
  (0,1) matches (1,1) via b=1 --> (0,1).
  Result: {(0,1)}.

The identity relation maps every state to itself, so composing
with it leaves any relation unchanged.

### (D1) Left Distributivity: ⊗ distributes over ⊕ from the left

```
R_1 ⊗ (R_2 ⊕ R_3)
  = {(0,1)} ; ({(1,2)} ∪ {(2,0)})
  = {(0,1)} ; {(1,2), (2,0)}
  = {(0,2)}

(R_1 ⊗ R_2) ⊕ (R_1 ⊗ R_3)
  = ({(0,1)} ; {(1,2)}) ∪ ({(0,1)} ; {(2,0)})
  = {(0,2)} ∪ {}
  = {(0,2)}   ✓
```

Step-by-step for `R_1 ; (R_2 ∪ R_3)`:
  (0,1) matches (1,2) via b=1 --> (0,2).
  (0,1) does not match (2,0) (need b=1 as first element, but it's 2).
  Result: {(0,2)}.

Step-by-step for `R_1 ; R_3`:
  (0,1): need (1,x) in R_3 = {(2,0)}. No match.
  Result: {}.

Holds because relational composition distributes over union.

### (D2) Right Distributivity: ⊗ distributes over ⊕ from the right

```
(R_1 ⊕ R_2) ⊗ R_3
  = ({(0,1)} ∪ {(1,2)}) ; {(2,0)}
  = {(0,1), (1,2)} ; {(2,0)}
  = {(1,0)}

(R_1 ⊗ R_3) ⊕ (R_2 ⊗ R_3)
  = ({(0,1)} ; {(2,0)}) ∪ ({(1,2)} ; {(2,0)})
  = {} ∪ {(1,0)}
  = {(1,0)}   ✓
```

Step-by-step for `{(0,1), (1,2)} ; {(2,0)}`:
  (0,1): need (1,x) in R_3 = {(2,0)}. No match.
  (1,2): matches (2,0) via b=2 --> (1,0).
  Result: {(1,0)}.

Symmetric argument to (D1).

### (Z) Zero Annihilation

```
emptyset ⊗ R_1  = {} ; {(0,1)} = {}  =  emptyset   ✓
R_1 ⊗ emptyset  = {(0,1)} ; {} = {}  =  emptyset   ✓
```

Composing with the empty relation produces no pairs. No intermediate
states exist to connect source to target.

All eight axioms are satisfied. R is a valid semiring.

> For the parsing-specific interpretation of these axioms, see
> [Section 4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Key Properties

### 4.1 Non-Commutativity

**Claim**: The relational semiring is *not* commutative (⊗ is not
commutative in general).

**Proof by counterexample**: Let G = {0, 1, 2}, R_1 = {(0, 1)},
R_2 = {(1, 2)}.

```
R_1 ⊗ R_2  = {(0,1)} ; {(1,2)} = {(0,2)}
R_2 ⊗ R_1  = {(1,2)} ; {(0,1)} = {}
```

Step-by-step for R_2 ; R_1:
  (1,2): need (2,x) in R_1 = {(0,1)}. No match.
  Result: {}.

Since {(0,2)} != {}, we have R_1 ⊗ R_2 != R_2 ⊗ R_1.   ∎

Non-commutativity is expected and correct: the order of state
transformations matters. Applying rule A then rule B is generally
different from applying B then A.

### 4.2 Idempotency

**Claim**: The relational semiring is idempotent (⊕ is idempotent).

**Proof**: For all R in 2^{G x G}:

```
R ⊕ R  =  R ∪ R  =  R
```

Set union with itself is a no-op.   ∎

Idempotency means that discovering the same reachability fact twice
does not change the analysis result. This is the correct semantic for
Boolean program analysis: we care about *which* state pairs are
reachable, not *how many times* they were discovered.

### 4.3 Finiteness

**Claim**: For a finite ground set G with |G| = n, the carrier has
exactly `2^{n^2}` elements.

**Proof**: The Cartesian product G x G has n^2 elements. The power
set of a set with m elements has 2^m elements. Therefore
|2^{G x G}| = 2^{n^2}.   ∎

Practical consequence: for n = 3 (the default test universe), the
carrier has 2^9 = 512 elements. For n = 8 (typical Boolean program
with 3 variables), the carrier has 2^64 elements -- large but
manageable since most elements are never constructed.

### 4.4 Heap Allocation

**Claim**: RelationalWeight cannot implement `Copy`.

**Reason**: The internal `HashSet<(G, G)>` is heap-allocated.
RelationalWeight implements the `HeapSemiring` trait rather than
the `Copy`-bounded `Semiring` trait. This constrains its use to
`HeapWpds` infrastructure.

---

## 5. Projections and Queries

RelationalWeight provides four projection methods for extracting
reachability information from analysis results:

```
┌─────────────────────────────────────────────────────────────┐
│  R = {(0,1), (0,2), (1,2)}     G = {0, 1, 2}               │
│                                                             │
│  domain(R)      = { 0, 1 }     source states with outgoing │
│  range(R)       = { 1, 2 }     target states with incoming  │
│  image(R, 0)    = { 1, 2 }     where can 0 reach?          │
│  preimage(R, 2) = { 0, 1 }     who can reach 2?            │
└─────────────────────────────────────────────────────────────┘
```

These projections are essential for WPDS analysis:
- After `poststar`, `image(initial_state)` gives the set of reachable
  target states.
- After `prestar`, `preimage(error_state)` gives the set of states
  from which the error is reachable.

---

## 6. Zero Annihilation

The zero element (empty relation `{}`) represents a state where no
source-target pairs are reachable. Its annihilation property
guarantees that unreachable states remain unreachable regardless of
composition:

```
{} ; R  =  {}     for all R in 2^{G x G}
R ; {}  =  {}     for all R in 2^{G x G}
```

This is the correct semantic for state-pair analysis: if any step
along a transformation chain has no state pairs, the entire chain has
no state pairs. No subsequent transformation can create reachability
from nothing.

In the implementation, `is_zero()` checks whether the `pairs`
HashSet is empty:

```rust
fn is_zero(&self) -> bool {
    self.pairs.is_empty()
}
```

---

## 7. Composition Computation

### Worked Example

Consider a parser with states G = {idle, parsing, recovering} and
two grammar rules:

```
Rule A:  idle -> parsing              weight = {(idle, parsing)}
Rule B:  parsing -> recovering        weight = {(parsing, recovering)}
Rule C:  idle -> recovering           weight = {(idle, recovering)}
         parsing -> parsing           weight ∪ {(parsing, parsing)}
```

**Sequencing A then B** (⊗):

```
R_A ; R_B  =  {(idle, parsing)} ; {(parsing, recovering)}
           =  {(idle, recovering)}
```

Starting idle, applying rule A takes us to parsing. Applying rule B
from parsing takes us to recovering. Net effect: idle -> recovering.

**Combining A and C** (⊕):

```
R_A ⊕ R_C  =  {(idle, parsing)} ∪ {(idle, recovering), (parsing, parsing)}
            =  {(idle, parsing), (idle, recovering), (parsing, parsing)}
```

The union shows all state transitions possible from either rule.

**Full path analysis** (A ; B) ⊕ C:

```
(R_A ⊗ R_B) ⊕ R_C
  = {(idle, recovering)} ∪ {(idle, recovering), (parsing, parsing)}
  = {(idle, recovering), (parsing, parsing)}
```

The result shows that idle can reach recovering (via A;B or directly
via C), and parsing can loop to itself (via C).

---

## 8. Connection to WPDS Analysis

The relational weight domain is the foundation of SLAM-style and
BLAST-style Boolean program analysis:

```
┌─────────────────────────────────────────────────────────────┐
│  Grammar Rule (WPDS Rule)                                    │
│                                                             │
│    <p, gamma_src>  -->  <p', gamma_tgt>                     │
│    weight: R ∈ 2^{G×G}                                     │
│                                                             │
│  Each pair (a, b) ∈ R means:                                │
│    "If the parser was in abstract state a before this rule, │
│     it will be in abstract state b after."                  │
│                                                             │
│  WPDS poststar: compose all rule weights along all paths    │
│    Result: {(a, c)} = states reachable from initial configs │
│                                                             │
│  WPDS prestar: compose rule weights backward                │
│    Result: {(a, c)} = states that can reach target configs  │
└─────────────────────────────────────────────────────────────┘
```

In PraTTaIL, this framework models grammar analysis: each grammar
rule is a "statement" that transforms the parser's abstract state.
WPDS composition tracks which parser states are reachable after
sequences of rule applications.

---

## 9. Comparison with BooleanWeight

The relational and Boolean semirings both model reachability, but at
different granularities:

| Property            | RelationalWeight                  | BooleanWeight              |
|---------------------|-----------------------------------|----------------------------|
| Carrier set         | 2^{G x G} (binary relations)      | {false, true}              |
| ⊕ (addition)        | set union                         | logical OR                 |
| ⊗ (multiplication)  | relational composition            | logical AND                |
| 0 (zero)            | empty relation                    | false                      |
| 1 (one)             | identity relation                 | true                       |
| Commutative?        | No (order matters)                | Yes                        |
| Idempotent?         | Yes: R ∪ R = R                    | Yes: true OR true = true   |
| Copy?               | No (heap-allocated)               | Yes                        |
| Granularity         | Per-state-pair reachability       | Scalar reachability        |
| Projection to Bool  | `is_zero()` (any pair reachable?) | identity                   |

BooleanWeight collapses all state pairs to a single bit: "is anything
reachable?" RelationalWeight preserves the full source-target mapping:
"for each source state, which target states are reachable?"

The relational semiring is strictly more informative. BooleanWeight is
the homomorphic image of RelationalWeight under the projection
`R -> (R != emptyset)`.

---

## 10. Pseudocode: Relational Composition

The core composition algorithm implements the nested-loop join:

```
ALGORITHM RelationalComposition(R_1, R_2)
────────────────────────────────────────────
  Input:  Relations R_1, R_2 ⊆ G x G
  Output: R_1 ; R_2 = {(a,c) | exists b: (a,b) ∈ R_1 ∧ (b,c) ∈ R_2}

  1.  result <- {}

  2.  for each (a, b) in R_1 do
  3.      for each (b', c) in R_2 do
  4.          if b == b' then
  5.              result <- result ∪ {(a, c)}
  6.      end for
  7.  end for

  8.  return result
```

**Complexity**: O(|R_1| * |R_2|) in the worst case. For sparse
relations (typical in program analysis), the number of matching
pairs is much smaller. An index on the first element of R_2 would
reduce this to O(|R_1| * avg_fan_out(R_2)).

**Optimization**: For dense relations on small G, a Boolean matrix
representation enables composition via matrix multiplication in
O(n^3) where n = |G|. This would be faster when |R_1| * |R_2| > n^3.

---

## 11. Rust Implementation

The following shows the core `RelationalWeight` implementation from
`prattail/src/relational.rs`.

```rust
/// Relational weight: binary relation on a finite set G.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalWeight<G: Clone + Eq + Hash + Debug + Send + Sync + 'static> {
    /// Set of (source, target) state pairs.
    pub pairs: HashSet<(G, G)>,
    /// The full universe of G values (needed for identity relation).
    universe: Vec<G>,
}

impl<G: ...> HeapSemiring for RelationalWeight<G> {
    fn zero() -> Self {
        RelationalWeight { pairs: HashSet::new(), universe: Vec::new() }
    }

    fn one() -> Self {
        RelationalWeight { pairs: HashSet::new(), universe: Vec::new() }
    }

    fn plus(&self, other: &Self) -> Self {
        let pairs: HashSet<(G, G)> = self.pairs.union(&other.pairs).cloned().collect();
        let universe = if self.universe.len() >= other.universe.len() {
            self.universe.clone()
        } else {
            other.universe.clone()
        };
        RelationalWeight { pairs, universe }
    }

    fn times(&self, other: &Self) -> Self {
        let mut pairs = HashSet::new();
        for (a, b) in &self.pairs {
            for (b2, c) in &other.pairs {
                if b == b2 {
                    pairs.insert((a.clone(), c.clone()));
                }
            }
        }
        // ... universe selection ...
        RelationalWeight { pairs, universe }
    }

    fn is_zero(&self) -> bool { self.pairs.is_empty() }

    fn is_one(&self) -> bool {
        if self.universe.is_empty() { return self.pairs.is_empty(); }
        self.pairs.len() == self.universe.len()
            && self.universe.iter().all(|g| self.pairs.contains(&(g.clone(), g.clone())))
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.pairs == other.pairs
    }
}
```

### Implementation Notes

- **Universe storage**: The `universe` field is stored alongside the
  pairs so that `identity()` can construct the correct identity
  relation without requiring the caller to pass the universe
  repeatedly. After binary operations, the larger universe is retained.

- **Context-free `zero()` and `one()`**: The `HeapSemiring` trait
  requires parameterless constructors. The trait-level `zero()` and
  `one()` return relations with an empty universe. Callers should use
  `RelationalWeight::empty(universe)` and
  `RelationalWeight::identity(universe)` when the universe context
  is available.

- **HashSet for pairs**: `HashSet<(G, G)>` provides O(1) amortized
  membership tests and insertion. The type parameter G must satisfy
  `Hash + Eq` for HashSet compatibility.

- **approx_eq ignores epsilon**: Binary relations are discrete objects
  with no floating-point imprecision. The epsilon parameter is
  accepted for trait compatibility but ignored.

- **Default = one()**: A newly created weight represents the identity
  transformation (every state maps to itself), not the empty relation
  (no state pairs).

---

## 12. Integration into PraTTaIL

RelationalWeight is used in three main subsystems:

### 12.1 HeapWpds Infrastructure (relational.rs)

`HeapWpds<W>` and `HeapWpdsRule<W>` mirror the standard `Wpds<W>`
types but accept `HeapSemiring`-bounded weights:

```
┌───────────────────────┐     ┌───────────────────────┐
│  Wpds<TropicalWeight> │     │  HeapWpds<Relational>  │
│  (Copy semirings)     │     │  (Heap semirings)      │
└───────────────────────┘     └────────────────────────┘
```

Both expose the same `from_gamma()` and `weight()` accessors.

### 12.2 ARA Weight Domain (ara.rs)

Alternating register automata use relational weights for state-pair
reachability tracking in their acceptance analysis.

### 12.3 Safety Verification (verify.rs)

Prestar on RelationalWeight confirms which initial states can reach
error states, providing precise safety verification for parser
grammars.

---

## 13. Source Reference & See Also

### Source Location

- **File**: `prattail/src/relational.rs`
- **Struct**: `RelationalWeight<G> { pairs: HashSet<(G, G)>, universe: Vec<G> }`
- **HeapSemiring trait**: lines 29--48
- **HeapWpds struct**: lines 219--237
- **HeapWpdsRule enum**: lines 239--280
- **Tests**: 13 tests covering all axioms and API methods

### Cross-References

- [Semiring Algebra Overview](../semirings.md) -- Axiom definitions
  and classification of all semirings
- [Boolean Weight Theory](boolean-weight.md) -- Scalar reachability:
  the simplest projection of relational weights
- [Provenance Weight Theory](provenance-weight.md) -- Another
  HeapSemiring weight sharing the HeapSemiring trait
- [Tensor Weight Theory](tensor-weight.md) -- Correlated multi-analysis
  composition
- [Relational Design Doc](../../../design/wfst/semirings/relational-weight.md) --
  Implementation decisions and pipeline integration details
- [WPDS Core](../../../src/wpds.rs) -- Standard WPDS with
  Copy-bounded semirings
- [Safety Verification](../../../src/verify.rs) -- Prestar analysis
  using relational weights
- [ARA](../../../src/ara.rs) -- Alternating register automata with
  relational weight domains

### Academic References

- T. Reps, A. Lal, and N. Kidd. "Program Analysis Using Weighted
  Pushdown Systems." In Proceedings of the 27th Conference on
  Foundations of Software Technology and Theoretical Computer Science
  (FSTTCS), 2007.
