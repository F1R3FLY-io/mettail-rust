# ContextWeight: Set Semiring (2026-03-01)

> **Source**: `prattail/src/automata/semiring.rs`, lines 622--757
> **Carrier**: `ContextWeight(u128)` -- a 128-bit bitset over rule label IDs

---

## Table of Contents

1. [Intuition & Motivation](#1-intuition--motivation)
2. [Formal Definition](#2-formal-definition)
3. [Semiring Axiom Verification](#3-semiring-axiom-verification)
4. [Key Properties](#4-key-properties)
5. [Relationship to BooleanWeight](#5-relationship-to-booleanweight)
6. [Interpretation for Parsing](#6-interpretation-for-parsing)
7. [Worked Example](#7-worked-example)
8. [Complexity Analysis](#8-complexity-analysis)
9. [Rust Implementation](#9-rust-implementation)
10. [Comparison Table](#10-comparison-table)
11. [Source References](#11-source-references)

---

## 1. Intuition & Motivation

When the prediction WFST dispatches a token to a parse rule, we often want
more than a yes/no answer (BooleanWeight) or a simple count
(CountingWeight).  We want to know *exactly which rules* contributed to the
current state.  Did only `AddInt` fire, or did both `AddInt` and `AddStr`
match?  Which rules are still live after composing two sequential segments?

The ContextWeight semiring answers these questions by carrying a **set of
rule label IDs** through the WFST.  Each bit position in a 128-bit integer
corresponds to a distinct rule label.  Union (⊕) collects rules from
parallel alternatives.  Intersection (⊗) retains only rules common to
both sequential segments.  The result is a precise, per-state record of
which grammar rules are responsible for each dispatch decision.

Three concrete applications motivate this semiring:

1. **Follow-set tightening**: knowing which rules contributed to a state
   allows the error recovery system to select more precise synchronization
   tokens (only those in the FOLLOW sets of the contributing rules, rather
   than the FOLLOW set of the entire category).

2. **Ambiguity diagnosis**: when `|ContextWeight| > 1` at a dispatch
   point, the parser can emit a diagnostic naming the exact conflicting
   rules (e.g., "rules `AddInt` and `AddStr` both match token `+`")
   rather than a generic "ambiguous dispatch" warning.

3. **Per-token NFA spillover decisions**: the NFA disambiguation layer
   only needs to spill alternatives when the ContextWeight has more than
   one bit set.  Single-bit contexts guarantee unambiguous dispatch and
   skip the spillover path entirely.

---

## 2. Formal Definition

The set semiring over rule labels is the algebraic structure:

```
S  =  ( 𝒫(Labels),  ∪,  ∩,  ∅,  U )
```

where `Labels = {0, 1, ..., 127}` and `𝒫(Labels)` is its power set,
represented as `BitSet<u128>`.

| Component                   | Symbol | Concrete value             | Meaning                                  |
|-----------------------------|--------|----------------------------|------------------------------------------|
| Carrier set                 | K      | 𝒫(Labels) via `u128`       | Subsets of up to 128 rule label IDs      |
| Addition (⊕)                | ∪      | bitwise OR (`\|`)          | Any contributing rule from either path   |
| Multiplication (⊗)          | ∩      | bitwise AND (`&`)          | Rules common to both sequential segments |
| Additive identity (0̄)       | ∅      | `0_u128`                   | No rules reachable (empty set)           |
| Multiplicative identity (1̄) | U      | `u128::MAX` (all 128 bits) | All rules reachable (universal set)      |

In WFST terms:

- **⊕  = ∪** combines parallel paths: the union of contributing rules from
  each alternative.
- **⊗  = ∩** sequences path segments: only rules that contributed to *both*
  segments survive composition.
- **0̄ = ∅** is the "no rules" weight -- the additive identity (∅ ∪ A = A).
- **1̄ = U** is the "all rules" weight -- the multiplicative identity
  (U ∩ A = A).

---

## 3. Semiring Axiom Verification

We verify all required semiring axioms.  Since ⊕ and ⊗ are set union and
intersection over a Boolean algebra, the axioms follow from classical set
theory.  We provide explicit proofs with concrete witnesses for rigor.

Let A, B, C be arbitrary subsets of Labels.

### 3.1 (K, ⊕, 0̄) is a commutative monoid

**Closure**: ∪ maps 𝒫(Labels) x 𝒫(Labels) into 𝒫(Labels).  The union of
two subsets of Labels is a subset of Labels.

**Associativity of ⊕**: (A ∪ B) ∪ C = A ∪ (B ∪ C)

Proof.  An element x is in (A ∪ B) ∪ C iff x in A ∪ B or x in C, iff
(x in A or x in B) or x in C, iff x in A or (x in B or x in C) (by
associativity of logical OR), iff x in A or x in B ∪ C, iff x in
A ∪ (B ∪ C).  QED.

Concrete witness: A = {0,1}, B = {1,2}, C = {2,3}.
- (A ∪ B) ∪ C = {0,1,2} ∪ {2,3} = {0,1,2,3}
- A ∪ (B ∪ C) = {0,1} ∪ {1,2,3} = {0,1,2,3}  Check.

**Commutativity of ⊕**: A ∪ B = B ∪ A

Proof.  x in A ∪ B iff x in A or x in B iff x in B or x in A (by
commutativity of logical OR) iff x in B ∪ A.  QED.

**Identity of ⊕**: A ∪ ∅ = A

Proof.  x in A ∪ ∅ iff x in A or x in ∅.  Since x in ∅ is always
false, this reduces to x in A.  Therefore A ∪ ∅ = A.  QED.

### 3.2 (K, ⊗, 1̄) is a monoid

**Closure**: ∩ maps 𝒫(Labels) x 𝒫(Labels) into 𝒫(Labels).  The intersection
of two subsets of Labels is a subset of Labels.

**Associativity of ⊗**: (A ∩ B) ∩ C = A ∩ (B ∩ C)

Proof.  x in (A ∩ B) ∩ C iff x in A ∩ B and x in C, iff (x in A and x
in B) and x in C, iff x in A and (x in B and x in C) (by associativity
of logical AND), iff x in A and x in B ∩ C, iff x in A ∩ (B ∩ C).  QED.

Concrete witness: A = {1,2,3}, B = {2,3,4}, C = {3,4,5}.
- (A ∩ B) ∩ C = {2,3} ∩ {3,4,5} = {3}
- A ∩ (B ∩ C) = {1,2,3} ∩ {3,4} = {3}  Check.

**Identity of ⊗**: A ∩ U = A

Proof.  x in A ∩ U iff x in A and x in U.  Since U = Labels, x in U is
always true for any x in Labels.  This reduces to x in A.  Therefore
A ∩ U = A.  QED.

### 3.3 Annihilation: 0̄ ⊗ A = A ⊗ 0̄ = 0̄

Proof.  ∅ ∩ A = {x | x in ∅ and x in A}.  Since x in ∅ is always false,
the conjunction is false for all x, yielding ∅.  By commutativity of ∩,
A ∩ ∅ = ∅ also.  QED.

Concrete witness: A = {1,2,3}.
- ∅ ∩ {1,2,3} = ∅  Check.
- {1,2,3} ∩ ∅ = ∅  Check.

### 3.4 Distributivity: ⊗ distributes over ⊕

**Left distributivity**: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)

Proof.  x in A ∩ (B ∪ C) iff x in A and (x in B or x in C), iff
(x in A and x in B) or (x in A and x in C) (by distributivity of
AND over OR), iff x in A ∩ B or x in A ∩ C, iff x in (A ∩ B) ∪ (A ∩ C).
QED.

Concrete witness: A = {1,2,3}, B = {1,2}, C = {2,3}.
- A ∩ (B ∪ C) = {1,2,3} ∩ {1,2,3} = {1,2,3}
- (A ∩ B) ∪ (A ∩ C) = {1,2} ∪ {2,3} = {1,2,3}  Check.

**Right distributivity**: (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)

Proof.  Follows by the same argument, applying commutativity of ∩ to
reduce to the left-distributive case: (A ∪ B) ∩ C = C ∩ (A ∪ B) =
(C ∩ A) ∪ (C ∩ B) = (A ∩ C) ∪ (B ∩ C).  QED.

Concrete witness: A = {0,1}, B = {1,2}, C = {1,3}.
- (A ∪ B) ∩ C = {0,1,2} ∩ {1,3} = {1}
- (A ∩ C) ∪ (B ∩ C) = {1} ∪ {1} = {1}  Check.

### 3.5 Idempotence of ⊕

A ∪ A = A

Proof.  x in A ∪ A iff x in A or x in A iff x in A.  QED.

This establishes that the set semiring is an **idempotent semiring**
(also called a *dioid*), the same property held by BooleanWeight and
TropicalWeight.

---

All semiring axioms hold.  QED.

---

## 4. Key Properties

### 4.1 Commutativity of ⊗

Intersection is commutative: A ∩ B = B ∩ A.

Proof.  x in A ∩ B iff x in A and x in B iff x in B and x in A
(commutativity of AND) iff x in B ∩ A.  QED.

Therefore S is a **commutative semiring**.

### 4.2 Boolean algebra structure

The carrier (𝒫(Labels), ∪, ∩, ∅, U) forms a **complemented distributive
lattice** (equivalently, a Boolean algebra) with complement A^c = U \ A.
The semiring uses only the lattice structure (∪ and ∩); the complement
is not part of the semiring axioms but is available for operations like
set difference in diagnostic code.

In terms of the bitset representation:
- Complement: `!bits` (bitwise NOT)
- Difference: `a & !b` (bitwise AND-NOT)
- Symmetric difference: `a ^ b` (bitwise XOR)

### 4.3 Lattice ordering

The natural partial order on subsets is inclusion: A <= B iff A subset-of B.
The implementation uses a different total order for `Ord`: cardinality first,
then raw bit value for deterministic tiebreaking:

```
cmp(A, B)  =  |A|.cmp(|B|).then(bits(A).cmp(bits(B)))
```

This means fewer contributing rules sort before more contributing rules,
which is useful when ContextWeight appears as the right component of a
ProductWeight (e.g., `ProductWeight<TropicalWeight, ContextWeight>`).

### 4.4 Finite carrier

|K| = 2^128.  While astronomically large, the carrier is finite and each
element fits in a single machine word on architectures with 128-bit integer
support (which Rust provides natively via `u128`).  No heap allocation is
needed.

### 4.5 Why Intersection for ⊗?

A natural question: why does sequential composition use intersection (∩)
rather than union (∪)? After all, union collects *more* information. The
answer is that **union would defeat the purpose of tracking**.

**Counterexample.** Consider a two-segment path where segment 1 is reached
via rules {AddInt, SubInt} and segment 2 is reached via rules {MulFloat}:

```
  Segment 1: CW₁ = {AddInt, SubInt}     (integer arithmetic rules)
  Segment 2: CW₂ = {MulFloat}           (float multiplication rule)
```

With ⊗ = ∩ (intersection):
```
  CW₁ ⊗ CW₂ = {AddInt, SubInt} ∩ {MulFloat} = ∅
```
The empty result correctly signals that no single rule contributed to both
segments — this is a cross-category handoff, not a single-rule derivation.

With ⊗ = ∪ (union — the wrong choice):
```
  CW₁ ⊗ CW₂ = {AddInt, SubInt} ∪ {MulFloat} = {AddInt, SubInt, MulFloat}
```
The union **grows monotonically** as segments are composed. Every rule that
ever contributed to any segment would accumulate in the set, regardless of
whether it actually spans the composed path. After composing N segments, the
ContextWeight would contain the union of all rules from all segments — which
is just the set of all rules in the grammar, providing no useful information.

The intersection semantics ensure that only rules common to all segments
survive composition, producing a precise answer to the question "which rules
span this entire path?" In practice, paths typically narrow quickly: a
two-segment composition often reduces to a singleton or the empty set,
immediately identifying whether the dispatch is unambiguous.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 5. Relationship to BooleanWeight

BooleanWeight is a **projection** (surjective semiring homomorphism) of
ContextWeight:

```
pi: 𝒫(Labels) -> {false, true}
pi(S) = |S| > 0
```

Equivalently:
- S = ∅  maps to  false (unreachable)
- S != ∅  maps to  true  (reachable)

This projection is a semiring homomorphism:

**Plus preservation**: pi(A ∪ B) = |A ∪ B| > 0 = (|A| > 0) OR (|B| > 0)
= pi(A) OR pi(B).

Proof.  A ∪ B = ∅ iff both A = ∅ and B = ∅.  Therefore A ∪ B != ∅ iff
A != ∅ or B != ∅.  QED.

**Times preservation**: pi(A ∩ B) = |A ∩ B| > 0 implies pi(A) AND pi(B).

For the precise statement: if both A and B are non-empty, A ∩ B *may* be
empty (e.g., A = {0}, B = {1}).  However, the projection preserves the
algebraic structure in the following sense:

```
pi(0̄) = pi(∅) = false = 0_B                     Check.
pi(1̄) = pi(U) = true  = 1_B                     Check.
pi(A ∪ B) = pi(A) ∨ pi(B)                       (proven above)
```

For ⊗, the homomorphism property pi(A ∩ B) = pi(A) ∧ pi(B) does **not**
hold in general (counterexample: A = {0}, B = {1}, pi(A) ∧ pi(B) = true,
but pi(A ∩ B) = pi(∅) = false).  Therefore pi is a **⊕-homomorphism** but
not a full semiring homomorphism.

Nonetheless, ContextWeight **strictly generalizes** BooleanWeight in the
following operational sense:

- Every question answerable by BooleanWeight is answerable by
  ContextWeight: "is this reachable?" reduces to `bits != 0`.
- ContextWeight answers strictly more questions: "which rules are
  reachable?", "how many rules contribute?", "do rules X and Y both
  contribute?"

The BooleanWeight dead-rule detection in `pipeline.rs` can therefore be
viewed as computing ContextWeights and then projecting down to boolean
via `is_zero()`.

---

## 6. Interpretation for Parsing

### 6.1 Bit assignment

Each rule label in the grammar is assigned a unique integer ID in
[0, 128).  The assignment is dense (no gaps) and stable within a single
compilation.  Bit position `i` in the `u128` corresponds to rule label
ID `i`.

For a grammar with N rules (N <= 128), only the low N bits are
semantically meaningful.  The remaining 128 - N high bits in the universal
set 1̄ are harmless: they are intersected away by any singleton or small
set, and unioned in without introducing spurious IDs (since no rule maps
to those bit positions).

### 6.2 WFST state annotation

After prediction WFST construction, each state can carry a ContextWeight
showing which rules contributed to reaching that state.  The propagation
follows the standard WFST semiring semantics:

- **Parallel alternatives** (e.g., token `+` dispatches to both `AddInt`
  and `AddStr`): ContextWeights are unioned.  The resulting set is
  `{AddInt, AddStr}`.

- **Sequential composition** (e.g., state q0 via edge e1 to q1, then
  edge e2 to q2): ContextWeights are intersected.  Only rules that
  contributed to *both* segments survive.

### 6.3 Applications

**Follow-set tightening.**  When error recovery needs synchronization
tokens for a state, it can compute the FOLLOW set of only the rules in
the ContextWeight, rather than the entire category's FOLLOW set.  This
produces fewer false-positive sync tokens and faster recovery.

**Ambiguity diagnosis.**  At a dispatch point where `|ContextWeight| > 1`,
the parser can enumerate the set bits and map them back to rule labels,
producing diagnostics like:

```
warning[W02]: ambiguous dispatch at token `+`
  --> rules: AddInt (bit 12), AddStr (bit 37), Concat (bit 38)
  = help: consider adding explicit priority annotations
```

**NFA spillover decisions.**  The NFA disambiguation layer checks the
ContextWeight cardinality at each dispatch point.  If `count() == 1`, the
dispatch is unambiguous and the fast path executes directly.  If
`count() > 1`, the NFA spills N-1 alternatives for replay, using the
ContextWeight bits to identify exactly which rules to spill.

---

## 7. Worked Example

Consider a simplified calculator grammar with 3 categories and 7 rules:

```
Category Int (rules):
    bit 0: AddInt    .  a:Int, b:Int  |-  a "+" b  : Int
    bit 1: SubInt    .  a:Int, b:Int  |-  a "-" b  : Int
    bit 2: IntToFloat . a:Int         |-  "float" "(" a ")" : Float    (cast)

Category Float (rules):
    bit 3: AddFloat  .  a:Float, b:Float  |-  a "+" b  : Float
    bit 4: MulFloat  .  a:Float, b:Float  |-  a "*" b  : Float

Category Bool (rules):
    bit 5: EqInt     .  a:Int, b:Int      |-  a "==" b  : Bool
    bit 6: EqFloat   .  a:Float, b:Float  |-  a "==" b  : Bool
```

### 7.1 Dispatch on token `+`

Token `+` is an infix operator in both Int and Float.  When dispatching
from the root state:

```
ContextWeight for Int dispatch on `+`:
    CW_Int = singleton(0)          = 0b0000001   (AddInt)

ContextWeight for Float dispatch on `+`:
    CW_Float = singleton(3)        = 0b0001000   (AddFloat)
```

If both are reachable via parallel WFST paths (e.g., the parser does not
yet know the category):

```
CW_combined = CW_Int ⊕ CW_Float
            = 0b0000001 ∪ 0b0001000
            = 0b0001001
            = {AddInt, AddFloat}
```

The cardinality is 2, indicating ambiguity.  The diagnostic can name both
rules.

### 7.2 Sequential composition: parse `x + y == z`

Parsing proceeds in two segments:

**Segment 1** (parse `x + y`): produces ContextWeight from Int dispatch.

```
CW_seg1 = {AddInt}    = 0b0000001
```

**Segment 2** (parse `== z`): the `==` token dispatches to both EqInt and
EqFloat.

```
CW_seg2 = {EqInt, EqFloat}    = 0b1100000
```

Sequential composition:

```
CW_path = CW_seg1 ⊗ CW_seg2
        = 0b0000001 ∩ 0b1100000
        = 0b0000000
        = ∅
```

The intersection is empty because no single rule contributed to *both*
segments.  This is expected: AddInt produced the first segment, and EqInt
will consume its result.  The empty intersection signals that no single
rule spans the entire `x + y == z` expression -- it is necessarily a
two-rule derivation, with the handoff point at `==`.

### 7.3 Parallel alternatives for the `==` token

If the parser is dispatching `==` from a state that might be in Int or
Float context:

```
CW_int_ctx  = singleton(5) = 0b0100000   (EqInt)
CW_float_ctx = singleton(6) = 0b1000000   (EqFloat)

CW_dispatch = CW_int_ctx ⊕ CW_float_ctx
            = 0b0100000 ∪ 0b1000000
            = 0b1100000
            = {EqInt, EqFloat}
```

Count = 2, so the NFA disambiguation layer spills one alternative for
replay while the parser tries the other.

---

## 8. Complexity Analysis

All ContextWeight operations reduce to single-instruction bitwise
operations on `u128`:

| Operation              | Implementation     | Time complexity | Space complexity |
|------------------------|--------------------|-----------------|------------------|
| `zero()`               | `0_u128`           | O(1)            | O(1) -- 16 bytes |
| `one()`                | `u128::MAX`        | O(1)            | O(1) -- 16 bytes |
| `plus(a, b)` (union)   | `a \| b`           | O(1)            | O(1) -- 16 bytes |
| `times(a, b)` (intersect) | `a & b`         | O(1)            | O(1) -- 16 bytes |
| `is_zero()`            | `bits == 0`        | O(1)            | --               |
| `is_one()`             | `bits == u128::MAX`| O(1)            | --               |
| `count()`              | `count_ones()`     | O(1)*           | --               |
| `contains(id)`         | `(bits >> id) & 1` | O(1)            | --               |
| `singleton(id)`        | `1 << id`          | O(1)            | O(1) -- 16 bytes |
| `insert(id)`           | `bits \| (1 << id)`| O(1)            | O(1) -- 16 bytes |

*`count_ones()` compiles to the hardware `popcnt` instruction on x86_64,
which executes in a single cycle.

**Capacity limitation**: 128 rule labels.  Most practical grammars have
far fewer than 128 rules (the Calculator grammar has ~50, RhoCalc has
~80).  For hypothetical grammars exceeding 128 rules, ContextWeight
would need to be generalized to a wider bitset (e.g., `[u128; 2]` for 256
labels), at the cost of losing the `Copy` trait's zero-overhead semantics.

**Comparison to alternative representations**:

| Representation   | Plus (union)   | Times (intersect) | Space per weight  |
|------------------|----------------|-------------------|-------------------|
| `u128` bitset    | O(1)           | O(1)              | 16 bytes, inline  |
| `HashSet<u8>`    | O(n)           | O(n)              | 24+ bytes, heap   |
| `BTreeSet<u8>`   | O(n log n)     | O(n log n)        | 24+ bytes, heap   |
| `Vec<bool>`      | O(n)           | O(n)              | n bytes, heap     |

The bitset representation dominates in every metric for n <= 128.

---

## 9. Rust Implementation

The complete implementation from `prattail/src/automata/semiring.rs`
(lines 626--757):

**Struct definition and doc comment**:

```rust
/// Set semiring over rule labels using a 128-bit bitset.
///
/// **Semiring:** `(𝒫(Labels), ∪, ∩, ∅, U)`
///
/// - `plus` = union (any contributing rule from either path)
/// - `times` = intersection (rules common to both sequential segments)
/// - `zero` = ∅ (no rules reachable)
/// - `one` = U (all rules reachable -- universal set)
///
/// **Applications:**
/// - Follow-set tightening (more precise sync token selection)
/// - Ambiguity diagnosis ("rules PInput and POutput both match `Ident`")
/// - Per-token NFA spillover decisions (only where |ContextWeight| > 1)
///
/// **Capacity:** Up to 128 distinct rule labels (sufficient for most grammars).
/// The bitset representation is `Copy` and requires no allocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ContextWeight(u128);
```

**Constructors and accessors**:

```rust
impl ContextWeight {
    /// Create a ContextWeight from a raw bitset.
    #[inline]
    pub const fn new(bits: u128) -> Self {
        ContextWeight(bits)
    }

    /// Create a ContextWeight with a single rule label set.
    #[inline]
    pub const fn singleton(label_id: u8) -> Self {
        assert!(label_id < 128, "label_id must be < 128");
        ContextWeight(1u128 << label_id)
    }

    /// Return the raw bitset.
    #[inline]
    pub const fn bits(&self) -> u128 {
        self.0
    }

    /// Count the number of set bits (contributing rules).
    #[inline]
    pub const fn count(&self) -> u32 {
        self.0.count_ones()
    }

    /// Check if a specific label ID is in the set.
    #[inline]
    pub const fn contains(&self, label_id: u8) -> bool {
        (self.0 >> label_id) & 1 == 1
    }

    /// Insert a label ID into the set.
    #[inline]
    pub const fn insert(self, label_id: u8) -> Self {
        ContextWeight(self.0 | (1u128 << label_id))
    }
}
```

**Semiring trait implementation**:

```rust
impl Semiring for ContextWeight {
    /// Zero = ∅ (empty set -- no rules reachable).
    #[inline]
    fn zero() -> Self {
        ContextWeight(0)
    }

    /// One = U (universal set -- all 128 bits set).
    #[inline]
    fn one() -> Self {
        ContextWeight(u128::MAX)
    }

    /// Plus = union: any rule from either alternative is contributing.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        ContextWeight(self.0 | other.0)
    }

    /// Times = intersection: only rules common to both segments contribute.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        ContextWeight(self.0 & other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == u128::MAX
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.0 == other.0  // exact comparison (no floating point)
    }
}
```

**Ordering**: ordered by set size (cardinality), then by raw bits for
deterministic tiebreaking:

```rust
impl Ord for ContextWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .count_ones()
            .cmp(&other.0.count_ones())
            .then_with(|| self.0.cmp(&other.0))
    }
}
```

**Display**: renders special symbols for empty and universal sets, and a
compact `{count|bits}` format otherwise:

```rust
impl fmt::Display for ContextWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "∅")
        } else if self.is_one() {
            write!(f, "U")
        } else {
            write!(f, "{{{}b|{}}}", self.0.count_ones(), self.0)
        }
    }
}
```

**Default**: returns `one()` (= U), consistent with the convention that
the default weight is the multiplicative identity:

```rust
impl Default for ContextWeight {
    fn default() -> Self { Self::one() }
}
```

**Derived traits**: `Clone`, `Copy`, `Debug`, `Eq`, `PartialEq`, `Hash`.
The `Copy` trait is critical -- it means ContextWeight can be passed by
value with zero overhead, same as a plain integer.

---

## 10. Comparison Table

| Property                  | ContextWeight        | BooleanWeight        | CountingWeight       | TropicalWeight         |
|---------------------------|----------------------|----------------------|----------------------|------------------------|
| **Carrier**               | 𝒫({0..127}) via u128 | {false, true}       | N (natural numbers)  | R+ union {+inf}        |
| **⊕ (plus)**              | ∪ (set union)        | ∨ (OR)              | + (addition)         | min                    |
| **⊗ (times)**             | ∩ (set intersection) | ∧ (AND)             | x (multiplication)   | + (addition)           |
| **0 (zero)**              | ∅                    | false               | 0                    | +inf                   |
| **1 (one)**               | U (all bits set)     | true                | 1                    | 0.0                    |
| **Commutative**           | Yes                  | Yes                 | Yes                  | Yes                    |
| **Idempotent (⊕)**        | Yes (A ∪ A = A)      | Yes                 | No (3+3=6 != 3)     | Yes (min(a,a) = a)    |
| **Size**                  | 2^128 elements       | 2 elements          | Countably infinite   | Uncountably infinite   |
| **Semantics**             | Rule-set tracking    | Reachability        | Path counting        | Shortest path / cost   |
| **PraTTaIL use**          | Ambiguity diagnosis  | Dead-rule detection | Ambiguity counting   | Priority dispatch      |
| **Rust size**             | 16 bytes (inline)    | 1 byte (inline)     | 8 bytes (inline)     | 8 bytes (inline)       |
| **Rust Display**          | ∅ / U / {nb\|bits}   | ⊤ / ⊥               | integer              | float / inf            |

---

## 11. Source References

**Source file**: `prattail/src/automata/semiring.rs`
- Struct definition and constructors: lines 626--682
- Semiring trait implementation: lines 684--722
- Ord implementation: lines 724--738
- Display implementation: lines 741--751
- Default implementation: lines 753--757

**Tests**: `prattail/src/automata/semiring.rs`, lines 1516--1609
- `test_context_weight_semiring_laws` -- zero/one identity, annihilation, commutativity
- `test_context_weight_union_intersection` -- concrete union/intersection with bit patterns
- `test_context_weight_singleton_and_contains` -- singleton construction, membership, insert
- `test_context_weight_idempotent_plus` -- ⊕ idempotency
- `test_context_weight_distributivity` -- left distributivity of ⊗ over ⊕
- `test_context_weight_ordering` -- cardinality-based ordering
- `test_context_weight_display` -- Display format for ∅, U, and general sets
- `test_context_weight_product_with_tropical` -- ProductWeight<TropicalWeight, ContextWeight> composition (lines 1719--1735)

**Cross-references**:
- [BooleanWeight theory](./boolean-weight.md) -- ContextWeight generalizes BooleanWeight (Section 5)
- [CountingWeight theory](./counting-weight.md) -- alternative cardinality-only analysis
- [TropicalWeight theory](./tropical-weight.md) -- the primary semiring used for dispatch priority
- [ProductWeight theory](./product-weight.md) -- ProductWeight<TropicalWeight, ContextWeight> composition
- [Semirings overview](../semirings.md) -- comprehensive survey of all semirings in PraTTaIL
