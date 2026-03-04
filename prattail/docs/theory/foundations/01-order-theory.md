# Order Theory Foundations for PraTTaIL

This document establishes the order-theoretic foundations used throughout
PraTTaIL's weighted automata pipeline. Every semiring, lattice, and
fixed-point computation in the codebase rests on the definitions and
theorems proven here. Cross-references to source files use the format
`semiring.rs:106`, meaning line 106 of
`prattail/src/automata/semiring.rs`.

---

## 1  Partial Orders and Posets

**Definition 1.1 (Partial Order).**
A *partial order* on a set S is a binary relation  ≤  on S satisfying,
for all a, b, c in S:

1. **Reflexivity.**  a ≤ a.
2. **Antisymmetry.**  a ≤ b  and  b ≤ a  implies  a = b.
3. **Transitivity.**  a ≤ b  and  b ≤ c  implies  a ≤ c.

**Definition 1.2 (Poset).**
A *partially ordered set* (poset) is a pair (S, ≤) where ≤ is a partial
order on S.

**Example 1.3 (Extended non-negative reals).**
The set  R+ = R_{\geq 0} ∪ {∞}  with the standard ≤ forms a poset
(R+, ≤).  PraTTaIL uses this as the carrier for `TropicalWeight`
(`semiring.rs:69`) and `EditWeight` (`semiring.rs:385`), where ∞ serves
as the unreachable element.

**Example 1.4 (Power set).**
For a finite set S, the power set 2^S with subset inclusion ⊆ forms a
poset (2^S, ⊆).  PraTTaIL uses this as the carrier for `ContextWeight`
(`semiring.rs:643`), where S = {0, 1, ..., 127} and the bitset `u128`
represents elements of 2^S.

**Hasse Diagram for (2^{a,b}, ⊆):**

```
           {a, b}
          ╱      ╲
        {a}      {b}
          ╲      ╱
            ∅
```

Each edge denotes the *covers* relation: X covers Y when Y ⊆ X and
there is no Z with Y ⊂ Z ⊂ X.  The diagram faithfully represents the
four-element Boolean lattice used throughout Section 4 below.

---

## 2  Meet, Join, and Lattices

**Definition 2.1 (Greatest Lower Bound / Meet).**
In a poset (S, ≤), an element m ∈ S is the *greatest lower bound* (or
*meet*) of a, b ∈ S, written m = a ∧ b, when:

1. m ≤ a  and  m ≤ b.                          (lower bound)
2. For all l ∈ S:  l ≤ a  and  l ≤ b  implies  l ≤ m.  (greatest)

**Definition 2.2 (Least Upper Bound / Join).**
An element j ∈ S is the *least upper bound* (or *join*) of a, b ∈ S,
written j = a ∨ b, when:

1. a ≤ j  and  b ≤ j.                          (upper bound)
2. For all u ∈ S:  a ≤ u  and  b ≤ u  implies  j ≤ u.  (least)

**Definition 2.3 (Lattice).**
A poset (L, ≤) is a *lattice* if every pair of elements a, b ∈ L has
both a meet a ∧ b and a join a ∨ b.

**Definition 2.4 (Bounded Lattice).**
A lattice (L, ≤) is *bounded* if it contains a *bottom* element ⊥ and a
*top* element ⊤ such that  ⊥ ≤ x ≤ ⊤  for all x ∈ L.

**Definition 2.5 (Distributive Lattice).**
A lattice is *distributive* if, for all a, b, c ∈ L:

    a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)

Equivalently (the dual law follows):

    a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)

**Definition 2.6 (Boolean Algebra).**
A bounded distributive lattice (L, ∧, ∨, ⊥, ⊤) is a *Boolean algebra*
if every element a ∈ L has a *complement* a' ∈ L satisfying:

    a ∧ a' = ⊥       and       a ∨ a' = ⊤

**Example 2.7.**
The power-set lattice (2^S, ∩, ∪, ∅, S) is a Boolean algebra with
complement A' = S \ A.  This is the structure underlying `ContextWeight`
(`semiring.rs:643`), where ∩ = bitwise AND, ∪ = bitwise OR,
∅ = `0u128`, S = `u128::MAX`, and complement = bitwise NOT.

---

## 3  Theorem: Idempotent Semiring Induces a Semilattice

We now prove that every idempotent commutative semiring carries a
natural partial order under which ⊕ acts as the join operation.

**Theorem 3.1 (Idempotent Semiring Order).**
Let (K, ⊕, ⊗, 0-bar, 1-bar) be a commutative semiring where ⊕ is
idempotent, i.e., a ⊕ a = a for all a ∈ K.  Define the relation:

    a ≤ b   ⟺   a ⊕ b = b

Then (K, ≤) is a partially ordered set, and ⊕ is the join (least upper
bound) under ≤.  That is, (K, ≤, ⊕) is a join-semilattice.

**Proof.**

*Part 1.  ≤ is a partial order.*

We verify the three axioms.

**Step 1 (Reflexivity).**  Let a ∈ K.  By idempotency,  a ⊕ a = a.
Hence  a ≤ a  by the definition of ≤.  ✓

**Step 2 (Antisymmetry).**  Suppose a ≤ b and b ≤ a.  Then:

    a ⊕ b = b          (from a ≤ b)
    b ⊕ a = a          (from b ≤ a)

By commutativity of ⊕,  a ⊕ b = b ⊕ a.  Substituting the two equations:

    b = a ⊕ b = b ⊕ a = a

Therefore a = b.  ✓

**Step 3 (Transitivity).**  Suppose a ≤ b and b ≤ c.  Then:

    a ⊕ b = b          (from a ≤ b)      ... (i)
    b ⊕ c = c          (from b ≤ c)      ... (ii)

We compute:

    a ⊕ c = a ⊕ (b ⊕ c)       [by (ii), substituting c = b ⊕ c]
           = (a ⊕ b) ⊕ c       [by associativity of ⊕]
           = b ⊕ c             [by (i), substituting a ⊕ b = b]
           = c                 [by (ii)]

Hence a ⊕ c = c, so a ≤ c.  ✓

*Part 2.  ⊕ is the join under ≤.*

We must show that for any a, b ∈ K, the element j = a ⊕ b is the least
upper bound of {a, b} under ≤.

**Claim 2a (j is an upper bound).**

We show a ≤ j.  Compute  a ⊕ j = a ⊕ (a ⊕ b) = (a ⊕ a) ⊕ b = a ⊕ b = j,
where the first rewrite is associativity and the second is idempotency.
Hence a ⊕ j = j, so a ≤ j.

Symmetrically,  b ⊕ j = b ⊕ (a ⊕ b) = (b ⊕ a) ⊕ b = (a ⊕ b) ⊕ b
= a ⊕ (b ⊕ b) = a ⊕ b = j.  (We used commutativity and idempotency.)
Hence b ≤ j.  ✓

**Claim 2b (j is least).**

Suppose u ∈ K with a ≤ u and b ≤ u.  Then a ⊕ u = u and b ⊕ u = u.
Compute:

    j ⊕ u = (a ⊕ b) ⊕ u = a ⊕ (b ⊕ u) = a ⊕ u = u

Hence j ⊕ u = u, so j ≤ u.  ✓

Since j = a ⊕ b is an upper bound of {a, b} that is less than or equal
to every other upper bound, it is the least upper bound.

Therefore (K, ≤, ⊕) is a join-semilattice.  **QED**

### 3.2  Applications to PraTTaIL Semirings

We now verify idempotency (or its failure) for each semiring and state
the resulting order.

**TropicalWeight** (`semiring.rs:106`).
a ⊕ b = min(a, b).  Idempotent: min(a, a) = a.  ✓
Natural order: a ≤ b  ⟺  min(a, b) = b  ⟺  a ≥_R b (reversed
standard order on R+ ∪ {∞}).  Equivalently, smaller tropical weights are
*higher* in the semilattice.  The join selects the minimum.

**BooleanWeight** (`semiring.rs:317`).
a ⊕ b = a ∨ b (logical OR).  Idempotent: a ∨ a = a.  ✓
Natural order: a ≤ b  ⟺  a ∨ b = b.  This gives false ≤ true,
the standard Boolean order.

**EditWeight** (`semiring.rs:428`).
a ⊕ b = min(a, b) over N ∪ {∞}.  Idempotent: min(a, a) = a.  ✓
Natural order: identical structure to TropicalWeight restricted to
integers.  Smaller edit distances are higher in the semilattice.

**ComplexityWeight** (`semiring.rs:821`).
a ⊕ b = min(a, b) over N ∪ {∞}.  Idempotent: min(a, a) = a.  ✓
Natural order: same structure as EditWeight.  See
`../wfst/semirings/complexity-weight.md` for the full proof.

**ContextWeight** (`semiring.rs:684`).
a ⊕ b = a ∪ b (bitwise OR).  Idempotent: A ∪ A = A.  ✓
Natural order: A ≤ B  ⟺  A ∪ B = B  ⟺  A ⊆ B (subset inclusion).

**CountingWeight** (`semiring.rs:235`).
a ⊕ b = a + b (integer addition).  NOT idempotent: 1 + 1 = 2 ≠ 1.
There is no natural semilattice order.  CountingWeight tracks path
*counts*, not path *preferences*, so an ordering on alternatives is not
meaningful.

**LogWeight** (`semiring.rs:982`, feature-gated: `wfst-log`).
a ⊕ b = -ln(exp(-a) + exp(-b)) (log-sum-exp).  NOT idempotent:
a ⊕ a = -ln(2 exp(-a)) = a - ln 2 ≠ a (for finite a).  There is no
natural semilattice order.  LogWeight preserves full probability mass;
it must sum, not select.

**EntropyWeight** (`semiring.rs:1186`, feature-gated: `wfst-log`).
a ⊕ b uses log-sum-exp on the weight component.  Inherits
non-idempotency from LogWeight.  No natural semilattice order.

**NbestWeight<N>** (`semiring.rs:1569`).
a ⊕ b merges two N-best lists.  NOT idempotent in general:
merging a single-entry list with itself may produce the same list
(dedup), but the cross-product under ⊗ doubles entries before merge,
so the semiring as a whole does not satisfy a ⊕ a = a universally for
composite weights.  No natural semilattice order.

**ProductWeight<S1, S2>** (`semiring.rs:528`).
Component-wise: (a1, a2) ⊕ (b1, b2) = (a1 ⊕ b1, a2 ⊕ b2).  Idempotent
if and only if both S1 and S2 are idempotent.  Inherits the product
order: (a1, a2) ≤ (b1, b2)  ⟺  a1 ≤ b1  and  a2 ≤ b2.

---

## 4  PraTTaIL's Lattice Semirings

### 4.1  Summary Table

| Semiring         | ⊕               | ⊗            | 0-bar          | 1-bar          | Idempotent? | Lattice?         | Source             |
|------------------|-----------------|--------------|----------------|----------------|-------------|------------------|--------------------|
| TropicalWeight   | min             | +            | +∞             | 0.0            | Yes         | Join-semilattice | `semiring.rs:106`  |
| BooleanWeight    | ∨               | ∧            | false          | true           | Yes         | Boolean algebra  | `semiring.rs:317`  |
| EditWeight       | min             | +            | ∞ (u32::MAX)   | 0              | Yes         | Join-semilattice | `semiring.rs:428`  |
| ComplexityWeight | min             | max          | ∞ (u32::MAX)   | 0              | Yes         | Join-semilattice | `semiring.rs:821`  |
| ContextWeight    | ∪               | ∩            | ∅ (0)          | U (u128::MAX)  | Yes         | Boolean algebra  | `semiring.rs:684`  |
| CountingWeight   | +               | x            | 0              | 1              | No          | --               | `semiring.rs:235`  |
| ProductWeight    | comp.           | comp.        | (0-bar, 0-bar) | (1-bar, 1-bar) | Iff both    | Iff both         | `semiring.rs:528`  |
| LogWeight        | log-sum-exp     | +            | +∞             | 0.0            | No          | --               | `semiring.rs:982`  |
| EntropyWeight    | log-sum-exp mix | + pair       | (∞, 0)         | (0, 0)         | No          | --               | `semiring.rs:1186` |
| NbestWeight<N>   | merge N-best    | cross N-best | []             | [(0, 0.0)]     | No          | --               | `semiring.rs:1569` |

### 4.2  BooleanWeight Is a Boolean Algebra

**Theorem 4.1.**
The structure ({false, true}, ∨, ∧, false, true) is a bounded
distributive lattice.  With logical negation as complement, it is a
Boolean algebra.

**Proof.**

*Carrier:*  B = {false, true}.
*Meet:*  a ∧ b = logical AND = ⊗ (`semiring.rs:335`).
*Join:*  a ∨ b = logical OR = ⊕ (`semiring.rs:330`).
*Bottom:*  ⊥ = false = 0-bar (`semiring.rs:320`).
*Top:*  ⊤ = true = 1-bar (`semiring.rs:325`).

**Step 1 (Bounded lattice).**
false ≤ true holds (false ∨ true = true), and for all x ∈ B,
false ≤ x ≤ true.  Meet and join exist for every pair (finite carrier).
Hence (B, ∧, ∨, false, true) is a bounded lattice.

**Step 2 (Distributivity).**
We must show a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c) for all a, b, c ∈ B.
With |B| = 2, there are 2^3 = 8 cases.

| a | b | c | b ∨ c | a ∧ (b ∨ c) | a ∧ b | a ∧ c | (a ∧ b) ∨ (a ∧ c) | Equal? |
|---|---|---|-------|-------------|-------|-------|-------------------|--------|
| F | F | F | F     | F           | F     | F     | F                 | ✓      |
| F | F | T | T     | F           | F     | F     | F                 | ✓      |
| F | T | F | T     | F           | F     | F     | F                 | ✓      |
| F | T | T | T     | F           | F     | F     | F                 | ✓      |
| T | F | F | F     | F           | F     | F     | F                 | ✓      |
| T | F | T | T     | T           | F     | T     | T                 | ✓      |
| T | T | F | T     | T           | T     | F     | T                 | ✓      |
| T | T | T | T     | T           | T     | T     | T                 | ✓      |

All 8 cases agree.  Therefore the lattice is distributive.

**Step 3 (Complementation).**
Define the complement as logical negation:  false' = true,  true' = false.

For a = false:  a ∧ a' = false ∧ true = false = ⊥.
                a ∨ a' = false ∨ true = true = ⊤.  ✓

For a = true:   a ∧ a' = true ∧ false = false = ⊥.
                a ∨ a' = true ∨ false = true = ⊤.  ✓

Every element has a complement, so (B, ∧, ∨, ', false, true) is a
Boolean algebra.  **QED**

**Concrete Grounding.**
`BooleanWeight` is used for dead-rule detection (`pipeline.rs`): a
grammar rule's reachability is projected onto the Boolean semiring, and
rules with weight `BooleanWeight(false)` for all tokens are flagged as
dead (Tier 3 of the four-tier analysis).

### 4.3  ContextWeight Is a Boolean Algebra

**Theorem 4.2.**
The structure (2^S, ∪, ∩, ∅, S) where S = {0, 1, ..., 127} is a
bounded distributive lattice.  With set complement as the complementation
operation, it is a Boolean algebra.

**Proof.**

*Carrier:*  L = 2^S = P({0, ..., 127}), represented as `u128`
(`semiring.rs:643`).
*Meet:*  A ∧ B = A ∩ B = bitwise AND = ⊗ (`semiring.rs:706`).
*Join:*  A ∨ B = A ∪ B = bitwise OR = ⊕ (`semiring.rs:700`).
*Bottom:*  ⊥ = ∅ = 0u128 = 0-bar (`semiring.rs:688`).
*Top:*  ⊤ = S = u128::MAX = 1-bar (`semiring.rs:694`).

**Step 1 (Bounded lattice).**
For all A ∈ L:  ∅ ⊆ A ⊆ S, so ⊥ ≤ A ≤ ⊤.  Meet and join exist for
every pair (standard set-theoretic operations on a power set).  Hence
(L, ∩, ∪, ∅, S) is a bounded lattice.

**Step 2 (Distributivity).**
We must show  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)  for all A, B, C ∈ L.

We prove set equality by showing mutual inclusion.

**(⊇).**  Let x ∈ (A ∩ B) ∪ (A ∩ C).  Then x ∈ A ∩ B  or  x ∈ A ∩ C.

  Case 1: x ∈ A ∩ B.  Then x ∈ A and x ∈ B.  Since x ∈ B, we have
  x ∈ B ∪ C.  Combined with x ∈ A, we get x ∈ A ∩ (B ∪ C).

  Case 2: x ∈ A ∩ C.  Then x ∈ A and x ∈ C.  Since x ∈ C, we have
  x ∈ B ∪ C.  Combined with x ∈ A, we get x ∈ A ∩ (B ∪ C).

Hence (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C).  ✓

**(⊆).**  Let x ∈ A ∩ (B ∪ C).  Then x ∈ A and x ∈ B ∪ C.
Since x ∈ B ∪ C, either x ∈ B or x ∈ C.

  Case 1: x ∈ B.  Then x ∈ A ∩ B, so x ∈ (A ∩ B) ∪ (A ∩ C).

  Case 2: x ∈ C.  Then x ∈ A ∩ C, so x ∈ (A ∩ B) ∪ (A ∩ C).

Hence A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C).  ✓

By mutual inclusion, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
The lattice is distributive.

**Step 3 (Complementation).**
Define A' = S \ A (bitwise NOT, i.e., `!bits` in Rust).

For any A ∈ L:

    A ∩ A' = A ∩ (S \ A) = ∅ = ⊥.

*Proof:*  Suppose x ∈ A ∩ A'.  Then x ∈ A and x ∈ S \ A, i.e., x ∈ A
and x ∉ A.  Contradiction.  Hence A ∩ A' = ∅.  ✓

    A ∪ A' = A ∪ (S \ A) = S = ⊤.

*Proof:*  Let x ∈ S.  Either x ∈ A or x ∉ A.  If x ∈ A, then
x ∈ A ∪ A'.  If x ∉ A, then x ∈ S \ A = A', so x ∈ A ∪ A'.
Hence S ⊆ A ∪ A'.  The reverse A ∪ A' ⊆ S is immediate since
A ⊆ S and A' ⊆ S.  ✓

Every element has a complement, so (2^S, ∩, ∪, ', ∅, S) is a Boolean
algebra.  **QED**

**Concrete Grounding.**
`ContextWeight` (`semiring.rs:643`) represents the set of grammar rules
that can produce a given token.  Composition via ⊗ = ∩ restricts to
rules valid in *both* sequential segments; combination via ⊕ = ∪ unions
the rules from alternative paths.  The Boolean-algebra structure ensures
complement operations are well-defined for follow-set tightening.

For the ComplexityWeight lattice proof, see
`../wfst/semirings/complexity-weight.md`.

---

## 5  Fixed-Point Theory

### 5.1  Definitions

**Definition 5.1 (Fixed Point).**
Given a function F: L --> L on a set L, an element x ∈ L is a *fixed
point* of F if F(x) = x.

**Definition 5.2 (Least Fixed Point).**
A fixed point x* of F is the *least fixed point*, written lfp(F), if for
every fixed point y of F, x* ≤ y.

**Definition 5.3 (Complete Lattice).**
A lattice (L, ≤) is *complete* if every subset S ⊆ L has both a meet
(greatest lower bound) ⋀ S and a join (least upper bound) ⋁ S.  In
particular, ⊥ = ⋁ ∅ and ⊤ = ⋀ ∅ exist.

**Definition 5.4 (Monotone Function).**
A function F: L --> L on a poset is *monotone* if  x ≤ y  implies
F(x) ≤ F(y)  for all x, y ∈ L.

**Definition 5.5 (Scott Continuity).**
A function F: L --> L on a complete lattice is *(Scott) continuous* if
for every directed set D ⊆ L,  F(⋁ D) = ⋁ { F(d) | d ∈ D }.  Every
continuous function is monotone.

### 5.2  Knaster-Tarski Theorem (Statement)

**Theorem 5.6 (Knaster-Tarski, 1955).**
Let (L, ≤) be a complete lattice and F: L --> L a monotone function.
Then the set of fixed points of F forms a complete lattice under ≤.  In
particular, F has a least fixed point:

    lfp(F)  =  ⋀ { x ∈ L | F(x) ≤ x }

*Reference:*  Tarski, A. (1955). "A lattice-theoretical fixpoint theorem
and its applications." *Pacific J. Math.*, 5(2), 285--309.

### 5.3  Kleene Fixed-Point Theorem (Full Proof)

**Theorem 5.7 (Kleene Fixed-Point Theorem).**
Let (L, ≤) be a complete lattice with bottom ⊥, and let F: L --> L be a
monotone and continuous function.  Then:

    lfp(F) = ⋁_{n ≥ 0} F^n(⊥)

where F^0(⊥) = ⊥ and F^{n+1}(⊥) = F(F^n(⊥)).

**Proof.**

**Step 1 (The Kleene chain is ascending).**

We show by induction on n that F^n(⊥) ≤ F^{n+1}(⊥) for all n ≥ 0.

*Base case (n = 0):*  F^0(⊥) = ⊥.  Since ⊥ is the bottom element,
⊥ ≤ F(⊥) = F^1(⊥).  ✓

*Inductive step:*  Assume F^n(⊥) ≤ F^{n+1}(⊥).  Since F is monotone,
applying F to both sides gives  F^{n+1}(⊥) ≤ F^{n+2}(⊥).  ✓

Therefore  ⊥ = F^0(⊥)  ≤  F(⊥)  ≤  F^2(⊥)  ≤  ...  is an ascending
chain.

**Step 2 (The supremum exists and is a fixed point).**

The set D = { F^n(⊥) | n ≥ 0 } is directed (it is a chain, and every
chain is directed).  Since L is a complete lattice, the supremum exists:

    x* = ⋁_{n ≥ 0} F^n(⊥)

By continuity of F:

    F(x*) = F( ⋁_{n ≥ 0} F^n(⊥) )
           = ⋁_{n ≥ 0} F( F^n(⊥) )       [continuity: F preserves directed suprema]
           = ⋁_{n ≥ 0} F^{n+1}(⊥)
           = ⋁_{m ≥ 1} F^m(⊥)             [re-indexing: m = n + 1]
           = ⋁_{m ≥ 0} F^m(⊥)             [adding F^0(⊥) = ⊥ does not change the
                                             supremum, since ⊥ ≤ F(⊥) ≤ x*]
           = x*

Hence F(x*) = x*, so x* is a fixed point of F.  ✓

**Step 3 (x* is the least fixed point).**

Let y be any fixed point of F, i.e., F(y) = y.  We show by induction
that F^n(⊥) ≤ y for all n ≥ 0, which implies x* = ⋁ F^n(⊥) ≤ y.

*Base case (n = 0):*  F^0(⊥) = ⊥ ≤ y  (since ⊥ is bottom).  ✓

*Inductive step:*  Assume F^n(⊥) ≤ y.  By monotonicity of F:

    F^{n+1}(⊥) = F(F^n(⊥)) ≤ F(y) = y

Hence F^{n+1}(⊥) ≤ y.  ✓

By induction, F^n(⊥) ≤ y for all n.  Since x* = ⋁_{n ≥ 0} F^n(⊥) is
the *least* upper bound of the chain, and y is an upper bound, we
conclude x* ≤ y.

Therefore x* = lfp(F).  **QED**

### 5.4  Concrete Grounding: FIRST Set Computation

PraTTaIL's `compute_first_sets()` at `prediction.rs:213` is a direct
implementation of Kleene iteration.

**Lattice.**  The lattice is the product lattice:

    L = ∏_{C ∈ Categories} 2^{Terminals}

ordered componentwise by ⊆.  This is a complete lattice: each component
2^{Terminals} is a complete lattice (power set, ordered by ⊆), and
products of complete lattices are complete.

**Bottom.**  ⊥ = (∅, ∅, ..., ∅) -- all FIRST sets empty.  In the code,
this corresponds to initializing all `FirstSet`s as empty
(`prediction.rs:218`).

**Transfer function.**  F maps the current FIRST-set tuple to a new one
by, for each rule "C --> alpha ...", adding FIRST(alpha) to FIRST(C).
When alpha is a terminal t, {t} is added; when alpha is a nonterminal D,
the current FIRST(D) is unioned in.

**Monotonicity.**  F is monotone: if FIRST sets S1 ⊆ S2 (componentwise),
then applying F to S2 unions in at least everything that applying F to
S1 would, since FIRST(D) can only be larger in S2.

**Convergence bound.**  Each iteration that makes progress adds at least
one terminal to at least one category's FIRST set.  The total number of
(category, terminal) pairs is |Categories| x |Terminals|, so
convergence occurs in at most |Categories| x |Terminals| + 1 iterations.
In practice, convergence is much faster.

**Code correspondence.**  The loop at `prediction.rs:228`:

```rust
loop {
    let mut changed = false;
    // ... propagate FIRST sets ...
    if !changed { break; }
}
```

implements exactly  x_{n+1} = F(x_n),  terminating when  x_{n+1} = x_n
(the `changed` flag is false), at which point  F(x*) = x*  and x* is
the least fixed point by Theorem 5.7.

---

## 6  References

1. Davey, B. A. & Priestley, H. A. (2002). *Introduction to Lattices
   and Order*, 2nd ed. Cambridge University Press.

2. Tarski, A. (1955). "A lattice-theoretical fixpoint theorem and its
   applications." *Pacific Journal of Mathematics*, 5(2), 285--309.

3. Birkhoff, G. (1967). *Lattice Theory*, 3rd ed. American Mathematical
   Society Colloquium Publications, Vol. 25.

4. Droste, M., Kuich, W., & Vogler, H., eds. (2009). *Handbook of
   Weighted Automata*. Springer Monographs in Theoretical Computer
   Science.

5. Kuich, W. & Salomaa, A. (1986). *Semirings, Automata, Languages*.
   EATCS Monographs on Theoretical Computer Science, Vol. 5. Springer.
