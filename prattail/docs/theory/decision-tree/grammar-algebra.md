# Grammar Algebra over Decision Trees

| Metadata | Value      |
|----------|------------|
| Date     | 2026-03-06 |
| Updated  | 2026-03-06 |

---

## Table of Contents

- [SS1 Overview](#1-overview)
- [SS2 Algebraic Definitions](#2-algebraic-definitions)
- [SS3 Theorem 1: DecisionAction Forms a Lattice](#3-theorem-1-decisionaction-forms-a-lattice)
- [SS4 Theorem 2: Distributive Lattice Property of psubtract](#4-theorem-2-distributive-lattice-property-of-psubtract)
- [SS5 Theorem 3: Composition Correctness of Join](#5-theorem-3-composition-correctness-of-join)
- [SS6 Theorem 4: Meet Yields the Common Sublanguage](#6-theorem-4-meet-yields-the-common-sublanguage)
- [SS7 Worked Examples with Trie Diagrams](#7-worked-examples-with-trie-diagrams)
- [SS8 Summary of Results](#8-summary-of-results)

---

## SS1 Overview

This document establishes the algebraic theory of grammar composition over
decision trees. The decision tree framework introduced in
[foundations.md](foundations.md) encodes per-category parse dispatch as a
`PathMap<DecisionAction>` -- a trie whose paths are byte-encoded token sequences
and whose leaves are parsing actions. The `PathMap` data structure (from the
PathMap crate) supports three algebraic operations -- `join`, `meet`, and
`subtract` -- that lift pointwise from the `DecisionAction` lattice to the
function space of all byte-path-to-action mappings.

We prove four main results:

1. **DecisionAction forms a lattice** (SS3): `pjoin` and `pmeet` satisfy
   commutativity, associativity, idempotency, and the absorption laws.

2. **Distributive lattice property of psubtract** (SS4): For all actions a, b,
   `a.psubtract(a.pmeet(b)) = a.psubtract(b)`.

3. **Composition correctness of join** (SS5): `join(T_A, T_B)` preserves all
   parses of both source grammars. If a token sequence is resolvable in T_A, it
   remains resolvable in `join(T_A, T_B)`.

4. **Meet yields the common sublanguage** (SS6): `meet(T_A, T_B)` retains
   exactly those paths present in both tries with the same rule labels.

Each theorem is proved with full case analysis. Throughout, we use the notation
and definitions from [foundations.md](foundations.md), particularly Definitions
9-11 (Lattice, DecisionAction Lattice, PathMap Lattice).

---

## SS2 Algebraic Definitions

We recall the essential definitions from the implementation and from
[foundations.md](foundations.md), extending them with the notation required for
the proofs in this document.

**Definition 1 (DecisionAction).** The type `DecisionAction` has three
variants:

```
    DecisionAction ::= Commit { rule_label, category, weight }
                     |  Ambiguous { candidates: Vec<AmbiguousCandidate> }
                     |  NonterminalBoundary { options: Vec<NTOption> }
```

For the algebraic theory, we restrict to the *algebraic fragment*:
`Commit` and `Ambiguous`. The `NonterminalBoundary` variant is treated as an
algebraic identity element (it passes through unchanged) by the implementation,
which returns `AlgebraicResult::Identity` when one operand is a
`NonterminalBoundary`. We address this explicitly in the proofs where relevant.

**Definition 2 (Rule Label Set).** For a `DecisionAction` a, define the
*rule label set* `labels(a)` as:

```
    labels(Commit { rule_label: l, .. })   = { l }
    labels(Ambiguous { candidates: cs })   = { c.rule_label | c in cs }
    labels(NonterminalBoundary { .. })     = emptyset
```

**Definition 3 (Canonical Representation).** We identify `Commit { l, c, w }`
with `Ambiguous { [ AmbiguousCandidate { l, c, w, 0 } ] }` when convenient.
Under this identification, every algebraic `DecisionAction` is a non-empty set
of candidates, and `Error` (the bottom) corresponds to the empty set. The
implementation uses `AlgebraicResult::None` for the empty set.

**Definition 4 (pjoin).** For actions a and b in the algebraic fragment:

```
    pjoin(a, b) = Ambiguous(candidates(a) `cup` candidates(b))
```

where `candidates(Commit { l, c, w })` = `[ AmbiguousCandidate { l, c, w, 0 } ]`
and `candidates(Ambiguous { cs })` = `cs`. The result is normalized: a
singleton candidate list yields `Commit`, an empty list yields
`AlgebraicResult::None` (representing `Error`).

**Definition 5 (pmeet).** For actions a and b in the algebraic fragment:

```
    pmeet(a, b) = filter(candidates(a), c -> c.rule_label in labels(b))
```

That is, retain only those candidates from a whose rule label also appears in b.
The result is normalized as with pjoin. Specifically:

```
    pmeet(a, b) = Ambiguous(candidates(a) `cap`_label candidates(b))
```

where `cap`_label denotes intersection filtered by rule label equality,
retaining the candidate metadata (category, weight) from a.

**Definition 6 (psubtract).** For actions a and b in the algebraic fragment:

```
    psubtract(a, b) = filter(candidates(a), c -> c.rule_label `notin` labels(b))
```

That is, remove from a all candidates whose rule label appears in b.

**Definition 7 (PathMap Operations).** Given two `PathMap<DecisionAction>`
values T_A and T_B (representing decision trees as trie maps from byte paths to
actions), the operations are defined pointwise:

```
    join(T_A, T_B)(p)     = pjoin(T_A(p), T_B(p))       for all paths p
    meet(T_A, T_B)(p)     = pmeet(T_A(p), T_B(p))       for all paths p
    subtract(T_A, T_B)(p) = psubtract(T_A(p), T_B(p))   for all paths p
```

where T(p) = `Error` (bottom) if path p is not present in trie T.

---

## SS3 Theorem 1: DecisionAction Forms a Lattice

**Theorem 1.** The pair `(DecisionAction, pjoin, pmeet)` forms a lattice. That
is, `pjoin` is commutative, associative, and idempotent; `pmeet` is
commutative, associative, and idempotent; and the two absorption laws hold.

We prove each property separately, with full case analysis. Throughout, let
a, b, c denote arbitrary `DecisionAction` values in the algebraic fragment, and
let `bot` denote `Error` (the empty candidate set, represented as
`AlgebraicResult::None`).

### 1.1 Commutativity of pjoin

**Claim:** For all a, b: `pjoin(a, b) = pjoin(b, a)`.

*Proof.* By Definition 4, `pjoin(a, b) = Ambiguous(candidates(a) cup candidates(b))`.
Set union is commutative: `candidates(a) cup candidates(b) = candidates(b) cup candidates(a)`.
Therefore `pjoin(a, b) = Ambiguous(candidates(b) cup candidates(a)) = pjoin(b, a)`. `square`

**Remark on implementation.** The implementation concatenates candidate lists
rather than computing a formal set union. The result may contain duplicate rule
labels if both operands contribute a candidate with the same label. For the
purpose of lattice theory, we consider two `Ambiguous` values equal when they
have the same set of rule labels (modulo multiplicity). In practice, duplicate
labels are harmless: the disambiguation layer (ordered trial or Pratt dispatch)
handles them idempotently.

### 1.2 Commutativity of pmeet

**Claim:** For all a, b: `pmeet(a, b) = pmeet(b, a)`.

*Proof.* By Definition 5:

```
    labels(pmeet(a, b)) = labels(a) `cap` labels(b)
    labels(pmeet(b, a)) = labels(b) `cap` labels(a)
```

Set intersection is commutative, so `labels(a) cap labels(b) = labels(b) cap labels(a)`.

Both pmeet(a, b) and pmeet(b, a) retain candidates whose labels lie in the
common set `labels(a) cap labels(b)`. The candidate metadata (category, weight)
is drawn from the first operand in the implementation. Under the label-equality
identification (two actions are lattice-equal when they have the same label
sets), `pmeet(a, b) = pmeet(b, a)`.

More precisely: `pmeet(a, b)` retains candidates from a with labels in
`labels(b)`, while `pmeet(b, a)` retains candidates from b with labels in
`labels(a)`. Since the common label set is identical, and the lattice ordering
is determined by label sets (not metadata), these are lattice-equal. `square`

### 1.3 Associativity of pjoin

**Claim:** For all a, b, c: `pjoin(pjoin(a, b), c) = pjoin(a, pjoin(b, c))`.

*Proof.* By Definition 4 and the canonical representation:

```
    labels(pjoin(pjoin(a, b), c))
        = labels(pjoin(a, b)) `cup` labels(c)
        = (labels(a) `cup` labels(b)) `cup` labels(c)
        = labels(a) `cup` (labels(b) `cup` labels(c))     (associativity of `cup`)
        = labels(a) `cup` labels(pjoin(b, c))
        = labels(pjoin(a, pjoin(b, c)))
```

Since label sets determine lattice equality, `pjoin(pjoin(a, b), c) = pjoin(a, pjoin(b, c))`. `square`

### 1.4 Associativity of pmeet

**Claim:** For all a, b, c: `pmeet(pmeet(a, b), c) = pmeet(a, pmeet(b, c))`.

*Proof.* By Definition 5:

```
    labels(pmeet(pmeet(a, b), c))
        = labels(pmeet(a, b)) `cap` labels(c)
        = (labels(a) `cap` labels(b)) `cap` labels(c)
        = labels(a) `cap` (labels(b) `cap` labels(c))     (associativity of `cap`)
        = labels(a) `cap` labels(pmeet(b, c))
        = labels(pmeet(a, pmeet(b, c)))
```

Since label sets determine lattice equality, `pmeet(pmeet(a, b), c) = pmeet(a, pmeet(b, c))`. `square`

### 1.5 Idempotency of pjoin

**Claim:** For all a: `pjoin(a, a) = a`.

*Proof.* We case-split on the form of a.

**Case 1: a = bot (Error).** `pjoin(bot, bot) = Ambiguous(emptyset cup emptyset) = Ambiguous(emptyset) = bot`. `checkmark`

**Case 2: a = Commit { l, c, w }.** Under the canonical representation,
`candidates(a) = [ AmbiguousCandidate { l, c, w, 0 } ]`.

```
    pjoin(a, a) = Ambiguous(candidates(a) `cup` candidates(a))
               = Ambiguous(candidates(a))       (S `cup` S = S)
               = a                              (singleton normalizes to Commit)
```
`checkmark`

**Case 3: a = Ambiguous { cs }.** `pjoin(a, a) = Ambiguous(cs cup cs) = Ambiguous(cs) = a`. `checkmark`

All cases yield `pjoin(a, a) = a`. `square`

### 1.6 Idempotency of pmeet

**Claim:** For all a: `pmeet(a, a) = a`.

*Proof.* We case-split on the form of a.

**Case 1: a = bot.** `pmeet(bot, bot)`: `labels(bot) = emptyset`, so
`labels(bot) cap labels(bot) = emptyset`, yielding `bot`. `checkmark`

**Case 2: a = Commit { l, c, w }.** `labels(a) = { l }`.
`labels(a) cap labels(a) = { l }`. The filter retains the single candidate
from a whose label is l, which is the sole candidate. Result: `Commit { l, c, w } = a`. `checkmark`

**Case 3: a = Ambiguous { cs }.** `labels(a) cap labels(a) = labels(a)`.
The filter retains all candidates in cs, yielding `Ambiguous { cs } = a`. `checkmark`

All cases yield `pmeet(a, a) = a`. `square`

### 1.7 Absorption Law: pjoin(a, pmeet(a, b)) = a

**Claim:** For all a, b: `pjoin(a, pmeet(a, b)) = a`.

*Proof.* Let S = labels(a) and T = labels(b).

```
    labels(pmeet(a, b)) = S `cap` T
    labels(pjoin(a, pmeet(a, b))) = S `cup` (S `cap` T)
```

By the set-theoretic absorption law: `S cup (S cap T) = S`.

Therefore `labels(pjoin(a, pmeet(a, b))) = S = labels(a)`, which gives
`pjoin(a, pmeet(a, b)) = a` under label-set equality. `square`

### 1.8 Absorption Law: pmeet(a, pjoin(a, b)) = a

**Claim:** For all a, b: `pmeet(a, pjoin(a, b)) = a`.

*Proof.* Let S = labels(a) and T = labels(b).

```
    labels(pjoin(a, b)) = S `cup` T
    labels(pmeet(a, pjoin(a, b))) = S `cap` (S `cup` T)
```

By the set-theoretic absorption law: `S cap (S cup T) = S`.

Therefore `labels(pmeet(a, pjoin(a, b))) = S = labels(a)`, which gives
`pmeet(a, pjoin(a, b)) = a` under label-set equality. `square`

### 1.9 Bottom and Top

**Claim:** `bot = Error` is the identity for pjoin and the annihilator for
pmeet. The universal action `top = Ambiguous({ all rules })` is the identity
for pmeet and the annihilator for pjoin.

*Proof of pjoin identity.* For any a:

```
    pjoin(bot, a) = Ambiguous(emptyset `cup` candidates(a)) = Ambiguous(candidates(a)) = a
    pjoin(a, bot) = Ambiguous(candidates(a) `cup` emptyset) = Ambiguous(candidates(a)) = a
```
`checkmark`

*Proof of pmeet annihilator.* For any a:

```
    pmeet(bot, a): labels(bot) `cap` labels(a) = emptyset `cap` labels(a) = emptyset -> bot
    pmeet(a, bot): labels(a) `cap` labels(bot) = labels(a) `cap` emptyset = emptyset -> bot
```
`checkmark`

*Proof of pmeet identity (with top).* Let U = { all rule labels }. For any a:

```
    pmeet(top, a): labels(top) `cap` labels(a) = U `cap` labels(a) = labels(a) -> a
    pmeet(a, top): labels(a) `cap` U = labels(a) -> a
```
`checkmark`

*Proof of pjoin annihilator (with top).* For any a:

```
    pjoin(top, a): labels(top) `cup` labels(a) = U `cup` labels(a) = U -> top
    pjoin(a, top): labels(a) `cup` U = U -> top
```
`checkmark`

Therefore `(DecisionAction, pjoin, pmeet)` is a bounded lattice with bottom
`Error` and top `Ambiguous({all rules})`. `square`

### 1.10 Conclusion

All eight lattice axioms (commutativity x2, associativity x2, idempotency x2,
absorption x2) are satisfied by (DecisionAction, pjoin, pmeet). Together with
the bounded bottom and top elements, **DecisionAction forms a bounded lattice**.
`square`

---

## SS4 Theorem 2: Distributive Lattice Property of psubtract

**Theorem 2.** For all `DecisionAction` values a, b:

```
    a.psubtract(a.pmeet(b)) = a.psubtract(b)
```

This identity characterizes the interaction between subtraction and meet in a
distributive lattice. It states that subtracting the part of a that overlaps
with b is the same as subtracting b directly from a. This is precisely the
property required by PathMap's `subtract` operation to compose correctly with
`meet`.

*Proof.* Let S = labels(a) and T = labels(b). We compute both sides and show
they produce the same label set.

**Left-hand side:**

Step 1. Compute `a.pmeet(b)`:
```
    labels(a.pmeet(b)) = S `cap` T
```

Step 2. Compute `a.psubtract(a.pmeet(b))`:
```
    labels(a.psubtract(a.pmeet(b))) = S \ (S `cap` T)
```

By the set difference identity `S \ (S cap T) = S \ T`:

*Proof of the set identity.* We show `S \ (S cap T) = S \ T` by mutual
inclusion.

(`subseteq`): Let x in S \ (S cap T). Then x in S and x notin S cap T. Since
x in S, the condition x notin S cap T implies x notin T (because if x were in
T, then x in S and x in T would give x in S cap T, contradicting x notin
S cap T). Therefore x in S and x notin T, so x in S \ T.

(`supseteq`): Let x in S \ T. Then x in S and x notin T. Since x notin T,
we have x notin S cap T (because S cap T subseteq T). Therefore x in S and
x notin S cap T, so x in S \ (S cap T).

By mutual inclusion, `S \ (S cap T) = S \ T`. `square` (sub-proof)

Therefore:
```
    labels(a.psubtract(a.pmeet(b))) = S \ T
```

**Right-hand side:**

By Definition 6:
```
    labels(a.psubtract(b)) = S \ T
```

**Conclusion:**

Both sides yield the label set `S \ T`. Moreover, both sides retain the same
candidate metadata from a (since psubtract filters candidates of a), so the
results are identical not just in label sets but in full candidate content.

Therefore `a.psubtract(a.pmeet(b)) = a.psubtract(b)` for all a, b. `square`

**Corollary 2a (Complement Partition).** For any a, b:

```
    pjoin(a.pmeet(b), a.psubtract(b)) = a
```

*Proof.* The label sets partition:

```
    labels(a.pmeet(b)) = S `cap` T
    labels(a.psubtract(b)) = S \ T
```

Since `(S cap T) cup (S \ T) = S` (partition of S by membership in T), and both
sides draw candidates from a, we have:

```
    labels(pjoin(a.pmeet(b), a.psubtract(b))) = (S `cap` T) `cup` (S \ T) = S = labels(a)
```

Therefore `pjoin(a.pmeet(b), a.psubtract(b)) = a`. `square`

**Corollary 2b (Distributivity).** DecisionAction forms a distributive lattice.
That is, for all a, b, c:

```
    a.pmeet(pjoin(b, c)) = pjoin(a.pmeet(b), a.pmeet(c))
```

*Proof.* Using label sets with S = labels(a), T = labels(b), U = labels(c):

```
    LHS: labels(a.pmeet(pjoin(b, c))) = S `cap` (T `cup` U)
    RHS: labels(pjoin(a.pmeet(b), a.pmeet(c))) = (S `cap` T) `cup` (S `cap` U)
```

By the set-theoretic distributive law: `S cap (T cup U) = (S cap T) cup (S cap U)`.

Therefore LHS = RHS. `square`

---

## SS5 Theorem 3: Composition Correctness of Join

**Theorem 3 (Parse Preservation under Join).** Let T_A and T_B be decision
trees (PathMap<DecisionAction>) for grammars G_A and G_B over the same syntactic
category C. Then:

(a) **Preservation:** If a path p resolves to action a in T_A, then p resolves
    to some action a' in `join(T_A, T_B)` such that `labels(a) subseteq labels(a')`.

(b) **Symmetry:** The same holds for T_B: if p resolves to action b in T_B,
    then p resolves to some b' in `join(T_A, T_B)` with `labels(b) subseteq labels(b')`.

(c) **Completeness:** Every path in `join(T_A, T_B)` comes from T_A, T_B, or
    both. No spurious paths are introduced.

**Remark.** Join may introduce *new ambiguities*: a path that was `Commit(R_i)`
in T_A and `Commit(R_j)` in T_B (with i != j) becomes `Ambiguous({R_i, R_j})`
in the joined tree. This is correct behavior -- the combined grammar genuinely
has two rules competing at that dispatch point.

*Proof.*

**Part (a): Preservation for T_A.**

Let p be a path in T_A with T_A(p) = a. We show that `join(T_A, T_B)(p)` exists
and `labels(a) subseteq labels(join(T_A, T_B)(p))`.

By Definition 7, `join(T_A, T_B)(p) = pjoin(T_A(p), T_B(p))`.

We have T_A(p) = a. For T_B(p), there are two cases:

**Case 1: p is not in T_B.** Then T_B(p) = bot (Error). By the identity
property of pjoin (SS3, Section 1.9):

```
    pjoin(a, bot) = a
```

Therefore `join(T_A, T_B)(p) = a`, and `labels(a) subseteq labels(a)` trivially. `checkmark`

**Case 2: p is in T_B with T_B(p) = b.** By Definition 4:

```
    pjoin(a, b) = Ambiguous(candidates(a) `cup` candidates(b))
```

The label set of the result is:

```
    labels(pjoin(a, b)) = labels(a) `cup` labels(b)
```

Since `labels(a) subseteq labels(a) cup labels(b)`, we have
`labels(a) subseteq labels(join(T_A, T_B)(p))`. `checkmark`

In both cases, the claim holds.

**Part (b): Preservation for T_B.**

Symmetric to Part (a), exchanging the roles of T_A and T_B. By commutativity
of pjoin (SS3, Section 1.1), `pjoin(a, b) = pjoin(b, a)`, so the same
argument applies with T_B as the primary operand. `checkmark`

**Part (c): Completeness.**

Let p be a path in `join(T_A, T_B)` with `join(T_A, T_B)(p) != bot`. By
Definition 7, `join(T_A, T_B)(p) = pjoin(T_A(p), T_B(p))`. For this to be
non-bot, at least one of T_A(p) or T_B(p) must be non-bot (since
`pjoin(bot, bot) = bot`). Therefore p is present in T_A, T_B, or both.

No path p with `T_A(p) = bot` and `T_B(p) = bot` can appear in the join, since
`pjoin(bot, bot) = bot` and the PathMap implementation prunes bot entries (via
`AlgebraicResult::None`). `checkmark`

**Conclusion.** `join(T_A, T_B)` preserves all parses of both grammars. If a
token sequence is resolvable in T_A, it remains resolvable in the joined tree
(with the same rule as one of possibly several candidates). New ambiguities
arise exactly when both grammars contribute different rules for the same path.
`square`

**Corollary 3a (Monotonicity).** Join is monotone with respect to the
information ordering: `T_A leq join(T_A, T_B)` and `T_B leq join(T_A, T_B)`,
where `leq` denotes the pointwise lattice ordering (a leq b iff pjoin(a, b) = b).

*Proof.* For any path p:

```
    pjoin(T_A(p), join(T_A, T_B)(p))
        = pjoin(T_A(p), pjoin(T_A(p), T_B(p)))
        = pjoin(pjoin(T_A(p), T_A(p)), T_B(p))     (associativity)
        = pjoin(T_A(p), T_B(p))                     (idempotency)
        = join(T_A, T_B)(p)
```

Therefore `T_A leq join(T_A, T_B)`. The argument for T_B is symmetric. `square`

**Corollary 3b (Idempotency of Grammar Union).** `join(T_A, T_A) = T_A`.

*Proof.* For any path p: `join(T_A, T_A)(p) = pjoin(T_A(p), T_A(p)) = T_A(p)`
by idempotency of pjoin (SS3, Section 1.5). `square`

---

## SS6 Theorem 4: Meet Yields the Common Sublanguage

**Theorem 4 (Common Sublanguage Characterization).** Let T_A and T_B be
decision trees for grammars G_A and G_B over the same syntactic category C.
Then `meet(T_A, T_B)` contains exactly those paths that are present in both T_A
and T_B with the same rule labels. Formally:

(a) **Soundness:** For every path p in `meet(T_A, T_B)` with action m:
    - p is present in T_A with action a such that `labels(m) subseteq labels(a)`.
    - p is present in T_B with action b such that `labels(m) subseteq labels(b)`.
    - `labels(m) = labels(a) cap labels(b)`.

(b) **Completeness:** For every path p present in both T_A and T_B, if
    `labels(T_A(p)) cap labels(T_B(p)) != emptyset`, then p is present in
    `meet(T_A, T_B)`.

(c) **Exactness:** The label set at each path in the meet is precisely the
    intersection of the label sets from the two source trees.

*Proof.*

**Part (a): Soundness.**

Let p be a path in `meet(T_A, T_B)` with `meet(T_A, T_B)(p) = m != bot`. By
Definition 7:

```
    m = pmeet(T_A(p), T_B(p))
```

For m to be non-bot, `pmeet(T_A(p), T_B(p))` must return a non-empty result.
By Definition 5, this requires `labels(T_A(p)) cap labels(T_B(p)) != emptyset`,
which implies both T_A(p) != bot and T_B(p) != bot. Therefore p is present in
both T_A and T_B.

Let a = T_A(p) and b = T_B(p). By Definition 5:

```
    labels(m) = labels(a) `cap` labels(b)
```

Since `labels(a) cap labels(b) subseteq labels(a)`, we have `labels(m) subseteq labels(a)`.
Since `labels(a) cap labels(b) subseteq labels(b)`, we have `labels(m) subseteq labels(b)`.

This establishes all three sub-claims of (a). `checkmark`

**Part (b): Completeness.**

Let p be a path present in both T_A and T_B with a = T_A(p), b = T_B(p), and
`labels(a) cap labels(b) != emptyset`.

By Definition 7, `meet(T_A, T_B)(p) = pmeet(a, b)`. By Definition 5,
`labels(pmeet(a, b)) = labels(a) cap labels(b) != emptyset`, so the result is
non-bot. Therefore p is present in `meet(T_A, T_B)`. `checkmark`

**Part (c): Exactness.**

This is immediate from Parts (a) and (b). At each path p in the meet:

```
    labels(meet(T_A, T_B)(p)) = labels(T_A(p)) `cap` labels(T_B(p))
```

The meet retains no more labels than the intersection (by Definition 5's
filter), and no fewer (by completeness: every label in the intersection
survives the filter). `checkmark`

**Conclusion.** `meet(T_A, T_B)` yields exactly the common sublanguage: the set
of paths where both grammars agree on at least one rule label, with the action
at each path reflecting precisely the shared rules. `square`

**Corollary 4a (Empty Meet).** If grammars G_A and G_B have no rules in common
(i.e., `labels(T_A(p)) cap labels(T_B(p)) = emptyset` for all paths p), then
`meet(T_A, T_B)` is the empty trie (bottom).

*Proof.* By Part (b), no path survives the meet since the intersection is empty
at every path. Therefore `meet(T_A, T_B) = bot`. `square`

**Corollary 4b (Meet Idempotency).** `meet(T_A, T_A) = T_A`.

*Proof.* For any path p:

```
    meet(T_A, T_A)(p) = pmeet(T_A(p), T_A(p)) = T_A(p)
```

by idempotency of pmeet (SS3, Section 1.6). `square`

**Corollary 4c (Meet-Join Absorption at PathMap Level).** For all decision
trees T_A, T_B:

```
    join(T_A, meet(T_A, T_B)) = T_A
    meet(T_A, join(T_A, T_B)) = T_A
```

*Proof.* By pointwise lifting and the absorption laws (SS3, Sections 1.7 and
1.8). For any path p:

```
    join(T_A, meet(T_A, T_B))(p)
        = pjoin(T_A(p), pmeet(T_A(p), T_B(p)))
        = T_A(p)                                   (absorption, SS3 Section 1.7)
```

The second absorption law is symmetric. `square`

---

## SS7 Worked Examples with Trie Diagrams

This section illustrates the algebraic operations on concrete decision trees.
We use a minimal grammar with three rules over category `Expr`:

- **R1** (`IfThenElse`): `if` `then` `else`
- **R2** (`LetIn`): `let` `in`
- **R3** (`WhileDo`): `while` `do`

Token encoding: `if` = 0x01, `then` = 0x02, `else` = 0x03, `let` = 0x04,
`in` = 0x05, `while` = 0x06, `do` = 0x07.

### 7.1 Source Trees

**Grammar A** contains rules R1 and R2. **Grammar B** contains rules R1 and R3.

```
    T_A (Grammar A: IfThenElse + LetIn)        T_B (Grammar B: IfThenElse + WhileDo)

            [root]                                      [root]
           /      \                                    /      \
         0x01    0x04                                0x01    0x06
         /          \                                /          \
       [*]         [*]                             [*]         [*]
       /             \                             /             \
     0x02           0x05                         0x02           0x07
     /                 \                         /                 \
   [*]           Commit(R2)                    [*]           Commit(R3)
   /              "LetIn"                      /              "WhileDo"
  0x03                                        0x03
  /                                           /
 Commit(R1)                                  Commit(R1)
 "IfThenElse"                                "IfThenElse"
```

Each `[*]` denotes an internal node; `[root]` is the trie root. Edges are
labeled with byte-encoded token identifiers. Leaves are `Commit` actions.

### 7.2 Join: join(T_A, T_B)

The join merges both trees pointwise. At each path, candidates are unioned.

```
    join(T_A, T_B)

                      [root]
                   /    |     \
                 0x01  0x04   0x06
                /        |       \
              [*]       [*]     [*]
              /           \       \
            0x02         0x05   0x07
            /               \       \
          [*]          Commit(R2)  Commit(R3)
          /             "LetIn"    "WhileDo"
         0x03
         /
    Commit(R1)
    "IfThenElse"
```

**Analysis by path:**

| Path                   | T_A        | T_B        | join(T_A, T_B)    |
|------------------------|------------|------------|--------------------|
| (0x01, 0x02, 0x03)    | Commit(R1) | Commit(R1) | Commit(R1)         |
| (0x04, 0x05)           | Commit(R2) | bot        | Commit(R2)         |
| (0x06, 0x07)           | bot        | Commit(R3) | Commit(R3)         |

Since R1 appears in both with the same label, `pjoin(Commit(R1), Commit(R1)) = Commit(R1)` (idempotency). The unique rules from each grammar are preserved with no ambiguity.

**Ambiguity example.** Suppose we modified Grammar B to also have a rule R4
(`LetInAlt`) with the same prefix `let in`. Then the path (0x04, 0x05) would
yield:

```
    pjoin(Commit(R2/"LetIn"), Commit(R4/"LetInAlt"))
        = Ambiguous({R2, R4})
```

This correctly reflects a genuine cross-grammar conflict.

### 7.3 Meet: meet(T_A, T_B)

The meet retains only paths where both grammars agree on rule labels.

```
    meet(T_A, T_B)

          [root]
            |
          0x01
            |
           [*]
            |
          0x02
            |
           [*]
            |
          0x03
            |
       Commit(R1)
       "IfThenElse"
```

**Analysis by path:**

| Path               | T_A        | T_B        | meet(T_A, T_B) |
|--------------------|------------|------------|----------------|
| (0x01, 0x02, 0x03) | Commit(R1) | Commit(R1) | Commit(R1)     |
| (0x04, 0x05)       | Commit(R2) | bot        | bot (pruned)   |
| (0x06, 0x07)       | bot        | Commit(R3) | bot (pruned)   |

Only the shared rule R1 survives the meet. Rules unique to either grammar are
eliminated because `pmeet(Commit(R_i), bot) = bot`.

### 7.4 Subtract: subtract(T_A, T_B)

Subtraction removes from T_A all rules whose labels appear in T_B at the same
path.

```
    subtract(T_A, T_B)

          [root]
            |
          0x04
            |
           [*]
            |
          0x05
            |
       Commit(R2)
       "LetIn"
```

**Analysis by path:**

| Path               | T_A        | T_B        | subtract(T_A, T_B) |
|--------------------|------------|------------|--------------------|
| (0x01, 0x02, 0x03) | Commit(R1) | Commit(R1) | bot (removed)      |
| (0x04, 0x05)       | Commit(R2) | bot        | Commit(R2)         |

R1 is removed because it appears in T_B at the same path. R2 is retained
because T_B has no rule at path (0x04, 0x05).

### 7.5 Verification of Theorem 2

We verify `a.psubtract(a.pmeet(b)) = a.psubtract(b)` at each path.

**Path (0x01, 0x02, 0x03):**

```
    a = Commit(R1),  b = Commit(R1)
    a.pmeet(b) = Commit(R1)         (labels: {R1} `cap` {R1} = {R1})
    a.psubtract(a.pmeet(b)) = a.psubtract(Commit(R1))
                             = bot   ({R1} \ {R1} = emptyset)
    a.psubtract(b) = bot             ({R1} \ {R1} = emptyset)
```
`checkmark`

**Path (0x04, 0x05):**

```
    a = Commit(R2),  b = bot
    a.pmeet(b) = bot                 ({R2} `cap` emptyset = emptyset)
    a.psubtract(a.pmeet(b)) = a.psubtract(bot)
                             = Commit(R2)   ({R2} \ emptyset = {R2})
    a.psubtract(b) = Commit(R2)              ({R2} \ emptyset = {R2})
```
`checkmark`

### 7.6 Verification of Corollary 2a (Complement Partition)

We verify `pjoin(a.pmeet(b), a.psubtract(b)) = a` at each path.

**Path (0x01, 0x02, 0x03):**

```
    a.pmeet(b) = Commit(R1)
    a.psubtract(b) = bot
    pjoin(Commit(R1), bot) = Commit(R1) = a
```
`checkmark`

**Path (0x04, 0x05):**

```
    a.pmeet(b) = bot
    a.psubtract(b) = Commit(R2)
    pjoin(bot, Commit(R2)) = Commit(R2) = a
```
`checkmark`

### 7.7 Verification of Corollary 4c (Absorption at PathMap Level)

We verify `join(T_A, meet(T_A, T_B)) = T_A`.

From SS7.3, `meet(T_A, T_B)` contains only path (0x01, 0x02, 0x03) -> Commit(R1).

```
    join(T_A, meet(T_A, T_B)):
```

| Path               | T_A        | meet(T_A, T_B) | join result |
|--------------------|------------|----------------|-------------|
| (0x01, 0x02, 0x03) | Commit(R1) | Commit(R1)     | Commit(R1)  |
| (0x04, 0x05)       | Commit(R2) | bot            | Commit(R2)  |

Result = T_A. `checkmark`

---

## SS8 Summary of Results

| Result      | Statement                                                           | Significance                                     |
|-------------|---------------------------------------------------------------------|--------------------------------------------------|
| Thm 1       | DecisionAction forms a bounded lattice under pjoin/pmeet            | Algebraic foundation for grammar operations      |
| Thm 1 (1.1) | pjoin is commutative                                                | Grammar union is order-independent               |
| Thm 1 (1.2) | pmeet is commutative                                                | Grammar intersection is order-independent        |
| Thm 1 (1.3) | pjoin is associative                                                | Multi-grammar union is well-defined              |
| Thm 1 (1.4) | pmeet is associative                                                | Multi-grammar intersection is well-defined       |
| Thm 1 (1.5) | pjoin is idempotent                                                 | Joining a grammar with itself is a no-op         |
| Thm 1 (1.6) | pmeet is idempotent                                                 | Meeting a grammar with itself is a no-op         |
| Thm 1 (1.7) | pjoin(a, pmeet(a, b)) = a                                           | Absorption law (join over meet)                  |
| Thm 1 (1.8) | pmeet(a, pjoin(a, b)) = a                                           | Absorption law (meet over join)                  |
| Thm 2       | a.psubtract(a.pmeet(b)) = a.psubtract(b)                            | Distributive lattice property                    |
| Cor 2a      | pjoin(a.pmeet(b), a.psubtract(b)) = a                               | Complement partition of label sets               |
| Cor 2b      | pmeet distributes over pjoin                                        | Full distributive lattice                        |
| Thm 3       | join(T_A, T_B) preserves all parses of both grammars                | Composition correctness                          |
| Cor 3a      | T_A `leq` join(T_A, T_B)                                            | Join is monotone                                 |
| Cor 3b      | join(T_A, T_A) = T_A                                                | Idempotency at PathMap level                     |
| Thm 4       | meet(T_A, T_B) yields exactly the common sublanguage                | Precise characterization of grammar intersection |
| Cor 4a      | Disjoint grammars have empty meet                                   | No false common rules                            |
| Cor 4b      | meet(T_A, T_A) = T_A                                                | Idempotency at PathMap level                     |
| Cor 4c      | join(T_A, meet(T_A, T_B)) = T_A and meet(T_A, join(T_A, T_B)) = T_A | Absorption at PathMap level                      |

**Implementation correspondence.** These results are realized in:

- `prattail/src/decision_tree.rs`: `impl Lattice for DecisionAction` (pjoin, pmeet) and `impl DistributiveLattice for DecisionAction` (psubtract).
- `prattail/src/decision_tree.rs`: `composition_trie_analysis()` uses `meet()`, `subtract()`, and `join()` on PathMap to compute common rules, unique rules, and new ambiguities.
- PathMap crate (`pathmap::ring`): `Lattice` and `DistributiveLattice` traits; `PathMap::join()`, `PathMap::meet()`, `PathMap::subtract()` implement pointwise lifting.
