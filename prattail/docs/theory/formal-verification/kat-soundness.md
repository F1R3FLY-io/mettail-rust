# KatSoundness.v -- KAT Denotational Semantics and Hoare Triple Soundness

**File:** `formal/rocq/mathematical_analyses/theories/KatSoundness.v`
**Lines:** 494
**Admitted:** 0
**Dependencies:** Conceptually builds on `SemiringLaws.v` (shares the semiring
type class), but technically standalone via re-parameterization.


## Intuition

Kleene Algebra with Tests (KAT) lets you reason about program
correctness using *algebra* instead of *logic*. The traditional way to
verify {p} e {q} ("if precondition p holds and program e runs, then
postcondition q holds") is Hoare logic, which requires building a
proof tree from axioms and inference rules. KAT reduces this to a
single algebraic equation:

```
{p} e {q}   is valid   iff   test(p) . e . test(not q) = 0
```

The left side is a logical statement; the right side is an equation in
a semiring with tests. If you can show the product is zero -- meaning
there is no execution path that starts in a state satisfying p, runs e,
and ends in a state violating q -- then the Hoare triple holds.

PraTTaIL uses this encoding to verify properties of parse actions via
algebraic simplification rather than proof-tree construction. This proof
file establishes that the encoding is both **sound** (zero implies
validity) and **complete** (validity implies zero).


## What It Proves

### Denotational Semantics

KAT expressions are given meaning as binary relations on an abstract
state type:

| Expression | Denotation |
|-----------|------------|
| `KZero` | Empty relation: no (s, s') pair |
| `KOne` | Identity: s = s' |
| `KTest t` | Guard: test_denote(t, s) holds and s = s' |
| `KAct n` | Action: action_val(n)(s, s') |
| `KSeq e1 e2` | Composition: exists s_mid, e1(s, s_mid) and e2(s_mid, s') |
| `KAlt e1 e2` | Union: e1(s, s') or e2(s, s') |
| `KStar e` | Reflexive-transitive closure of e |

### Main Theorems

**Soundness:**

```
Theorem kat_hoare_soundness :
  forall p e q,
    denotes_empty (hoare_condition p e q) ->
    hoare_valid p e q.
```

If test(p) . e . test(not q) denotes the empty relation, then
for all states s, s': p(s) and e(s, s') implies q(s').

**Completeness:**

```
Theorem kat_hoare_completeness :
  forall p e q,
    hoare_valid p e q ->
    denotes_empty (hoare_condition p e q).
```

If the Hoare triple is valid, then test(p) . e . test(not q) denotes
the empty relation.

**Biconditional:**

```
Theorem kat_hoare_iff :
  forall p e q,
    hoare_valid p e q <-> denotes_empty (hoare_condition p e q).
```

The two formulations are logically equivalent.

### KAT Algebraic Laws

These verify the simplification identities used by `simplify()` in
`kat.rs`:

| Law | Statement | Theorem |
|-----|-----------|---------|
| Alt identity | 0 + e = e, e + 0 = e | `alt_zero_left`, `alt_zero_right` |
| Alt idempotent | e + e = e | `alt_idempotent` |
| Star of zero | 0* = 1 | `star_zero` |
| Star of one | 1* = 1 | `star_one` |
| Test true | test(true) = 1 | `test_true_is_one` |
| Test false | test(false) = 0 | `test_false_is_zero` |
| Test contradiction | b . not(b) = 0 | `test_and_neg_is_zero` |
| Seq associativity | (e1;e2);e3 = e1;(e2;e3) | `seq_assoc` |
| Seq zero | 0;e = 0, e;0 = 0 | `seq_zero_left`, `seq_zero_right` |
| Seq one | 1;e = e, e;1 = e | `seq_one_left`, `seq_one_right` |

### Hoare Logic Derived Rules

| Rule | Statement | Theorem |
|------|-----------|---------|
| Consequence | Strengthen pre, weaken post | `hoare_consequence` |
| Skip | {p} skip {p} | `hoare_skip` |
| Sequencing | {p} e1 {r}, {r} e2 {q} implies {p} e1;e2 {q} | `hoare_seq` |
| Choice | {p} e1 {q}, {p} e2 {q} implies {p} e1+e2 {q} | `hoare_choice` |
| Star (invariant) | {p} e {p} implies {p} e* {p} | `hoare_star` |
| Zero | {p} 0 {q} for any p, q | `hoare_zero` |

Each rule is also verified for consistency with the KAT encoding:
`kat_skip_sound` and `kat_zero_sound` show that applying the rule
preserves emptiness of the hoare_condition.


## Why It Matters

```
  ┌────────────────────────────────────────────────────────┐
  │  Pipeline: verify_hoare_triple()                       │
  │  "Is this parse action correct w.r.t. these guards?"   │
  ├────────────────────────────────────────────────────────┤
  │  KAT Encoding: test(p) . e . test(not q) = 0          │ <-- THIS
  ├────────────────────────────────────────────────────────┤
  │  Algebraic Simplification: simplify()                  │
  │  (apply the verified laws until normal form)           │
  └────────────────────────────────────────────────────────┘
```

PraTTaIL's KAT module (`kat.rs`) encodes parse actions as KAT
expressions and verifies correctness properties by algebraic
simplification. The verified laws guarantee that `simplify()` preserves
semantic equivalence, and the soundness/completeness theorem guarantees
that checking the simplified expression against zero is equivalent to
checking the Hoare triple.


## Proof Strategy

### Boolean Tests: Algebra of State Predicates

Boolean tests form a subalgebra with decidable operations:

```
  Inductive bool_test :=
    | BTrue | BFalse
    | BAtom (n : nat)
    | BNot (t : bool_test)
    | BAnd (t1 t2 : bool_test)
    | BOr (t1 t2 : bool_test).
```

Tests are interpreted via an atom valuation `atom_val : nat -> (state ->
Prop)`. The key hypothesis is:

```
Hypothesis test_decidable : forall t s,
  test_denote t s \/ ~ test_denote t s.
```

This decidability assumption is critical for the soundness proof: it
enables a case split on whether `q` holds at the final state `s'`.

### Soundness: Proof by Contradiction

The soundness proof has an elegant structure:

1. Assume `denotes_empty (hoare_condition p e q)` -- no execution path
   satisfies test(p) . e . test(not q).
2. Given states s, s' with p(s) and e(s, s'), must show q(s').
3. Use `test_decidable` to split on q(s'):
   - If q(s'): done.
   - If not q(s'): construct a witness for hoare_condition,
     contradicting emptiness.

The witness construction is direct:

```
denote (KSeq (KTest p) (KSeq e (KTest (BNot q)))) s s'
  = exists s. (p(s) /\ s=s) /\ exists s'. (e(s,s') /\ (not q(s') /\ s'=s'))
```

All conjuncts are available from the assumptions.

### Completeness: Direct Witness Destruction

The completeness proof goes the other direction:

1. Assume `hoare_valid p e q` -- for all s, s', p(s) and e(s,s') implies
   q(s').
2. Must show no (s, s') satisfies the hoare_condition.
3. Given a hypothetical witness, decompose it to get p(s), e(s, s'), and
   not q(s').
4. From hoare_valid, p(s) and e(s, s') gives q(s') -- contradicting
   not q(s').

### Star Rule: Induction on rel_star

The Kleene star `e*` is modeled as the reflexive-transitive closure of
the denotation of `e`:

```
Inductive rel_star (R : state_rel) : state_rel :=
  | star_refl : forall s, rel_star R s s
  | star_step : forall s1 s2 s3,
      R s1 s2 -> rel_star R s2 s3 -> rel_star R s1 s3.
```

The Hoare star rule `{p} e {p} implies {p} e* {p}` is proven by
induction on `rel_star`:

- **Base (star_refl):** s = s', so p(s) = p(s').
- **Step (star_step):** e relates s to s_mid, and e* relates s_mid to
  s'. By the invariant hypothesis, p(s) and e(s, s_mid) gives p(s_mid).
  By the inductive hypothesis, p(s_mid) and e*(s_mid, s') gives p(s').


## The Central Formula

The entire proof file revolves around a single equation:

```
  {p} e {q}   <-->   test(p) . e . test(not q) = 0
```

Reading this equation:

- `test(p)` is a filter: it passes only states satisfying p (and acts
  as identity on those states).
- `e` is the program: it transforms states.
- `test(not q)` is a filter: it passes only states violating q.
- The composition test(p) . e . test(not q) captures all executions
  that start satisfying p, run e, and end violating q.
- If this is zero (empty relation), there are no such executions,
  meaning the Hoare triple is valid.

The elegance of KAT is that this equation can be checked by algebraic
manipulation (the `simplify()` function in Rust), without building a
Hoare logic proof tree.


## Rust Code Traceability

| Rocq Definition | Rust Counterpart | File |
|----------------|-----------------|------|
| `bool_test` | `BooleanTest` | `kat.rs:56-69` |
| `kat_expr` | `KatExpr` | `kat.rs:131-147` |
| `test_denote` | `eval_test()` | `kat.rs:421-430` |
| `denote` | Symbolic bisimulation semantics | `kat.rs:312-382` |
| `hoare_valid` | `verify_hoare_triple()` | `kat.rs:568-578` |
| `hoare_condition` | `KatExpr::hoare_condition()` | `kat.rs:179-184` |
| `kat_simplify` (laws) | `simplify()` | `kat.rs:516-553` |
| `KZero`, `KOne` | `KatExpr::Zero`, `KatExpr::One` | `kat.rs:134-135` |
| `KSeq`, `KAlt` | `KatExpr::Seq`, `KatExpr::Alt` | `kat.rs:143-145` |
| `KStar` | `KatExpr::Star` | `kat.rs:147` |
| `KTest` | `KatExpr::Test` | `kat.rs:139` |


## Theoretical References

- Kozen, D. (1997). "Kleene algebra with tests." ACM TOPLAS 19(3).
  Introduced the KAT framework and the Hoare triple encoding.
- Kozen, D. & Smith, F. (1996). "Kleene algebra with tests:
  completeness and decidability." CSL 1996. PSPACE decision procedure.
- Kozen, D. (2000). "On Hoare logic and Kleene algebra with tests."
  Survey of the KAT-Hoare relationship.
