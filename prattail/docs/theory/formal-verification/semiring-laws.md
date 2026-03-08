# SemiringLaws.v -- Semiring Axiom Proofs

**File:** `formal/rocq/mathematical_analyses/theories/SemiringLaws.v`
**Lines:** 877
**Admitted:** 0
**Dependencies:** Standalone (no imports from other proof files)


## Intuition

Every weight in PraTTaIL's analysis pipeline flows through semiring
arithmetic: weights are added (choice/join) and multiplied
(sequencing/composition). If the arithmetic laws are wrong -- if
multiplication fails to distribute over addition, or zero fails to
annihilate -- then every downstream analysis built on weighted automata,
WPDS poststar, or KAT verification silently produces incorrect results.

This proof file establishes that three key weight domains used by the
analysis pipeline genuinely satisfy the semiring axioms. It then extends
the KAT domain with Kleene star and Boolean test embeddings, culminating
in a machine-checked proof of Hoare triple soundness.


## What It Proves

### Part 1: Provenance Semiring N[X]

The provenance semiring tracks *how* a result was derived -- which rules
contributed and with what multiplicity. It is the polynomial semiring
N[X] where:

- **Elements:** polynomials with natural number coefficients
- **Plus (+):** pointwise coefficient addition (union of derivations)
- **Times (x):** convolution product (sequential composition of derivations)
- **Zero (0):** the zero polynomial (no derivation)
- **One (1):** coefficient 1 at the empty monomial (identity derivation)

Proven axioms:

| ID | Axiom | Rocq Theorem |
|----|-------|-------------|
| P1 | a + b = b + a | `prov_plus_comm` |
| P2 | (a + b) + c = a + (b + c) | `prov_plus_assoc` |
| P3 | 0 + a = a | `prov_plus_zero_l` |
| P4 | (a x b) x c = a x (b x c) | `prov_times_assoc` |
| P5 | 1 x a = a | `prov_times_one_l` |
| P5' | a x 1 = a | `prov_times_one_r` |
| P6 | a x (b + c) = a x b + a x c | `prov_distr_l` |
| P6' | (a + b) x c = a x c + b x c | `prov_distr_r` |
| P7 | 0 x a = 0 | `prov_times_zero_l` |
| P7' | a x 0 = 0 | `prov_times_zero_r` |

### Part 2: Relational Weight Domain

The relational semiring models program semantics as binary relations on
states. It is the natural choice for interprocedural dataflow analysis:

- **Elements:** binary relations R : nat -> nat -> Prop
- **Plus (+):** set union (choice between transformations)
- **Times (x):** relational composition (sequential execution)
- **Zero (0):** empty relation (no transformation)
- **One (1):** identity relation (skip)

Proven axioms (same table structure as above: R1-R7, R7').

**Bonus theorem:** The relational semiring is idempotent (R + R = R),
which the provenance semiring is not. This distinction matters for
fixpoint convergence analysis.

### Part 3: Kleene Algebra with Tests (KAT)

Extends any semiring satisfying the axioms above with:

**Star axioms:**

| ID | Axiom | Rocq Theorem |
|----|-------|-------------|
| K1 | a* = 1 + a x a* | `K1_star_unfold` |
| K2 | 0* = 1 | `K2_star_zero` |
| K3 | 1* = 1 | `K3_star_one` |

**Boolean test embedding:**

| ID | Axiom | Rocq Theorem |
|----|-------|-------------|
| B1 | test(p) x test(q) = test(p && q) | `B1_test_and` |
| B2 | test(p) + test(q) = test(p \|\| q) | `B2_test_or` |
| B3 | test(p) x test(not p) = 0 | `B3_test_negb_and` |
| B3' | test(p) + test(not p) = 1 | `B3_test_negb_or` |
| B4 | test(p) x test(p) = test(p) | `B4_test_idempotent` |
| B5 | test(p) x test(q) = test(q) x test(p) | `B5_test_times_comm` |

**Hoare triple soundness:**

| ID | Rule | Rocq Theorem |
|----|------|-------------|
| H1 | {true} skip {true} | `H1_skip_preserves_true` |
| H2 | {false} e {q} (ex falso) | `H2_false_precondition` |
| H3 | {p} e {true} | `H3_true_postcondition` |
| H4 | {p} abort {q} | `H4_abort_valid` |
| H5 | Sequential composition | `H5_sequential` |
| H6a | Strengthen precondition | `H6a_strengthen_pre` |
| H6b | Weaken postcondition | `H6b_weaken_post` |
| H7 | Soundness biconditional | `H7_hoare_soundness` |


## Why It Matters

The semiring laws are the *algebraic foundation* that the entire
analysis stack rests on:

```
  ┌─────────────────────────────────────────────────────────────┐
  │  Pipeline Analyses (lint, WPDS, cost-benefit, recovery)     │
  ├─────────────────────────────────────────────────────────────┤
  │  Weighted Automata (WFST compose, viterbi, poststar)        │
  ├─────────────────────────────────────────────────────────────┤
  │  Semiring Arithmetic (plus, times, star, zero, one)         │ <-- THIS
  └─────────────────────────────────────────────────────────────┘
```

If distributivity fails, WPDS saturation does not compute correct
reachability weights. If the annihilation law fails, dead-rule detection
produces false negatives. If the star axiom is unsound, KAT-based
verification gives wrong Hoare verdicts.


## Proof Strategy

### Provenance: Extensional Equality

Polynomials are modeled as functions `Monomial -> nat` (coefficient
lookup). Equality is extensional:

```
poly_eq p q := forall m : Monomial, p m = q m
```

This representation avoids normalization concerns. The additive axioms
(P1-P3) reduce to arithmetic facts about natural numbers, discharged by
`lia`. The multiplicative axioms (P4-P7) are axiomatized via hypotheses
on the convolution product, since defining the full summation over
monomial decompositions would require decidable monomial factorization.
The axioms faithfully capture the guarantees of the Rust implementation.

### Relational: Set-Theoretic Reasoning

Relations are modeled as characteristic functions `nat -> nat -> Prop`.
Equality is pointwise biconditional:

```
rel_eq R S := forall x y, R x y <-> S x y
```

Proofs proceed by unfolding definitions and applying `tauto` or
`firstorder`. The key insight for composition associativity (R4) is the
existential witness reshuffling:

```
exists y, (exists z, R x z /\ S z y) /\ T y w
  <-> exists z, R x z /\ exists y, S z y /\ T y w
```

### KAT: Case Analysis on Booleans + Setoid Rewriting

Boolean tests are modeled with `test : bool -> K`, mapped to `kone`
(true) or `kzero` (false). The test embedding theorems (B1-B5) proceed
by case analysis on the Boolean arguments:

```
intros [] []; simpl;
rewrite ?test_true, ?test_false, ?ktimes_one_l, ...;
reflexivity.
```

The Hoare triple theorems use **Setoid rewriting** infrastructure
(`Add Parametric Relation`, `Add Parametric Morphism`) so that
`keq`-equalities can be rewritten with Rocq's `rewrite` tactic. This
dramatically simplifies the equational chain proofs for H5 (sequential
composition) and the hoare_filter lemma.

### H5 (Sequential Composition): The Filter Lemma

The hardest proof in the file. The key insight is the **filter property**:

If {p} e {q} holds (meaning test(p) x e x test(not q) = 0), then:

```
test(p) x e = test(p) x e x test(q)
```

This is proven via the excluded middle for tests:

```
test(p) x e = test(p) x e x 1
            = test(p) x e x (test(q) + test(not q))
            = test(p) x e x test(q) + test(p) x e x test(not q)
            = test(p) x e x test(q) + 0
            = test(p) x e x test(q)
```

With this lemma in hand, H5 follows by:
1. Reassociating the product test(p) x (e1 x e2) x test(not q)
2. Inserting test(r) via the filter lemma on H1
3. Recognizing the right factor as H2 (which equals zero)
4. Applying the annihilation law


## Rust Code Traceability

| Rocq Definition | Rust Counterpart | File |
|----------------|-----------------|------|
| `Semiring` class | `trait Semiring` | `automata/semiring.rs:36` |
| `poly_zero`, `poly_one` | `ProvenanceWeight::zero`, `::one` | `provenance.rs:149,155` |
| `poly_plus`, `poly_times` | `ProvenanceWeight::plus`, `::times` | `provenance.rs:180,193` |
| `rel_zero`, `rel_one` | `RelationalWeight::empty`, `::identity` | `relational.rs:75,83` |
| `rel_plus`, `rel_times` | `HeapSemiring::plus/times` for Relational | `relational.rs:155,165` |
| `kstar` | `KatExpr::Star` | `kat.rs:147` |
| `test` | `KatExpr::Test` | `kat.rs:139` |
| `hoare_valid` | `verify_hoare_triple()` | `kat.rs:568` |


## Semiring Instance Assembly

Each part concludes by assembling a `Semiring` instance that fills in all
type class fields. This is the Rocq analogue of implementing the
`Semiring` trait in Rust:

```
#[export] Instance ProvenanceSemiringInstance : Semiring Poly := { ... }.
#[export] Instance RelationalSemiringInstance : Semiring Rel := { ... }.
#[export] Instance KATSemiringInstance : Semiring K := { ... }.
```

These instances make the semiring operations available for use by
downstream proofs (e.g., KatSoundness.v) via type class resolution.
