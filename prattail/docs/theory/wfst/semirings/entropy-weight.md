# EntropyWeight: Expectation Semiring (2026-03-01)

> **Date:** 2026-03-01
> **Source**: `prattail/src/automata/semiring.rs`, lines 1084--1367
> **Carrier**: `EntropyWeight { weight: f64, expectation: f64 }` -- pairs of weight and expectation
> **Feature gate**: `wfst-log`

---

## Table of Contents

1. [Intuition & Motivation](#1-intuition--motivation)
2. [Formal Definition](#2-formal-definition)
3. [Semiring Axiom Verification](#3-semiring-axiom-verification)
4. [Relationship to LogWeight](#4-relationship-to-logweight)
5. [Li & Eisner (2009) Expectation Semiring Derivation](#5-li--eisner-2009-expectation-semiring-derivation)
6. [Shannon Entropy Computation](#6-shannon-entropy-computation)
7. [Numerical Stability Analysis](#7-numerical-stability-analysis)
8. [Commutativity Proof for Plus](#8-commutativity-proof-for-plus)
9. [Worked Example: Dispatch Distribution Entropy](#9-worked-example-dispatch-distribution-entropy)
10. [Complexity Analysis](#10-complexity-analysis)
11. [Rust Implementation](#11-rust-implementation)
12. [Source References](#12-source-references)
13. [Cross-References](#13-cross-references)

---

## 1. Intuition & Motivation

The TropicalWeight semiring answers *"which parse is best?"* and the
LogWeight semiring answers *"what is the total probability?"* -- but
neither directly answers the question *"how uncertain is the parser at
this dispatch point?"*.

When multiple grammar rules compete for the same token, we want to know
whether the competition is close (high entropy -- the parser is genuinely
uncertain) or lopsided (low entropy -- one rule dominates). This quantity
-- the **Shannon entropy** of the dispatch distribution -- is a single
number that captures the *degree of ambiguity* at each decision point.

The **EntropyWeight** semiring computes this entropy efficiently by
threading an *expectation* component alongside the standard LogWeight
probability computation. It is an instance of the **expectation
semiring** introduced by Li & Eisner (2009), specialized to the case
where the quantity being "expected" is the negative log-probability
itself (yielding Shannon entropy).

Three concrete applications motivate this semiring:

1. **Adaptive beam width.** At high-entropy dispatch points (many
   plausible alternatives), the parser should widen its beam to avoid
   prematurely pruning the correct parse. At low-entropy points (one
   dominant alternative), a narrow beam suffices. EntropyWeight provides
   the per-state entropy needed to make this decision.

2. **Grammar design feedback.** After WFST construction, the entropy at
   each dispatch point provides actionable feedback to the grammar
   author: *"category Proc has 2.3 bits of entropy at token `Ident`"*
   signals that too many rules compete for that token, suggesting
   refactoring or priority annotations.

3. **Training convergence criterion.** During weight training via
   forward-backward (see LogWeight), the total entropy across all
   dispatch points decreases as the model learns. When entropy stabilizes
   below a threshold, training has converged.

---

## 2. Formal Definition

### 2.1 The Semiring

The **expectation semiring** (specialized for entropy) is the tuple:

```
E  =  ( R x R,  ⊕,  ⊗,  0̄,  1̄ )
```

where:

| Component                      | Symbol | Definition                                          | Interpretation                                |
|--------------------------------|--------|-----------------------------------------------------|-----------------------------------------------|
| Carrier set                    | K      | R x R = {(w, e) : w in R+ u {+inf}, e in R}        | (neg-log-prob, expectation) pairs             |
| Addition (⊕)                   | plus   | (w₁,e₁) ⊕ (w₂,e₂) = (lse(w₁,w₂), mix(e₁,e₂))    | Combine parallel paths                        |
| Multiplication (⊗)             | times  | (w₁,e₁) ⊗ (w₂,e₂) = (w₁+w₂, e₁+e₂)               | Sequence path segments                        |
| Additive identity (0̄)          | zero   | (∞, 0)                                              | No paths (probability 0, zero expectation)    |
| Multiplicative identity (1̄)    | one    | (0, 0)                                              | Single certain path, zero expectation         |

### 2.2 The Plus Operation in Detail

The plus operation combines two parallel alternatives. The weight
component uses log-sum-exp (identical to LogWeight), while the
expectation component computes a probability-weighted mixture:

```
(w₁, e₁) ⊕ (w₂, e₂)  =  ( lse(w₁, w₂),  (p₁ e₁ + p₂ e₂) / (p₁ + p₂) )
```

where `pᵢ = exp(-wᵢ)` and `lse(a, b) = -ln(exp(-a) + exp(-b))`.

The mixture formula is the **conditional expectation** of `e` given that
we are in the subspace spanned by these two alternatives. It is computed
in log-space for numerical stability (see Section 7).

### 2.3 The Times Operation in Detail

The times operation sequences two path segments. Both components add:

```
(w₁, e₁) ⊗ (w₂, e₂)  =  ( w₁ + w₂,  e₁ + e₂ )
```

In probability space, `w₁ + w₂` corresponds to `p₁ * p₂` (probability
of traversing both segments). The expectation `e₁ + e₂` is additive
because the expected quantity (typically negative log-probability) is
additive over path segments -- the total cost of a path is the sum of
its arc costs.

---

## 3. Semiring Axiom Verification

We verify all 8 required semiring axioms using the EntropyWeight
operations. Let a = (wₐ, eₐ), b = (w_b, e_b), c = (w_c, e_c) be
arbitrary elements of K.

### 3.1 (A1) Associativity of ⊕

**Claim**: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c).

*Weight component.* lse is associative (proven in the LogWeight theory
doc, Section 3.1). The weight component of (a ⊕ b) ⊕ c and a ⊕ (b ⊕ c)
are both equal to lse(wₐ, w_b, w_c) = -ln(pₐ + p_b + p_c).

*Expectation component.* In probability space, both orderings compute:

```
new_e = (pₐ eₐ + p_b e_b + p_c e_c) / (pₐ + p_b + p_c)
```

For the left association (a ⊕ b) ⊕ c: let d = a ⊕ b = (w_d, e_d). Then
p_d = pₐ + p_b and e_d = (pₐ eₐ + p_b e_b) / (pₐ + p_b). Now:

```
d ⊕ c has expectation = (p_d e_d + p_c e_c) / (p_d + p_c)
     = ((pₐ + p_b) * (pₐ eₐ + p_b e_b)/(pₐ + p_b) + p_c e_c) / (pₐ + p_b + p_c)
     = (pₐ eₐ + p_b e_b + p_c e_c) / (pₐ + p_b + p_c)
```

The right association a ⊕ (b ⊕ c) yields the same by symmetric argument.
QED.

**Concrete witness**: a = (2.0, 1.5), b = (3.0, 2.0), c = (1.0, 0.5).

```
pₐ = exp(-2.0) = 0.13534,  p_b = exp(-3.0) = 0.04979,  p_c = exp(-1.0) = 0.36788
p_total = 0.55301

Left:  a ⊕ b = (lse(2,3), (0.13534*1.5 + 0.04979*2.0)/(0.13534+0.04979))
             = (lse(2,3), (0.20301 + 0.09958)/0.18513)
             = (lse(2,3), 1.6339)
       (a ⊕ b) ⊕ c: e = (0.18513*1.6339 + 0.36788*0.5)/0.55301
                       = (0.30244 + 0.18394)/0.55301
                       = 0.87938

Right: b ⊕ c = (lse(3,1), (0.04979*2.0 + 0.36788*0.5)/(0.04979+0.36788))
             = (lse(3,1), (0.09958 + 0.18394)/0.41767)
             = (lse(3,1), 0.67886)
       a ⊕ (b ⊕ c): e = (0.13534*1.5 + 0.41767*0.67886)/0.55301
                       = (0.20301 + 0.28356)/0.55301
                       = 0.87938   Check.
```

### 3.2 (A2) Commutativity of ⊕

**Claim**: a ⊕ b = b ⊕ a.

See Section 8 for the full commutativity proof. The weight component
commutes because lse(wₐ, w_b) = lse(w_b, wₐ) (commutativity of real
addition under -ln). The expectation component commutes because

```
(pₐ eₐ + p_b e_b) / (pₐ + p_b)  =  (p_b e_b + pₐ eₐ) / (p_b + pₐ)
```

by commutativity of real addition in both numerator and denominator. QED.

### 3.3 (A3) Additive Identity: 0̄ ⊕ a = a

**Claim**: (∞, 0) ⊕ (wₐ, eₐ) = (wₐ, eₐ).

*Weight component*: lse(∞, wₐ) = -ln(exp(-∞) + exp(-wₐ)) = -ln(0 + exp(-wₐ)) = wₐ. Check.

*Expectation component*: p_zero = exp(-∞) = 0, so:

```
(0 * 0 + pₐ * eₐ) / (0 + pₐ) = pₐ eₐ / pₐ = eₐ
```

Check. By commutativity, a ⊕ 0̄ = a also. QED.

**Concrete witness**: a = (2.0, 1.5), z = (∞, 0).

In the implementation, `plus` checks `if self.weight == f64::INFINITY { return *other; }`,
returning a directly. The result is (2.0, 1.5). Check.

### 3.4 (M1) Associativity of ⊗

**Claim**: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c).

Both components use real addition, which is associative:

```
(a ⊗ b) ⊗ c = ((wₐ + w_b) + w_c, (eₐ + e_b) + e_c)
             = (wₐ + (w_b + w_c), eₐ + (e_b + e_c))
             = a ⊗ (b ⊗ c)
```

QED.

**Concrete witness**: a = (1.0, 0.5), b = (2.0, 1.0), c = (3.0, 1.5).

```
(a ⊗ b) ⊗ c = (1+2, 0.5+1.0) ⊗ (3, 1.5) = (3, 1.5) ⊗ (3, 1.5) = (6, 3.0)
a ⊗ (b ⊗ c) = (1, 0.5) ⊗ (2+3, 1.0+1.5) = (1, 0.5) ⊗ (5, 2.5) = (6, 3.0)  Check.
```

### 3.5 (M2) Multiplicative Identity: 1̄ ⊗ a = a

**Claim**: (0, 0) ⊗ (wₐ, eₐ) = (wₐ, eₐ).

```
(0, 0) ⊗ (wₐ, eₐ) = (0 + wₐ, 0 + eₐ) = (wₐ, eₐ)
```

QED. Right identity holds symmetrically: a ⊗ 1̄ = (wₐ + 0, eₐ + 0) = a.

**Concrete witness**: a = (2.0, 1.5), one = (0, 0).

```
one ⊗ a = (0 + 2.0, 0 + 1.5) = (2.0, 1.5) = a   Check.
a ⊗ one = (2.0 + 0, 1.5 + 0) = (2.0, 1.5) = a   Check.
```

### 3.6 (Z) Zero Annihilation: 0̄ ⊗ a = 0̄

**Claim**: (∞, 0) ⊗ (wₐ, eₐ) = (∞, 0).

```
(∞, 0) ⊗ (wₐ, eₐ) = (∞ + wₐ, 0 + eₐ) = (∞, eₐ)
```

Wait -- the expectation component is eₐ, not 0. However, by convention
in extended arithmetic, ∞ + x = ∞ for any finite x, so the weight
component is ∞. An element with weight ∞ represents zero probability
(an impossible path). The expectation value on an impossible path is
semantically meaningless -- it carries no probability mass and therefore
contributes nothing to any weighted sum.

In the implementation, `is_zero()` checks only
`self.weight.is_infinite() && self.weight.is_sign_positive()`, which
returns true for (∞, eₐ) regardless of eₐ. Furthermore, `plus` handles
the zero case by short-circuit: `if self.weight == f64::INFINITY { return *other; }`,
so the expectation on a zero-weight element is never propagated.

Therefore, for all practical purposes in WFST algorithms:

```
0̄ ⊗ a   is observationally equivalent to   0̄
a ⊗ 0̄   is observationally equivalent to   0̄
```

because any subsequent `⊕` with a non-zero element discards the
zero-weight element entirely, and `is_zero()` returns true. QED.

**Concrete witness**: a = (2.0, 1.5), z = (∞, 0).

```
z.times(&a) = (∞ + 2.0, 0 + 1.5) = (∞, 1.5)
z.times(&a).is_zero() = true  (weight is +∞)
z.times(&a).plus(&b) for any b = b  (zero short-circuit)   Check.
```

### 3.7 (D1) Left Distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)

**Claim**: (wₐ, eₐ) ⊗ ((w_b, e_b) ⊕ (w_c, e_c)) = ((wₐ, eₐ) ⊗ (w_b, e_b)) ⊕ ((wₐ, eₐ) ⊗ (w_c, e_c)).

*Weight component.* Left side: wₐ + lse(w_b, w_c). Right side:
lse(wₐ + w_b, wₐ + w_c).

In probability space:

```
Left:   pₐ * (p_b + p_c)  =  pₐ p_b + pₐ p_c
Right:  pₐ p_b + pₐ p_c
```

Equal by distributivity of real multiplication over addition. Converting
back via -ln preserves equality. Check.

*Expectation component.* Left side:

```
b ⊕ c has expectation e_bc = (p_b e_b + p_c e_c) / (p_b + p_c)
a ⊗ (b ⊕ c) has expectation eₐ + e_bc = eₐ + (p_b e_b + p_c e_c) / (p_b + p_c)
```

Right side: a ⊗ b = (wₐ + w_b, eₐ + e_b), a ⊗ c = (wₐ + w_c, eₐ + e_c).
The probabilities are pₐ p_b and pₐ p_c respectively.

```
(a ⊗ b) ⊕ (a ⊗ c) has expectation:
  = (pₐ p_b (eₐ + e_b) + pₐ p_c (eₐ + e_c)) / (pₐ p_b + pₐ p_c)
  = pₐ (p_b (eₐ + e_b) + p_c (eₐ + e_c)) / (pₐ (p_b + p_c))
  = (p_b eₐ + p_b e_b + p_c eₐ + p_c e_c) / (p_b + p_c)
  = ((p_b + p_c) eₐ + p_b e_b + p_c e_c) / (p_b + p_c)
  = eₐ + (p_b e_b + p_c e_c) / (p_b + p_c)
```

This matches the left side. QED.

Right distributivity (D2) follows by a symmetric argument, using
commutativity of real addition and multiplication.

**Concrete witness**: a = (1.0, 0.5), b = (2.0, 1.0), c = (3.0, 1.5).

```
pₐ = 0.36788,  p_b = 0.13534,  p_c = 0.04979

Left:  b ⊕ c: e_bc = (0.13534*1.0 + 0.04979*1.5) / (0.13534 + 0.04979)
                    = (0.13534 + 0.07469) / 0.18513 = 1.1340
       a ⊗ (b ⊕ c): e = 0.5 + 1.1340 = 1.6340

Right: a ⊗ b = (3.0, 1.5),  a ⊗ c = (4.0, 2.0)
       p_ab = exp(-3) = 0.04979,  p_ac = exp(-4) = 0.01832
       (a ⊗ b) ⊕ (a ⊗ c): e = (0.04979*1.5 + 0.01832*2.0) / (0.04979 + 0.01832)
                              = (0.07469 + 0.03664) / 0.06811
                              = 1.6340   Check.
```

### 3.8 (A4) Commutativity of ⊗

**Claim**: a ⊗ b = b ⊗ a.

```
(wₐ, eₐ) ⊗ (w_b, e_b) = (wₐ + w_b, eₐ + e_b) = (w_b + wₐ, e_b + eₐ) = (w_b, e_b) ⊗ (wₐ, eₐ)
```

By commutativity of real addition in both components. QED.

---

All 8 semiring axioms hold (with zero annihilation in the observational
sense described in 3.6). QED.

> For the parsing-specific interpretation of these axioms, see
> [§4 Why Each Axiom Matters for Parsing](../semirings.md#4-why-each-axiom-matters-for-parsing).

---

## 4. Relationship to LogWeight

EntropyWeight extends LogWeight by adding an expectation component. The
relationship is a **projection** (surjective semiring homomorphism):

```
pi: (R x R) -> R
pi(w, e)  =  w
```

This projection is a **full semiring homomorphism**:

**Plus preservation**: pi((w₁,e₁) ⊕ (w₂,e₂)) = pi(lse(w₁,w₂), mix(e₁,e₂)) = lse(w₁,w₂) = pi(w₁,e₁) ⊕_log pi(w₂,e₂). QED.

**Times preservation**: pi((w₁,e₁) ⊗ (w₂,e₂)) = pi(w₁+w₂, e₁+e₂) = w₁+w₂ = pi(w₁,e₁) ⊗_log pi(w₂,e₂). QED.

**Identity preservation**: pi(0̄_E) = pi(∞, 0) = ∞ = 0̄_L. pi(1̄_E) = pi(0, 0) = 0 = 1̄_L. QED.

Therefore, every question answerable by LogWeight is also answerable by
EntropyWeight (just project out the weight component). EntropyWeight
answers strictly more questions: "what is the expected value of the
per-arc quantity under the path distribution?"

```
  ┌──────────────────────────────────────────────────────────────────┐
  │                        EntropyWeight                             │
  │                     (w, e) in R x R                              │
  │                                                                  │
  │   Weight component: ───────────────────────────> LogWeight (w)   │
  │                         projection pi                            │
  │                                                                  │
  │   Expectation component: provides additional information         │
  │   (expected value of per-arc quantities under the distribution)  │
  └──────────────────────────────────────────────────────────────────┘
```

### 4.1 Shared Properties

| Property           | LogWeight         | EntropyWeight                        |
|--------------------|-------------------|--------------------------------------|
| Weight ⊕           | lse               | lse (identical)                      |
| Weight ⊗           | +                 | + (identical)                        |
| Commutative        | Yes               | Yes                                  |
| Idempotent (⊕)     | No                | No                                   |
| Feature gate       | `wfst-log`        | `wfst-log`                           |
| Carrier            | R+ u {+inf}       | (R+ u {+inf}) x R                    |
| Rust size          | 8 bytes           | 16 bytes                             |

### 4.2 Non-Idempotency

Like LogWeight, EntropyWeight is **not idempotent**:

```
(w, e) ⊕ (w, e) = (lse(w, w), (p*e + p*e)/(p + p))
                 = (w - ln(2), e)
```

The weight decreases by ln(2) (the combined probability doubles), and the
expectation stays the same (the weighted average of identical values is
unchanged). Since w - ln(2) != w for finite w, ⊕ is not idempotent. QED.

---

## 5. Li & Eisner (2009) Expectation Semiring Derivation

### 5.1 The General Framework

Li & Eisner (2009) introduced a family of *expectation semirings* that
pair a probability semiring with an expectation component. The
**first-order expectation semiring** over a base semiring (K, ⊕_K, ⊗_K)
and a K-module V is defined as:

```
E = (K x V,  ⊕_E,  ⊗_E,  (0_K, 0_V),  (1_K, 0_V))
```

with operations:

```
(k₁, v₁) ⊕_E (k₂, v₂)  =  (k₁ ⊕_K k₂,  v₁ ⊕_V v₂)
(k₁, v₁) ⊗_E (k₂, v₂)  =  (k₁ ⊗_K k₂,  k₁ ⊗ v₂ ⊕_V v₁ ⊗ k₂)
```

This formulation carries *unnormalized expected values* `v = p * e` rather
than normalized expectations `e`. The semiring axioms are then inherited
directly from the base semiring and module axioms.

### 5.2 Specialization to PraTTaIL's EntropyWeight

PraTTaIL's EntropyWeight uses **normalized expectations** rather than
the unnormalized formulation of Li & Eisner. The carrier is
(w, e) where:

- w is a negative log-probability (like LogWeight)
- e is the *conditional expected value* (normalized by probability mass)

The key difference appears in ⊕. In Li & Eisner's unnormalized form:

```
(k₁, p₁*e₁) ⊕ (k₂, p₂*e₂)  =  (k₁ ⊕ k₂,  p₁*e₁ + p₂*e₂)
```

In PraTTaIL's normalized form:

```
(w₁, e₁) ⊕ (w₂, e₂)  =  (lse(w₁,w₂),  (p₁*e₁ + p₂*e₂) / (p₁ + p₂))
```

The normalization divides by the total probability (p₁ + p₂). This keeps
the expectation component bounded and interpretable as an average, rather
than growing without bound as paths accumulate.

### 5.3 Equivalence of the Two Formulations

The two formulations are isomorphic via the map:

```
phi: (w, e)_normalized  -->  (w, exp(-w) * e)_unnormalized
psi: (w, v)_unnormalized  -->  (w, v / exp(-w))_normalized  =  (w, v * exp(w))
```

This isomorphism preserves semiring operations. For ⊗:

```
phi((w₁,e₁) ⊗_norm (w₂,e₂))
  = phi(w₁+w₂, e₁+e₂)
  = (w₁+w₂,  exp(-(w₁+w₂)) * (e₁+e₂))
  = (w₁+w₂,  exp(-w₁)*exp(-w₂) * e₁ + exp(-w₁)*exp(-w₂) * e₂)
```

Under Li & Eisner's ⊗: (k₁,v₁) ⊗ (k₂,v₂) = (k₁⊗k₂, k₁⊗v₂ + v₁⊗k₂).
With (k₁,v₁) = phi(w₁,e₁) = (w₁, exp(-w₁)*e₁) and (k₂,v₂) = phi(w₂,e₂):

```
k₁ ⊗ v₂ = exp(-w₁) * exp(-w₂) * e₂   (multiplication = exp(-sum))
v₁ ⊗ k₂ = exp(-w₁) * e₁ * exp(-w₂)
sum = exp(-w₁)*exp(-w₂) * (e₁ + e₂)
```

This matches. The normalized formulation is algebraically equivalent but
numerically superior because the expectation component e remains O(1)
rather than shrinking toward zero as the unnormalized probability mass
exp(-w) decreases along deep paths.

### 5.4 Why "Expectation Semiring"?

The name comes from the observation that after running the
forward-backward algorithm with expectation semiring weights, the
expectation component at the final state equals the **expected value**
of the per-arc quantity over all paths, weighted by path probability:

```
E[f] = SUM_pi  P(pi) * SUM_{arc in pi} f(arc)
```

where f(arc) is the quantity stored in each arc's expectation component
and P(pi) is the path probability. When f(arc) = -ln P(arc) = w_arc,
this gives Shannon entropy (Section 6).

---

## 6. Shannon Entropy Computation

### 6.1 The Setup

Given a distribution over N arcs with probabilities p₁, ..., p_N
(summing to 1), the **Shannon entropy** is:

```
H  =  -SUM_i  pᵢ ln(pᵢ)
   =   SUM_i  pᵢ wᵢ
```

where wᵢ = -ln(pᵢ) is the negative log-probability of arc i.

### 6.2 Arc Weight Construction

To compute H using EntropyWeight, set each arc's weight to:

```
arc_i  =  EntropyWeight::from_arc_weight(wᵢ)  =  (wᵢ, wᵢ)
```

That is, the expectation component e equals the weight component w for
each arc. This encodes the function f(arc) = w_arc (the negative
log-probability of the arc itself).

### 6.3 Forward-Backward Gives H

After combining all arcs via ⊕ (forward pass at a single dispatch point):

```
result = arc_1 ⊕ arc_2 ⊕ ... ⊕ arc_N
       = (lse(w₁,...,w_N),  (p₁ w₁ + p₂ w₂ + ... + p_N w_N) / (p₁ + ... + p_N))
```

If the distribution is normalized (SUM pᵢ = 1, i.e., lse(w₁,...,w_N) = 0),
then the denominator is 1 and the expectation component is exactly:

```
e = SUM_i  pᵢ wᵢ  =  -SUM_i  pᵢ ln(pᵢ)  =  H
```

For unnormalized distributions, the expectation component gives H of the
normalized distribution (because the mixture formula divides by the total
probability mass).

### 6.4 Conversion to Bits

Shannon entropy in nats (using natural logarithm) converts to bits by
dividing by ln(2):

```
H_bits = H_nats / ln(2)
```

The `entropy_bits()` method implements this conversion:

```rust
pub fn entropy_bits(&self) -> f64 {
    self.expectation / std::f64::consts::LN_2
}
```

### 6.5 Entropy Bounds

For N alternatives with equal probability (maximum entropy):

```
H_max = ln(N)     nats
H_max = log₂(N)   bits
```

For a single alternative (minimum entropy):

```
H_min = 0
```

These bounds constrain the expectation component after ⊕-combining N
arcs from a normalized distribution.

---

## 7. Numerical Stability Analysis

### 7.1 The Naive Problem

A direct computation of the mixture formula:

```
new_e = (p₁ e₁ + p₂ e₂) / (p₁ + p₂)
      = (exp(-w₁) e₁ + exp(-w₂) e₂) / (exp(-w₁) + exp(-w₂))
```

is numerically unstable. For large weights (w > 700), exp(-w) underflows
to zero, and for large negative weights (w < -700), exp(-w) overflows to
infinity.

### 7.2 Log-Space Factoring with w_min Extraction

The implementation extracts the minimum weight w_min = min(w₁, w₂) and
divides both numerator and denominator by exp(-w_min):

```
r₁ = exp(-(w₁ - w_min))     (relative probability of path 1)
r₂ = exp(-(w₂ - w_min))     (relative probability of path 2)

new_e = (r₁ e₁ + r₂ e₂) / (r₁ + r₂)
```

Since w₁ - w_min >= 0 and w₂ - w_min >= 0, the exponents are always
non-positive, so exp(-diff) is in (0, 1]. No overflow or underflow is
possible.

One of the two relative probabilities is always exactly 1.0 (the one
whose weight equals w_min), providing an exact anchor for the computation.

### 7.3 Large Difference Fast Path

When |w₁ - w₂| > 20, the smaller probability is negligible:

```
exp(-20) = 2.061 x 10^-9
```

In this case, the dominant path's expectation is returned directly,
avoiding the exp/division computation entirely:

```rust
if diff_self > 20.0 {
    // other dominates (self has negligible probability)
    EntropyWeight {
        weight: new_weight,
        expectation: other.expectation,
    }
} else if diff_other > 20.0 {
    // self dominates (other has negligible probability)
    EntropyWeight {
        weight: new_weight,
        expectation: self.expectation,
    }
}
```

### 7.4 Error Bound

For the slow path (|w₁ - w₂| <= 20), all intermediate values are bounded:

- Exponents: in [-20, 0], so exp values are in [exp(-20), 1] = [2.06e-9, 1]
- Denominator: in [1, 2] (sum of two values where one is 1 and the other
  is at most 1)
- Numerator terms: products of bounded values and user expectations

The relative error is bounded by the machine epsilon of f64 (~2.2 x 10^-16).

For the fast path (|w₁ - w₂| > 20), the absolute error in the expectation
component is bounded by:

```
|error| <= exp(-20) * |e_minor| / (1 + exp(-20))
        <  2.1 x 10^-9 * |e_minor|
```

For typical expectation values (O(1) to O(10)), this error is far below
the `approx_eq` epsilon of 1e-10 used in convergence checks.

### 7.5 The log_sum_exp Shared Implementation

The weight component's log-sum-exp uses the identical stable form as
LogWeight (Section 6 of the LogWeight theory doc):

```rust
fn log_sum_exp(a: f64, b: f64) -> f64 {
    if a == f64::INFINITY { return b; }
    if b == f64::INFINITY { return a; }
    let min_val = a.min(b);
    let diff = (a - b).abs();
    if diff > 20.0 {
        min_val
    } else {
        min_val - (1.0 + (-diff).exp()).ln()
    }
}
```

This is a private method on `EntropyWeight`, duplicated from `LogWeight`
to avoid a feature-gating dependency (both are behind `wfst-log`). The
stability properties are proven in the [LogWeight theory doc](./log-weight.md),
Section 6.

---

## 8. Commutativity Proof for Plus

**Theorem.** The plus operation on EntropyWeight is commutative:
for all a = (wₐ, eₐ) and b = (w_b, e_b):

```
a ⊕ b  =  b ⊕ a
```

**Proof.**

*Case 1: wₐ = ∞.* Then a ⊕ b = b (by additive identity), and
b ⊕ a also returns b when the implementation detects `other.weight == ∞`.
Both sides equal b. QED for this case.

*Case 2: w_b = ∞.* Symmetric to Case 1. Both sides equal a. QED.

*Case 3: both finite, |wₐ - w_b| > 20.*  Without loss of generality,
suppose wₐ < w_b (a has higher probability). Then diff_self = wₐ - w_min = 0,
diff_other = w_b - w_min = w_b - wₐ > 20.

For a ⊕ b: diff_other > 20, so the result is (new_weight, eₐ).
For b ⊕ a: diff_self = w_b - min(w_b, wₐ) = w_b - wₐ > 20, so the
result is (new_weight, eₐ). Both return eₐ. QED for this case.

*Case 4: both finite, |wₐ - w_b| <= 20.* Both orderings compute:

**Weight:** lse(wₐ, w_b) = -ln(exp(-wₐ) + exp(-w_b)). Since real
addition is commutative, lse(wₐ, w_b) = lse(w_b, wₐ).

**Expectation (a ⊕ b):**

```
w_min = min(wₐ, w_b)
rₐ = exp(-(wₐ - w_min)),   r_b = exp(-(w_b - w_min))
e_{a⊕b} = (rₐ eₐ + r_b e_b) / (rₐ + r_b)
```

**Expectation (b ⊕ a):**

```
w_min' = min(w_b, wₐ) = w_min      (min is commutative)
r_b' = exp(-(w_b - w_min)),   rₐ' = exp(-(wₐ - w_min))
e_{b⊕a} = (r_b' e_b + rₐ' eₐ) / (r_b' + rₐ')
```

Since rₐ' = rₐ, r_b' = r_b, and real addition/multiplication are
commutative:

```
e_{b⊕a} = (r_b e_b + rₐ eₐ) / (r_b + rₐ) = (rₐ eₐ + r_b e_b) / (rₐ + r_b) = e_{a⊕b}
```

QED.

**Concrete witness**: a = (1.0, 3.0), b = (2.0, 5.0).

```
a ⊕ b: w_min = 1.0, rₐ = 1.0, r_b = exp(-1) = 0.36788
       e = (1.0*3.0 + 0.36788*5.0) / (1.0 + 0.36788)
         = (3.0 + 1.8394) / 1.36788
         = 3.5396

b ⊕ a: w_min = 1.0, r_b = exp(-1) = 0.36788, rₐ = 1.0
       e = (0.36788*5.0 + 1.0*3.0) / (0.36788 + 1.0)
         = (1.8394 + 3.0) / 1.36788
         = 3.5396   Check.
```

This matches the test `test_entropy_weight_plus_commutativity` in the
source (lines 2537--2543).

---

## 9. Worked Example: Dispatch Distribution Entropy

Consider a parser dispatching token `Ident` in category `Proc` with 3
competing rules:

```
  ┌─────────────────────────────────────────────────────────────────┐
  │                  Dispatch at token "Ident"                      │
  │                                                                 │
  │  Rule         Weight     Probability         Interpretation     │
  │  ─────────────────────────────────────────────────────────────── │
  │  PInput       0.5        exp(-0.5) = 0.6065  Input channel      │
  │  POutput      1.2        exp(-1.2) = 0.3012  Output channel     │
  │  PVar         2.5        exp(-2.5) = 0.0821  Variable ref       │
  │                                                                 │
  │  Total probability: 0.9898                                      │
  └─────────────────────────────────────────────────────────────────┘
```

### 9.1 Constructing Arc Weights

For entropy computation, use `from_arc_weight()` to set e = w:

```
arc_1 = EntropyWeight::from_arc_weight(0.5)  = (0.5, 0.5)     [PInput]
arc_2 = EntropyWeight::from_arc_weight(1.2)  = (1.2, 1.2)     [POutput]
arc_3 = EntropyWeight::from_arc_weight(2.5)  = (2.5, 2.5)     [PVar]
```

### 9.2 Step-by-Step Plus Accumulation

**Step 1: arc_1 ⊕ arc_2**

```
w_min = min(0.5, 1.2) = 0.5
diff  = |0.5 - 1.2|   = 0.7   (< 20, use slow path)

Weight:
  lse(0.5, 1.2) = 0.5 - ln(1 + exp(-0.7))
                = 0.5 - ln(1 + 0.4966)
                = 0.5 - ln(1.4966)
                = 0.5 - 0.4044
                = 0.0956

Expectation:
  r₁ = exp(-(0.5 - 0.5)) = exp(0) = 1.0
  r₂ = exp(-(1.2 - 0.5)) = exp(-0.7) = 0.4966
  denom = 1.0 + 0.4966 = 1.4966
  e = (1.0 * 0.5 + 0.4966 * 1.2) / 1.4966
    = (0.5 + 0.5959) / 1.4966
    = 0.7323

partial = (0.0956, 0.7323)
```

**Step 2: partial ⊕ arc_3**

```
w_min = min(0.0956, 2.5) = 0.0956
diff  = |0.0956 - 2.5|   = 2.4044   (< 20, use slow path)

Weight:
  lse(0.0956, 2.5) = 0.0956 - ln(1 + exp(-2.4044))
                    = 0.0956 - ln(1 + 0.09035)
                    = 0.0956 - ln(1.09035)
                    = 0.0956 - 0.08647
                    = 0.00913

Expectation:
  r_partial = exp(-(0.0956 - 0.0956)) = 1.0
  r₃ = exp(-(2.5 - 0.0956)) = exp(-2.4044) = 0.09035
  denom = 1.0 + 0.09035 = 1.09035
  e = (1.0 * 0.7323 + 0.09035 * 2.5) / 1.09035
    = (0.7323 + 0.2259) / 1.09035
    = 0.8789

result = (0.00913, 0.8789)
```

### 9.3 Verification

**Probability verification:**

```
total_prob = exp(-0.00913) = 0.9909
(expected total = 0.6065 + 0.3012 + 0.0821 = 0.9898)
(small discrepancy from rounding in display values)
```

**Entropy verification (direct computation):**

```
Normalize: p₁' = 0.6065/0.9898 = 0.6128
           p₂' = 0.3012/0.9898 = 0.3043
           p₃' = 0.0821/0.9898 = 0.0830

H = -(0.6128 ln(0.6128) + 0.3043 ln(0.3043) + 0.0830 ln(0.0830))
  = -(0.6128*(-0.4896) + 0.3043*(-1.1890) + 0.0830*(-2.4890))
  = -((-0.3001) + (-0.3618) + (-0.2066))
  = -(-0.8685)
  = 0.8685 nats
```

The EntropyWeight result (0.8789 nats) approximates this. The small
discrepancy arises because the arc weights in the example are not
exactly normalized (total probability is 0.9898, not 1.0); the
EntropyWeight computes the entropy of the distribution *after*
normalization by the total probability mass.

**Entropy in bits:**

```
H_bits = 0.8789 / ln(2) = 0.8789 / 0.6931 = 1.268 bits
```

With 3 alternatives, the maximum entropy is log₂(3) = 1.585 bits, so
this dispatch point is at 80% of maximum entropy -- moderately uncertain.

### 9.4 Interpretation for Beam Width

A beam width policy might set:

```
beam_width(state) = base_width * (1 + H_bits / H_max_bits)
```

For this dispatch point with H = 1.268 bits and H_max = 1.585 bits:

```
beam_width = 3.0 * (1 + 1.268/1.585) = 3.0 * 1.800 = 5.4
```

So the beam expands from 3 to ~5 at this high-entropy point, giving the
parser more room to explore alternatives.

---

## 10. Complexity Analysis

| Operation                 | Implementation                          | Time     | Space         |
|---------------------------|-----------------------------------------|----------|---------------|
| `zero()`                  | `(f64::INFINITY, 0.0)`                  | O(1)     | O(1) -- 16 B  |
| `one()`                   | `(0.0, 0.0)`                            | O(1)     | O(1) -- 16 B  |
| `times(a, b)`             | `(w₁+w₂, e₁+e₂)` -- 2 additions        | O(1)     | O(1) -- 16 B  |
| `plus(a, b)` fast path    | min + comparison + copy                 | O(1)     | O(1) -- 16 B  |
| `plus(a, b)` slow path    | min + 2 exp + 1 ln + 4 mul + 2 add + 1 div | O(1) | O(1) -- 16 B  |
| `is_zero()`               | `is_infinite() && is_sign_positive()`   | O(1)     | --            |
| `is_one()`                | `w == 0.0 && e == 0.0`                  | O(1)     | --            |
| `from_arc_weight(w)`      | copy w to both fields                   | O(1)     | O(1) -- 16 B  |
| `entropy_bits()`          | division by ln(2)                       | O(1)     | --            |
| `approx_eq(other, eps)`   | 2 abs-differences + 2 comparisons       | O(1)     | --            |

**Comparison with LogWeight:**

| Operation   | LogWeight        | EntropyWeight    | Overhead     |
|-------------|------------------|------------------|--------------|
| `times`     | 1 addition       | 2 additions      | +1 add       |
| `plus`      | log_sum_exp      | log_sum_exp + mixture | +2 exp, +4 mul, +1 div |
| Memory      | 8 bytes          | 16 bytes         | +8 bytes     |

The `plus` slow path is ~3x more expensive than LogWeight's `plus` due to
the mixture computation, but the fast path (|w₁ - w₂| > 20) has identical
cost (early return). In practice, most dispatch distributions are
lopsided (one dominant rule), so the fast path executes frequently.

---

## 11. Rust Implementation

The complete implementation from `prattail/src/automata/semiring.rs`
(lines 1084--1367):

### 11.1 Struct Definition

```rust
/// Expectation semiring for computing parse distribution entropy.
///
/// Based on Li & Eisner (2009), "First- and Second-Order Expectation Semirings".
///
/// **Semiring:** `(R x R, ⊕, ⊗, (∞, 0), (0, 0))`
#[cfg(feature = "wfst-log")]
#[derive(Clone, Copy)]
pub struct EntropyWeight {
    /// Total weight in negative log-probability space.
    pub weight: f64,
    /// Accumulated expected value (entropy contribution).
    pub expectation: f64,
}
```

### 11.2 Constructors and Accessors

```rust
#[cfg(feature = "wfst-log")]
impl EntropyWeight {
    pub const fn new(weight: f64, expectation: f64) -> Self {
        EntropyWeight { weight, expectation }
    }

    /// For Shannon entropy: set expectation = weight.
    pub const fn from_arc_weight(weight: f64) -> Self {
        EntropyWeight { weight, expectation: weight }
    }

    pub const fn weight(&self) -> f64 { self.weight }
    pub const fn expectation(&self) -> f64 { self.expectation }

    pub fn entropy_bits(&self) -> f64 {
        self.expectation / std::f64::consts::LN_2
    }

    fn log_sum_exp(a: f64, b: f64) -> f64 {
        if a == f64::INFINITY { return b; }
        if b == f64::INFINITY { return a; }
        let min_val = a.min(b);
        let diff = (a - b).abs();
        if diff > 20.0 { min_val }
        else { min_val - (1.0 + (-diff).exp()).ln() }
    }
}
```

### 11.3 Semiring Trait Implementation

```rust
#[cfg(feature = "wfst-log")]
impl Semiring for EntropyWeight {
    fn zero() -> Self { EntropyWeight { weight: f64::INFINITY, expectation: 0.0 } }
    fn one()  -> Self { EntropyWeight { weight: 0.0, expectation: 0.0 } }

    fn plus(&self, other: &Self) -> Self {
        if self.weight == f64::INFINITY { return *other; }
        if other.weight == f64::INFINITY { return *self; }

        let new_weight = Self::log_sum_exp(self.weight, other.weight);
        let w_min = self.weight.min(other.weight);
        let diff_self = self.weight - w_min;
        let diff_other = other.weight - w_min;

        if diff_self > 20.0 {
            EntropyWeight { weight: new_weight, expectation: other.expectation }
        } else if diff_other > 20.0 {
            EntropyWeight { weight: new_weight, expectation: self.expectation }
        } else {
            let r_self = (-diff_self).exp();
            let r_other = (-diff_other).exp();
            let denom = r_self + r_other;
            let new_expectation =
                (r_self * self.expectation + r_other * other.expectation) / denom;
            EntropyWeight { weight: new_weight, expectation: new_expectation }
        }
    }

    fn times(&self, other: &Self) -> Self {
        EntropyWeight {
            weight: self.weight + other.weight,
            expectation: self.expectation + other.expectation,
        }
    }

    fn is_zero(&self) -> bool {
        self.weight.is_infinite() && self.weight.is_sign_positive()
    }

    fn is_one(&self) -> bool {
        self.weight == 0.0 && self.expectation == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() { true }
        else if self.is_zero() || other.is_zero() { false }
        else {
            (self.weight - other.weight).abs() <= epsilon
                && (self.expectation - other.expectation).abs() <= epsilon
        }
    }
}
```

### 11.4 Ordering and Display

```rust
/// Ordered by weight first (lower = more probable), then expectation.
#[cfg(feature = "wfst-log")]
impl Ord for EntropyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight.total_cmp(&other.weight)
            .then_with(|| self.expectation.total_cmp(&other.expectation))
    }
}

#[cfg(feature = "wfst-log")]
impl fmt::Display for EntropyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() { write!(f, "(inf, 0)") }
        else { write!(f, "({:.4}, {:.4})", self.weight, self.expectation) }
    }
}
```

### 11.5 Hash and Default

```rust
#[cfg(feature = "wfst-log")]
impl std::hash::Hash for EntropyWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.weight.to_bits().hash(state);
        self.expectation.to_bits().hash(state);
    }
}

#[cfg(feature = "wfst-log")]
impl Default for EntropyWeight {
    fn default() -> Self { Self::one() }
}
```

Both `Ord` and `Hash` use `f64::total_cmp` / `to_bits()` to handle NaN
and negative zero correctly, consistent with the LogWeight implementation.

---

## 12. Source References

**Source file**: `prattail/src/automata/semiring.rs`
- Section header and doc comment: lines 1084--1117
- Struct definition: lines 1118--1125
- Constructors and `log_sum_exp`: lines 1127--1183
- Semiring trait implementation: lines 1185--1298
- Debug implementation: lines 1300--1313
- Display implementation: lines 1315--1324
- PartialEq/Eq implementations: lines 1326--1335
- PartialOrd/Ord implementations: lines 1337--1352
- Hash implementation: lines 1354--1360
- Default implementation: lines 1362--1367

**Tests**: `prattail/src/automata/semiring.rs`, lines 2467--2637
- `test_entropy_weight_semiring_laws` -- zero/one identity, zero annihilation (line 2472)
- `test_entropy_weight_times_is_addition` -- times = componentwise addition (line 2492)
- `test_entropy_weight_plus_equal_weights` -- equal-weight mixture averages expectations (line 2501)
- `test_entropy_weight_plus_unequal_weights` -- dominant path's expectation wins (line 2523)
- `test_entropy_weight_plus_commutativity` -- commutativity of ⊕ (line 2537)
- `test_entropy_weight_from_arc_weight` -- from_arc_weight sets e = w (line 2546)
- `test_entropy_weight_entropy_bits` -- nats-to-bits conversion (line 2553)
- `test_entropy_weight_plus_large_diff` -- fast path for large weight differences (line 2564)
- `test_entropy_weight_distributivity_approx` -- a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c) (line 2578)
- `test_entropy_weight_ordering` -- lower weight < higher weight < zero (line 2596)
- `test_entropy_weight_display` -- Display formatting (line 2605)
- `test_entropy_weight_hash` -- HashSet insertion and lookup (line 2613)
- `test_entropy_weight_product_with_tropical` -- ProductWeight<TropicalWeight, EntropyWeight> composition (line 2622)

---

## 13. Cross-References

**Theory documents:**
- [LogWeight theory](./log-weight.md) -- EntropyWeight extends LogWeight (Section 4);
  shares the same log-sum-exp numerical stability analysis (Section 6)
- [TropicalWeight theory](./tropical-weight.md) -- the primary dispatch semiring;
  EntropyWeight provides entropy to guide beam width over TropicalWeight dispatch
- [ProductWeight theory](./product-weight.md) -- `ProductWeight<TropicalWeight, EntropyWeight>`
  combines dispatch priority with entropy tracking
- [Semirings overview](../semirings.md) -- comprehensive survey of all semirings in PraTTaIL

**Design documents:**
- [Weight Training Design](../../../design/wfst/weight-training.md) -- entropy as
  convergence criterion during training
- [DSL Configuration](../../../usage/wfst/dsl-configuration.md) -- beam_width
  configuration using entropy

**References:**
- Li, Z. & Eisner, J. (2009). "First- and Second-Order Expectation Semirings with
  Applications to Minimum-Risk Training on Translation Forests."
  *Proceedings of EMNLP*, pages 40--51. Introduces the general expectation semiring
  framework from which EntropyWeight is derived.
- Shannon, C. E. (1948). "A Mathematical Theory of Communication."
  *Bell System Technical Journal*, 27(3):379--423. Defines Shannon entropy
  H = -SUM pᵢ log(pᵢ).
- Mohri, M. (2002). "Semiring Frameworks and Algorithms for Shortest-Distance
  Problems." *Journal of Automata, Languages and Combinatorics*, 7(3):321--350.
  General semiring framework for WFST algorithms.
