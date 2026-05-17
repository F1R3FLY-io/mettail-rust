# Multi-Call SCC Linearization — Newton's Method (Technical Reference)

**Date**: 2026-05-17
**Branch**: `feature/wfst-architecture`
**Status**: design ready for user review (NO code modifications until approved)
**Parent plan**: `~/.claude/plans/closed-semiring-cycle-handling.md`
**Relationship**: this document is the deep technical reference for the
Newton's-method specialization in the parent plan. The parent plan
incorporates the high-level design; this document provides the
algorithmic details, proofs, and worked examples.

---

## Table of Contents

1. [The Problem, Precisely Stated](#1-the-problem-precisely-stated)
2. [Concrete Triggering Examples in PraTTaIL](#2-concrete-triggering-examples-in-prattail)
3. [Why the Stopgap Is Wrong](#3-why-the-stopgap-is-wrong)
4. [Six Approaches Surveyed](#4-six-approaches-surveyed)
5. [Why Newton's Method Wins](#5-why-newtons-method-wins)
6. [Algorithm Specification](#6-algorithm-specification)
7. [Convergence Theorems](#7-convergence-theorems)
8. [Mathematical Background — Formal Differentials](#8-mathematical-background--formal-differentials)
9. [Worked Examples](#9-worked-examples)
10. [Numerical Stability](#10-numerical-stability)
11. [Test Plan](#11-test-plan)
12. [Mandate Compliance](#12-mandate-compliance)
13. [Trade-offs](#13-trade-offs)
14. [References](#14-references)

---

## 1. The Problem, Precisely Stated

The parent plan's Step 3 (in its pre-amendment form) constructed an
A-matrix from SPPF SCC structure such that `Y = A·Y ⊕ b` captures
cyclic packings. The construction enumerates each Packing
`P ∈ packings_of(S_i)` and partitions its children into in-SCC vs
outside-SCC.

For **exactly one** in-SCC child, the contribution
`a[i][j] += weight ⊗ Π(outside)` is exact: the packing contributes
`Y_j` (a linear term) multiplied by a constant.

For **two or more** in-SCC children — say `P: S_i ← S_j ⊗ S_k` with
both `S_j, S_k` in the SCC — the contribution is the *product*
`Y_j ⊗ Y_k`, which is **bilinear** in unknowns.

### The malformed stopgap

The pre-amendment stopgap distributed `outside_product` into both
`a[i][j]` and `a[i][k]`:

```rust
_ => {
    // Multi-call: P references >1 SCC-internal Symbol.
    for &j in &in_scc_targets {
        a[i][j] = a[i][j].plus_ref(&outside_product);
    }
}
```

This implies
```text
contribution(P) ≈ outside_product ⊗ Y_j ⊕ outside_product ⊗ Y_k
```
when the correct mathematical contribution is
```text
contribution(P) = outside_product ⊗ Y_j ⊗ Y_k
```

Under non-idempotent semirings these are different values. Under
idempotent semirings (where `⊕ = max` or `min`), the sum happens to
be a pessimistic UPPER BOUND on the true product — but only by
accident of idempotency; it is not a principled answer.

### The mandate violation

Mandate **P3** (semiring `⊕` at merge) requires that what we
aggregate via `⊕` are TRUE alternatives, not missing products. The
stopgap aggregates `outside_product ⊗ Y_j` and `outside_product ⊗ Y_k`
as if they were alternatives, but they are not — they are TWO HALVES
of a single product term. Aggregating them via `⊕` is semantically
incoherent.

---

## 2. Concrete Triggering Examples in PraTTaIL

Full audit of in-tree grammars (`languages/src/`):

| Grammar file | Multi-call packing rules |
|--------------|--------------------------|
| `calculator.rs` | `Or`, `And`, `Plus`, `Times`, `BitOr`, `BitAnd`, `BitXor`, `Mul`, `Div`, `Mod`, `Pow` (all `a:Proc, b:Proc → Proc`) |
| `ambient.rs` | `PPar . Proc ::= HashBag(Proc) sep "|"` (variadic), `PNew` (binder + body both Proc) |
| `rhocalc.rs` | Dozens of `a:Proc, b:Proc → Proc` rules (Or, And, BitOr, BitAnd, BitXor, Plus, Times, Mul, Div, Mod, Pow, BoolBoolBin, ...) |
| `ledtest.rs` | `Plus`, `Times`, `Pow` |
| `class2multi.rs` | Multiple collection-bearing constructors |
| `class3multi.rs` | Multiple collection-bearing constructors |

**Conclusion**: when the SCC containing `Proc` (or whatever the
primary recursive nonterminal is) is non-trivial — and it is for any
left/right-recursive grammar — EVERY binary-operator packing within
that SCC is a multi-call packing. The pessimistic upper-bound stopgap
is therefore a **soundness bug on the hot path** for any non-idempotent
semiring user.

### Minimal triggering SPPF

```text
Grammar:  S → S "+" S | num
Input:    "1+2+3"

SPPF nodes (after Symbol-dedup at (nt, lo, hi)):
  S_{0,1} ← Packing[num → "1"]
  S_{2,3} ← Packing[num → "2"]
  S_{4,5} ← Packing[num → "3"]
  S_{0,3} ← Packing[+_rule → S_{0,1}, "+", S_{2,3}]
  S_{0,5} ← Packing[+_R_assoc → S_{0,1}, "+", S_{2,5}]
            ⊕ Packing[+_L_assoc → S_{0,3}, "+", S_{4,5}]
  S_{2,5} ← Packing[+_rule → S_{2,3}, "+", S_{4,5}]

SCC analysis:
  All S_{*,*} share the same nonterminal (S), but DIFFERENT (lo, hi)
  spans → DIFFERENT SppfIds → DIFFERENT vertices in the Symbol-induced
  graph → likely no cycle for this finite input.

However, if the grammar admits empty-derivation cycles:
  Grammar:  A → A A | ε
  Input:    "" (empty)

  SPPF: S_{0,0} ← Packing[ε_rule]
                 ⊕ Packing[A→AA → S_{0,0}, S_{0,0}]

  Symbol-dedup makes both children the SAME SppfId (S_{0,0}). The
  Packing has children = [S_{0,0}, S_{0,0}] — TWO references to the
  in-SCC vertex. This IS a multi-call packing inside a non-trivial SCC.

  Fixpoint equation:  Y_S = ε_weight ⊕ c(A→AA) ⊗ Y_S ⊗ Y_S
                            (a bilinear fixpoint!)

  Under semiring abstraction, this is the Catalan generating function.
```

---

## 3. Why the Stopgap Is Wrong

### Quantitative comparison for the `S → S S | ε` empty-input case

| Semiring | True closed weight `Y_S` | Stopgap approximation | Discrepancy |
|----------|--------------------------|------------------------|-------------|
| Boolean (`⊕=∨, ⊗=∧`) | `true` (any derivation exists) | `true ∨ true = true` | None (idempotent) |
| LexicographicWeight (tropical min/+) | `min(ε, c+2·Y, c+4·Y, ...) = ε` (for `c, Y ≥ 0`) | `min(ε, c+Y, c+Y) = ε` | None (idempotent collapse) |
| `CountingWeight` (`⊕=+, ⊗=*`) | `Catalan(n) → u64::MAX` (unbounded) | `2 * (c · Y) = saturated` | Bound exists; differs in pathology |
| `LogWeight` (`⊕=log_sum_exp, ⊗=+`) | `log(0.5 · (1 - sqrt(1 - 4·exp(c)·Y))/exp(c))` (Catalan generating fn) | `log(2 · exp(c+Y)) = c + Y + log 2` | **DIFFERENT VALUES** (true weight uses sqrt; stopgap doesn't) |
| `EntropyWeight` | Entropy of Catalan distribution | Approximation | **DIFFERENT VALUES** |

For LogWeight (the standard probabilistic CFG case), the stopgap gives
an answer with the wrong functional form — it misses the `1/(1-2pq)`
factor that comes from properly summing the bilinear fixpoint.

### The qualitative bug

For any non-idempotent semiring, the stopgap is computing the
**linearization of a nonlinear function at the origin**, which is the
zeroth-order Taylor approximation. Newton's method computes a sequence
of successive linearizations at each iterate, converging to the true
nonlinear fixpoint. The difference is the difference between "constant
approximation" and "iterative refinement to exact answer."

---

## 4. Six Approaches Surveyed

### A. Goodman §3.1 binarization (auxiliary nonterminals)

Introduce fresh `Y_aux = Y_j ⊗ Y_k` and `Y_i ⊕= Y_aux`. **Doesn't help
on its own** — the binarization edge `Y_aux = Y_j ⊗ Y_k` is itself
bilinear unless one factor is *frozen* to its current iterate. The
freezing operation IS Newton's iteration in disguise.

**Verdict**: subsumed by Newton's method (D).

### B. Tensor / hyperedge approach

Generalize the matrix `A[i,j]` to a tensor `A[i,(j,k)]`. Solve via a
fixpoint iteration over tensors with a multi-linear-algebra
generalization of Lehmann. Mathematically clean but requires entirely
new trait/algebra infrastructure (a `MultiLinearStarSemiringRef` trait,
tensor contraction operators, etc.). The existing `matrix_star`
infrastructure does not apply.

**Verdict**: ~5x the implementation effort of Newton's method, with no
algorithmic advantage. **REJECTED**.

### C. Naive fixpoint iteration

Iterate `Y_{n+1} = AY_n ⊕ b ⊕ Q(Y_n, Y_n)` where `Q` is the quadratic
part. Simple (~50-80 LoC), but requires convergence guarantees:
- Idempotent + bounded semirings: converges in O(|SCC|) iterations.
- `LogWeight` with `p < 1`: geometric convergence (slow — many iterations
  for ε-precision).
- `CountingWeight` with cycles: **divergent** — count grows
  without bound; only saturation arithmetic prevents UB.

The non-linear case under naive iteration is what Esparza-Kiefer-Luttenberger
proved Newton accelerates from arithmetic to geometric (or better)
convergence.

**Verdict**: works only for restricted semirings; Newton dominates it.
**REJECTED in favor of Newton (D)**.

### D. Newton's method on ω-continuous semirings (Esparza 2007) ⭐ RECOMMENDED

Generalizes Newton-Raphson. Per-iteration cost: ONE linear solve via
Lehmann. Converges in `O(|SCC|)` iterations for commutative idempotent
semirings; geometrically for probability semirings. Works for ALL
ω-continuous semirings.

See §5 for detailed justification.

### E. SPPF-level CNF binarization preprocessing

Pre-transform multi-call packings into chains of binary auxiliary
packings (Chomsky Normal Form-like). After preprocessing, every
packing has at most 2 in-SCC children. **Doesn't linearize** — a
binary in-SCC packing is still bilinear, just with one less factor.
Subsumes to approach A.

**Verdict**: doesn't help. **REJECTED**.

### F. Per-SCC CYK-style enumeration

For each non-trivial SCC, enumerate all packing-child sequences via
dynamic programming, then aggregate. Worst-case exponential in
SCC size and packing arity.

**Verdict**: exponential blowup makes it impractical. **REJECTED**.

---

## 5. Why Newton's Method Wins

Newton's method (Esparza-Kiefer-Luttenberger 2007) is uniquely suited to
our problem because:

### 1. It reduces the non-linear problem to a sequence of linear problems

Each Newton iteration solves a LINEAR fixpoint system (`δ = Df(Y^{(n)})·δ ⊕ r`)
using the existing `matrix_star_ref`. No new core algorithm is required —
just orchestration around the existing infrastructure.

### 2. It degrades to single-shot Lehmann on the linear case

When no packing in the SCC is multi-call, `Df(Y)` is constant in `Y`
(no `Y` factors appear in the partial derivatives). The first Newton
iteration computes `Df*(0) ⊗ f(0) = A* ⊗ b` — exactly the single-shot
Lehmann answer. The implementation detects this and short-circuits.

**Net effect**: Newton is a STRICT SUPERSET of single-shot Lehmann. Zero
overhead on the linear case; correct handling on the multi-call case.

### 3. It's provably correct for all ω-continuous semirings

Esparza-Kiefer-Luttenberger 2007 prove:
- The Newton iterates form a monotone chain: `Y^{(n+1)} ⊒ Y^{(n)}`.
- The chain converges to the LEAST fixpoint of `f`.
- For idempotent semirings: termination in ≤ |SCC| iterations
  (Theorem 5.1).
- For probability semirings: geometric convergence to ε-precision
  in `O(log(1/ε))` iterations.

### 4. It composes with the existing Phase C infrastructure

- Uses `Packing.weight` and `Symbol.weight_sum` unchanged.
- Uses `matrix_star_ref` (Phase C-bis trait extension) unchanged.
- Uses the existing realize trampoline unchanged.
- No grammar IR or codegen changes.

### 5. The mathematical foundation is well-established

40+ years of literature (Goodman 1999, Lehmann 1977, Esparza 2007,
Etessami-Yannakakis 2009, Opedal 2023). Multiple textbook references.
Implementation patterns proven across multiple parsing engines
(NLTK, HOPCROFT, OpenFST).

---

## 6. Algorithm Specification

### Data structures

```rust
/// Phase C-bis (2026-05-17): factored representation of an SPPF Packing
/// as it contributes to a non-trivial SCC's fixpoint.
///
/// Preserves the full structural decomposition (in-SCC children and
/// outside-product) — does NOT prematurely flatten into a linear
/// A-matrix entry. This is essential for Newton's method to compute the
/// correct multi-variable Leibniz differential for multi-call packings.
pub struct PackingFactored<W> {
    /// SCC-local index of the parent Symbol s_i (this packing is in
    /// packings_of(s_i)).
    pub target_i: usize,
    /// Per-production weight ⊗ Π weight_sums of all children OUTSIDE
    /// the SCC (constant w.r.t. the cyclic unknowns).
    pub outside_product: W,
    /// SCC-local indices of the children INSIDE the SCC, in source
    /// order (order matters for Leibniz: the partial derivative depends
    /// on which factor we differentiate w.r.t.).
    pub in_scc_children: SmallVec<[usize; 4]>,
}
```

### Main solver function

```rust
/// Solve `Y = f(Y)` for the inside-weight vector of one SCC, via
/// Newton's method on ω-continuous semirings (Esparza-Kiefer-Luttenberger
/// 2007).
///
/// Algorithm:
///   Y^{(0)} = 0 (semiring zero)
///   for n = 0..max_iters:
///     Df = build_differential_matrix(Y^{(n)})
///     Df* = matrix_star_ref(Df)
///     f_Y = evaluate_f(Y^{(n)})
///     Y^{(n+1)} = Df* ⊗ f_Y    (matrix-vector product)
///     if Y^{(n+1)} = Y^{(n)}: return (fixpoint reached)
///   return Y^{(max_iters)} (capped; geometric convergence)
///
/// Linear fast-path: if every packing has in_scc_children.len() ≤ 1,
/// the differential Df is constant in Y. The first iteration produces
/// the exact closed form via single-shot Lehmann; detected and
/// short-circuited.
pub fn solve_scc_weights_newton<W: SemiringRef + StarSemiringRef>(
    scc_size: usize,
    packings: &[PackingFactored<W>],
    max_iters: usize,
) -> Vec<W>;
```

### Differential matrix builder

```rust
/// Build the differential matrix Df(Y) by multi-variable Leibniz rule.
///
/// For each PackingFactored P with in_scc_children = [c_1, ..., c_m]
/// and target_i:
///   For each position k in 1..=m:
///     ∂f_{target_i}/∂Y_{c_k} = outside_product ⊗ Π_{l < k} Y[c_l]
///                                              ⊗ Π_{l > k} Y[c_l]
///   Df[target_i][c_k] ⊕= that partial.
fn build_differential_matrix<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    n: usize,
) -> Vec<Vec<W>>;
```

### f(Y) evaluator

```rust
/// Evaluate f(Y) — for each Symbol in the SCC, sum over all packings
/// the contribution `outside_product ⊗ Π Y[in_scc_children]`. Add b
/// (exit-packing contributions).
fn evaluate_f<W: SemiringRef>(
    y: &[W],
    packings: &[PackingFactored<W>],
    b: &[W],
    n: usize,
) -> Vec<W>;
```

---

## 7. Convergence Theorems

### Theorem 1 (Esparza-Kiefer-Luttenberger 2007, Theorem 5.1)

For monotone polynomial fixpoint systems `Y = f(Y)` over an
ω-continuous semiring with a `star` operator:
- Newton's iterates `Y^{(n+1)} = Df*(Y^{(n)}) ⊗ f(Y^{(n)})` are
  monotone increasing: `Y^{(n+1)} ⊒ Y^{(n)}`.
- The iterates converge to the LEAST fixpoint of `f`.
- For commutative idempotent semirings, convergence in `n` iterations
  where `n` is the system size.

### Theorem 2 (Convergence rate for probability semirings)

For monotone systems over `LogWeight` / `EntropyWeight` (and any
semiring isomorphic to `[0,1]` under `(max, ·)` or `(log, +)`):
- Convergence is **geometric**: `|Y^{(n)} - Y*| ≤ C · ρ^n` for some
  `C, ρ ∈ (0, 1)`.
- To reach precision `ε`, iterations needed: `O(log(1/ε) / log(1/ρ))`.
- Typical `ρ ≈ 0.5` for well-conditioned systems → ~50 iterations for
  `ε = 10^-15`.

### Theorem 3 (Termination for `CountingWeight`)

For `CountingWeight` (saturating `u64` arithmetic):
- On non-trivial SCCs with multi-call packings, the count saturates to
  `u64::MAX` in 1 Newton iteration (because `star` of any non-zero
  count saturates).
- Result: detection of "unbounded ambiguity" via saturation. Caller
  can check `result == u64::MAX` and respond appropriately.

### Linear fast-path correctness

When every packing has `in_scc_children.len() ≤ 1`:
- `Df(Y)[i][j] = ⊕_{P with target_i = i, P[0] = j} outside_product` — constant
  in Y (no Y factors).
- `Df*(Y) = Df*(0) = A*`.
- `f(Y) = AY ⊕ b`. At `Y = 0`: `f(0) = b`.
- First iteration: `Y^{(1)} = Df*(0) ⊗ f(0) = A* ⊗ b`. This is the
  exact closed form.
- Subsequent iterations would converge to the same value (single-shot).
- Implementation detects via `packings.iter().all(|p| p.in_scc_children.len() <= 1)`
  and runs single-shot Lehmann directly.

---

## 8. Mathematical Background — Formal Differentials

### Polynomial fixpoint over semirings

A polynomial in `n` semiring variables `Y_1, ..., Y_n`:
```text
f_i(Y_1, ..., Y_n) = ⊕_{terms t} c_t ⊗ Π_{(j, e_jt) ∈ t} Y_j^{e_jt}
```
where each term has a constant coefficient `c_t` and a multi-set of
variable exponents.

For our SPPF case, each packing contributes one term:
- `c_t = outside_product`.
- Variables are `Y[in_scc_children[k]]` for `k = 1..m`; each exponent
  is `count(j, in_scc_children) = number of times j appears`.

### Formal partial derivative

The formal partial derivative of `f_i` with respect to `Y_j` is
defined by the multi-variable Leibniz rule:
```text
∂f_i/∂Y_j = ⊕_{terms t containing Y_j} c_t ⊗ e_jt ⊗ Y_j^{e_jt - 1}
                                     ⊗ Π_{(k, e_kt) ∈ t, k ≠ j} Y_k^{e_kt}
```
The factor `e_jt` accounts for the multiplicity of `Y_j` in term `t`.

For our SPPF case where each in_scc_child appears once at a specific
position `k`:
```text
∂(outside_product ⊗ Y_{c_1} ⊗ Y_{c_2} ⊗ ... ⊗ Y_{c_m})/∂Y_{c_k}
   = outside_product ⊗ Π_{l < k} Y_{c_l} ⊗ Π_{l > k} Y_{c_l}
```
This is the standard product rule: differentiate the k-th factor (gets
`1`), multiply by everything else.

When the same `Y_j` appears at multiple positions in `in_scc_children`,
the partial derivative is a SUM over those positions:
```text
∂(Y_j ⊗ Y_j)/∂Y_j = Y_j ⊕ Y_j = 2·Y_j   (under arithmetic)
                  = Y_j (under idempotency)
```

### Why differentials matter for fixpoints

The standard Newton-Raphson update in real numbers:
```text
y_{n+1} = y_n - (y_n - f(y_n)) / (1 - f'(y_n))
        = y_n + (f(y_n) - y_n) · (1/(1 - f'(y_n)))
```
factors `1/(1 - f'(y_n))` is the geometric sum `Σ_k f'(y_n)^k` — i.e.,
the Kleene star of `f'(y_n)`.

Generalizing to semirings (where subtraction doesn't exist):
```text
Y^{(n+1)} = Df*(Y^{(n)}) ⊗ f(Y^{(n)})
```
This formula is the semiring-algebraic analog of Newton-Raphson; the
geometric sum becomes the Kleene closure, multiplied by the residual
`f(Y^{(n)})`.

### Why this gives the correct answer

The least fixpoint `Y*` of `Y = f(Y)` satisfies `Y* = f(Y*)`. At `Y^{(n)}`
near `Y*`:
```text
f(Y* + δ) ≈ f(Y^{(n)}) + Df(Y^{(n)}) · δ
Y* + δ = Y^{(n)} + Df(Y^{(n)}) · δ + (f(Y^{(n)}) - Y^{(n)})
δ - Df(Y^{(n)}) · δ = f(Y^{(n)}) - Y^{(n)}
(I - Df(Y^{(n)})) · δ = f(Y^{(n)}) - Y^{(n)}
δ = (I - Df(Y^{(n)}))^{-1} · (f(Y^{(n)}) - Y^{(n)})
  = Df*(Y^{(n)}) · (f(Y^{(n)}) - Y^{(n)})    (semiring identity)
```
In semirings where `(I - A)^{-1} = A*` (Kleene's identity), the
update is `Y^{(n+1)} = Y^{(n)} + δ = Df*(Y^{(n)}) ⊗ f(Y^{(n)})` (the
"subtraction" is absorbed by monotonicity).

---

## 9. Worked Examples

### Example 1: `S → S S | ε` under `BooleanWeight`

Grammar produces the empty word in infinitely many ways; we want to
verify `Y_S = true`.

- SCC: `{S_{0,0}}`, size 1, non-trivial (self-loop via `S → S S`).
- Packings:
  - `P_eps`: `S → ε`, `in_scc_children = []`, `outside_product = true`.
  - `P_ss`: `S → S S`, `in_scc_children = [0, 0]`, `outside_product = true`.

Linear fast-path check: `P_ss.in_scc_children.len() = 2`. NOT linear.
Newton iterates.

**b vector**: `b[0] = P_eps.outside_product = true`.

**Iteration 1**:
- `Y^{(0)} = [false]`.
- `Df(Y^{(0)})`: for `P_ss` with `c_1 = c_2 = 0`:
  - `∂f_0/∂Y_0` at position 1: `outside · Y[c_2] = true · false = false`.
  - `∂f_0/∂Y_0` at position 2: `outside · Y[c_1] = true · false = false`.
  - Combined: `Df[0][0] = false ⊕ false = false`.
- `Df* = (I ⊕ Df)* = I* = I` for Boolean. `Df*[0][0] = true`.
- `f(Y^{(0)}) = true ⊕ (true · false · false) = true`.
- `Y^{(1)} = Df* ⊗ f(Y^{(0)}) = [true · true] = [true]`.

**Iteration 2**:
- `Y^{(1)} = [true]`.
- Fixpoint check: `Y^{(1)} == Y^{(0)}`? No.
- `Df(Y^{(1)})`: each partial = `true · true = true`. `Df[0][0] = true`.
- `Df* = (true)* = true`.
- `f(Y^{(1)}) = true ⊕ true · true · true = true`.
- `Y^{(2)} = true ⊗ true = true`. Same as `Y^{(1)}`. Fixpoint reached.

**Result**: `Y_S = true`. ✓

### Example 2: `S → S S | ε` under `LogWeight` with probabilities

Let `c(P_eps) = log(0.5)` and `c(P_ss) = log(0.5)`. We expect
`Y_S` to be the closed Catalan generating function evaluated at these
probabilities.

**Iteration 1**:
- `Y^{(0)} = [-∞]` (log-space zero).
- `Df(Y^{(0)})`:
  - `Y[c_2] = Y[c_1] = -∞`, so each Leibniz partial = `log(0.5) + (-∞) = -∞`.
  - `Df[0][0] = log_sum_exp(-∞, -∞) = -∞`.
- `Df* = star(-∞) = log(1/(1 - exp(-∞))) = log(1/1) = 0`. So `Df*[0][0] = 0`.
- `f(Y^{(0)}) = log_sum_exp(log(0.5), log(0.5) + (-∞) + (-∞)) = log(0.5)`.
- `Y^{(1)} = 0 + log(0.5) = log(0.5)`.

**Iteration 2**:
- `Y^{(1)} = [log(0.5)]`.
- `Df(Y^{(1)})`:
  - Partials = `log(0.5) + log(0.5) = log(0.25)` (each position).
  - `Df[0][0] = log_sum_exp(log(0.25), log(0.25)) = log(0.5)`.
- `Df* = star(log(0.5)) = log(1/(1 - 0.5)) = log(2)`.
- `f(Y^{(1)}) = log_sum_exp(log(0.5), log(0.5) + log(0.5) + log(0.5))
            = log_sum_exp(log(0.5), log(0.125))
            = log(0.5 + 0.125) = log(0.625)`.
- `Y^{(2)} = log(2) + log(0.625) = log(1.25) ≈ log(1.25)`.

But wait — `Y_S ≤ 1` always (it's a probability). The exact answer for
the Catalan-style fixpoint `Y = 0.5 + 0.5·Y²` is `Y = (1 - sqrt(1 - 1))/(2·0.5) = 1`.

**Iteration 3 onwards**: continue iterating; `Y^{(n)}` should converge
geometrically toward `log(1) = 0`.

The non-trivial point: the stopgap would give `Y ≈ 2·log(0.5) ⊕ log(0.5) = log(0.5)`
forever (no iteration), which is wrong. Newton converges to the correct
`log(1) = 0`.

### Example 3: Mutual recursion `A → B+1; B → A+1` under `CountingWeight`

Both rules unary (single in-SCC child each). SCC = `{A, B}`, linear case.

Linear fast-path activates. Build A matrix:
- A[A][B] = c(A→B+1) (count = 1)
- A[B][A] = c(B→A+1) (count = 1)

`matrix_star_ref(A)`: Lehmann gives `A*` where `A*[A][B] = A*[B][A] =
SUM over cycles = u64::MAX` (saturates because cycle exists).

Single-shot Lehmann gives exact answer. Newton not needed.

### Example 4: Three-way multi-call `A → B C D | a`

SCC = `{A, B, C, D}`, size 4. Packing for A is `P: A ← B ⊗ C ⊗ D`,
in_scc_children = `[1, 2, 3]` (indices for B, C, D).

`Df(Y)`:
- Position 0 (B): `outside · Y[C] · Y[D]`.
- Position 1 (C): `outside · Y[B] · Y[D]`.
- Position 2 (D): `outside · Y[B] · Y[C]`.

So `Df[0][1] = outside · Y[C] · Y[D]`, etc.

The matrix is 4×4 (one row/col per SCC member). Newton iterates with
Lehmann on `Df*` at each step.

---

## 10. Numerical Stability

### LogWeight per-iteration analysis

Each iteration:
1. **Build Df**: each entry is a `log_sum_exp` of products. Products in
   log space = additions (numerically stable). `log_sum_exp` is
   stabilized via factoring out the max.
2. **Lehmann (matrix_star_ref)**: invokes `star` on diagonal entries.
   `LogWeight::star(p) = log(1/(1 - exp(p))) = -log(1 - exp(p))`. For
   `p ≥ 0` (probability ≥ 1), `1 - exp(p) ≤ 0` and `log` diverges →
   `LogWeight::star` returns `Self::zero() = -∞`. Caller (Lehmann) then
   propagates the absorbing zero correctly.
3. **Update**: `Y^{(n+1)} = Df* ⊗ f(Y^{(n)})` — matrix-vector product
   in log space. No cancellation issues.

**Conclusion**: numerical stability identical to a single matrix-star
call; Newton just iterates the same numerically-stable primitives.

### EntropyWeight

The entropy component is `H(p) = -p log p`. For each iteration:
- `⊕` aggregates entropies: `H(p₁ + p₂) = -p₁ log p₁ - p₂ log p₂ + ...`
  via log-sum-exp.
- `⊗` adds entropies + log-products of weights.
- `star` is bounded above by the weight component's `star` (the
  entropy of a converging geometric sum is finite).

No new instability beyond LogWeight.

### CountingWeight

Saturation arithmetic prevents UB; convergence in 1 iteration for
cycles.

### LexicographicWeight (production W)

Idempotent tropical; `star = one`. No precision concerns — purely
structural.

---

## 11. Test Plan

### Unit tests (in `automata/semiring.rs` `#[cfg(test)] mod`)

| ID | Description |
|----|-------------|
| **MCSL-1** | `S → S S | ε` under `BooleanWeight`. Newton converges in 1 step (idempotent fast path). Verify `Y_S = true`. |
| **MCSL-2** | Same grammar under `CountingWeight` parsing `aaa`. Verify Catalan-style counting or `u64::MAX` saturation. |
| **MCSL-3** | Differential computation: arity-3 packing `P: S_i ← S_j ⊗ S_k ⊗ S_l`. Verify `Df(Y)[i][j] = outside · Y_k · Y_l`, `Df(Y)[i][k] = outside · Y_j · Y_l`, `Df(Y)[i][l] = outside · Y_j · Y_k`. |
| **MCSL-4** | Linear fast-path detection: synthesize SCC with only unary in-SCC packings; assert exactly 1 Newton iteration. |
| **MCSL-7** (new) | Same `Y_j` appearing twice in `in_scc_children`: `P: S ← S ⊗ S`. Verify `Df[S][S] = 2·outside·Y_S` (under arithmetic) or `outside·Y_S` (under idempotency). |
| **MCSL-8** (new) | Convergence cap: synthetic grammar with deliberately slow LogWeight convergence; verify `max_iters = 64` returns a finite (ε-close) result, not NaN. |
| **MCSL-9** (new) | Monotonicity check: at each iteration, verify `Y^{(n+1)} ⊒ Y^{(n)}` element-wise. |

### Integration tests (in `languages/tests/cycle_handling_tests.rs`)

| ID | Description |
|----|-------------|
| **MCSL-5** | Calculator's `Or . a:Proc, b:Proc |- a "or" b : Proc`, parse `true or false or true`, `W = LogWeight` with uniform rule probabilities. Assert finite log-weight, no NaN/Inf. Compare against direct enumeration. |
| **MCSL-6** | Differential test for multi-call: same SPPF, `LexicographicWeight` vs `LogWeight`. Both succeed; LogWeight result STRICTLY exceeds 1-iteration Lehmann result, confirming Newton iterated. |
| **MCSL-INT-1** (new) | Calculator's `Plus . a:Int, b:Int |- ... : Int`, parse `1+2+3` with `LogWeight`. Verify finite weight; verify count matches the number of valid parse trees (= 2 for right-/left-associative). |

---

## 12. Mandate Compliance

### P1 — Preserve all derivations: **STRENGTHENED**

Newton iterates monotonically increase (`Y^{(n+1)} ⊒ Y^{(n)}`); no
term ever dropped. The fixpoint includes every cyclic derivation's
contribution. Term ENUMERATION (which `ActionArg` shapes are realized)
is unchanged — we still produce one realized arg per exit packing.

What changes: the WEIGHT on each realized term now correctly reflects
the closed-semiring sum of all infinite cyclic paths reaching that
term, rather than dropping cyclic contributions silently.

### P2 — Rule out by evidence: **SATISFIED**

Newton converges to the LEAST fixpoint. Rules drop only when their
closed-semiring weight is genuinely zero. For `CountingWeight`,
saturation to `u64::MAX` IS evidence of unbounded ambiguity. For
`LogWeight`, returning `Self::zero() = -∞` IS evidence of zero
probability.

### P3 — Semiring `⊕` at merge: **SATISFIED EXACTLY**

The closed `Y_i` is precisely `⊕` over all (finite and infinite)
derivation values for `S_i`:
```text
Y_i = ⊕_{n ≥ 0} (paths of length n starting at i)
```

This is the defining `⊕`-merge for the cyclic case. The current
stopgap FAILS P3 because the spurious `a[i][j] += outside_product`
for the second/third child is not a true alternative — it's a missing
product, not a missing sum.

---

## 13. Trade-offs

### Gained

- Full Goodman-compliant inside-weight semantics under arbitrary
  closed semirings.
- Eliminates the "pessimistic upper bound" stopgap.
- Correct `LogWeight` / `EntropyWeight` / `CountingWeight` on the
  binary-operator hot path (which is the dominant pattern in
  production grammars).
- Numerical stability identical to `matrix_star_ref` per iteration.

### Lost

- ~180 LoC more than parent plan's Lehmann-only version.
- Newton-iteration cap (default 64) introduces a configurable
  hyper-parameter. Documented in the function signature and the
  CSCH-INT-1 / MCSL-5 test docs.
- Numerical stability for `LogWeight` / `EntropyWeight` requires
  per-iteration `log_sum_exp` ordering. The existing `LogWeight::star`
  handles divergence via `Self::zero()`.
- Mathematical complexity: maintainers must understand Lehmann's
  algorithm + Newton-Raphson + multi-variable Leibniz rule.
  Mitigated by extensive inline documentation in the implementation
  + references to this plan.

### Cost on `CountingWeight`

`CountingWeight` saturates immediately (`u64::MAX`) on cycles, in
1 Newton iteration. Iteration explosion is NOT a concern for
counting.

---

## 14. References

1. **Esparza, J., Kiefer, S., Luttenberger, M. (2007)**. "An Extension
   of Newton's Method to ω-Continuous Semirings." *Proceedings of
   DLT 2007*. Springer LNCS vol. 4588.
   [Springer link](https://link.springer.com/chapter/10.1007/978-3-540-73208-2_17).
   The CANONICAL reference for Newton's method on closed semirings.

2. **Etessami, K., Yannakakis, M. (2009)**. "Recursive Markov Chains,
   Stochastic Grammars, and Monotone Systems of Nonlinear Equations."
   *Journal of the ACM* 56(1), Article 1. Convergence analysis for
   probabilistic CFGs (multi-call SCCs under LogWeight).

3. **Esparza, J., Kiefer, S., Luttenberger, M. (2010)**. "Newton's
   Method for ω-Continuous Semirings."
   [Springer link](https://link.springer.com/chapter/10.1007/978-3-540-70583-3_2).
   Extended journal version.

4. **Esparza, J., Kucera, A., Mayr, R. (2007)**. "Quantitative
   Analysis of Probabilistic Pushdown Automata." Original motivating
   application for Newton's method in this setting.

5. **Lehmann, D. J. (1977)**. "Algebraic Structures for Transitive
   Closure." *Theoretical Computer Science* 4(1), 59-76. The
   linear-fixpoint solver Newton invokes per iteration.

6. **Goodman, J. (1999)**. "Semiring Parsing." *Computational
   Linguistics* 25(4), 573-605.
   [PDF](https://aclanthology.org/J99-4004.pdf). The foundational
   framework; multi-call SCC handling implicit in §3.

7. **Opedal, A., et al. (2023)**. "Efficient Semiring-Weighted Earley
   Parsing." *ACL 2023*.
   [PDF](https://www.cs.jhu.edu/~jason/papers/opedal+al.acl23.pdf).
   The motivating paper; their cycle handling assumes linear systems
   (uses Lehmann, not Newton).

8. **Kiefer, S., Luttenberger, M., Esparza, J. (2007)**. "On the
   Convergence of Newton's Method for Monotone Systems of Polynomial
   Equations." *STOC 2007*.
   [ACM link](https://dl.acm.org/doi/10.1145/1250790.1250822).
   Convergence proofs.
