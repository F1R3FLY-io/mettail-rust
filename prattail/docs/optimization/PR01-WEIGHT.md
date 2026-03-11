# PR01-WEIGHT: Probabilistic Weight Blending

Advanced Automata Codegen Optimization — M7 Probabilistic → Constructor Ordering

## 1. Quick Start

**What it does**: Blends corpus-trained selectivity scores into WFST
constructor weights for better rule ordering. More frequently used rules
are tried first, improving cache locality and branch prediction.

**When it activates**: When the `probabilistic` feature is enabled and
`ProbabilisticAnalysis.is_normalized == true`.

**Feature gate**: `probabilistic`

**Optimization gate**: `probabilistic_weight_blend` (env: `PRATTAIL_OPT_PROBABILISTIC_WEIGHT_BLEND`)

**Status**: `OptimizationStatus::Auto`

## 2. Intuition

WFST structural weights capture grammar topology: which rules are
reachable, how deep they nest, what their branching factor is. But
topology alone doesn't know which rules are *used most often in practice*.

Probabilistic weights from corpus training capture frequency: rule `+`
fires 45% of the time, `*` fires 30%, `^^` fires 0.8%.

The blend combines both signals:

```
w_blend(r) = (w_wfst(r) + w_prob(r)) / 2

where w_prob(r) = -ln(selectivity(r))   // tropical: lower = more frequent
```

This is an arithmetic mean in the tropical semiring. When both signals
agree (rule is both structurally important and frequently used), the
blend strongly favors it. When they disagree, the blend averages.

## 3. Formula

In the tropical semiring ⟨ℝ ∪ {∞}, min, +, ∞, 0⟩:

- **WFST weight** w_wfst(r): structural cost from WFST prediction analysis
- **Probabilistic weight** w_prob(r) = -ln(selectivity(r)): transform [0,1] selectivity to tropical domain
  - selectivity 0.5 → w_prob = 0.693
  - selectivity 0.01 → w_prob = 4.605
  - selectivity 0.001 → w_prob = 6.908
- **Blended weight**: w_blend = (w_wfst + w_prob) / 2

**Properties**:
- Bounded: min(w_wfst, w_prob) ≤ w_blend ≤ max(w_wfst, w_prob)
- Concordant: if both signals rank r₁ above r₂, the blend agrees
- Zero selectivity: skipped (would produce -ln(0) = ∞)

## 4. Example

Binary operator grammar after training on 5,000 programs:

```
Rule        w_wfst   selectivity   w_prob    w_blend
────────────────────────────────────────────────────
Expr + Expr   2.0     0.45         0.80      1.40   ← ordered first
Expr * Expr   2.0     0.30         1.20      1.60
Expr - Expr   2.0     0.15         1.90      1.95
Expr / Expr   2.0     0.08         2.53      2.26
Expr ^^ Expr  2.0     0.008        4.83      3.41   ← ordered last
```

Without blending, all 5 rules have equal WFST weight (2.0) — random order.
With blending, `+` is tried first (cache-hot) and `^^` last.

## 5. Safety

Weight ordering only affects match arm ordering in generated Ascent code.
The Ascent fixpoint evaluates all matching rules regardless of order. By
Tarski's fixpoint theorem (1955), the least fixpoint of a monotone operator
is unique and order-independent.

See [codegen-soundness.md](../theory/optimization/codegen-soundness.md) §4.

## 6. Related

- [PR01-DCE](PR01-DCE.md) — Probabilistic dead-rule elimination
- [Sprint 3 Rule Ordering](README.md) — Base constructor weight ordering
- [Probabilistic Automata Design](../design/probabilistic-automata.md) — Full M7 design
