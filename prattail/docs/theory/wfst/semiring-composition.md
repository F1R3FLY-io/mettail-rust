# Multi-Semiring Composition: Quick Reference

PraTTaIL's pipeline uses **10 semiring types** over a **shared WFST topology**.
A single automaton is built once (from grammar declarations) and then queried
through different algebraic lenses depending on the analysis being performed.
This document defines the three **composition modes** that govern how multiple
semirings interact across the pipeline.

> **Reading time:** 5–10 minutes.  For the full source-level orchestration map,
> see [`architecture/wfst/semiring-orchestration.md`](../../architecture/wfst/semiring-orchestration.md).

---

## Table of Contents

1. [Why Multiple Semirings?](#1-why-multiple-semirings)
2. [Mode 1 — Re-Interpretation (Implicit Projection)](#2-mode-1--re-interpretation-implicit-projection)
3. [Mode 2 — ProductWeight Joint Tracking](#3-mode-2--productweight-joint-tracking)
4. [Mode 3 — Cross-Structure Data Flow](#4-mode-3--cross-structure-data-flow)
5. [Decision Tree](#5-decision-tree)
6. [Pipeline Timing Diagram](#6-pipeline-timing-diagram)
7. [Formal Properties](#7-formal-properties)
8. [See Also](#8-see-also)

---

## 1. Why Multiple Semirings?

Each semiring answers a **different question** about the same automaton:

| Semiring                | Question                                            |
|:------------------------|:----------------------------------------------------|
| `TropicalWeight`        | What is the lowest-cost parse?                      |
| `BooleanWeight`         | Is this path reachable at all?                      |
| `CountingWeight`        | How many derivations exist?                         |
| `EditWeight`            | What is the minimum edit distance?                  |
| `ContextWeight`         | Which rules contribute to this path?                |
| `ComplexityWeight`      | How much lookahead does this path need?             |
| `ProductWeight<S₁, S₂>` | Answer two questions simultaneously                 |
| `LogWeight`             | What is the real-valued (log-space) probability?    |
| `EntropyWeight`         | What is the entropy of the derivation distribution? |
| `NbestWeight<N>`        | What are the N-best alternatives?                   |

The grammar topology (states, transitions, accept states) is computed **once**.
Only the **weight algebra** changes between analyses. This "shared topology,
multiple passes" design avoids duplicating automaton construction and ensures
all analyses agree on the same grammar structure.

---

## 2. Mode 1 — Re-Interpretation (Implicit Projection)

### Definition

A Mode 1 composition takes an existing WFST weighted in semiring **K₁** and
queries it as though it were weighted in semiring **K₂**, by applying a
**semiring homomorphism** φ: K₁ → K₂ at query time.  No new data structure is
allocated — the projection is implicit in the query predicate.

### Mathematical Character

```
φ: K₁ → K₂   such that:
    φ(0_K₁) = 0_K₂
    φ(1_K₁) = 1_K₂
    φ(a ⊕  b) = φ(a) ⊕  φ(b)
    φ(a ⊗  b) = φ(a) ⊗  φ(b)
```

The homomorphism is never explicitly constructed as a function. Instead, the
query collapses the original weight to a boolean or counting value inline.

### Concrete Instances

| Instance                   | K₁               | K₂                 | Homomorphism                    | Source                  |
|:---------------------------|:-----------------|:-------------------|:--------------------------------|:------------------------|
| Tier 3 dead-rule detection | `TropicalWeight` | `BooleanWeight`    | `w ↦ (w ≠ +∞)`                  | `pipeline.rs:216–232`   |
| CountingWeight in dispatch | `TropicalWeight` | `CountingWeight`   | `entries.len() as u64`          | `prediction.rs:1640`    |
| NFA spillover diagnostics  | `TropicalWeight` | `BooleanWeight`    | `w ↦ (w < threshold)`           | `trampoline.rs`         |
| DeadStateElimination       | `TropicalWeight` | `BooleanWeight`    | forward ∧ backward reachability | `transducer.rs:107–122` |
| confidence_gap             | `TropicalWeight` | ℝ (not a semiring) | second − first weight           | `wfst.rs:422–428`       |

### When to Use

Choose Mode 1 when:
- The analysis needs only a **coarser** view of existing weights
- **No new data** needs to be stored per-edge
- The projection can be expressed as a **predicate** or simple arithmetic on existing weights

---

## 3. Mode 2 — ProductWeight Joint Tracking

### Definition

A Mode 2 composition uses `ProductWeight<S₁, S₂>` to carry **two metrics
simultaneously** through a single graph traversal.  The product semiring
applies `plus` and `times` component-wise:

```
(K₁ × K₂, ⊕, ⊗, 0, 1)  where:
    (a₁, a₂) ⊕  (b₁, b₂) = (a₁ ⊕₁ b₁, a₂ ⊕₂ b₂)
    (a₁, a₂) ⊗  (b₁, b₂) = (a₁ ⊗₁ b₁, a₂ ⊗₂ b₂)
    0 = (0₁, 0₂)
    1 = (1₁, 1₂)
```

**Ordering** is lexicographic: the left component is primary, the right
component breaks ties.  This means `ProductWeight<TropicalWeight, EditWeight>`
first optimizes parse priority, then minimizes edit distance among tied paths.

### Concrete Instances

| Instance                            | S₁               | S₂               | Purpose                                     | Source                                  |
|:------------------------------------|:-----------------|:-----------------|:--------------------------------------------|:----------------------------------------|
| `RecoveryCost`                      | `TropicalWeight` | `EditWeight`     | Joint priority + min-edit recovery          | `recovery.rs:58`                        |
| Nearly-dead detection               | `BooleanWeight`  | `CountingWeight` | Reachability + derivation count in one pass | `pipeline.rs:450–574`                   |
| `ProductWeight<Tropical, Counting>` | `TropicalWeight` | `CountingWeight` | Best parse + uniqueness (confidence)        | `lattice.rs` tests, `product-weight.md` |
| `ProductWeight<Boolean, Counting>`  | `BooleanWeight`  | `CountingWeight` | Reachability + path count                   | `pipeline.rs:458`                       |

### Viterbi Compatibility Note

`viterbi_generic<W>()` requires `W: Semiring + Ord` and assumes `W::zero()`
is the **largest** (worst) element under `Ord`.  This holds for:

| Weight                          | `zero()`    | Ord-largest?                    |
|:--------------------------------|:------------|:--------------------------------|
| `TropicalWeight`                | `+∞`        | Yes                             |
| `EditWeight`                    | `u32::MAX`  | Yes                             |
| `ProductWeight<Tropical, Edit>` | `(+∞, MAX)` | Yes (lexicographic)             |
| `CountingWeight`                | `0`         | **No** — zero is the *smallest* |

`CountingWeight` is NOT Viterbi-compatible standalone. Use it via
`ProductWeight<TropicalWeight, CountingWeight>` or forward-backward algorithms.

### When to Use

Choose Mode 2 when:
- Two metrics must be computed over the **same graph traversal**
- The second metric acts as a **tiebreaker** when the primary metric ties
- You want to **avoid a second traversal** (e.g., forward-backward twice)

---

## 4. Mode 3 — Cross-Structure Data Flow

### Definition

A Mode 3 composition extracts **scalar values** from one WFST structure's
semiring computations and **injects** them as construction parameters into a
different structure.  This is NOT a semiring operation — the extracted values
lose their algebraic identity and become plain `f64` or bitset values.

### Concrete Flows

#### Flow A — Prediction Discount Injection

```
PredictionWfst (TropicalWeight)
        │
        │  pred.predict(sync_tok) → best_weight: f64
        │
        ▼
    discount = max(1.0 − best_weight, 0.1)
        │
        ▼
RecoveryWfst.prediction_discounts[sync_id] = discount
```

**Source:** `recovery.rs:1342–1365` (`build_recovery_wfsts`)

The prediction WFST's tropical weights are extracted as raw `f64` values,
transformed into discount factors, and stored in the recovery WFST's
`prediction_discounts` HashMap.  The algebraic properties of the tropical
semiring are consumed and discarded — the recovery WFST treats discounts as
plain multiplicative factors.

#### Flow B — Context Weight Injection

```
PredictionWfst (TropicalWeight)
        │
        │  pred.actions → rule indices: [u8]
        │
        ▼
    ContextWeight = ∪{singleton(idx) | idx ∈ actions}
        │
        ▼
RecoveryWfst.follow_contexts[sync_id] = ContextWeight
```

**Source:** `recovery.rs:1367–1425` (`build_recovery_wfsts`)

Rule indices from the prediction WFST are packed into `ContextWeight` bitsets
(a *different* semiring) and stored in the recovery WFST for follow-set
tightening at recovery time.  The tropical weights of the prediction WFST are
ignored — only the structural rule membership matters.

### When to Use

Choose Mode 3 when:
- Results from one analysis inform the **construction** (not query) of another
- The extracted data has **different dimensionality** than the source semiring
- No algebraic relationship between the source and target semirings exists

---

## 5. Decision Tree

```
 Adding a new analysis to the pipeline?
 │
 ├── Does it only need a coarser view of existing weights?
 │   │
 │   ├── Yes ──→ MODE 1: Re-Interpretation
 │   │           Define φ: K₁ → K₂ as a query predicate.
 │   │           No new allocation needed.
 │   │
 │   └── No ───→ Do you need two metrics from the same traversal?
 │               │
 │               ├── Yes ──→ MODE 2: ProductWeight
 │               │           Use ProductWeight<S₁, S₂>.
 │               │           Left = primary, Right = tiebreaker.
 │               │           Check Viterbi compatibility if using shortest-path.
 │               │
 │               └── No ───→ Does one analysis feed construction of another?
 │                           │
 │                           ├── Yes ──→ MODE 3: Cross-Structure Data Flow
 │                           │           Extract values, transform, inject.
 │                           │           Document the transformation clearly.
 │                           │
 │                           └── No ───→ You may need a new semiring type.
 │                                       See semirings.md for the trait spec.
```

---

## 6. Pipeline Timing Diagram

The three modes appear at different pipeline stages.  Each horizontal band
represents one composition mode's active window:

```
Pipeline Stage:   1─NFA  2─DFA  3─WFST  4─Dispatch  5─Recovery  6─Codegen  7─Lint
                  ─────  ─────  ──────  ──────────  ──────────  ─────────  ─────

Mode 1            ·····  ·····  ······  ████████··  ··········  ·········  █████
(Re-Interp)                             │dispatch   │                     │dead-rule
                                        │counting   │                     │Tier 3
                                        └───────────┘                     │DeadState
                                                                          └─Elim

Mode 2            ·····  ·····  ······  ··········  ██████████  ·········  █████
(ProductW)                                          │RecoveryCost         │nearly
                                                    │Tropical×Edit        │dead
                                                    └─────────────────────│Bool×
                                                                          │Count
                                                                          └─────

Mode 3            ·····  ·····  ······  ··········  ██████████  ·········  ·····
(Cross-Struct)                                      │discount injection
                                                    │context injection
                                                    └──────────
```

**Legend:** `█` = active, `·` = inactive

---

## 7. Formal Properties

### Mode 1 — Soundness

**Claim:** If φ: K₁ → K₂ is a semiring homomorphism and the WFST
computation is correct under K₁, then the Mode 1 projection yields correct
results under K₂.

**Justification:** By the homomorphism axioms, φ preserves `⊕` and `⊗`.
The shortest-path (or reachability, or path-count) computation over the
projected weights produces the same result as first projecting, then computing:

```
φ(⊕ᵢ ⊗ⱼ wᵢⱼ) = ⊕ᵢ ⊗ⱼ φ(wᵢⱼ)
```

For PraTTaIL's implicit projections (e.g., `w ↦ (w ≠ +∞)`), the homomorphism
from `TropicalWeight` to `BooleanWeight` is verified:
- `φ(+∞) = false = 0_Bool` ✓
- `φ(0.0) = true = 1_Bool` ✓
- `φ(min(a,b)) = φ(a) ∨ φ(b)` ✓ (either being finite ⇒ min is finite)
- `φ(a+b) = φ(a) ∧ φ(b)` ✓ (both finite ⇒ sum is finite)

### Mode 2 — Correctness

**Claim:** `ProductWeight<S₁, S₂>` with lexicographic `Ord` preserves the
primary semiring's optimality when used with Viterbi, provided `S₁::zero()`
is the largest element under `S₁::Ord`.

**Justification:** Lexicographic comparison `(a₁, a₂) < (b₁, b₂)` iff
`a₁ < b₁` or (`a₁ = b₁` and `a₂ < b₂`).  Viterbi selects the minimum-weight
path.  Since the left component is compared first, the path optimal under S₁
is always preferred; the right component only breaks ties in S₁.

**Caveat:** The `plus` operation is component-wise, NOT lexicographic.  This
means `ProductWeight` is not a lexicographic semiring in the formal sense
(which would require `plus` to also be lexicographic).  For Viterbi, only
`Ord` matters — but for algorithms relying on `plus` (like forward-backward),
the component-wise `plus` yields the correct per-component aggregation.

### Mode 3 — Monotonicity

**Claim:** Mode 3 transformations preserve the monotonicity of the target
structure with respect to its own semiring.

**Justification:** The extracted values are injected as **fixed constants**
into the target structure (e.g., `prediction_discounts` is a static HashMap).
They do not participate in the target's semiring operations — they are
external parameters.  Therefore, the target semiring's algebraic properties
(associativity, commutativity, distributivity) are unaffected.

**Conservativity:** PraTTaIL's Mode 3 flows are designed to be conservative:
- Discount injection: `discount ∈ (0.0, 1.0]`, so multiplying by a discount
  can only reduce or maintain a recovery cost — never increase it
- Context injection: `ContextWeight::one()` (universal set) is used for
  structural tokens, ensuring no valid sync token is filtered out

---

## 8. See Also

| Document                                                                         | Scope                                                                              |
|:---------------------------------------------------------------------------------|:-----------------------------------------------------------------------------------|
| [`semiring-orchestration.md`](../../architecture/wfst/semiring-orchestration.md) | Full pipeline annotation with source references                                    |
| [`semirings.md`](semirings.md)                                                   | Semiring trait definition and all 10 concrete types                                |
| [`semirings/product-weight.md`](semirings/product-weight.md)                     | ProductWeight composition catalog                                                  |
| [`semirings/boolean-weight.md`](semirings/boolean-weight.md)                     | BooleanWeight reachability analysis                                                |
| [`semirings/context-weight.md`](semirings/context-weight.md)                     | ContextWeight set-semiring details                                                 |
| [`semirings/complexity-weight.md`](semirings/complexity-weight.md)               | ComplexityWeight bottleneck analysis                                               |
| [`dead-rule-detection.md`](../../design/wfst/dead-rule-detection.md)             | Five-tier dead-rule analysis (Modes 1 + 4)                                         |
| [`pipeline-integration.md`](../../architecture/wfst/pipeline-integration.md)     | Pipeline step-by-step data flow                                                    |
| [`composed-dispatch.md`](../../design/composed-dispatch.md)                      | Composed dispatch table construction                                               |
| [`stream-to-lattice.md`](stream-to-lattice.md)                                   | Stream-to-Lattice Conversion — the lattice structures that Mode 1/2/3 operate over |
