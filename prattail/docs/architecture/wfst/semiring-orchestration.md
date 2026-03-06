# Semiring Orchestration Across the Pipeline

This document maps every pipeline step that uses semiring operations to its
**composition mode** (as defined in [`theory/wfst/semiring-composition.md`](../../theory/wfst/semiring-composition.md)),
the concrete semiring type(s) involved, the source function, and the data flow.

**Prerequisites:** Familiarity with the three composition modes:
- **Mode 1** — Re-Interpretation (implicit projection, no allocation)
- **Mode 2** — ProductWeight joint tracking (two metrics, one traversal)
- **Mode 3** — Cross-Structure Data Flow (extract → transform → inject)

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Master Pipeline Annotation Table](#2-master-pipeline-annotation-table)
3. [Mode 1 Detail](#3-mode-1-detail)
4. [Mode 2 Detail](#4-mode-2-detail)
5. [Mode 3 Detail](#5-mode-3-detail)
6. [Complete Data Flow Diagram](#6-complete-data-flow-diagram)
7. [Decision Guide for Contributors](#7-decision-guide-for-contributors)
8. [Invariants & Correctness](#8-invariants--correctness)
9. [Source Reference Map](#9-source-reference-map)

---

## 1. Introduction

PraTTaIL's code generation pipeline transforms a `LanguageSpec` into lexer and
parser source code.  The pipeline builds **WFST structures** (prediction,
recovery, transducer cascade) at compile time and annotates them with weights
from multiple semirings.

The pipeline has 7 logical stages:

```
1─NFA → 2─DFA → 3─WFST → 4─Dispatch → 5─Recovery → 6─Codegen → 7─Lint
```

Semiring composition happens at stages 4, 5, and 7.  Stages 1–3 use only
`TropicalWeight` (the primary semiring).  Stage 6 emits code but does not
perform semiring operations.

---

## 2. Master Pipeline Annotation Table

Each row describes one semiring usage site.  The **Mode** column refers to the
three composition modes defined in the quick reference.

| #  | Stage | Function                             | Semiring(s)                            | Mode  | Purpose                                        |
|:--:|:-----:|:-------------------------------------|:---------------------------------------|:-----:|:-----------------------------------------------|
| 1  |   3   | `PredictionWfst::build()`            | `TropicalWeight`                       |   —   | Primary WFST construction; no composition      |
| 2  |   3   | `TransducerCascade::run()`           | `TropicalWeight`                       |   —   | Optimization passes; single semiring           |
| 3  |   3   | `DeadStateElimination::apply()`      | `TropicalWeight` → `BooleanWeight`     | **1** | Forward/backward reachability check            |
| 4  |   4   | `compute_composed_dispatch()`        | `TropicalWeight` + `CountingWeight`    | **1** | Ambiguity warning: `entries.len()` as counting |
| 5  |   4   | `predict_with_confidence()`          | `TropicalWeight` + `CountingWeight`    | **1** | Derivation count annotation                    |
| 6  |   4   | `confidence_gap()`                   | `TropicalWeight` → `f64`               | **1** | Second-best − best weight                      |
| 7  |   5   | `RecoveryCost` type alias            | `ProductWeight<Tropical, Edit>`        | **2** | Joint priority + min-edit recovery             |
| 8  |   5   | `build_recovery_wfsts()` — discounts | `TropicalWeight` → `f64` → discounts   | **3** | Prediction discount injection                  |
| 9  |   5   | `build_recovery_wfsts()` — contexts  | `TropicalWeight` → `ContextWeight`     | **3** | Follow context injection                       |
| 10 |   5   | `find_best_recovery()` Viterbi       | `RecoveryCost` = `ProductWeight<T, E>` | **2** | Shortest-path over product semiring            |
| 11 |   7   | `detect_dead_rules()` Tier 3         | `TropicalWeight` → `BooleanWeight`     | **1** | WFST-unreachable rules                         |
| 12 |   7   | `detect_inter_category_dead_paths()` | `BooleanWeight`                        | **1** | Forward/backward co-reachability               |
| 13 |   7   | `detect_nearly_dead_paths()`         | `ProductWeight<Boolean, Counting>`     | **2** | Reachability + derivation count                |
| 14 |   7   | `viterbi_generic()`                  | `W: Semiring + Ord`                    | **2** | Generic lattice path extraction                |
| 15 |   7   | `linear_to_lattice_generic()`        | `W: Semiring`                          |   —   | Lattice construction with typed weights        |

### Feature-Gated Additions (`wfst-log`)

| #  | Stage | Function             | Semiring(s)      | Mode | Purpose                           |
|:--:|:-----:|:---------------------|:-----------------|:----:|:----------------------------------|
| 16 |   7   | `forward_backward()` | `LogWeight`      |  —   | Log-space probability computation |
| 17 |   7   | `compute_entropy()`  | `EntropyWeight`  |  —   | Derivation entropy                |
| 18 |   7   | `n_best_paths()`     | `NbestWeight<N>` |  —   | N-best path extraction            |

---

## 3. Mode 1 Detail

### 3.1 Tier 3 Dead-Rule Detection (BooleanWeight projection)

**Stage:** 7 (Lint) · **Source:** `pipeline.rs:216–232`

The prediction WFST stores `TropicalWeight` per transition.  Tier 3 checks
whether **any** token in a category's FIRST set dispatches to a given rule:

```rust
let reachable = first_sets
    .get(&rule_info.category)
    .map_or(false, |fs| {
        fs.tokens.iter().any(|tok| {          // ⊕  = ∨ (disjunction)
            wfst.predict(tok)
                .iter()
                .any(|a| a.action.rule_label() == rule_info.label)  // φ: w ↦  (w ≠ +∞)
        })
    });
```

The `.any()` call is the implicit `BooleanWeight::plus()` (disjunction).
The predicate `a.action.rule_label() == rule_info.label` collapses the
tropical weight to `BooleanWeight(true)` if the action exists at all.

**Homomorphism:** `φ(w) = BooleanWeight(w ≠ TropicalWeight::zero())`

### 3.2 CountingWeight in Composed Dispatch

**Stage:** 4 (Dispatch) · **Source:** `prediction.rs:1638–1641`

After collecting all dispatch entries for a (category, token) pair, the
pipeline constructs a `CountingWeight` to detect ambiguity:

```rust
let derivation_count = CountingWeight::new(entries.len() as u64);
if derivation_count.count() > 1 {
    // Emit ambiguity warning with all alternatives listed
}
```

This is a Mode 1 re-interpretation: the set of `TropicalWeight` actions
is projected onto a single `CountingWeight` via `|entries|`.  The
`CountingWeight` is not stored — it is used inline for diagnostic output.

**Homomorphism:** `φ({w₁, …, wₙ}) = CountingWeight(n)`

### 3.3 predict_with_confidence

**Stage:** 4 (Dispatch) · **Source:** `wfst.rs:362–366`

Annotates each predicted action with the total number of alternatives:

```rust
pub fn predict_with_confidence(&self, token_name: &str)
    -> Vec<(&WeightedAction, CountingWeight)>
{
    let actions = self.predict(token_name);
    let count = CountingWeight::new(actions.len() as u64);
    actions.into_iter().map(|a| (a, count)).collect()
}
```

Each action retains its original `TropicalWeight`; the `CountingWeight` is
attached alongside as a Mode 1 re-interpretation of the action set cardinality.

### 3.4 DeadStateElimination (Implicit Boolean)

**Stage:** 3 (WFST Optimization) · **Source:** `transducer.rs:107–122`

The `DeadStateElimination` optimization pass removes states not reachable
from the start state or with no path to a final state.  This is logically
a `BooleanWeight` forward-backward check:

```
forward[s]  = ∨ (paths from start to s)
backward[s] = ∨ (paths from s to any final)
alive[s]    = forward[s] ∧ backward[s]
```

The implementation uses direct reachability sets (not the `forward_backward.rs`
module), but the algebraic structure is identical to `BooleanWeight`
computation.

### 3.5 confidence_gap

**Stage:** 4 (Dispatch) · **Source:** `wfst.rs:422–428`

Extracts the weight difference between the best and second-best predictions:

```rust
pub fn confidence_gap(&self, token_name: &str) -> f64 {
    let actions = self.predict(token_name);
    match (actions.first(), actions.get(1)) {
        (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
        _ => f64::INFINITY,
    }
}
```

Strictly, this is a projection from `TropicalWeight` to `f64` (not a semiring),
but the pattern is Mode 1: existing weights are re-interpreted without new
structure allocation.

---

## 4. Mode 2 Detail

### 4.1 RecoveryCost = ProductWeight\<TropicalWeight, EditWeight\>

**Stage:** 5 (Recovery) · **Source:** `recovery.rs:53–58`

```rust
/// B2: Joint recovery cost — tropical for parse quality, edit-distance for repair minimality.
pub type RecoveryCost = ProductWeight<TropicalWeight, EditWeight>;
```

The recovery WFST assigns `RecoveryCost` to each repair action:

| Repair Action    | Tropical Cost | Edit Count | Combined    |
|:-----------------|:--------------|:-----------|:------------|
| Skip (per token) | 0.5           | 1          | `(0.5, 1)`  |
| Delete           | 1.0           | 1          | `(1.0, 1)`  |
| Swap             | 1.25          | 2          | `(1.25, 2)` |
| Substitute       | 1.5           | 2          | `(1.5, 2)`  |
| Insert           | 2.0           | 2          | `(2.0, 2)`  |

The `find_best_recovery()` function runs Viterbi over `RecoveryCost`:
- **Primary objective:** Minimize tropical cost (parse quality)
- **Secondary objective:** Among equal tropical costs, minimize edit count

**Lexicographic Ord guarantee:** Since `TropicalWeight::zero() = +∞` is the
largest `TropicalWeight` and `EditWeight::zero() = u32::MAX` is the largest
`EditWeight`, the product `(+∞, MAX)` is the largest `RecoveryCost`, satisfying
Viterbi's DP invariant.

### 4.2 ProductWeight\<BooleanWeight, CountingWeight\> for Nearly-Dead Paths

**Stage:** 7 (Lint) · **Source:** `pipeline.rs:434–574`

```rust
type BoolCount = ProductWeight<BooleanWeight, CountingWeight>;
```

A single forward-backward pass over the inter-category graph computes **both**:
- `left` (`BooleanWeight`): whether a category is reachable
- `right` (`CountingWeight`): how many derivation paths reach it

```rust
let forward = forward_scores::<BoolCount>(&edges, num_nodes);
let backward = backward_scores::<BoolCount>(&edges, num_nodes, root_idx);
```

Categories where `fwd.left.is_reachable() == true` but
`fwd.right.count() / max_count < NEARLY_DEAD_RATIO` (0.01) are flagged.

**Efficiency:** Without `ProductWeight`, detecting nearly-dead paths would
require two separate traversals — one for `BooleanWeight` (to filter truly
dead categories) and one for `CountingWeight` (to compute derivation ratios).
The product semiring computes both in a single pass.

### 4.3 Generic Lattice Path Extraction

**Stage:** 7 (Lint / Runtime) · **Source:** `lattice.rs:490–497`

```rust
pub fn viterbi_generic<T: Clone, S: Clone, W: Semiring + Ord>(
    lattice: &TokenLattice<T, S, W>,
    final_node: usize,
) -> Option<ViterbiPath<T, S, W>>
```

Any `ProductWeight` composition that satisfies `Semiring + Ord` can be used
with `viterbi_generic()`.  Current test-verified compositions:

| Composition                                    | Tested | Viterbi-OK          |
|:-----------------------------------------------|:-------|:--------------------|
| `ProductWeight<TropicalWeight, EditWeight>`    | ✓      | ✓                   |
| `ProductWeight<BooleanWeight, CountingWeight>` | ✓      | ✓                   |
| `EditWeight` (standalone)                      | ✓      | ✓                   |
| `CountingWeight` (standalone)                  | ✓      | ✗ (zero = smallest) |

---

## 5. Mode 3 Detail

### 5.1 Flow A — Prediction Discount Injection

**Stage:** 5 (Recovery) · **Source:** `recovery.rs:1342–1365`

```
┌────────────────────────────┐
│  PredictionWfst (per-cat)  │  K₁ = TropicalWeight
│  pred.predict(sync_tok)    │
│         │                  │
│         ▼                  │
│  best_weight: f64          │  ← extract raw value
└─────────┬──────────────────┘
          │
          ▼  transform: discount = max(1.0 − best_weight, 0.1)
          │
┌─────────┴──────────────────┐
│  RecoveryWfst (per-cat)    │  K₂ = RecoveryCost (Tropical × Edit)
│  prediction_discounts:     │
│    HashMap<TokenId, f64>   │  ← inject as external parameter
└────────────────────────────┘
```

**Transformation detail:**

```rust
let predictions = pred.predict(sync_name);
if let Some(best) = predictions.first() {
    let discount = (1.0 - best.weight.value().min(0.9)).max(0.1);
    discounts.insert(sync_id, discount);
}
```

- `weight = 0.0` (highest confidence) → `discount = 1.0` (no discount)
- `weight = 0.5` (moderate confidence) → `discount = 0.5`
- `weight ≥ 0.9` (low confidence) → `discount = 0.1` (floor)

The discount multiplicatively reduces recovery costs for sync tokens that
the prediction WFST considers likely.  This biases error recovery toward
sync tokens that are grammatically expected.

### 5.2 Flow B — Context Weight Injection

**Stage:** 5 (Recovery) · **Source:** `recovery.rs:1367–1425`

```
┌────────────────────────────┐
│  PredictionWfst (per-cat)  │  K₁ = TropicalWeight
│  pred.actions[idx]         │
│         │                  │
│         ▼                  │
│  action_idx: u8            │  ← extract structural info (rule index)
└─────────┬──────────────────┘
          │
          ▼  transform: ContextWeight::singleton(idx) for each action
          │  then:      ∪ (union) across all actions
          │
┌─────────┴──────────────────┐
│  RecoveryWfst (per-cat)    │  K₂ = ContextWeight (Set Semiring)
│  follow_contexts:          │
│    HashMap<TokenId,        │
│            ContextWeight>  │  ← inject as external parameter
└────────────────────────────┘
```

**Context flow detail:**

```rust
for (action_idx, _action) in pred.actions.iter().enumerate() {
    if action_idx < 128 {
        reachable = reachable.insert(action_idx as u8);
    }
}
// Structural tokens get ContextWeight::one() (universal set)
if structural_names.contains(sync_name.as_str()) {
    follow_ctxs.insert(sync_id, ContextWeight::one());
} else {
    follow_ctxs.insert(sync_id, reachable);
}
```

The `ContextWeight` bitset encodes which rules in the prediction WFST can
reach a given sync token.  At recovery time, the intersection with the
active dispatch context filters out sync tokens that are unreachable from
the current parse state.

---

## 6. Complete Data Flow Diagram

This diagram traces all semiring data through the pipeline, annotating each
edge with the composition mode used:

```
                          LanguageSpec
                              │
                              ▼
                    ┌─────────────────────┐
                    │ Stage 1–2: NFA/DFA  │
                    ├─────────────────────┤
                    │ (TropicalWeight     │
                    │  only)              │
                    └──────────┬──────────┘
                               │
                               ▼
                    ┌─────────────────────┐
                    │ Stage 3: WFST       │
                    ├─────────────────────┤
                    │                     │
                    │ PredictionWfst      │──── DeadStateElimination ───┐
                    │   [TropicalWeight]  │     Mode 1: BooleanWeight   │
                    │                     │     (transducer.rs)         │
                    │ TransducerCascade   │◄────────────────────────────┘
                    └───┬────────────┬────┘
                        │            │
           ┌────────────┘            └────────────┐
           ▼                                      ▼
┌─────────────────────┐                ┌──────────────────────┐
│ Stage 4: Dispatch   │                │ Stage 5: Recovery    │
├─────────────────────┤                ├──────────────────────┤
│ compute_composed_   │  Mode 3 ──────►│ build_recovery_      │
│   dispatch()        │  Flow A:       │   wfsts()            │
│ ┌─────────────────┐ │  discount      │                      │
│ │ CountingWeight  │ │  injection     │ ┌──────────────────┐ │
│ │ (Mode 1: len()) │ │                │ │ RecoveryCost     │ │
│ └─────────────────┘ │  Mode 3 ──────►│ │ ProductWeight    │ │
│                     │  Flow B:       │ │ <Tropical, Edit> │ │
│ predict_with_       │  context       │ │ (Mode 2)         │ │
│   confidence()      │  injection     │ └──────────────────┘ │
│ ┌─────────────────┐ │                │                      │
│ │ CountingWeight  │ │                │ prediction_          │
│ │ (Mode 1)        │ │                │   discounts: f64     │
│ └─────────────────┘ │                │ follow_contexts:     │
│                     │                │   ContextWeight      │
│ confidence_gap()    │                │                      │
│ ┌─────────────────┐ │                │ find_best_recovery() │
│ │ f64 extraction  │ │                │ Viterbi over         │
│ │ (Mode 1)        │ │                │ RecoveryCost         │
│ └─────────────────┘ │                │ (Mode 2)             │
└──────────┬──────────┘                └──────────┬───────────┘
           │                                      │
           └────────────┬─────────────────────────┘
                        ▼
             ┌─────────────────────┐
             │ Stage 6: Codegen    │
             ├─────────────────────┤
             │ (emits code; no     │
             │  semiring ops)      │
             └──────────┬──────────┘
                        │
                        ▼
             ┌─────────────────────┐
             │ Stage 7: Lint       │
             ├─────────────────────┤
             │ detect_dead_rules() │
             │ Tier 3: Mode 1      │
             │ Tropical→Boolean    │
             │                     │
             │ detect_inter_       │
             │   category_dead_    │
             │   paths()           │
             │ Mode 1: Boolean     │
             │                     │
             │ detect_nearly_      │
             │   dead_paths()      │
             │ Mode 2: Product     │
             │ <Boolean, Counting> │
             │                     │
             │ viterbi_generic()   │
             │ Mode 2: W: Semiring │
             │   + Ord             │
             └─────────────────────┘
```

---

## 7. Decision Guide for Contributors

When adding a new analysis that involves semiring weights:

### Step 1: Identify the Question

What information do you need?
- **Existence/reachability** → `BooleanWeight`
- **Optimal path cost** → `TropicalWeight`
- **Path count** → `CountingWeight`
- **Edit distance** → `EditWeight`
- **Rule participation** → `ContextWeight`
- **Parsing complexity** → `ComplexityWeight`

### Step 2: Does the Information Already Exist?

Check the master table (§2).  If the WFST already carries weights that
answer your question via a simple predicate, use **Mode 1**.

### Step 3: Do You Need Two Metrics?

If you need two metrics from the same traversal (e.g., "is it reachable
AND how many paths?"), use **Mode 2** with `ProductWeight<S₁, S₂>`.

Check Viterbi compatibility (§4.3) if you plan to use shortest-path
extraction.

### Step 4: Does One Analysis Feed Another's Construction?

If Analysis A's results are parameters for constructing Structure B, use
**Mode 3**.  Document:
1. What values are extracted from A
2. How they are transformed
3. Where they are injected into B
4. Why the transformation is conservative (no false negatives)

### Step 5: None of the Above?

You may need a new semiring type.  Add it to `automata/semiring.rs` with:
- `Semiring` trait implementation
- `Display`, `Ord`, `Hash` implementations
- Unit tests verifying the semiring axioms
- Documentation in `docs/theory/wfst/semirings/`

---

## 8. Invariants & Correctness

### Mode 1: Homomorphism Soundness

Every Mode 1 instance in PraTTaIL uses one of two homomorphisms:

**`φ₁: TropicalWeight → BooleanWeight`**
```
φ₁(w) = BooleanWeight(w ≠ +∞)
```
Verification:
- `φ₁(+∞) = false = 0_Bool` ✓ (zero maps to zero)
- `φ₁(0.0) = true = 1_Bool` ✓ (one maps to one)
- `φ₁(min(a,b)) = (min(a,b) ≠ +∞) = (a ≠ +∞) ∨ (b ≠ +∞) = φ₁(a) ∨ φ₁(b)` ✓
- `φ₁(a+b) = (a+b ≠ +∞) = (a ≠ +∞) ∧ (b ≠ +∞) = φ₁(a) ∧ φ₁(b)` ✓

**`φ₂: Set{TropicalWeight} → CountingWeight`**
```
φ₂({w₁, …, wₙ}) = CountingWeight(n)
```
This is a set-cardinality projection, not a weight homomorphism.  It is sound
because `CountingWeight` is used only for diagnostic purposes (ambiguity
warnings), not for path computation.

### Mode 2: Viterbi Compatibility

For `viterbi_generic<W>()` correctness, `W` must satisfy:
1. `W::zero()` is the Ord-largest element (DP initialization)
2. `W::times()` is monotone under Ord (relaxation soundness)
3. No negative-weight cycles (termination)

| ProductWeight Composition         | (1) zero = largest | (2) times monotone  | (3) no neg cycles |
|:----------------------------------|:------------------:|:-------------------:|:-----------------:|
| `<TropicalWeight, EditWeight>`    |   ✓ `(+∞, MAX)`    | ✓ addition monotone |  ✓ all costs ≥ 0  |
| `<BooleanWeight, CountingWeight>` |   ✓ `(false, 0)`   |          ✓          |         ✓         |

### Mode 3: Conservative Injection

Both Mode 3 flows maintain conservativity:

**Flow A (discounts):**
- `discount ∈ (0.0, 1.0]` — multiplying a recovery cost by discount can only
  decrease or maintain it, never increase.  Recovery with discounting finds
  paths that are ≤ the cost found without discounting.
- Tokens with no prediction data get `discount = 1.0` (no change).

**Flow B (context filtering):**
- Structural tokens receive `ContextWeight::one()` (universal set) — they
  are never filtered out, ensuring Eof/RParen/RBrace are always valid sync points.
- Non-structural tokens receive the union of all action indices — a
  conservative overapproximation.  No valid sync token is accidentally excluded.

---

## 9. Source Reference Map

| #  | Mode | Instance                               | Source File            | Line Range    |
|:--:|:----:|:---------------------------------------|:-----------------------|:--------------|
| 1  |  1   | Tier 3 dead-rule (Boolean projection)  | `pipeline.rs`          | 216–232       |
| 2  |  1   | CountingWeight in dispatch             | `prediction.rs`        | 1638–1641     |
| 3  |  1   | predict_with_confidence                | `wfst.rs`              | 362–366       |
| 4  |  1   | confidence_gap                         | `wfst.rs`              | 422–428       |
| 5  |  1   | DeadStateElimination                   | `transducer.rs`        | 107–122       |
| 6  |  1   | Inter-category dead paths (Boolean)    | `pipeline.rs`          | 329–427       |
| 7  |  2   | RecoveryCost type alias                | `recovery.rs`          | 53–58         |
| 8  |  2   | RecoveryCost in repair costs           | `recovery.rs`          | 71–100        |
| 9  |  2   | find_best_recovery Viterbi             | `recovery.rs`          | 1100–1291     |
| 10 |  2   | Nearly-dead detection (Bool × Count)   | `pipeline.rs`          | 434–574       |
| 11 |  2   | viterbi_generic                        | `lattice.rs`           | 490–497       |
| 12 |  2   | linear_to_lattice_generic              | `lattice.rs`           | 568–576       |
| 13 |  3   | Prediction discount injection (Flow A) | `recovery.rs`          | 1342–1365     |
| 14 |  3   | Context weight injection (Flow B)      | `recovery.rs`          | 1367–1425     |
| 15 |  —   | PredictionWfst construction            | `wfst.rs`              | 1–50          |
| 16 |  —   | TransducerCascade                      | `transducer.rs`        | 263–431       |
| 17 |  —   | Semiring trait + 10 types              | `automata/semiring.rs` | 28–51 (trait) |
