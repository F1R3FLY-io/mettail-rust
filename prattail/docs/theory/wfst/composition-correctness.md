# Composition Correctness Theorems

This document formalizes four correctness properties that must hold after
composing two prediction WFSTs via the `compose_with_wfst()` operation.
The properties are verified at runtime by `composition_verify.rs`.

## Notation

- **𝒲_A**, **𝒲_B**: Source prediction WFSTs for grammars A and B
- **𝒲_M = 𝒲_A ⊕ 𝒲_B**: Merged prediction WFST (result of composition)
- **𝓛(𝒲)**: The language of WFST 𝒲, defined as the set of (token, action) pairs
  reachable from the start state via a single transition
- **predict(𝒲, t)**: The set of weighted actions returned by 𝒲 when queried with token t
- **w(𝒲, t, a)**: The weight of action a for token t in 𝒲

## Shared Categories

Two WFSTs share a category when both 𝒲_A and 𝒲_B have the same `category` field.
For shared categories, the merge operation performs a WFST union on the start state's
transitions. For non-shared categories, the WFSTs are passed through unchanged.

---

## Theorem 1: Union Completeness (Language Containment)

**Statement:**

∀ (t, a) ∈ 𝓛(𝒲_A) ∪ 𝓛(𝒲_B) : (t, a) ∈ 𝓛(𝒲_M)

Every token-action pair reachable in either source WFST is also reachable in the
merged WFST.

**Proof:**

Let (t, a) ∈ 𝓛(𝒲_A). Then there exists a transition from 𝒲_A's start state on
token t to an action index pointing to action a. The `compose_with_wfst()` operation
constructs 𝒲_M as follows:

1. If category(𝒲_A) is not shared with any category in B, then 𝒲_A is included in
   𝒲_M unchanged. The transition is preserved identically.

2. If category(𝒲_A) is shared, the merge creates a new start state and imports ALL
   transitions from both 𝒲_A's and 𝒲_B's start states. The transition for (t, a)
   from 𝒲_A is imported into 𝒲_M's start state verbatim, with the same action index
   mapping.

In both cases, predict(𝒲_M, t) includes a. By symmetry, the same holds for
(t, a) ∈ 𝓛(𝒲_B).

Therefore 𝓛(𝒲_A) ∪ 𝓛(𝒲_B) ⊆ 𝓛(𝒲_M). ∎

---

## Theorem 2: Union Soundness (No Spurious Actions)

**Statement:**

∀ (t, a) ∈ 𝓛(𝒲_M) : (t, a) ∈ 𝓛(𝒲_A) ∪ 𝓛(𝒲_B)

No phantom token-action pairs are introduced by the merge.

**Proof:**

The `compose_with_wfst()` operation constructs 𝒲_M by:

1. For non-shared categories: 𝒲_A (or 𝒲_B) is passed through unchanged.
   No new transitions or actions are constructed. Therefore all (t, a) pairs
   exist in the source.

2. For shared categories: The merge operation:
   - Creates a new `Vec<WeightedAction>` from `actions_a` followed by re-indexed
     `actions_b`
   - Creates transitions by importing from both start states (adjusting action_idx
     for B's actions by `offset = |actions_a|`)
   - No new `DispatchAction` values are constructed — every action in the merged
     vector is an exact clone of an action from A or B

Since no new DispatchAction values are synthesized, every action in 𝒲_M was in
exactly one source WFST.

Therefore 𝓛(𝒲_M) ⊆ 𝓛(𝒲_A) ∪ 𝓛(𝒲_B). ∎

---

## Theorem 3: Weight Preservation

**Statement:**

For all (t, a) ∈ 𝓛(𝒲_M):

- If (t, a) ∈ 𝓛(𝒲_A) \ 𝓛(𝒲_B): w(𝒲_M, t, a) = w(𝒲_A, t, a)
- If (t, a) ∈ 𝓛(𝒲_B) \ 𝓛(𝒲_A): w(𝒲_M, t, a) = w(𝒲_B, t, a)
- If (t, a) ∈ 𝓛(𝒲_A) ∩ 𝓛(𝒲_B) (shared action):
  w(𝒲_M, t, a) = resolve(w(𝒲_A, t, a), w(𝒲_B, t, a))

where `resolve` is the configured weight resolution policy (default: min).

**Proof:**

**Case 1 (single-source):** When (t, a) is from a single source, the weight is
cloned directly from the source's `WeightedAction.weight`. No weight transformation
occurs during `compose_with_wfst()`.

**Case 2 (shared action):** When both sources define the same action label for token
t, the merge preserves both transitions. The `WeightReconciliation` optimization pass
(Phase 7) then applies the configured weight resolution policy. Under the default
`Min` policy, the lower weight is kept, matching the tropical semiring's ⊕ operation
(min over ℝ ∪ {∞}).

Before the optimization pass runs, the merged WFST contains both weights, and
`predict()` returns both sorted by weight (lowest first). The optimization pass
reconciles to a single weight per action. ∎

---

## Theorem 4: Dispatch Determinism Preservation

**Statement:**

If |predict(𝒲_A, t)| = 1 and |predict(𝒲_B, t)| = 1 and the action labels are
disjoint, then |predict(𝒲_M, t)| = 2.

More generally: for any token t,
|predict(𝒲_M, t)| ≤ |predict(𝒲_A, t)| + |predict(𝒲_B, t)|.

**Proof:**

The merge operation imports all transitions from both start states. For token t:

- 𝒲_A contributes |predict(𝒲_A, t)| transitions
- 𝒲_B contributes |predict(𝒲_B, t)| transitions

Since both label sets are disjoint (guaranteed by `DuplicateRuleLabel` validation
in `compose.rs` step 2), no deduplication occurs and all transitions are preserved.

Therefore |predict(𝒲_M, t)| = |predict(𝒲_A, t)| + |predict(𝒲_B, t)|.

For the specific case where both sources have exactly one action with disjoint labels,
|predict(𝒲_M, t)| = 1 + 1 = 2 (exactly one action from each grammar).

**Note:** When labels are NOT disjoint (same rule label with different weights),
the merge preserves both transitions. The `ComposedDispatchMinimization` pass
can deduplicate these, keeping the best weight. ∎

---

## Runtime Verification

The `composition_verify::verify_composition()` function checks all four properties
at runtime using the public `predict()` API. Violations produce structured
`PropertyViolation` records. The verification runs after WFST union in
`compose_with_wfst()`:

- **P1 (Containment)** violations are logged as warnings and indicate that the
  merge lost actions from a source WFST
- **P2 (Soundness)** violations trigger a `debug_assert!` failure in debug builds,
  as phantom actions indicate a bug in the merge implementation
- **P3 (Weight)** violations are logged as warnings (indicate cross-grammar weight
  conflicts in shared categories)
- **P4 (Determinism)** violations are expected when grammars share token sets
  (informational warning, not a hard failure)

---

## Relationship to Existing Composition Theory

These theorems correspond to standard WFST algebra results:

| Theorem | WFST Analog |
|---------|-------------|
| T1 (Completeness) | Union: 𝓛(A ∪ B) ⊇ 𝓛(A) ∪ 𝓛(B) |
| T2 (Soundness) | Union: 𝓛(A ∪ B) ⊆ 𝓛(A) ∪ 𝓛(B) |
| T3 (Weight) | Tropical semiring: w(a ⊕ b) = min(w(a), w(b)) |
| T4 (Determinism) | Determinization: |δ(q, σ)| ≤ 1 per source |

Together, T1 + T2 establish that `𝓛(A ⊕ B) = 𝓛(A) ∪ 𝓛(B)` — the composition
preserves the language exactly. T3 ensures weight semantics are maintained.
T4 bounds the growth of non-determinism.
