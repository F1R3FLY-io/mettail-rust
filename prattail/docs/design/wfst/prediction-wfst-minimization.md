# PredictionWfst Minimization (B3)

> **Date:** 2026-03-01

After the prediction WFSTs are built by `build_prediction_wfsts()`, each
category's WFST may contain numerous final states that are observationally
identical.  B3 minimization merges these redundant states, reducing the
static WFST data size without affecting prediction correctness.  This
document describes the problem, the signature-based merging algorithm,
its integration into the pipeline, and its relationship to full Hopcroft
minimization.

---

## Table of Contents

1. [Problem: Redundant Final States](#1-problem-redundant-final-states)
2. [StateSignature](#2-statesignature)
3. [The minimize() Algorithm](#3-the-minimize-algorithm)
4. [Pipeline Integration](#4-pipeline-integration)
5. [Worked Example](#5-worked-example)
6. [Impact Analysis](#6-impact-analysis)
7. [Relationship to Hopcroft Minimization](#7-relationship-to-hopcroft-minimization)
8. [Test Coverage](#8-test-coverage)
9. [Source References](#9-source-references)

---

## 1. Problem: Redundant Final States

The prediction WFST uses a two-state architecture: a single start state
(state 0) fans out to one final state per registered dispatch action.
Each transition from state 0 carries the token label, action index, and
tropical weight.  The final states themselves carry only acceptance
metadata:

- `is_final = true`
- `final_weight = TropicalWeight::one()` (i.e., 0.0)
- No outgoing transitions (terminal sinks)

Since all differentiating information (token, weight, action index) lives
on the *transitions*, not on the final states, every final state in the
two-state architecture has identical observable behavior.  A WFST with 10
tokens produces 10 final states that are all equivalent.

The `union()` method exacerbates this.  When two WFSTs are merged (e.g.,
during cross-category composition), each incoming transition creates a
*new* final state:

```rust
// From union() — line 404-407 of wfst.rs:
let final_id = self.states.len() as WfstStateId;
self.states
    .push(WfstState::final_state(final_id, TropicalWeight::one()));
```

After a union of two WFSTs with 5 tokens each, the combined WFST has
up to 10 final states.  All 10 share the signature `(true, 0.0_bits, [])`.

This redundancy has three costs:

1. **Memory** -- each `WfstState` carries a `Vec<WeightedTransition>`
   (empty for finals, but the allocation header still takes 24 bytes on
   64-bit platforms) plus the `id`, `is_final`, and `final_weight` fields.

2. **Serialization volume** -- `emit_prediction_wfst_static()` emits one
   `(usize, usize, bool, f64)` tuple per state in the CSR state-offsets
   array.  Redundant states inflate the generated code.

3. **Traversal overhead** -- any algorithm that iterates over states (e.g.,
   `predict_with_confidence()`, future lattice construction) pays O(n)
   where n includes redundant states.

---

## 2. StateSignature

The `StateSignature` struct captures the observable behavior of a WFST
state.  Two states with identical signatures are equivalent: they accept
the same inputs, produce the same outputs, and transition to the same
targets with the same weights.

```rust
// wfst.rs ~line 112
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct StateSignature {
    is_final: bool,
    final_weight_bits: u64,
    /// Sorted transitions: (token_id, action_idx, target_state_id, weight_bits)
    transitions: Vec<(TokenId, u32, WfstStateId, u64)>,
}
```

### Design decisions

**Bit-exact weight comparison.**  The `final_weight_bits` field stores
`f64::to_bits()`, not the raw `f64`.  This avoids floating-point
comparison pitfalls: `NaN != NaN` under IEEE 754, but
`f64::NAN.to_bits() == f64::NAN.to_bits()`.  For tropical weights, NaN
should never appear, but the bit representation provides a safe and exact
equality check that satisfies the `Eq` and `Hash` trait requirements
(which `f64` does not).

**Sorted transitions.**  The `from_state()` constructor sorts the
transition tuples before storing them:

```rust
// wfst.rs ~line 120-134
impl StateSignature {
    fn from_state(state: &WfstState) -> Self {
        let mut transitions: Vec<(TokenId, u32, WfstStateId, u64)> = state
            .transitions
            .iter()
            .map(|t| (t.input, t.action_idx, t.to, t.weight.value().to_bits()))
            .collect();
        transitions.sort();

        StateSignature {
            is_final: state.is_final,
            final_weight_bits: state.final_weight.value().to_bits(),
            transitions,
        }
    }
}
```

Sorting ensures that two states with the same transitions in different
insertion order produce the same signature.  The 4-tuple
`(token_id, action_idx, target_state_id, weight_bits)` has a natural
lexicographic `Ord` since all four components are unsigned integers.

**Private type.**  `StateSignature` is `pub(crate)`-private -- it is an
implementation detail of `minimize()` and not exposed in the public API.

---

## 3. The minimize() Algorithm

`PredictionWfst::minimize()` is a signature-based state-merging pass.  It
runs in five phases:

```
Phase 1: Build signatures    ─── O(S × T)
Phase 2: Map to representatives ─── O(S)
Phase 3: Update transitions  ─── O(T)
Phase 4: Collect referenced  ─── O(S + T)
Phase 5: Compact IDs         ─── O(S + T)
```

where S = number of states and T = total number of transitions.

### Phase 1 & 2: Signature construction and representative mapping

```rust
// wfst.rs ~line 437-460
pub fn minimize(&mut self) -> usize {
    if self.states.len() <= 1 {
        return 0;
    }

    // Build a signature for each state: (is_final, final_weight_bits, sorted transitions)
    // States with identical signatures are equivalent.
    let mut sig_to_representative: HashMap<StateSignature, WfstStateId> = HashMap::new();
    let mut state_mapping: Vec<WfstStateId> = Vec::with_capacity(self.states.len());

    for state in &self.states {
        let sig = StateSignature::from_state(state);
        let representative = *sig_to_representative
            .entry(sig)
            .or_insert(state.id);
        state_mapping.push(representative);
    }

    let original_count = self.states.len();
    let unique_count = sig_to_representative.len();

    if unique_count == original_count {
        return 0; // No merging possible
    }
```

The first state encountered with a given signature becomes the
*representative* for all states sharing that signature.  The
`state_mapping` vector maps each original state index to its
representative's ID.  If the number of unique signatures equals the
original state count, no merging is possible and the algorithm returns
early.

### Phase 3: Redirect transitions

```rust
    // Update all transitions to point to representative states
    for state in &mut self.states {
        for trans in &mut state.transitions {
            if let Some(&mapped) = state_mapping.get(trans.to as usize) {
                trans.to = mapped;
            }
        }
    }
```

Every transition's `to` field is updated to point to the representative
state.  After this phase, non-representative states are unreferenced --
no transition targets them.

### Phase 4: Collect referenced states

```rust
    // Collect which state IDs are still referenced (as representatives)
    let mut referenced: HashSet<WfstStateId> = HashSet::new();
    referenced.insert(self.start);
    for state in &self.states {
        for trans in &state.transitions {
            referenced.insert(trans.to);
        }
    }
```

The referenced set contains the start state plus every state that is the
target of at least one transition.  Non-representative and orphaned
states are not in this set.

### Phase 5: Remove unreferenced states and compact IDs

```rust
    // Remove unreferenced states and build an ID remapping
    let mut new_states: Vec<WfstState> = Vec::with_capacity(unique_count);
    let mut id_remap: HashMap<WfstStateId, WfstStateId> = HashMap::new();

    // Ensure start state gets ID 0
    if let Some(start_state) = self.states.iter().find(|s| s.id == self.start) {
        let new_id = new_states.len() as WfstStateId;
        id_remap.insert(start_state.id, new_id);
        let mut cloned = start_state.clone();
        cloned.id = new_id;
        new_states.push(cloned);
    }

    for state in &self.states {
        if state.id == self.start {
            continue; // Already added
        }
        if !referenced.contains(&state.id) {
            continue; // Orphaned — skip
        }
        // Only keep representative states (skip duplicates)
        if state_mapping.get(state.id as usize).copied() != Some(state.id) {
            continue;
        }
        let new_id = new_states.len() as WfstStateId;
        id_remap.insert(state.id, new_id);
        let mut cloned = state.clone();
        cloned.id = new_id;
        new_states.push(cloned);
    }

    // Apply the ID remapping to all transitions
    for state in &mut new_states {
        for trans in &mut state.transitions {
            if let Some(&new_from) = id_remap.get(&trans.from) {
                trans.from = new_from;
            }
            if let Some(&new_to) = id_remap.get(&trans.to) {
                trans.to = new_to;
            }
        }
    }

    self.start = *id_remap.get(&self.start).unwrap_or(&0);
    self.states = new_states;

    original_count - self.states.len()
}
```

The start state is always assigned ID 0.  All other referenced,
representative states receive contiguous IDs starting from 1.  The final
`id_remap` pass updates both `from` and `to` fields in all transitions
to reflect the compacted ID space.  The method returns the number of
states removed.

### Algorithm flow diagram

```
  ┌─────────────────────────────────────────────────────────────────────┐
  │ minimize()                                                          │
  │                                                                     │
  │  states.len() ≤ 1 ──yes──→ return 0                                │
  │       │no                                                           │
  │       ▼                                                             │
  │  ┌──────────────────────────┐                                       │
  │  │ for each state:          │                                       │
  │  │   sig = from_state(s)    │                                       │
  │  │   sig_to_repr[sig] ??= s │                                       │
  │  │   state_mapping[s] = repr│                                       │
  │  └────────────┬─────────────┘                                       │
  │               │                                                     │
  │  unique == original ──yes──→ return 0                               │
  │       │no                                                           │
  │       ▼                                                             │
  │  ┌──────────────────────────┐                                       │
  │  │ for each transition:     │                                       │
  │  │   t.to = mapping[t.to]   │   (redirect to representatives)       │
  │  └────────────┬─────────────┘                                       │
  │               ▼                                                     │
  │  ┌──────────────────────────┐                                       │
  │  │ referenced = {start}     │                                       │
  │  │   ∪ { t.to | t ∈ trans } │   (reachability from start)           │
  │  └────────────┬─────────────┘                                       │
  │               ▼                                                     │
  │  ┌──────────────────────────┐                                       │
  │  │ new_states:              │                                       │
  │  │   start → ID 0           │                                       │
  │  │   other repr states →    │                                       │
  │  │     contiguous IDs 1..N  │                                       │
  │  │ remap all transitions    │                                       │
  │  └────────────┬─────────────┘                                       │
  │               ▼                                                     │
  │  return original_count - new_states.len()                           │
  └─────────────────────────────────────────────────────────────────────┘
```

---

## 4. Pipeline Integration

B3 minimization is invoked in `pipeline.rs` immediately after
`build_prediction_wfsts()` and before beam width configuration:

```rust
// pipeline.rs ~line 845-857
// B3: Minimize prediction WFSTs — merge equivalent states
{
    let mut total_removed = 0usize;
    for wfst in prediction_wfsts.values_mut() {
        total_removed += wfst.minimize();
    }
    if total_removed > 0 {
        eprintln!(
            "  \x1b[36minfo\x1b[0m: B3 WFST minimization removed {} redundant state(s)",
            total_removed
        );
    }
}

// Apply beam width configuration
if let Some(beam_value) = bundle.beam_width.to_option() {
    let beam = crate::automata::semiring::TropicalWeight::new(beam_value);
    for wfst in prediction_wfsts.values_mut() {
        wfst.set_beam_width(Some(beam));
    }
}
```

### Placement rationale

The minimization must run *after* `build_prediction_wfsts()` because the
WFSTs must be fully constructed before equivalence analysis can proceed.
It must run *before* beam width configuration because:

1. `set_beam_width()` does not modify state structure -- it only sets a
   metadata field on the `PredictionWfst`.  Minimization does not inspect
   beam width, so the ordering is a logical separation of concerns.

2. Downstream consumers (CSR serialization, lint analysis, dead-rule
   detection) benefit from the minimized state set.  Fewer states means
   smaller CSR arrays and faster iteration.

### Pipeline sequence (excerpt)

```
  build_dispatch_action_tables()
       │
       ▼
  build_prediction_wfsts()         ← construct per-category WFSTs
       │
       ▼
  B3: minimize()                   ← merge equivalent states (this step)
       │
       ▼
  set_beam_width()                 ← apply beam pruning threshold
       │
       ▼
  run_lints()                      ← W01 dead-rule detection, etc.
       │
       ▼
  emit_prediction_wfst_static()    ← CSR serialization into generated code
```

### Diagnostic output

When minimization removes states, a cyan `info` diagnostic is printed to
stderr.  Example output for the Calculator grammar:

```
  info: B3 WFST minimization removed 28 redundant state(s)
```

This diagnostic is suppressed when no states are removed (common for
trivial grammars with a single category and no ambiguity).

---

## 5. Worked Example

Consider a grammar category `Expr` with 10 token-to-action mappings,
each producing a `Direct` dispatch action at weight 0.0:

```
  Tokens: T0, T1, T2, T3, T4, T5, T6, T7, T8, T9
  Actions: R_T0, R_T1, ..., R_T9   (all Direct, weight 0.0)
```

### Before minimize()

```
  ┌─────────────────────────────────────────────────────┐
  │  PredictionWfst for Expr  (11 states)               │
  │                                                     │
  │              T0/0.0/0   ┌───┐                       │
  │           ┌────────────→│ 1 │ (final, w=0.0)        │
  │           │  T1/0.0/1   └───┘                       │
  │           ├────────────→┌───┐                       │
  │           │             │ 2 │ (final, w=0.0)        │
  │           │  T2/0.0/2   └───┘                       │
  │  ┌───┐   ├────────────→┌───┐                       │
  │  │ 0 │───┤             │ 3 │ (final, w=0.0)        │
  │  │   │   │  ...         └───┘                       │
  │  │   │   │                                          │
  │  │   │   │  T9/0.0/9   ┌────┐                      │
  │  └───┘   └────────────→│ 10 │ (final, w=0.0)       │
  │  start                  └────┘                      │
  └─────────────────────────────────────────────────────┘
```

State count: 11 (1 start + 10 finals).

### Signature analysis

| State | is_final | final_weight_bits | transitions | Signature hash |
|-------|----------|-------------------|-------------|----------------|
| 0     | false    | `(+inf).to_bits()`| 10 entries  | H0 (unique)    |
| 1     | true     | `0.0.to_bits()`   | []          | **H1**         |
| 2     | true     | `0.0.to_bits()`   | []          | **H1**         |
| 3     | true     | `0.0.to_bits()`   | []          | **H1**         |
| ...   | ...      | ...               | ...         | **H1**         |
| 10    | true     | `0.0.to_bits()`   | []          | **H1**         |

All 10 final states (1-10) share signature **H1** =
`StateSignature { is_final: true, final_weight_bits: 0, transitions: [] }`.

Phase 1 result: `sig_to_representative` maps H0 to state 0, H1 to
state 1 (first encountered).

Phase 2 result: `state_mapping = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]`.

Phase 3: All transitions from state 0 are redirected to state 1:

```
  T0/0.0/0 → state 1
  T1/0.0/1 → state 1
  T2/0.0/2 → state 1
  ...
  T9/0.0/9 → state 1
```

Phase 4: `referenced = {0, 1}`.  States 2-10 are unreferenced.

Phase 5: New state vector has 2 entries.  State 0 (start) gets ID 0,
state 1 (merged final) gets ID 1.

### After minimize()

```
  ┌───────────────────────────────────────────┐
  │  PredictionWfst for Expr  (2 states)      │
  │                                           │
  │              T0/0.0/0                      │
  │           ┌──────────┐                    │
  │           │ T1/0.0/1 │                    │
  │           │ T2/0.0/2 │   ┌───┐            │
  │  ┌───┐   │ ...       ├──→│ 1 │ (final)    │
  │  │ 0 │───┤ T9/0.0/9 │   └───┘            │
  │  └───┘   └──────────┘                    │
  │  start                                    │
  └───────────────────────────────────────────┘
```

State count: 2 (1 start + 1 merged final).  Removed: 9 states.

All 10 transitions now point to the same final state.  The action index
on each transition is preserved, so `predict("T3")` still returns action
index 3, resolving to `R_T3` in the action table.  The weight 0.0 is
carried on the transition, not the final state, so prediction semantics
are unchanged.

---

## 6. Impact Analysis

### Two-state architecture: maximal merging

In the standard two-state architecture produced by
`build_prediction_wfsts()`, every final state has the signature
`(true, 0.0_bits, [])`.  This means *all* final states merge into a
single representative, reducing the WFST from `1 + N` states to exactly
2 states (start + 1 merged final), where N is the number of dispatch
actions.

| Scenario | States before | States after | Reduction |
|----------|--------------|-------------|-----------|
| 3 tokens, no ambiguity | 4 | 2 | 50% |
| 10 tokens, all Direct | 11 | 2 | 82% |
| 20 tokens, mixed weights | 21 | 2 | 90% |
| 50 tokens (large grammar) | 51 | 2 | 96% |

### After union(): duplicate elimination

The `union()` method creates a new final state per imported transition.
If two WFSTs with 5 tokens each are unioned, the result has 11 states
(1 start + 5 original finals + 5 imported finals).  After minimization,
this collapses to 2 states -- the same as a single WFST.

### Static WFST data size reduction

The CSR serialization emits one entry per state in `WFST_STATE_OFFSETS`:

```rust
static WFST_STATE_OFFSETS_Expr: &[(usize, usize, bool, f64)] = &[
    // (offset, num_transitions, is_final, final_weight)
    (0, 10, false, f64::INFINITY),  // state 0: start
    (10, 0, true,  0.0),            // state 1: merged final
    // Without B3: 10 more entries here (states 2-10)
];
```

For a grammar with 5 categories averaging 15 tokens each:

| Metric | Without B3 | With B3 | Savings |
|--------|-----------|---------|---------|
| State entries | 5 x 16 = 80 | 5 x 2 = 10 | 87% |
| State data (bytes) | 80 x 32 = 2,560 | 10 x 32 = 320 | 87% |

The transition arrays are unaffected (same number of transitions
regardless of how many final states exist), so the overall WFST static
data reduction is typically 10-30% depending on the ratio of state
metadata to transition data.

### Zero impact on prediction correctness

The algorithm preserves correctness through two invariants:

1. **Action indices are preserved.**  The `action_idx` field on each
   transition is never modified by `minimize()`.  The action table
   (`Vec<WeightedAction>`) is not touched.  Thus, `predict("T3")`
   returns the same action before and after minimization.

2. **Transition weights are preserved.**  The `weight` field on each
   transition is never modified.  The signature-based merging only
   affects the `to` field (redirecting to the representative).  Since
   final states carry `TropicalWeight::one()` (0.0), the total path
   cost is:

   ```
   path_cost = transition_weight + final_weight
             = transition_weight + 0.0
             = transition_weight
   ```

   This is unchanged by the merge.

---

## 7. Relationship to Hopcroft Minimization

The `automata/minimize.rs` module provides a full Hopcroft minimization
algorithm for DFAs:

```rust
// automata/minimize.rs ~line 95
pub fn minimize_dfa(dfa: &Dfa) -> Dfa {
    // Hopcroft's algorithm with inverse transition map
    // O(n log n) where n = number of states
    ...
}
```

### Why not use Hopcroft for PredictionWfst?

| Property | Hopcroft | Signature-based (B3) |
|----------|----------|---------------------|
| Time complexity | O(n log n) | O(n) amortized |
| Handles multi-level WFSTs | Yes | Yes (general signatures) |
| Implementation complexity | High (partition refinement, inverse maps) | Low (HashMap insert) |
| Weighted transitions | Requires extension | Native (weight bits in signature) |
| Optimality guarantee | Minimal DFA | Minimal under signature equivalence |

For the two-state star topology that `PredictionWfst` uses, Hopcroft's
partition refinement loop is unnecessary overhead.  The initial partition
{non-final, final} immediately stabilizes because no final state has
outgoing transitions -- there is nothing to refine.  The signature-based
approach captures this in a single pass.

### When would Hopcroft be needed?

If `PredictionWfst` were extended to support multi-level paths (e.g.,
for lookahead disambiguation requiring 2+ tokens), the WFST would no
longer be a star graph.  Final states might have different outgoing
transition structures, and intermediate states could have non-trivial
equivalence classes.  In that scenario, the signature-based approach
still works (signatures capture arbitrary transition structure), but
Hopcroft would guarantee O(n log n) instead of the O(n x T) worst case
for signature construction with large transition sets.

For the current two-state architecture, signature-based merging is both
simpler and faster.

### Formal equivalence

Both algorithms compute the same result for the two-state case:

**Claim**: For a star-topology WFST where all final states have
identical `(is_final, final_weight)` and no outgoing transitions,
Hopcroft minimization and signature-based merging produce isomorphic
minimal WFSTs.

**Proof sketch**: Hopcroft starts with partition `P = {F, Q\F}` where
`F` is the set of final states.  Since no state in `F` has outgoing
transitions, no transition from any state in `Q\F` (i.e., the start
state) distinguishes between elements of `F`.  The refinement loop
terminates immediately with `P = {{start}, F}`, merging all final
states into one representative -- identical to the signature-based
result.

---

## 8. Test Coverage

Eight tests in `wfst.rs` (under the `// -- B3: minimize() tests` section)
validate the minimization algorithm:

| # | Test | Scenario | Key assertions |
|---|------|----------|----------------|
| 1 | `test_minimize_empty_wfst` | No states to merge (empty builder) | `removed == 0` |
| 2 | `test_minimize_single_state` | WFST with only start state | `removed == 0`, `num_states() == 1` |
| 3 | `test_minimize_merges_all_simple_finals` | 3 tokens, 3 identical finals | `removed == 2`, `num_states() == 2`, prediction preserved |
| 4 | `test_minimize_merges_identical_finals_after_union` | 2 tokens, union-created duplicates | `removed == 1`, `num_states() == 2`, both tokens predict correctly |
| 5 | `test_minimize_after_union_with_overlapping_tokens` | Union with overlapping `Ident` token | `removed == 1`, `num_states() == 2`, both alternatives preserved (w=0.5, w=2.0) |
| 6 | `test_minimize_preserves_beam_width` | Beam width 1.5 set before minimize | `beam_width() == Some(TropicalWeight::new(1.5))` after minimize |
| 7 | `test_minimize_large_union_many_duplicates` | 10 tokens, all weight 0.0 | `removed == 9`, `num_states() == 2`, all 10 tokens predict correctly |
| 8 | `test_minimize_mixed_weights_partial_merge` | 4 tokens (2 at w=0.0, 2 at w=1.0) | `removed == 3`, `num_states() == 2` (weights are on transitions, finals are still identical) |

### Test design principles

- **Boundary cases** (tests 1-2): Empty and single-state WFSTs must be
  handled gracefully (early return, no crash).

- **Core merging** (tests 3-4): The fundamental two-state architecture
  and post-union scenarios.

- **Correctness preservation** (tests 3-5, 7-8): Every test verifies
  that `predict()` returns the same actions and weights after
  minimization.

- **Metadata preservation** (test 6): Beam width is orthogonal to state
  structure and must survive minimization unchanged.

- **Scale** (test 7): 10 tokens demonstrate the N-to-1 final state
  merging pattern at a non-trivial scale.

- **Weight independence** (test 8): Confirms that transition weights
  (which vary) do not affect final-state merging (which depends only
  on final-state properties).

---

## 9. Source References

| Symbol | File | Line |
|--------|------|------|
| `StateSignature` struct | `prattail/src/wfst.rs` | ~112 |
| `StateSignature::from_state()` | `prattail/src/wfst.rs` | ~120 |
| `PredictionWfst::minimize()` | `prattail/src/wfst.rs` | ~437 |
| `PredictionWfst::union()` | `prattail/src/wfst.rs` | ~375 |
| `PredictionWfst::num_states()` | `prattail/src/wfst.rs` | ~271 |
| `WfstState::final_state()` | `prattail/src/wfst.rs` | ~83 |
| B3 pipeline integration block | `prattail/src/pipeline.rs` | ~844 |
| `build_prediction_wfsts()` | `prattail/src/wfst.rs` | ~653 |
| `minimize_dfa()` (Hopcroft) | `prattail/src/automata/minimize.rs` | ~95 |
| B3 minimize tests (8 tests) | `prattail/src/wfst.rs` | ~1483 |

### Cross-references

- [Prediction WFSTs](prediction.md) -- Two-state architecture, weight
  assignment, beam pruning, and CSR serialization.
- [Pipeline Integration](../../architecture/wfst/pipeline-integration.md)
  -- Data flow showing B3 in the pipeline sequence.
- [Dead-Rule Detection](dead-rule-detection.md) -- W01 lint that
  consumes the minimized WFSTs downstream.
