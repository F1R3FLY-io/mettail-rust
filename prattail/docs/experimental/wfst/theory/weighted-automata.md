# Weighted Finite-State Transducers

## 1. Motivation

A classical finite-state automaton (FSA) answers a yes/no membership
question: "is this string in the language?" A weighted finite-state
transducer (WFST) generalises that to a quantitative question: "with what
weight does each parse alternative match the current lookahead?"

In PraTTaIL, the prediction WFST answers exactly this question for every
category. Given the next token, it returns a *ranked* list of dispatch
actions — ordered by tropical weight so the most-likely parse path is
tried first. For unambiguous tokens this ranking is trivial (one action
at weight 0.0); for ambiguous tokens it encodes a learned or heuristic
preference ordering that reduces expected backtracking cost.

---

## 2. Formal Definition

A WFST over semiring **S = (K, ⊕, ⊗, 0̄, 1̄)** is a 7-tuple:

```
M = (Σ, Q, I, F, δ, λ, ρ)
```

where:

| Symbol | Type | Description |
|:------:|:----:|:------------|
| Σ      | set  | Input alphabet — the set of token variants |
| Q      | set  | Finite set of states |
| I      | I ⊆ Q | Initial (start) states |
| F      | F ⊆ Q | Final (accepting) states |
| δ      | Q × Σ → Q | Transition function |
| λ      | I → K | Initial weight function |
| ρ      | F → K | Final weight function |

Each arc in δ carries a label σ ∈ Σ and a weight w ∈ K.

### 2.1 Path Weight

A **path** π = (q₀, σ₁, w₁, q₁), (q₁, σ₂, w₂, q₂), …, (qₙ₋₁, σₙ, wₙ, qₙ)
from initial state q₀ ∈ I to final state qₙ ∈ F has path weight:

```
w(π) = λ(q₀) ⊗ w₁ ⊗ w₂ ⊗ … ⊗ wₙ ⊗ ρ(qₙ)
```

The initial and final weights λ, ρ bracket the arc weights.

### 2.2 String Weight

The **string weight** of an input string x is the ⊕-combination of the
weights of all accepting paths labelled x:

```
‖M‖(x) = ⊕ { w(π) : π is an accepting path labelled x }
```

Under TropicalWeight, this selects the minimum-weight (best) accepting
path. Under LogWeight, it sums over all accepting paths.

---

## 3. Epsilon Transitions

An **epsilon transition** carries no input label: the automaton may
change state without consuming a token. Epsilon is represented as a
special sentinel label:

```rust
pub const EPSILON_TOKEN: TokenId = TokenId::MAX;  // = 65535
```

Epsilon transitions are used in PraTTaIL's recovery WFSTs to model
unconditional fallback states — states the automaton enters without
requiring a specific token to be present.

In the prediction WFST (non-recovery path), epsilon transitions are
not used; every arc corresponds to a concrete token.

---

## 4. TokenId and TokenIdMap

### 4.1 TokenId

Rather than comparing token variant names as strings on hot paths,
each distinct token variant is assigned a compact numeric identifier:

```rust
pub type TokenId = u16;
```

`u16` supports up to 65,535 distinct token variants. Typical PraTTaIL
grammars have 20–100 token variants, so the range is never a practical
constraint. `EPSILON_TOKEN = u16::MAX = 65535` is reserved.

### 4.2 TokenIdMap

`TokenIdMap` provides a bidirectional mapping between token variant names
and their `TokenId`s:

```rust
pub struct TokenIdMap {
    name_to_id: BTreeMap<String, TokenId>,
    id_to_name: Vec<String>,
}
```

Key properties:

- **Deterministic assignment**: `from_names()` sorts and deduplicates
  the input before assigning IDs. The same set of token names always
  produces the same ID assignments regardless of iteration order.
- **O(log n) lookup** by name (BTreeMap), **O(1) lookup** by ID (Vec index).
- **Shared across categories**: one `TokenIdMap` is built from the union
  of all FIRST sets after pipeline construction, then cloned into each
  per-category `PredictionWfst`. This ensures that the same token name
  always maps to the same ID everywhere.

Construction:

```rust
let token_map = TokenIdMap::from_names(
    all_first_set_tokens.into_iter()
);
```

---

## 5. PraTTaIL WFST Architecture

### 5.1 The PredictionWfst

```rust
pub struct PredictionWfst {
    pub category:    String,
    pub states:      Vec<WfstState>,
    pub start:       WfstStateId,
    pub actions:     Vec<WeightedAction>,
    pub token_map:   TokenIdMap,
    pub beam_width:  Option<TropicalWeight>,
}
```

Each `WfstState` holds:

```rust
pub struct WfstState {
    pub id:            WfstStateId,
    pub is_final:      bool,
    pub final_weight:  TropicalWeight,
    pub transitions:   Vec<WeightedTransition>,
}
```

Each `WeightedTransition` is one arc in the WFST:

```rust
pub struct WeightedTransition {
    pub from:       WfstStateId,
    pub input:      TokenId,    // EPSILON_TOKEN for ε-arcs
    pub action_idx: u32,        // index into PredictionWfst::actions
    pub to:         WfstStateId,
    pub weight:     TropicalWeight,
}
```

### 5.2 Two-State Architecture

The prediction WFST uses a minimal two-level structure: one shared start
state (state 0) and one dedicated final state per registered action.
This is sufficient because prediction is a single-token decision —
the parser peeks at exactly one token and then selects an action.

```
State 0 (start)
  ├─── token A, w=0.0 ──► State 1 (final, action 0)
  ├─── token B, w=0.0 ──► State 2 (final, action 1)
  ├─── token B, w=0.5 ──► State 3 (final, action 2)   ← ambiguous
  └─── token C, w=2.0 ──► State 4 (final, action 3)
```

For ambiguous tokens (multiple arcs with the same label from state 0),
the actions are sorted by weight during `predict()` so the lowest-weight
(most-preferred) alternative is tried first.

Future extension to k-token lookahead would chain k states before the
final state, encoding multi-token decision paths.

### 5.3 Sentinel Values

```rust
pub type WfstStateId = u32;
pub const NO_STATE: WfstStateId = WfstStateId::MAX;  // = 4,294,967,295
```

`NO_STATE` is used as a sentinel in data structures that may reference
an absent or not-yet-computed state.

---

## 6. Diagram: 5-State PredictionWfst for Category `Expr`

Consider a grammar category `Expr` with four dispatch actions.
Two actions share the token `Ident` (ambiguous), so the WFST has
two arcs from state 0 labelled with the same token ID:

```
  Tokens:  Plus(id=0), Ident(id=1), LParen(id=2)
  Actions: 0=Add(Direct), 1=Var(Variable), 2=CastToName(CrossCategory+backtrack), 3=Group(Grouping)

                     id=0, w=0.0
  ┌──────────────────────────────────────────────────────► State 1 [final, w=1̄]
  │                                                         (action 0: Add)
  │             id=1, w=2.0
  │         ┌────────────────────────────────────────────► State 2 [final, w=1̄]
  │         │                                               (action 1: Var)
  │         │     id=1, w=0.5
  │         │  ┌─────────────────────────────────────────► State 3 [final, w=1̄]
  │         │  │                                            (action 2: CastToName)
  │         │  │    id=2, w=0.0
  │         │  │  ┌──────────────────────────────────────► State 4 [final, w=1̄]
  │         │  │  │                                         (action 3: Group)
  │         │  │  │
  ▼         ┊  ┊  ▼
State 0 ────┼──┼─────
 (start)    ┊  ┊
            └──┘
         (crossing
          of id=1
            arcs)
```

The two `id=1` arcs (Ident) cross conceptually; the dotted marks (┊) show
the crossing point. `predict("Ident")` traverses both arcs and returns:

```
[{ action: CastToName, weight: 0.5 },
 { action: Var,        weight: 2.0 }]
```

The lower-weight CastToName is tried first; Var is the fallback.

---

## 7. Tracing predict() Through the WFST

### 7.1 The predict() Method

```rust
pub fn predict(&self, token_name: &str) -> Vec<&WeightedAction> {
    let token_id = match self.token_map.get(token_name) {
        Some(id) => id,
        None     => return Vec::new(),
    };

    let start_state = &self.states[self.start as usize];
    let mut results: Vec<&WeightedAction> = start_state
        .transitions
        .iter()
        .filter(|t| t.input == token_id)
        .filter_map(|t| self.actions.get(t.action_idx as usize))
        .collect();

    results.sort_by(|a, b| a.weight.cmp(&b.weight));
    results
}
```

Step-by-step for `predict("Ident")` on the 5-state diagram above:

1. **Token resolution**: `token_map.get("Ident")` → `id=1`.
2. **Arc scan**: iterate transitions of state 0, keep those where
   `input == 1` — finds arcs to states 2 (w=2.0) and 3 (w=0.5).
3. **Action lookup**: dereference `action_idx` into `self.actions`.
4. **Sort**: results ordered by weight ascending → [w=0.5, w=2.0].
5. **Return**: `[CastToName, Var]`.

### 7.2 Beam-Pruned Prediction

When a beam width is configured, `predict_pruned()` additionally filters
out actions whose weight exceeds `best_weight + beam_width`:

```rust
pub fn predict_pruned(&self, token_name: &str) -> Vec<&WeightedAction> {
    let actions = self.predict(token_name);
    match (self.beam_width, actions.first()) {
        (Some(beam), Some(best)) => {
            let threshold = best.weight.value() + beam.value();
            actions.into_iter()
                   .filter(|a| a.weight.value() <= threshold)
                   .collect()
        }
        _ => actions,
    }
}
```

With `beam_width = 1.0` on the example above:

```
best = 0.5
threshold = 0.5 + 1.0 = 1.5
→ keeps w=0.5 (CastToName)
→ prunes w=2.0 (Var, exceeds 1.5)
```

The best action is always preserved regardless of beam width (since
`best.weight ≤ threshold` by construction).

---

## 8. WFST Construction Pipeline

`build_prediction_wfsts()` in `wfst.rs` assembles the per-category WFSTs
after FIRST/FOLLOW set computation in the pipeline:

```
1. Collect all token names from all FIRST sets.
2. Build a shared TokenIdMap (sorted, deduped → deterministic IDs).
3. For each category:
   a. Create a PredictionWfstBuilder with the shared TokenIdMap.
   b. For each (token, action) in category's dispatch table:
      i.  Compute TropicalWeight via compute_action_weight().
      ii. Register the action with builder.add_action().
   c. builder.build() → PredictionWfst.
4. Return BTreeMap<String, PredictionWfst>.
```

The `build()` method materialises the two-state structure:

```rust
pub fn build(self) -> PredictionWfst {
    let mut start_state = WfstState::new(0);
    let mut states = Vec::with_capacity(1 + self.transitions.len());
    states.push(WfstState::new(0)); // placeholder

    for (token_id, action_idx, weight) in &self.transitions {
        let final_id = states.len() as WfstStateId;
        states.push(WfstState::final_state(final_id, TropicalWeight::one()));
        start_state.transitions.push(WeightedTransition {
            from: 0, input: *token_id, action_idx: *action_idx,
            to: final_id, weight: *weight,
        });
    }
    states[0] = start_state;
    PredictionWfst { /* ... */ }
}
```

One final state per action, all reachable from state 0. Total states = 1 + |actions|.

---

## 9. Runtime Prediction

### 9.1 Static Embedding

The pipeline serializes each `PredictionWfst` into generated code as
CSR (Compressed Sparse Row) static arrays. At runtime, the WFST is
reconstructed via `PredictionWfst::from_flat()` and consulted per-token
during parsing.

The runtime prediction path for a given lookahead token:

```
1. Resolve token name → TokenId via the embedded TokenIdMap
2. Scan state 0's transitions for matching input label
3. Collect all matching WeightedAction entries
4. Sort by ascending weight
5. Return to parser for try-in-order dispatch
```

This is equivalent to a single-step traversal of the two-state WFST:
one transition from the start state to a final state per matching action.
The total cost is O(k) where k is the number of actions matching the
token — typically 1-3 for well-designed grammars.

### 9.2 Trained Weight Override

`PredictionWfst::with_trained_weights()` replaces heuristic weights
with learned weights from a `TrainedModel`. The WFST structure is
unchanged; only the transition weights are updated. This means the
prediction ranking reflects corpus statistics rather than static grammar
topology.

---

## 10. Test Coverage

**`wfst.rs` (16 tests):**

| Test | What it verifies |
|:-----|:----------------|
| `test_prediction_wfst_builder_basic` | State count = 1 + actions |
| `test_prediction_wfst_predict_deterministic` | Single-action token returns one result |
| `test_prediction_wfst_predict_ambiguous_ordered_by_weight` | Lower-weight returned first |
| `test_compute_action_weight` | Weight values for all DispatchAction variants |
| `test_generate_weighted_dispatch_empty` | Empty WFST returns None |
| `test_generate_weighted_dispatch_produces_comments` | Code comment includes "ambiguous" |
| `test_beam_pruning_none_is_identity` | No beam → same as predict() |
| `test_beam_pruning_filters_high_weight` | Threshold correctly applied |
| `test_beam_pruning_preserves_best` | Best action always returned |
| `test_beam_width_from_builder` | Builder sets beam_width |
| `test_beam_width_from_language_spec` | DSL `beam_width: 1.5` → TropicalWeight(1.5) |

**`token_id.rs` (4 tests):**

| Test | What it verifies |
|:-----|:----------------|
| `test_token_id_map_basic` | get_or_insert is idempotent |
| `test_token_id_map_lookup` | Bidirectional name↔id lookup |
| `test_token_id_map_from_names` | Deduplication and sort order |
| `test_token_id_map_iter` | Iteration in ID order |

---

## 11. Source Reference

| Symbol | Location |
|:-------|:---------|
| `WfstStateId`, `NO_STATE` | `prattail/src/wfst.rs` lines 36–39 |
| `WeightedTransition` | `prattail/src/wfst.rs` lines 44–56 |
| `WfstState` | `prattail/src/wfst.rs` lines 59–91 |
| `WeightedAction` | `prattail/src/wfst.rs` lines 93–100 |
| `PredictionWfst` | `prattail/src/wfst.rs` lines 117–195 |
| `PredictionWfstBuilder` | `prattail/src/wfst.rs` lines 202–279 |
| `build_prediction_wfsts` | `prattail/src/wfst.rs` lines 294–337 |
| `compute_action_weight` | `prattail/src/wfst.rs` lines 349–372 |
| `TokenId`, `EPSILON_TOKEN` | `prattail/src/token_id.rs` lines 13–16 |
| `TokenIdMap` | `prattail/src/token_id.rs` lines 22–91 |

---

**See also:**
- [`semirings.md`](semirings.md) — semiring axioms and the TropicalWeight / LogWeight types
- [`viterbi-and-forward-backward.md`](viterbi-and-forward-backward.md) — algorithms that operate over WFST-weighted DAGs
