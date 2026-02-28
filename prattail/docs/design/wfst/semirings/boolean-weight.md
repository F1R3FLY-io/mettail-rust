# BooleanWeight -- Design & Pipeline Integration

The boolean semiring `({false, true}, or, and, false, true)` tests reachability.
In PraTTaIL's pipeline, it serves one purpose: identifying dead rules at codegen
time. Rules that no token can reach via the prediction WFST are unreachable and
receive a compile-time warning.

---

## 1. Role in Pipeline

BooleanWeight underpins dead-rule detection in `pipeline.rs:552-589`. For each
grammar rule, the pipeline checks whether any token in the category's FIRST set
has a prediction WFST transition that routes to that rule. If no token reaches
the rule, it is dead code.

| Stage | File | Lines | Description |
|-------|------|-------|-------------|
| Dead-rule scan | `pipeline.rs` | 552-589 | Iterate rules, query WFST, emit warnings |
| Type definition | `semiring.rs` | 283-363 | BooleanWeight struct, Semiring impl |

Dead-rule detection runs unconditionally during the Generate phase (no feature
gate). It executes after prediction WFST construction and before dispatch
codegen, ensuring warnings appear before code emission.

---

## 2. Design Decision: Implicit Boolean

The current implementation does **not** explicitly project the prediction WFST
onto BooleanWeight. Instead, it performs reachability queries directly against
the TropicalWeight WFST (`pipeline.rs:574-580`):

```rust
let reachable = first_sets
    .get(&rule_info.category)
    .map_or(false, |fs| {
        fs.tokens.iter().any(|tok| {
            wfst.predict(tok).iter().any(|a| a.action.rule_label() == rule_info.label)
        })
    });
```

This is an **implicit boolean projection**: the predicate
`any(action.rule_label() == rule.label)` is equivalent to projecting each WFST
transition's weight onto BooleanWeight via `w -> BooleanWeight(w != zero)` and
then computing `plus` (disjunction) across all transitions.

**Rationale**:

- The explicit projection would allocate a separate BooleanWeight WFST per
  category, duplicating the transition structure just to replace f64 weights
  with bool. For the simple "is any path non-zero?" query, the implicit
  version is both simpler and allocation-free.
- The BooleanWeight type in `semiring.rs` serves as the **formal model**. Its
  existence enables future extensions (see section 5) and ensures the design
  is documented in terms of standard semiring theory rather than ad-hoc
  boolean checks.

---

## 3. Current Implementation

The dead-rule detection walk-through in `pipeline.rs:552-589`:

```
for each rule_info in bundle.rule_infos:
  |
  // Step 1: Skip rules handled outside prefix dispatch
  if rule_info.is_infix
     || rule_info.is_var
     || rule_info.is_literal
     || rule_info.is_cross_category
     || rule_info.is_cast:
    continue  // see section 4 for rationale
  |
  // Step 2: Get prediction WFST for this rule's category
  wfst = prediction_wfsts[rule_info.category]
  |
  // Step 3: Check reachability (implicit boolean projection)
  reachable = false
  for each token in FIRST(rule_info.category):
    for each action in wfst.predict(token):
      if action.rule_label() == rule_info.label:
        reachable = true
        break
  |
  // Step 4: Emit warning if unreachable
  if !reachable:
    eprintln!(
      "warning: rule {} in category {} is unreachable (dead code) --
       no token in FIRST({}) dispatches to it via prediction WFST",
      rule_info.label, rule_info.category, rule_info.category
    )
```

The warning is emitted via `eprintln!` rather than a structured diagnostic
because PraTTaIL runs inside a proc-macro context. Future work could use
`proc_macro::Diagnostic` once stabilized.

---

## 4. Exclusion Filters

The following rule types are excluded from dead-rule detection
(`pipeline.rs:562-564`):

| Rule Type | Field | Reason |
|-----------|-------|--------|
| **Infix** | `is_infix` | Handled by the Pratt infix loop, not prefix dispatch. The WFST only covers prefix dispatch. |
| **Variable** | `is_var` | Built-in prefix handler for `Token::Ident`; not routed through the prediction WFST. |
| **Literal** | `is_literal` | Built-in prefix handler for `Token::Integer`, `Token::Float`, etc.; same as var. |
| **Cross-category** | `is_cross_category` | Handled by dispatch wrappers (`dispatch.rs`); the WFST may not have explicit actions for these. |
| **Cast** | `is_cast` | Handled by Pratt prefix cast handlers; dispatch is via unique-to-source FIRST set tokens, not WFST actions. |

These rule types have non-standard dispatch paths that bypass the prediction
WFST. Checking them against the WFST would produce false-positive "dead rule"
warnings for every infix operator and every literal/variable rule.

---

## 5. Future: Explicit Boolean Projection

An explicit projection would enable two additional optimizations:

### 5a. Unreachable State Elimination

Project the full DFA onto BooleanWeight, then remove states where all outgoing
transitions have weight `false`. This simplifies the DFA before minimization,
potentially reducing the transition table size.

### 5b. Grammar Simplification

After boolean projection, compute the reachable and co-reachable state sets.
Rules that appear only on unreachable or non-co-reachable paths can be
automatically removed from the grammar, eliminating dead code without warnings.

### 5c. Implementation Sketch

```rust
fn project_boolean(wfst: &PredictionWfst) -> BTreeMap<String, BooleanWeight> {
    let mut reachability = BTreeMap::new();
    for token in wfst.token_map.all_names() {
        let actions = wfst.predict(&token);
        let reachable = BooleanWeight::new(!actions.is_empty());
        for action in actions {
            let label = action.action.rule_label();
            let current = reachability
                .entry(label.to_string())
                .or_insert(BooleanWeight::zero());
            *current = current.plus(&reachable);
        }
    }
    reachability
}
```

This would replace the inline loop in `pipeline.rs:556-589` with a single
projection call, making the code more compositional.

---

## 6. Semiring Properties

BooleanWeight is **idempotent**: `plus(true, true) = true`. This means
repeated merging of the same reachability evidence does not change the result --
a desirable property for fixed-point reachability analysis.

It is the simplest semiring in PraTTaIL's hierarchy:

```
Boolean  <--project--  Tropical  --embed-->  Log
  |                       |
  |                       +-- EditWeight (isomorphic over N)
  |
  +-- "is there any path?"
```

---

## 7. Source Reference & See Also

- **Type definition**: `semiring.rs:283-363`
- **Dead-rule detection**: `pipeline.rs:552-589`
- **Theory**: `prattail/docs/theory/wfst/semirings.md` -- section 7
- **Pipeline integration**: `prattail/docs/benchmarks/wfst-pipeline-integration.md`
- **Tropical weight**: `tropical-weight.md` -- the weight from which boolean
  reachability is projected
