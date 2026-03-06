# BooleanWeight -- Design & Pipeline Integration

The boolean semiring `({false, true}, or, and, false, true)` tests reachability.
In PraTTaIL's pipeline, it serves one purpose: identifying dead rules at codegen
time. Rules that no token can reach via the prediction WFST are unreachable and
receive a compile-time warning.

---

## 1. Role in Pipeline

BooleanWeight underpins dead-rule detection via a four-tier analysis in
`detect_dead_rules()` (`pipeline.rs:106–207`).  Each grammar rule is
classified by exactly one tier: literal rules (tier 1), same-category
infix/var rules (tier 2), and prefix/cast/cross-category rules (tier 3).
Tier 3 performs the implicit BooleanWeight projection — checking whether
any token in the category's FIRST set dispatches to the rule through the
prediction WFST.

| Stage                        | File          | Lines   | Description                                              |
|------------------------------|---------------|---------|----------------------------------------------------------|
| Four-tier dead-rule analysis | `pipeline.rs` | 106–207 | `detect_dead_rules()` returns `Vec<DeadRuleWarning>`     |
| W01 lint wrapper             | `lint.rs`     | 786–832 | `lint_w01_dead_rule()` maps warnings to `LintDiagnostic` |
| Type definition              | `semiring.rs` | 283–363 | BooleanWeight struct, Semiring impl                      |

Dead-rule detection runs unconditionally during the Generate phase (no feature
gate).  It executes after prediction WFST construction, surfaced through the
unified lint layer (`lint.rs`, lint ID W01) with structured `LintDiagnostic`
entries and variant-specific hints.

---

## 2. Design Decision: Implicit Boolean

The current implementation does **not** explicitly project the prediction WFST
onto BooleanWeight. Instead, it performs reachability queries directly against
the TropicalWeight WFST (Tier 3 in `pipeline.rs:183–203`):

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

Dead-rule detection uses a four-tier algorithm in `detect_dead_rules()`
(`pipeline.rs:106–207`):

```
for each rule R in rule_infos:

    // Tier 1: Literal rules — structural check
    if R.is_literal:
        has_native = categories.any(c → c.name == R.category && c.native_type.is_some())
        if not has_native: warn LiteralNoNativeType
        continue

    // Tier 2: Same-category infix/var — category reachability
    if (R.is_infix && !R.is_cross_category) || R.is_var:
        if R.category ∉ reachable_categories: warn UnreachableCategory
        continue

    // Tier 3: Prefix/cast/cross-category — WFST dispatch query
    wfst = prediction_wfsts[R.category]
    reachable = ∨_{T ∈ FIRST(R.category)} [wfst.predict(T) routes to R]
    if not reachable: warn WfstUnreachable

where:
    reachable_categories = μX. {C | FIRST(C) ≠ ∅}
                             ∪ {C | ∃ cast/cross-cat rule r: r.source ∈ X ∧ r.target = C}
```

Warnings are surfaced via the unified lint layer: `lint_w01_dead_rule()` in
`lint.rs:786–832` wraps each `DeadRuleWarning` variant into a
`LintDiagnostic` with structured formatting (Rust compiler style:
`warning[W01]: ...`) and variant-specific hint messages.

---

## 4. Coverage by Tier

The four-tier system covers **all** rule types — no rule is excluded from
detection.  Each tier handles a specific subset:

| Tier  | Rule Types Covered                                                                 | Detection Method                          |
|-------|------------------------------------------------------------------------------------|-------------------------------------------|
| **1** | Literal rules (`is_literal`)                                                       | Structural: category has `native_type`?   |
| **2** | Same-cat infix (`is_infix && !is_cross_category`), postfix, mixfix, var (`is_var`) | Graph: category in reachable fixed-point? |
| **3** | Prefix, cast (`is_cast`), cross-category (`is_cross_category`)                     | WFST: any FIRST token dispatches to rule? |

This replaces the previous single-pass implementation that skipped 5 rule
types (infix, var, literal, cross-category, cast).  The four-tier design
eliminates those exclusions: literal rules are handled structurally (tier 1),
infix/var rules are handled via category reachability (tier 2), and cast and
cross-category rules are handled via WFST dispatch queries (tier 3).

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

This would replace the Tier 3 loop in `pipeline.rs:183–203` with a single
projection call, making the code more compositional.

---

## 6. Semiring Properties

BooleanWeight is **idempotent**: `plus(true, true) = true`. This means
repeated merging of the same reachability evidence does not change the result --
a desirable property for fixed-point reachability analysis.

It is the simplest semiring in PraTTaIL's hierarchy:

```
            ┌─────────┐                ┌───────┐
Boolean  ◀──┤ project ├──  Tropical  ──┤ embed ├──▶  Log
   ▲        └─────────┘       ▲        └───────┘
   │                          │
   │                          └── EditWeight (isomorphic over N)
   │
   └── "is there any path?"
```

---

## 7. Source Reference & See Also

- **Type definition**: `semiring.rs:283–363`
- **`detect_dead_rules()` (four-tier)**: `pipeline.rs:106–207`
- **`DeadRuleWarning` enum**: `pipeline.rs:48–96`
- **`lint_w01_dead_rule()`**: `lint.rs:786–832`
- **`run_lints()` entry point**: `lint.rs:136–176`
- **Dead-rule detection design**: [../dead-rule-detection.md](../dead-rule-detection.md)
- **Theory**: `prattail/docs/theory/wfst/semirings.md` — section 7
- **Pipeline integration**: `prattail/docs/architecture/wfst/pipeline-integration.md` — §4
- **Tropical weight**: `tropical-weight.md` — the weight from which boolean
  reachability is projected
