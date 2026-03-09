# Extended Weighted Pushdown Systems (EWPDS)

| Property       | Value                                    |
|----------------|------------------------------------------|
| Feature gate   | `wpds-extended`                          |
| Source file    | `prattail/src/ewpds.rs` (~416 lines)    |
| Pipeline phase | Post-WPDS analysis                       |
| Lint codes     | S04 (merge-site mismatch)                |

## Rationale

Standard Weighted Pushdown Systems model interprocedural analysis where each call/return boundary uses uniform semiring multiplication to combine caller and callee weights. This fails when the caller has local state invisible to the callee -- a situation that arises naturally in name-binding calculi. Extended WPDS (EWPDS) resolves this by attaching per-push-rule *merging functions* `g: D x D -> D` that combine the caller's local state with the callee's global effect at return sites. In PraTTaIL, rho calculus has `PNew` (scoped names) and `PInput` (binding inputs). When one process calls another via communication, the caller's local bindings are invisible to the callee -- exactly the scenario EWPDS merging functions model.

## Theoretical Foundations

**Definition (EWPDS, Reps et al. 2007).** An Extended WPDS extends a standard WPDS with merge functions:
- Standard WPDS rule: `<p, gamma> hookrightarrow <p', gamma' gamma''>` with weight `w`
- EWPDS rule: `<p, gamma> hookrightarrow <p', gamma' gamma''>` with weight `w` and merge function `g`

At a return site, the combined weight is `g(w_caller, w_callee)` instead of `w_caller otimes w_callee`.

**Definition (Merge Function).** A merge function `g: D x D -> D` must satisfy:
- `g(0, d) = g(d, 0) = 0` (zero annihilation)
- `g(d_1 oplus d_2, d_3) = g(d_1, d_3) oplus g(d_2, d_3)` (left-distributive over plus)
- When `g(d_1, d_2) = d_1 otimes d_2`, EWPDS reduces to standard WPDS.

**Definition (Default Merge).** The default merge function is standard semiring multiplication: `g(w_1, w_2) = w_1 otimes w_2`. This recovers standard WPDS behavior.

**Definition (Override Merge).** The override merge function allows the callee's effect to replace specific components of the caller's state: `g(R_1, R_2) = R_1[a mapsto R_2(a)]`. For relational domains, this models local variable scoping.

**Theorem (EWPDS Poststar Correctness, Lal & Reps 2006).** The EWPDS poststar saturation procedure terminates and computes the correct forward reachability set, with merge functions applied at all call/return boundaries.

### References

1. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*, Definitions 12-13.
2. Lal, A. & Reps, T. (2006). "Improving pushdown system model checking." *CAV*.
3. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.

## Algorithm Pseudocode

### 1. EWPDS Construction from Standard WPDS

```
FUNCTION from_wpds(wpds):
    extended_push_rules := []
    push_rules_by_source := empty map

    FOR EACH rule in wpds.rules:
        IF rule is Push(from_gamma, to_gamma_bottom, to_gamma_top, weight):
            idx := |extended_push_rules|
            push_rules_by_source[from_gamma].add(idx)
            extended_push_rules.add(EwpdsPushRule(
                from_gamma, to_gamma_bottom, to_gamma_top,
                weight, merge_fn = DefaultMerge
            ))

    RETURN Ewpds(base = wpds, extended_push_rules, push_rules_by_source)
```

### 2. EWPDS Poststar with Merge Functions

```
FUNCTION ewpds_poststar(ewpds):
    // Start with standard poststar for pop and replace rules
    result := poststar(ewpds.base)

    // Apply merge functions for extended push rules
    FOR EACH rule in ewpds.extended_push_rules:
        caller_weight := result.symbol_weight(rule.from_gamma)
        callee_weight := result.symbol_weight(rule.to_gamma_top)

        IF NOT caller_weight.is_zero() AND NOT callee_weight.is_zero():
            merged := rule.merge_fn.merge(caller_weight, callee_weight)
            // Update return-site transition weight
            FOR EACH transition t in result where t.symbol == rule.to_gamma_bottom:
                t.weight := merged

    RETURN result
```

### 3. Merge-Site Detection (Pipeline Bridge)

```
FUNCTION extend_from_bundle(wpds_analysis, all_syntax):
    merge_site_labels := []

    FOR EACH (category, rule_label, items) in all_syntax:
        IF any item in items is Binder:
            merge_site_labels.add("{category}.{rule_label}")

    IF merge_site_labels is empty:
        RETURN None

    RETURN EwpdsAnalysis(|merge_site_labels|, merge_site_labels)
```

## Complexity Analysis

| Operation              | Time               | Space              |
|------------------------|--------------------|--------------------|
| `from_wpds`            | O(R)               | O(P)               |
| `ewpds_poststar`       | O(|post*| + P . T) | O(|A|)             |
| `set_merge_fn`         | O(P_s)             | O(1)               |
| `extend_from_bundle`   | O(S . I)           | O(M)               |

Where R = WPDS rules, P = push rules, T = transitions in result, |post*| = standard poststar cost, |A| = automaton size, P_s = push rules from source, S = syntax rules, I = items per rule, M = merge sites.

## Architecture Diagram

```
  ┌──────────────────────────────────────────────────────────────┐
  │                     EWPDS Architecture                        │
  │                                                              │
  │  Standard WPDS                                               │
  │  ┌──────────────────────────────────────────┐                │
  │  │  Pop rules:     ⟨p, γ⟩ ↪ ⟨p', ε⟩       │                │
  │  │  Replace rules: ⟨p, γ⟩ ↪ ⟨p', γ'⟩      │                │
  │  │  Push rules:    ⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩  │ ← standard    │
  │  └──────────────────────────────────────────┘                │
  │       │                                                      │
  │       ▼                                                      │
  │  EWPDS Extension                                             │
  │  ┌──────────────────────────────────────────┐                │
  │  │  Push rule + merge fn g:                 │                │
  │  │  ⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩ with g(w₁, w₂)  │ ← extended    │
  │  └──────────────────────────────────────────┘                │
  │       │                                                      │
  │       ▼                                                      │
  │  ewpds_poststar()                                            │
  │       │                                                      │
  │       ├── poststar(base) for pop/replace rules               │
  │       ├── merge_fn.merge(w_caller, w_callee)                 │
  │       │   for each extended push rule                        │
  │       │                                                      │
  │       ▼                                                      │
  │  PAutomaton (forward reachability with local state)          │
  └──────────────────────────────────────────────────────────────┘
```

## Merge Function Selection

```
  Rule with no local state          Rule with local bindings
  (standard category call)          (PNew, PInput with Binder)
  ┌─────────────────────┐          ┌─────────────────────────┐
  │  g(w₁, w₂) = w₁⊗w₂ │          │  g(w₁, w₂) = custom    │
  │  (DefaultMerge)      │          │  (OverrideMerge or      │
  │                      │          │   domain-specific)      │
  └─────────────────────┘          └─────────────────────────┘
           │                                  │
           └──────────────┬───────────────────┘
                          ▼
                 EWPDS Push Rule
                 (from_gamma, to_gamma_bottom,
                  to_gamma_top, weight, merge_fn)
```

## PraTTaIL Integration

### Pipeline Bridge Functions

- **`extend_from_bundle(wpds_analysis, all_syntax)`** -- Scans `all_syntax` for rules containing `SyntaxItemSpec::Binder` items. Each binder marks a call/return boundary where an EWPDS merge function can combine caller and callee weights. Returns `None` when no binder sites are found (standard WPDS suffices).

### Lint Emission

- **S04 (merge-site mismatch)**: Emitted when a binder rule lacks a corresponding merge function, suggesting that local state may be incorrectly combined at the call/return boundary.

## Rust Implementation Notes

| Type                 | Role                                                    |
|----------------------|---------------------------------------------------------|
| `MergeFunction<W>`   | Trait: `merge(&self, caller: &W, callee: &W) -> W`     |
| `DefaultMerge`       | Standard semiring multiplication (recovers WPDS)        |
| `OverrideMerge<W>`   | Callee overrides caller's local state components        |
| `EwpdsPushRule<W>`   | Push rule with from/to symbols, weight, merge_fn        |
| `Ewpds<W>`           | Full EWPDS: base WPDS + extended push rules + index     |
| `EwpdsAnalysis`      | Pipeline result: merge_site_count, merge_site_labels    |

## Worked Example

Consider a rho calculus grammar with `PNew` (name creation):

```
PNew . Proc ::= "new" Binder(x:Name) "in" Proc(body) ;
PSend. Proc ::= Name(chan) "!" "(" Name(msg) ")" ;
```

**Step 1: Identify merge sites.**

`extend_from_bundle` scans the syntax and finds `PNew` has a `Binder` item. Merge site: `Proc.PNew`.

```
EwpdsAnalysis {
  merge_site_count: 1,
  merge_site_labels: ["Proc.PNew"]
}
```

**Step 2: Build EWPDS.**

The standard WPDS push rule for `PNew` calling into the body:
```
⟨p, Proc⟩ ↪ ⟨p', PNew@1, Proc⟩  with weight w
```

After `from_wpds`, this becomes an EWPDS push rule with `DefaultMerge`.

**Step 3: Set custom merge function.**

For `PNew`, the caller's scope includes the newly bound name `x`, which is invisible to the callee. The merge function should preserve the caller's binding:

```rust
ewpds.set_merge_fn(
    &StackSymbol::category_entry("Proc"),
    &StackSymbol::category_entry("Proc"),
    Box::new(OverrideMerge::new()),
);
```

**Step 4: Run EWPDS poststar.**

The poststar computes forward reachability with the custom merge at `PNew`'s return site, correctly combining the caller's local `x` binding with the callee's global effect.

## References

1. Reps, T., Lal, A. & Kidd, N. (2007). "Program analysis using weighted pushdown systems." *FSTTCS*.
2. Lal, A. & Reps, T. (2006). "Improving pushdown system model checking." *CAV*.
3. Schwoon, S. (2002). *Model-Checking Pushdown Systems.* PhD thesis, TU Munich.
4. Reps, T., Schwoon, S., Jha, S. & Melski, D. (2005). "Weighted pushdown systems and their application to interprocedural dataflow analysis." *SCP*, 58(1-2).
5. Bouajjani, A., Esparza, J. & Maler, O. (1997). "Reachability analysis of pushdown automata." *CONCUR*.
