# COMP-08: wpds-refactoring-suggestion

**Severity:** Note
**Category:** WPDS

## Description

Emits grammar restructuring suggestions based on WPDS call graph analysis (G33/G34/G35/G36). Three heuristics identify categories that may benefit from restructuring:

1. **Hub splitting** -- A category with high fan-in AND fan-out (`fan_in > 5 && fan_out > 5`) is a hub that can cause cascading ambiguity. Splitting it into smaller, more focused categories may improve dispatch determinism.

2. **Inlining** -- A category with exactly 1 caller, at most 3 rules, and no outgoing calls (`fan_in = 1 && rule_count <= 3 && fan_out = 0`) is a candidate for inlining into its sole caller. This eliminates cross-category `Push`/`Pop` overhead.

3. **Cycle-breaking** -- A mutual recursion cycle with more than 2 members (`|SCC| > 2`) increases WPDS saturation time and can obscure dead-rule detection. Introducing an intermediate category can break the cycle.

## Trigger Conditions

COMP-08 fires (one diagnostic per match) when WPDS analysis is available and any of the three heuristics match:

- **Hub:** `fan_in[cat] > 5 && fan_out[cat] > 5`
- **Inline:** `fan_in[cat] == 1 && rule_count(cat) <= 3 && fan_out[cat] == 0`
- **Cycle-break:** `cycle.categories.len() > 2`

## Example

### Hub Splitting

```
note[COMP-08]: category `Expr` is a hub (fan-in=7, fan-out=8); consider splitting
               into smaller categories
  = hint: hub categories can cause cascading ambiguity; splitting may improve
          dispatch determinism and parse performance
```

### Inlining

```
note[COMP-08]: category `BoolOp` has 1 caller (`Expr`), 2 rules, no outgoing calls;
               consider inlining into `Expr`
  = hint: inlining small leaf categories eliminates cross-category Push/Pop
          overhead in the WPDS and simplifies the call graph
```

### Cycle-Breaking

```
note[COMP-08]: mutual recursion cycle with 4 categories: {Expr, Type, Pattern, Guard};
               consider introducing an intermediate category to break the cycle
  = hint: large mutual-recursion cycles increase WPDS saturation time and can
          obscure dead-rule detection
```

## Resolution

These are informational suggestions (Note severity). The grammar author should evaluate each suggestion against their design goals:

1. **Hub splitting:** Identify subsets of rules in the hub category that share common callers or callees, and factor them into dedicated categories.
2. **Inlining:** Move the leaf category's rules directly into the caller category. This is straightforward when the leaf has no recursive structure. Note: PraTTaIL does not perform automatic inlining -- this is a manual grammar restructuring suggestion.
3. **Cycle-breaking:** Identify the weakest edge in the cycle (fewest call sites or lowest weight) and introduce an intermediate category to break it.

## Hint Explanation

Each heuristic has a specific hint:

- **Hub:** "hub categories can cause cascading ambiguity" -- When many categories both call and are called by a single category, ambiguity in that category can propagate through the entire grammar.
- **Inline:** "inlining small leaf categories eliminates cross-category Push/Pop overhead" -- Each cross-category call adds Push/Pop rules to the WPDS and frames to the trampoline stack. Inlining removes this overhead.
- **Cycle-break:** "large mutual-recursion cycles increase WPDS saturation time" -- Tarjan SCC decomposition identifies cycles, and poststar saturation complexity increases with SCC size.

## Related Lints

- [G08](../grammar/G08-missing-cast-to-root.md) -- Missing cast-to-root detection. COMP-08 hub splitting may help categories that G08 flags.
- [C04](../cross-category/C04-wide-cross-overlap.md) -- Wide cross-category overlap. Hub categories often have wide overlaps.
