# W13: wpds-unreachable

**Severity:** Warning
**Category:** WFST-Specific

## Description

Detects rules whose entire category is unreachable under WPDS (Weighted Pushdown System) stack-aware analysis. While Tiers 1--3 of dead-rule detection use finite-state analysis (FIRST sets, WFST reachability), Tier 5 uses full pushdown analysis to model the call stack. It constructs a WPDS from the grammar's inter-category `Push`/`Replace`/`Pop` rules, runs `poststar()` with `BooleanWeight` to saturate all reachable configurations from the root category, and flags rules in categories whose entry symbols are never reached.

This analysis catches cases that finite-state analysis cannot: a category may have valid FIRST-set tokens and a well-formed WFST, but if no reachable category ever dispatches to it via a cross-category reference, its rules can never execute during parsing. The WPDS models the full `Push`/`Pop` call/return structure, so it correctly handles transitive call chains, mutual recursion, and deeply nested category references.

### D15 Witness Traces

Each W13 diagnostic may include a **witness trace** (sub-diagnostic D15). The witness trace uses BFS on the G33 call graph to find the shortest hypothetical `Push` chain from a reachable category to the dead category. This helps the grammar author understand *why* the category is unreachable and *what cross-category reference would make it reachable*.

## Trigger Conditions

A W13 diagnostic fires when **all** of the following hold:

1. The grammar has 2 or more categories (WPDS analysis is skipped for single-category grammars).
2. The optimization gate `G25` (WpdsReachabilityCheck) is enabled.
3. `poststar(BooleanWeight)` on the WPDS built from the grammar yields `symbol_weight(StackSymbol::category_entry(cat)).is_zero()` for the rule's category — meaning the category entry is never reached from the root.
4. The rule survives Tiers 1--4 (it was not already flagged by FIRST-set, WFST, or semantic liveness analysis, or resurrected by Tier 4).

## Example

### Grammar

```
language! {
    name: OrphanGrammar;
    primary: Expr;

    category Expr {
        native_type: Integer;
        Num = INTEGER;
        Add = Expr "+" Expr;
    }

    // Orphan: no category ever dispatches to it
    category Orphan {
        OrphanRule = "orphan";
        OrphanAdd = Orphan "+" Orphan;
    }
}
```

### Output

```
warning[W13]: rule `OrphanRule` in category `Orphan` is unreachable via WPDS
              stack-aware analysis
  = in category `Orphan`, rule `OrphanRule`
  = hint: this rule's category is not reachable from the root via any valid
          call/return path; consider adding a cross-category reference or
          removing the rule
  witness trace:
    Orphan has no path from any reachable category

warning[W13]: rule `OrphanAdd` in category `Orphan` is unreachable via WPDS
              stack-aware analysis
  = in category `Orphan`, rule `OrphanAdd`
  = hint: this rule's category is not reachable from the root via any valid
          call/return path; consider adding a cross-category reference or
          removing the rule
  witness trace:
    Orphan has no path from any reachable category
```

## Resolution

1. **Add a cross-category reference.** If `Orphan` should be reachable, add a rule in a reachable category that references it. For example, add `CastOrphan = Orphan;` in the `Expr` category, or a rule like `UseOrphan = "use" Orphan;` in `Expr`.

2. **Remove the orphan category.** If the category and its rules are no longer needed, remove them from the grammar to reduce generated code size and eliminate misleading syntax.

3. **Check for missing grammar structure.** The witness trace shows the shortest hypothetical call chain that would make the category reachable. If the trace shows a plausible path (e.g., `Expr → Type → Orphan`), the missing link identifies which cross-category reference to add.

## Hint Explanation

**"this rule's category is not reachable from the root via any valid call/return path; consider adding a cross-category reference or removing the rule"** — The WPDS constructs a model of the parser's call stack. Starting from the primary category's entry symbol, poststar saturation explores all configurations reachable through `Push` (cross-category call), `Replace` (intraprocedural), and `Pop` (return) rules. If a category's entry symbol never appears in any reachable configuration, no sequence of parsing decisions can ever enter that category.

The witness trace (D15) provides actionable guidance by showing the BFS shortest path on the reverse call graph from the dead category back toward reachable categories. If no path exists, the category is fully disconnected from the grammar's call structure.

## Related Lints

- [W01](W01-dead-rule.md) — Four-tier dead-rule detection (Tiers 1--4). W13 (Tier 5) runs after W01 and catches rules that survive all four prior tiers.
- [G02](../grammar/G02-unused-category.md) — Detects categories declared but never referenced in any rule. G02 is a structural check; W13 provides deeper pushdown-level confirmation.
- [D15](../wpds/D15-wpds-witness-trace.md) — Witness trace sub-diagnostic appended to W13 warnings.
