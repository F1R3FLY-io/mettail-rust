# W16: wpds-weight-inversion

**Severity:** Warning
**Category:** WFST-Specific

## Description

Detects cases where the WPDS-derived optimal weight order contradicts the WFST dispatch weight for rules in the same category. If rule A has a lower (better) WFST weight than rule B, but WPDS analysis shows that B is more reachable across stack contexts (lower WPDS category weight), this constitutes a weight inversion across analysis layers.

The WFST operates at the finite-state level (token-to-rule dispatch), while the WPDS operates at the pushdown level (stack-aware reachability). A disagreement between these layers suggests that the WFST weights may not accurately reflect the actual reachability of rules when stack context is considered.

## Trigger Conditions

A W16 diagnostic fires when:

1. A category has both a prediction WFST and WPDS category weights.
2. For a pair of rules `(A, B)` in the same category's WFST predictions:
   - `A.wfst_weight < B.wfst_weight` (A has better WFST priority), AND
   - `A.wfst_weight + 1.0 < B.wfst_weight` (significant gap), AND
   - The category has calling contexts (`calling_context_count > 0`), AND
   - `wpds_weight_A > wpds_weight_B + 0.5` (WPDS disagrees on ordering).

## Example

### Grammar

```
language! {
    name: DispatchLang;
    primary: Expr;

    category Expr {
        native_type: Integer;
        Num      = <int>;
        Add      = Expr "+" Expr;
        UseType  = "(" Type ")";      // Push to Type (common path)
        UseMeta  = "meta" "(" Meta ")"; // Push to Meta (rare path)
    }

    category Type {
        IntType  = "int";
        ArrType  = "int" "[" "]";     // Both start with "int" → NFA spillover
    }

    category Meta {
        MetaInt  = "int";
        MetaStr  = "string";
    }
}
```

Suppose the WFST assigns `Meta` a weight of 0.3 (fewer rules, less ambiguity) and `Type` a weight of 1.2 (NFA spillover penalizes it). But the WPDS call graph shows `Type` has `fan_in = 2` (called from `Expr.UseType` and `Decl.LetDecl`) while `Meta` has `fan_in = 1` (only `Expr.UseMeta`). The WFST prioritizes `Meta` over `Type`, but the WPDS shows `Type` is more frequently reachable across stack contexts.

### Output

```
warning[W16]: rule `MetaInt` has WFST weight 0.3 but WPDS category weight 2.1 --
              WPDS suggests `Type` (WPDS weight 0.8) is more reachable than `Meta`
  = in category `Meta`
  = hint: WPDS stack-aware analysis suggests a different optimal dispatch order
          than the WFST prediction weights
```

## Resolution

This is a Warning diagnostic. Consider the following options:

1. **Reorder rules** so the WFST weight order aligns with WPDS reachability. If `Type` is genuinely reached more often, its rules should have lower (better) WFST weights.

2. **Accept the divergence** if the WFST order is intentional. For example, if `Meta` rules should be tried first for error recovery or disambiguation reasons, the inversion is by design.

3. **Investigate the call graph.** The divergence often reveals unexpected call patterns — for instance, a category that appears simple at the finite-state level but is called from many stack contexts. Run with `D14` (WPDS complexity report) enabled to see the full call graph metrics.

4. **Adjust dispatch weights.** If the WFST weights are derived from rule specificity alone, consider incorporating WPDS reachability data. INT-01 (`wpds_refine_prediction_weights()`) does this automatically with small tiebreaking offsets, but large inversions may require manual weight adjustment.

## Hint Explanation

**"WPDS stack-aware analysis suggests a different optimal dispatch order than the WFST prediction weights"** -- The WFST assigns dispatch weights based on rule specificity and declaration order. The WPDS assigns weights based on how reachable a category is across all possible stack configurations. When these disagree, the parser may preferentially try a rule that is actually less likely to succeed given the full call context.

## Related Lints

- [W06](W06-weight-inversion.md) -- WFST-internal weight inversion (specificity vs weight). W16 extends this to cross-layer (WFST vs WPDS).
- [W04](W04-weight-gap-anomaly.md) -- Large weight gaps in WFST predictions.
