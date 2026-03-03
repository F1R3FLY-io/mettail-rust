# W06: weight-inversion

**Severity:** Note
**Category:** WFST-Specific

## Description

Detects cases where a less-specific rule has a lower (better) weight in the prediction WFST than a more-specific rule for the same dispatch token. Specificity is measured as the count of syntax items in the rule's `all_syntax` definition: a rule with more syntax items is considered more specific because it constrains a longer sequence of tokens.

In well-calibrated grammars, more-specific rules should generally have lower (better) weights because they match more constrained input patterns. When the parser encounters an ambiguous token, it tries alternatives in weight order (lowest first). If a less-specific rule has a better weight, the parser will preferentially attempt the shorter, less-constrained match before the longer, more-constrained one. This can lead to:

- **Suboptimal parse paths:** The less-specific rule succeeds on a prefix of the input, consuming fewer tokens than the more-specific rule would have, potentially leaving trailing tokens that cause parse errors downstream.
- **Unintuitive behavior:** Grammar authors typically expect the most-specific matching rule to be preferred, following the "longest match" principle common in lexer generators.

This lint is informational (Note severity) because weight inversions are not always bugs -- some grammars intentionally prefer shorter matches or use weight asymmetry for disambiguation strategies that prioritize generality.

## Trigger Conditions

A W06 diagnostic fires when **all** of the following hold:

1. The category `cat` has a prediction WFST in `prediction_wfsts`.

2. The category has a FIRST set in `first_sets`.

3. For a token `t` in `first_set.sorted_tokens()`, calling `wfst.predict(t)` returns at least 2 `WeightedAction` entries.

4. For some pair `(i, j)` where `i < j` in the sorted predictions:
   - `spec_i < spec_j` (rule `i` is less specific -- has fewer syntax items), AND
   - `w_i < w_j` (rule `i` has a lower/better weight than the more-specific rule `j`).

   where `spec_*` is looked up from the `all_syntax` map as `syntax.len()` for each rule label.

## Example

### Grammar

```
language! {
    name: MatchLang;
    primary: Proc;

    category Int {
        native_type: Integer;

        IntLit      = <int>;
        IntNeg      = "-" Int;
        IntAdd      = Int "+" Int;
    }

    category Bool {
        native_type: Boolean;

        BoolLit     = <bool>;
        BoolNot     = "!" Bool;
        BoolAnd     = Bool "&&" Bool;
    }

    category Proc {
        // 3 syntax items: "match" Int Proc
        PMatch      = "match" Int "{" Proc "}";

        // 7 syntax items: a much more specific match-with-guard form
        PMatchGuard = "match" Int "if" Bool "{" Proc "}";

        POutput     = "stdout" "!" "(" Int ")";
        PNil        = "Nil";
        CastInt     = Int;
    }
}
```

Suppose the WFST assigns `PMatch` a weight of 0.4 (3 syntax items) and `PMatchGuard` a weight of 1.2 (7 syntax items). The less-specific `PMatch` has the better (lower) weight, but `PMatchGuard` is more specific. This means the parser will always try the shorter `PMatch` first, even when the input contains the `"if" Bool` guard clause, potentially consuming `"match" Int "{" Proc "}"` and leaving `"if" Bool "{" Proc "}"` as unparsed trailing tokens.

### Output

```
note[W06]: weight inversion for token `match` in category `Proc`: less-specific rule `PMatch` (5 items, weight 0.40) has better priority than more-specific `PMatchGuard` (7 items, weight 1.20)
  = in category `Proc`
  = hint: more-specific rules should typically have lower (better) weights — check rule ordering or WFST weights
```

## Resolution

This is an informational diagnostic (severity: Note). Consider the following options:

1. **Swap the weights.** Assign the more-specific rule (`PMatchGuard`) a lower weight than the less-specific rule (`PMatch`). This ensures the parser tries the longer, more-constrained match first. If it fails (the input lacks the guard clause), the parser falls back to `PMatch`.

2. **Reorder rules in the grammar.** If weights are derived from declaration order, move `PMatchGuard` before `PMatch` so it receives a lower default weight:
   ```
   category Proc {
       PMatchGuard = "match" Int "if" Bool "{" Proc "}";
       PMatch      = "match" Int "{" Proc "}";
       ...
   }
   ```

3. **Add a distinguishing token.** Make the two rules unambiguous by giving one a unique prefix:
   ```
   PMatchGuard = "match_if" Int Bool "{" Proc "}";
   ```
   This eliminates the weight-ordering concern entirely.

4. **Accept the inversion.** If the grammar intentionally prefers the shorter match (e.g., in a context where the guard clause is parsed separately by a later pass), the inversion is by design and the note can be ignored.

## Hint Explanation

**"more-specific rules should typically have lower (better) weights -- check rule ordering or WFST weights"** -- The tropical semiring `(min, +)` assigns priority to lower weights. In most grammars, the "longest match" principle applies: when two rules can both match starting from the same token, the rule that constrains more of the input should be preferred, because it produces a more complete parse.

Specificity is computed as the count of `SyntaxItemSpec` elements in the rule's `all_syntax` definition. This is a syntactic approximation -- it counts terminals, non-terminals, and optional groups equally. While not a perfect proxy for semantic specificity, it captures the intuition that rules with more syntactic constraints are more specific.

The lint checks all pairs `(i, j)` within the weight-sorted predictions for a token, not just adjacent pairs. This ensures that inversions between the best and third-best rule (for example) are also detected, even if the second-best rule has intermediate specificity and weight.

## Related Lints

- [W04](W04-weight-gap-anomaly.md) -- Detects large weight gaps suggesting near-determinism; a weight inversion with a large gap means the parser strongly prefers the less-specific rule
- [G03](../grammar/G03-ambiguous-prefix.md) -- Detects ambiguous prefixes structurally; weight inversions only matter when the prefix is ambiguous (otherwise there is no alternative to invert against)
