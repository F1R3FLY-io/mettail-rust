# R06: inverted-recovery-costs

**Severity:** Warning
**Category:** Recovery

## Description

Detects violations of the expected cost hierarchy in the `RecoveryConfig` for error recovery strategies. The recovery system uses a Viterbi minimum-cost search to select the cheapest repair action when a parse error occurs. The repair actions are ranked by a cost hierarchy that reflects the intrusiveness of each repair:

| Rank | Strategy   | Default Cost | Rationale                                                       |
|------|------------|--------------|-----------------------------------------------------------------|
| 1    | Skip       | 0.5/token    | Least intrusive: advance past unexpected tokens to a sync point |
| 2    | Delete     | 1.0          | Low cost: pretend the token was not there                       |
| 3    | Swap       | 1.25         | Moderate: preserves all tokens, just reordered                  |
| 4    | Substitute | 1.5          | Moderate: replace with something valid                          |
| 5    | Insert     | 2.0          | Most intrusive: fabricate a token that was not in the input     |

When a cost earlier in the hierarchy exceeds a cost later in the hierarchy (e.g., `delete_cost > insert_cost`), the Viterbi search will prefer the more intrusive action over the less intrusive one, which typically produces lower-quality error messages and less intuitive repairs. For example, if `insert_cost < skip_per_token`, the recovery system will prefer fabricating tokens over simply skipping unexpected ones, leading to confusing "expected X" messages when the real issue is extraneous input.

The lint performs pair-wise checks across all 5 strategies in hierarchy order. For a configuration with `n = 5` strategies, there are `n * (n - 1) / 2 = 10` pairs to check. Each violation is reported as a separate warning with both cost values, so the grammar author can see exactly which pair is inverted.

## Trigger Conditions

A warning is emitted for **each** pair `(i, j)` where `i < j` in the hierarchy order and `cost_i > cost_j`. Specifically, the hierarchy is checked as:

```
skip_per_token < delete_cost < swap_cost < substitute_cost < insert_cost
```

The five named fields from `RecoveryConfig` are:
1. `skip_per_token` (default: 0.5)
2. `delete_cost` (default: 1.0)
3. `swap_cost` (default: 1.25)
4. `substitute_cost` (default: 1.5)
5. `insert_cost` (default: 2.0)

Equal costs do **not** trigger the lint -- only strict inversions (`cost_i > cost_j`).

## Example

### Grammar

```
language! {
    name: InvertedCosts,
    types {
        ![i32] as Expr
    },
    terms {
        Lit   . n:Expr |- n                  : Expr ![n];
        Add   . a:Expr, b:Expr |- a "+" b    : Expr ![a + b];
        Sub   . a:Expr, b:Expr |- a "-" b    : Expr ![a - b];
        Group . a:Expr |- "(" a ")"          : Expr ![a];
    },
    recovery {
        skip_per_token: 0.5,
        delete_cost: 3.0,       // <-- inverted: higher than substitute and insert
        swap_cost: 1.25,
        substitute_cost: 1.5,
        insert_cost: 2.0,
    },
}
```

In this configuration, `delete_cost` (3.0) exceeds `swap_cost` (1.25), `substitute_cost` (1.5), and `insert_cost` (2.0). This produces 3 warnings -- one for each pair where the earlier-ranked strategy is more expensive than the later-ranked one.

### Output

```
warning[R06]: RecoveryConfig cost hierarchy violated: delete_cost (3.00) > swap_cost (1.25)
  = hint: expected hierarchy: skip < delete < swap < substitute < insert; adjust delete_cost or swap_cost to restore the hierarchy

warning[R06]: RecoveryConfig cost hierarchy violated: delete_cost (3.00) > substitute_cost (1.50)
  = hint: expected hierarchy: skip < delete < swap < substitute < insert; adjust delete_cost or substitute_cost to restore the hierarchy

warning[R06]: RecoveryConfig cost hierarchy violated: delete_cost (3.00) > insert_cost (2.00)
  = hint: expected hierarchy: skip < delete < swap < substitute < insert; adjust delete_cost or insert_cost to restore the hierarchy
```

## Resolution

Adjust the cost values in the `recovery` block to restore the expected ordering:

1. **Review each reported pair.** Each warning identifies two strategies and their costs. The strategy listed first should have a lower cost than the one listed second.

2. **Choose which cost to adjust.** Either lower the first strategy's cost or raise the second strategy's cost. The choice depends on which repair behavior is desired:
   - If delete should genuinely be expensive (e.g., in a language where every token matters), raise the later strategies' costs to be above `delete_cost`.
   - If the high `delete_cost` was unintentional, lower it to a value between `skip_per_token` and `swap_cost`.

3. **Verify the full hierarchy.** After adjusting, confirm that all 5 values are strictly ordered:
   ```
   skip_per_token < delete_cost < swap_cost < substitute_cost < insert_cost
   ```

4. **Use the defaults as a guide.** The default values (0.5, 1.0, 1.25, 1.5, 2.0) are tuned for typical programming language grammars. Deviating from this ordering should be done deliberately and with clear justification.

## Hint Explanation

The hint "expected hierarchy: skip < delete < swap < substitute < insert; adjust {name_i} or {name_j} to restore the hierarchy" summarizes the expected invariant and names the two offending strategies. The hierarchy reflects a principle of least surprise for error recovery:

- **Skip** is cheapest because it makes no claims about what the correct code should look like -- it simply advances past unexpected tokens to a known-good position. This produces the most conservative error messages ("unexpected token X").
- **Delete** is next because removing a single token is a minimal edit that preserves the rest of the input structure.
- **Swap** is moderate because it reorders two adjacent tokens without adding or removing any, preserving all original content while correcting a common transposition typo.
- **Substitute** is more intrusive because it replaces one token with a different one, asserting a specific correction that may not match the programmer's intent.
- **Insert** is most expensive because it fabricates a token that was never in the source, which is the strongest possible claim about what the programmer "meant to write."

Violating this hierarchy causes the Viterbi search to prefer more intrusive repairs over less intrusive ones, which generally produces confusing diagnostics.

## Related Lints

- [R07](./R07-transposition-candidate.md) -- identifies operator pairs that are candidates for the SwapTokens repair action whose effectiveness depends on the swap_cost being correctly positioned in the hierarchy
