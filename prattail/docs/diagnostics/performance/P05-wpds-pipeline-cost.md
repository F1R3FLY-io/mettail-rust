# P05: wpds-pipeline-cost

**Severity:** Info
**Category:** Performance

## Description

Reports the wall-clock time spent on WPDS analysis during the compile-time pipeline, along with the analysis dimensions (|Gamma|, |Delta|, unreachable rule count). This allows grammar authors and pipeline developers to assess the cost of WPDS analysis and decide whether to keep the G25 gate enabled.

## Trigger Conditions

P05 fires when WPDS analysis completes (grammar has >=2 categories, G25 gate enabled, and the analysis produces a `WpdsAnalysis` result with timing data).

## Example

### Grammar

Any grammar with 2+ categories triggers WPDS analysis. Larger grammars with mutual
recursion and deep call chains will show higher |Δ| and longer analysis times.

### Output

```
info[P05]: WPDS analysis completed in 1.23ms (|Γ|=24, |Δ|=38, 2 unreachable rules)
```

For small grammars (3--5 categories), analysis typically completes in <1ms. For large
grammars with 10+ categories and mutual recursion, expect 1--5ms.

## Resolution

This is an informational diagnostic. No action required. If the WPDS analysis time is a concern:

- For grammars with many categories and deep mutual recursion, WPDS saturation can take several milliseconds.
- The G25 gate can be disabled via the cost-benefit framework if the analysis cost exceeds its benefit.
- WPDS analysis is O_s(|Delta|^2 * H) in the worst case, where H is the weight domain height.

## Hint Explanation

No hint is emitted for Info-level diagnostics.

## Related Lints

- [D14](../wpds/D14-wpds-complexity-report.md) -- WPDS complexity report (structural metrics). P05 complements D14 with timing data.
- I05 (cost-benefit-recommendations) -- Cost-benefit optimization recommendations (no dedicated doc page).
