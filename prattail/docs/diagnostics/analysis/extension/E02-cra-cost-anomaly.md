# E02: cra-cost-anomaly

**Severity:** Warning
**Category:** analysis/extension
**Feature Gate:** `cra`

## Description

Detects anomalous register values in the Cost Register Automaton (CRA) analysis of the grammar's streaming cost model. A CRA processes the token stream while maintaining a finite set of registers holding semiring values. At each step, registers are updated via semiring operations (addition and multiplication) applied to the current register contents and the input cost. E02 fires when a register value exceeds an expected threshold, indicating that the grammar's cost structure may have pathological behavior.

### CRA Register Update Model

A Cost Register Automaton `A = (Q, Sigma, R, delta, mu, q_0, nu)` consists of:

- `Q` -- finite state set (parse states)
- `Sigma` -- input alphabet (token types)
- `R = {r_0, r_1, ..., r_{k-1}}` -- finite register set
- `delta: Q x Sigma -> Q` -- state transition function
- `mu: Q x Sigma -> (R -> Expr(R, cost))` -- register update function
- `q_0` -- initial state
- `nu: Q -> Expr(R)` -- output function

On reading input symbol `a` in state `q`, the CRA transitions to `delta(q, a)` and updates each register `r_i` according to:

```
r_i' = mu(q, a)(r_i)
```

where `mu(q, a)(r_i)` is an expression built from:
- Current register values: `r_0, r_1, ..., r_{k-1}`
- Input cost: `cost(a)`
- Semiring operations: `+` (plus) and `x` (times)
- Semiring constants: `0` (zero) and `1` (one)

```
  Input stream:  a_1,  a_2,  a_3,  ...
                  |     |     |
                  v     v     v
  State:    q_0 ---> q_1 ---> q_2 ---> ...
                  |     |     |
  Registers:     |     |     |
  r_0: 0 ------> r_0'------> r_0'' --> ...
  r_1: 0 ------> r_1'------> r_1'' --> ...
        ^              ^              ^
        |              |              |
   mu(q_0, a_1)   mu(q_1, a_2)   mu(q_2, a_3)
```

### Cost Anomaly Detection

A cost anomaly occurs when a register value after processing the grammar's token patterns exceeds a threshold derived from the grammar's structural complexity. For a grammar with `|R|` rules, `|C|` categories, and maximum nesting depth `D`, the threshold is typically:

```
threshold(r_i) = f(|R|, |C|, D)
```

where `f` is a function calibrated to the register's semantic role (e.g., nesting depth accumulator, ambiguity counter, error recovery penalty).

Register values exceeding this threshold indicate:
- **Unbounded cost growth:** Recursive categories that accumulate cost without bound.
- **Quadratic or exponential amplification:** Register update functions that multiply costs in a pattern that grows faster than linear in the input length.
- **Pathological grammar patterns:** Ambiguous rules whose cost compounds through alternation.

## Trigger Conditions

E02 fires once per anomalous register value. Specifically:

- The `cra` feature gate is enabled.
- The pipeline has computed a `CraAnalysis` result.
- The `cost_anomalies` field contains at least one `(description, value)` pair.
- One E02 diagnostic is emitted per anomaly, identifying the register and its value.

If no cost anomalies are detected, E02 is silent.

## Example

### Grammar

```
language! {
    name: DeepNest;
    primary: Expr;

    category Expr {
        native_type: Integer;

        Num      = <int>;
        Add      = Expr "+" Expr;
        Paren    = "(" Expr ")";
        Nest     = "nest" "(" Expr "," Expr "," Expr ")";
    }
}
```

The `Nest` rule takes three `Expr` sub-expressions, each of which may recursively contain `Nest`. The CRA register tracking nesting cost accumulates multiplicatively: each level of `Nest` triples the sub-expression count. For sufficiently deep nesting, the register value exceeds the threshold.

### Output

```
warning[E02] (DeepNest): CRA register value exceeds threshold: nesting_cost_r0 = 729
  = hint: review the grammar's quantitative cost model
```

## Resolution

1. **Identify the register and its semantic role.** The description field (e.g., `nesting_cost_r0`) indicates which cost metric is anomalous. Common registers include:
   - `nesting_depth` -- tracks recursive nesting depth
   - `ambiguity_count` -- tracks the number of ambiguous alternatives explored
   - `recovery_penalty` -- tracks error recovery cost accumulation

2. **Trace the register update function.** Determine which grammar rules contribute to the register's growth. Multiplicative updates (e.g., `r_i' = r_i x cost(a)`) grow faster than additive ones (`r_i' = r_i + cost(a)`).

3. **Restructure the grammar to bound cost growth.** Options include:
   - Limit recursive depth by introducing iterative alternatives (e.g., replace nested `Nest` with a flat list: `NestList = "nest" "(" ExprList ")"`).
   - Cap register values via min/max guards in the cost model.
   - Split categories to isolate cost-intensive sub-grammars.

4. **Adjust the threshold** if the anomalous value is expected for the grammar's intended use case. Not all high register values indicate problems -- a grammar designed for deeply nested structures may legitimately produce large values.

## Hint Explanation

> review the grammar's quantitative cost model

The hint directs the grammar author to examine the CRA's register update functions and their interaction with the grammar's recursive structure. The anomaly is quantitative, not structural: the grammar may be well-formed but have cost characteristics that lead to unexpectedly large register values during analysis. Reviewing the cost model may reveal multiplicative amplification patterns that can be mitigated.

## Related Lints

- [E01](E01-provenance-trace.md) -- Provenance trace analysis. Provenance polynomials provide the "how" behind derivations; CRA registers provide the "how much." Together they characterize both the structure and cost of parse derivations.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes CRA computation when the feature is enabled.
- [P04](../../performance/P04-many-alternatives.md) -- Many alternatives in a category can amplify CRA register growth through the alternation operator.
