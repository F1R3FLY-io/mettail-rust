# L02: ltl-verified

**Severity:** Note
**Category:** analysis/temporal
**Feature Gate:** `ltl`

## Description

L02 is the positive counterpart to L01. It fires when one or more LTL properties have been verified as satisfied by the grammar's execution model. Satisfaction means that every possible infinite execution trace of the grammar conforms to the temporal specification -- no counterexample exists.

The verification relies on an emptiness check of the product automaton constructed from the system model and the Buchi automaton for the negated property. If the product automaton's language is empty (no accepting strongly connected component is reachable from the initial state), the original property holds universally.

### SCC Emptiness Check

The product automaton `A_prod = A_sys x B_neg` is checked for language emptiness using Tarjan's algorithm for strongly connected components:

```
                  A_prod = A_sys x B_neg(phi)
                           |
                           v
              ┌────────────────────────────┐
              │  Tarjan SCC decomposition   │
              │                            │
              │  Identify all SCCs in the  │
              │  product automaton's graph  │
              └────────────────────────────┘
                           |
                           v
              ┌────────────────────────────┐
              │  For each SCC C:           │
              │                            │
              │  1. Is C reachable from    │
              │     the initial state?     │
              │                            │
              │  2. Does C contain a       │
              │     state (q_sys, q_buchi) │
              │     where q_buchi in F?    │
              │     (F = accepting states  │
              │      of B_neg)             │
              └────────────────────────────┘
                           |
                  ┌────────┴────────┐
                  |                 |
                  v                 v
            No such SCC       At least one
            exists            accepting SCC
                  |                 |
                  v                 v
          L(A_prod) = empty   L(A_prod) != empty
                  |                 |
                  v                 v
            Property phi      Property phi
            SATISFIED         VIOLATED (L01)
            (L02 fires)
```

The key insight is that an infinite word is accepted by a Buchi automaton if and only if the run visits some accepting state infinitely often. This requires the run to eventually enter an SCC containing an accepting state and stay there forever. If no such reachable accepting SCC exists, no accepting run exists, and the product language is empty.

### What L02 Reports

L02 emits a single aggregate diagnostic summarizing how many properties passed. Rather than emitting one diagnostic per satisfied property, it counts all satisfied results and reports the total. This keeps the diagnostic output concise for grammars with many LTL specifications.

## Trigger Conditions

L02 fires when all of the following hold:

- The `ltl` feature gate is enabled.
- The pipeline has computed `ltl_results` (a `Vec<LtlCheckResult>`).
- At least one entry in `ltl_results` is `LtlCheckResult::Satisfied`.
- A single L02 diagnostic is emitted with the count of satisfied properties.

If every result is `Violated` or `Inconclusive` (i.e., zero `Satisfied` entries), L02 does not fire.

## Example

### Grammar

```
language! {
    name: BalancedLang;
    primary: Expr;

    category Expr {
        native_type: Integer;

        Num    = <int>;
        Paren  = "(" Expr ")";
        Add    = Expr "+" Expr;
    }
}
```

With LTL properties:

```
Property 0: G(open_paren -> F close_paren)    -- every "(" is eventually matched by ")"
Property 1: G(!error_state)                     -- the parser never enters an error state
Property 2: G(shift -> X(reduce | shift))      -- after a shift, the next action is reduce or shift
```

If all three properties are satisfied by the grammar's execution model:

### Output

```
note[L02] (BalancedLang): 3 LTL properties satisfied
```

If only properties 0 and 2 are satisfied but property 1 is violated:

```
warning[L01] (BalancedLang): LTL property #1 violated (Buchi product non-empty): error_state
  = hint: the grammar's execution traces can violate this temporal property

note[L02] (BalancedLang): 2 LTL properties satisfied
```

## Resolution

No action is required. L02 is an informational diagnostic confirming that the grammar meets its temporal specifications. It provides confidence that grammar modifications have not broken previously verified properties.

If L02 reports fewer satisfied properties than expected, check for L01 warnings that identify the violated properties.

## Related Lints

- [L01](L01-ltl-violated.md) -- Complementary: fires per violated LTL property with a lasso-shaped counterexample trace.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes LTL model checking when the `ltl` feature is enabled.
