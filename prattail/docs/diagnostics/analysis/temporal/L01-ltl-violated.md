# L01: ltl-violated

**Severity:** Warning
**Category:** analysis/temporal
**Feature Gate:** `ltl`

## Description

A grammar's execution traces form an infinite-word language over the alphabet of parse actions (shift, reduce, dispatch, recover). Linear Temporal Logic (LTL) properties constrain which infinite traces are permissible. L01 fires when the model checker discovers that the grammar can produce an execution trace that violates a specified LTL property.

The violation detection works by constructing the product of the system model (a WPDS configuration automaton) with a Buchi automaton compiled from the negated LTL formula. If the product automaton's language is non-empty, there exists at least one infinite execution trace that violates the property. The counterexample is reported as a lasso-shaped trace: a finite prefix leading to a repeating loop.

### LTL Semantics

An infinite trace `pi = s_0, s_1, s_2, ...` satisfies an LTL formula `phi` (written `pi |= phi`) according to:

```
pi, i |= p          iff  p in Label(s_i)           (atomic proposition)
pi, i |= not phi    iff  pi, i |/= phi              (negation)
pi, i |= phi /\ psi iff  pi, i |= phi and pi, i |= psi  (conjunction)
pi, i |= phi \/ psi iff  pi, i |= phi or  pi, i |= psi  (disjunction)
pi, i |= X phi      iff  pi, i+1 |= phi             (next state)
pi, i |= F phi      iff  there exists j >= i such that pi, j |= phi   (eventually)
pi, i |= G phi      iff  for all   j >= i,     pi, j |= phi   (always/globally)
pi, i |= phi U psi  iff  there exists j >= i such that pi, j |= psi
                          and for all i <= k < j, pi, k |= phi   (until)
```

A system satisfies `phi` iff every trace `pi` of the system satisfies `pi, 0 |= phi`.

### Buchi x WPDS Product Construction

The model checking algorithm proceeds in three stages:

```
                     LTL property phi
                           |
                           v
                    Negate: not phi
                           |
                           v
              ┌────────────────────────────┐
              │   ltl_to_buchi(not phi)     │
              │   GPVW tableau algorithm    │
              └────────────────────────────┘
                           |
                           v
                  B_neg = Buchi(not phi)
                           |
         WPDS configs      |
              |             |
              v             v
       ┌──────────────────────────┐
       │  Product Automaton       │
       │  A_prod = A_sys x B_neg  │
       │                          │
       │  States: (q_sys, q_buchi)│
       │  Accept: q_buchi in F    │
       └──────────────────────────┘
                    |
                    v
       ┌──────────────────────────┐
       │  SCC Emptiness Check     │
       │                          │
       │  Find accepting SCC:    │
       │  SCC with state in F    │
       │  reachable from initial  │
       └──────────────────────────┘
                    |
           ┌───────┴───────┐
           |               |
           v               v
     No accepting    Accepting SCC
     SCC found       found
           |               |
           v               v
      Satisfied       Violated
      (L02)           (L01)
                           |
                           v
              ┌─────────────────────────┐
              │  Counterexample:        │
              │  prefix: s0 -> ... -> sn│
              │  lasso:  sn -> ... -> sn│
              │  (finite prefix + loop) │
              └─────────────────────────┘
```

The counterexample has a **lasso shape**: a finite prefix from the initial state to a state in the accepting SCC, followed by a cycle through the accepting SCC back to that state. This lasso witnesses an infinite trace where the negated property holds infinitely often -- meaning the original property is violated.

## Trigger Conditions

L01 fires once per violated LTL property. Specifically:

- The `ltl` feature gate is enabled.
- The pipeline has computed `ltl_results` (a `Vec<LtlCheckResult>`).
- At least one entry in `ltl_results` is `LtlCheckResult::Violated { prefix, lasso }`.
- One L01 diagnostic is emitted per `Violated` result, indexed by position in the results vector.

## Example

### Grammar

```
language! {
    name: StreamParser;
    primary: Stmt;

    category Stmt {
        native_type: Identifier;

        Open   = "open" "(" Expr ")";
        Close  = "close" "(" Expr ")";
        Seq    = Stmt ";" Stmt;
        CastE  = Expr;
    }

    category Expr {
        native_type: Integer;

        Var   = <ident>;
        Num   = <int>;
        Add   = Expr "+" Expr;
    }
}
```

With an LTL property specifying that every `open` action is eventually followed by a `close` action:

```
G(open -> F close)
```

If the grammar permits an infinite sequence of `open` actions without any `close` (e.g., recursive `Seq` producing unbounded `Open` without `Close`), the product automaton is non-empty.

### Output

```
warning[L01] (StreamParser): LTL property #0 violated (Buchi product non-empty): open
  = hint: the grammar's execution traces can violate this temporal property
```

## Resolution

1. **Examine the counterexample trace.** The `prefix` field identifies the sequence of parse actions leading to the violating state; the `lasso` field identifies the repeating cycle. Together they form a concrete infinite execution that violates the property.

2. **Identify the grammar structure enabling the violation.** Common causes:
   - Recursive categories that can unfold without reaching a required action.
   - Missing synchronization points (e.g., no rule forcing a matching `close` after `open`).
   - Error recovery paths that skip required actions.

3. **Modify the grammar to enforce the property.** Options include:
   - Adding structural constraints (e.g., matched delimiters as a single rule `Block = "open" "(" Expr ")" "close"`).
   - Splitting categories to separate open/close into paired constructs.
   - Adding guard rules that prevent unbounded nesting without closure.

4. **Re-run compilation.** If the property is now satisfied, L02 will confirm it.

## Hint Explanation

> the grammar's execution traces can violate this temporal property

The hint identifies the root cause: the grammar's structure admits at least one infinite execution trace that fails to satisfy the LTL formula. The trace is constructive -- the Buchi product automaton's accepting SCC provides a concrete witness. The grammar author should examine which parse paths enable the violation and restructure accordingly.

## Related Lints

- [L02](L02-ltl-verified.md) -- Complementary: fires when all LTL properties are satisfied (SCC emptiness check succeeds for every property).
- [W13](../../wfst/W13-wpds-unreachable.md) -- WPDS unreachability analysis. L01 uses the same WPDS infrastructure but checks temporal properties rather than reachability.
- [D14](../../wpds/D14-wpds-complexity-report.md) -- WPDS complexity report. The Buchi product size is bounded by `|A_sys| x |B_neg|`, so D14's metrics help predict L01 analysis cost.
- [P06](../P06-analysis-pipeline-cost.md) -- Reports total analysis phase time, which includes LTL model checking when enabled.
