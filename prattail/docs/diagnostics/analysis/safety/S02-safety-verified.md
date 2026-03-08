# S02: safety-verified

**Severity:** Note
**Category:** analysis/safety
**Feature Gate:** always-on

## Description

S02 is the positive counterpart to S01. It fires when the WPDS prestar analysis
proves that *no* bad state is reachable from the grammar's initial configuration.
This is a certificate of correctness: the parser's inter-procedural control flow,
as modeled by the weighted pushdown system, cannot reach any configuration
flagged as unsafe.

The rationale for emitting this as a diagnostic (rather than staying silent) is
observability. Grammar authors who have intentionally structured their grammars
to avoid unsafe dispatch paths benefit from confirmation that the property holds.
In CI pipelines, the presence of S02 in the diagnostic log serves as an auditable
record that safety verification was run and passed.

Formally, let pre*(A_bad) be the saturated P-automaton (as described in S01).
S02 fires when the initial configuration c_0 is *not* in L(pre*(A_bad)), i.e.:

  w(c_0) = 0   (the zero element of the semiring)

For `BooleanWeight`, this means `false` (unreachable). For `TropicalWeight`,
this means `+infinity` (infinite cost, i.e. no finite-cost path exists).

The property verified is a universally quantified statement over all reachable
configurations:

  forall c in Reach(P, c_0) . c not in Bad

where Reach(P, c_0) is the set of configurations reachable from c_0 under the
WPDS transition relation, and Bad is the set of bad configurations.

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The pipeline's safety verification module has been executed, producing a
   `SafetyResult`.
2. The result's `safe` field is `true`.

The lint is silent when:
- No `SafetyResult` is available (analysis was not run).
- The result's `safe` field is `false` (S01 fires instead).

## Example

### Grammar

```
language! {
    name: SafeCalc;
    primary: Expr;

    category Expr {
        native_type: Integer;
        IntLit = <int>;
        Add    = Expr "+" Expr;
        Mul    = Expr "*" Expr;
        Neg    = "-" Expr;
        Paren  = "(" Expr ")";
    }
}
```

This grammar has a single category with no cross-category calls, no orphan
categories, and no stale dispatch entries. The WPDS has a trivial call graph
(one SCC, no push/pop transitions beyond the root), and prestar confirms that
no bad configuration is reachable.

### Output

```
note[S02] (SafeCalc): no bad states reachable -- safety property verified
```

## Resolution

No action is required. S02 is purely informational. It confirms that the
grammar's inter-procedural structure is consistent and that the WPDS prestar
analysis found no path from the initial configuration to any bad state.

If S02 is unexpected (you expected a safety violation), verify that:
- The bad-state specification is correct (the right configurations are marked
  as bad in the P-automaton).
- The WPDS transition rules accurately model the grammar's cross-category
  dispatch.
- No relevant categories or rules were accidentally omitted.

## Hint Explanation

S02 does not include a hint, as no corrective action is needed.

## Related Lints

- [S01](S01-safety-violation.md) -- The complementary warning: fires when prestar *does* find a path to a bad state
- [S03](S03-cegar-refinement.md) -- CEGAR refinement may be used alongside or instead of direct prestar for more precise verdicts
- [S06](S06-algebraic-summary.md) -- Tarjan path expression summary provides structural context for the call graph analyzed by the safety checker
