# S04: ewpds-merge-site

**Severity:** Note
**Category:** analysis/safety
**Feature Gate:** `wpds-extended`

## Description

Reports the number and locations of *merge function sites* identified by the
Extended Weighted Pushdown System (EWPDS) analysis. A merge site is a position
in the grammar where a cross-category call boundary coincides with a name-binding
construct (a `Binder` syntax item), enabling the EWPDS to combine caller and
callee weights at return points using a merge function rather than simple
semiring multiplication.

The rationale for reporting merge sites is precision awareness. In a standard
WPDS, the caller's weight and the callee's summary are combined via semiring
multiplication (w_call otimes w_callee). This is correct but potentially
imprecise when the caller and callee interact through shared bindings. An EWPDS
replaces this with a ternary merge function:

  merge(w_call, w_entry, w_callee)

where w_entry is the weight at the callee's entry point. The merge function can
encode correlations between the call site context and the callee's behavior that
plain multiplication discards.

In PraTTaIL, each `SyntaxItemSpec::Binder` position marks a call/return boundary
where a name binding is established. The EWPDS scanner identifies these positions
and labels them as merge sites. The S04 diagnostic reports how many such sites
exist and which rules contain them, giving grammar authors visibility into where
the extended analysis provides additional precision.

### Merge site identification

```
  Rule with Binder syntax item:

    PNew . x:Name, body:Proc |- "new" x "in" body : Proc;
                    ^                  ^
                    │                  │
           Binder position     Name binding scope
                    │
                    v
            ┌──────────────┐
            │  Merge Site  │
            │  rule: PNew  │
            │  cat:  Proc  │
            └──────────────┘

  At the call boundary:
    caller context (Proc) ──> callee (Name) ──> return to (Proc)

  Standard WPDS:     w_result = w_call otimes w_callee
  EWPDS:             w_result = merge(w_call, w_entry, w_callee)
```

The merge function has access to both the caller's pre-call weight and the
callee's entry weight, allowing it to track which bindings flow across the
call boundary and how they interact with the callee's scope.

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. The `wpds-extended` feature is enabled.
2. The pipeline's EWPDS module (`ewpds.rs`) has been executed, producing an
   `EwpdsAnalysis`.
3. The result's `merge_site_count` is greater than zero.

The lint is silent when:
- The `wpds-extended` feature is not enabled.
- No `EwpdsAnalysis` is available (analysis was not run).
- The `merge_site_count` is zero (no binder positions found).

## Example

### Grammar

```
language! {
    name: RhoCalc;
    primary: Proc;

    category Proc {
        PNew   = "new" Name "in" Proc;      // Binder: Name
        PSend  = Name "!" "(" Proc ")";
        PRecv  = Name "?" "(" Name ")" Proc; // Binder: Name (2nd)
        PPar   = Proc "|" Proc;
        PZero  = "0";
    }

    category Name {
        Ident = <ident>;
    }
}
```

Here, `PNew` and `PRecv` both contain `Binder` syntax items (the `Name`
parameters that introduce binding scopes). The EWPDS scanner identifies
two merge sites.

### Output

```
note[S04] (RhoCalc): identified 2 merge function site(s): Proc.PNew, Proc.PRecv
```

## Resolution

S04 is informational. No corrective action is needed. The diagnostic helps
grammar authors understand:

1. **Which rules require merge functions.** Merge sites are where the EWPDS
   provides additional precision over a standard WPDS. If precision is not
   needed at a particular call boundary, the grammar can be restructured to
   avoid the binder.

2. **Performance implications.** Each merge site adds a ternary combine
   operation during the EWPDS saturation phase. For grammars with many merge
   sites, the analysis cost increases. If the additional precision is not
   needed, consider whether the binder positions are essential.

3. **Correctness of scope modeling.** The merge site labels confirm which
   rules the EWPDS considers as call/return boundaries with binding
   interactions. If a rule is missing from the list (or present unexpectedly),
   review its syntax items for `Binder` positions.

## Hint Explanation

S04 does not include a hint, as it is purely informational. The merge site
count and labels provide direct visibility into the EWPDS analysis scope.

## Related Lints

- [S05](S05-ara-invariant.md) -- ARA (Algebraic Program Analysis with Recurrences) uses the EWPDS merge sites to discover affine invariants at call boundaries
- [N03](../concurrency/N03-scope-violation.md) -- Scope violations detected by nominal analysis; EWPDS merge sites correspond to the same binding boundaries
- [N04](../concurrency/N04-scope-narrowing.md) -- Scope narrowing suggestions for binders that are also EWPDS merge sites
- [S01](S01-safety-violation.md) -- Safety verification uses the EWPDS model when the `wpds-extended` feature is enabled
