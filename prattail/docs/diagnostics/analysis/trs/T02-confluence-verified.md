# T02: confluence-verified

**Severity:** Note
**Category:** analysis/trs
**Feature Gate:** `trs-analysis`

## Description

Confirms that the grammar's term rewriting system (TRS) is **confluent**: every
critical pair is joinable, meaning that regardless of which rewrite rule is
applied first, all reduction sequences converge to the same normal form.

Confluence is one of the two pillars of a **convergent** (canonical) rewriting
system. A TRS R is confluent when for every term t:

    if  t ->*_R u  and  t ->*_R v,  then  exists w  such that  u ->*_R w  and  v ->*_R w

By the Knuth-Bendix critical pair theorem, this global property is equivalent to
a finite local check: R is confluent if and only if every critical pair
langle s, t rangle satisfies s downarrow t (joinability). T02 fires when this
finite check succeeds for all N critical pairs.

```
         t
        / \
       /   \
      /     \
  rule_i    rule_j
    /         \
   v           v
   s           t
   \           /
    \         /
     v       v
       w           all pairs join  =>  T02 fires
```

The diagram above is the **Church-Rosser diamond**: for every fork, a join
exists. When T02 fires, every fork-join diagram in the TRS closes, and the
system has the Church-Rosser property.

The diagnostic reports the total number of critical pairs checked, giving the
grammar author confidence in the analysis scope. A system with zero critical
pairs is trivially confluent (no overlaps exist); this is reported as
"all 0 critical pairs are joinable".

## Trigger Conditions

All of the following must hold:

- The `trs-analysis` feature is enabled at compile time.
- A `ConfluenceAnalysis` result is available in the lint context.
- The `is_confluent` field is `true` (all critical pairs were found to be
  joinable, and none have `Unknown` status preventing the determination).

Exactly one T02 diagnostic is emitted per grammar (system-level property, not
per-rule).

## Example

### Grammar

```rust
language! {
    name: BoolSimplify,
    types {
        ![bool] as Bool
    },
    terms {
        True  . |- "true" : Bool ![true];
        False . |- "false" : Bool ![false];
        And   . a:Bool, b:Bool |- a "&&" b : Bool ![a && b] fold;
        Or    . a:Bool, b:Bool |- a "||" b : Bool ![a || b] fold;
        Not   . a:Bool |- "!" a : Bool ![!a];

        // Simplification rewrites (all critical pairs join):
        // !!x -> x             (double negation)
        // !(a && b) -> !a || !b  (De Morgan)
        // !(a || b) -> !a && !b  (De Morgan)
        // true && x -> x       (identity)
        // false || x -> x      (identity)
    },
}
```

### Output

```
note[T02] (BoolSimplify): all 6 critical pairs are joinable — system is confluent
```

## Resolution

No action is required. T02 is an informational note confirming a desirable
property. The grammar's rewriting rules produce deterministic results regardless
of evaluation order.

When T02 fires alongside [T04](T04-termination-verified.md), the TRS is
**convergent** -- every term has a unique normal form that can be reached by any
reduction strategy. This is the strongest guarantee for a rewriting-based
grammar transformation.

## Hint Explanation

This lint has no hint. The system is confluent and no corrective action is
needed.

## Related Lints

- [T01](T01-non-joinable-critical-pair.md) -- The negative counterpart: emitted
  for each individual critical pair that fails to join. T01 and T02 are mutually
  exclusive at the system level (T02 fires only when zero T01 warnings exist).
- [T04](T04-termination-verified.md) -- Termination verification. When both T02
  and T04 fire, the TRS is convergent (confluent + terminating).
- [T03](T03-non-terminating-cycle.md) -- If T02 fires but T03 also fires, the
  TRS is confluent but potentially non-terminating -- an unusual but valid
  state (e.g., lambda calculus is confluent but not strongly normalizing).
