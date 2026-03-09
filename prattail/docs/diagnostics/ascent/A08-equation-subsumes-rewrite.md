# A08: equation-subsumes-rewrite

**Severity:** Note
**Category:** Ascent / Equation-Rewrite Interaction
**Feature Gate:** none (always active)

## Description

Detects constructors that appear in **two or more** dependency groups,
suggesting that an **equation may subsume a rewrite** for the same
constructor.  Equations are bidirectional (`a = b` means both `a -> b` and
`b -> a`), while rewrites are unidirectional (`a ~> b` means only `a -> b`).
When both an equation and a rewrite involve the same constructor, the
equation's bidirectional nature strictly subsumes the rewrite's one-way
transformation.

```
  Constructor "Normalize" in 2 groups:
  ┌──────────────────────────┐     ┌──────────────────────────┐
  │ G1 (equation group):     │     │ G2 (rewrite group):      │
  │   Normalize(X) = X       │     │   Normalize(X) ~> X      │
  │   (bidirectional)        │     │   (unidirectional)        │
  └──────────────────────────┘     └──────────────────────────┘
                │                                │
                v                                v
        equation already                rewrite is redundant
        provides both directions        (subsumed by equation)
```

If the equation `Normalize(X) = X` is declared, the rewrite `Normalize(X) ~> X`
is redundant because the equation already provides the same reduction (plus
the reverse direction).  Keeping both wastes Ascent computation cycles and
inflates the generated struct with duplicate rules.

The lint detects this by counting how many distinct dependency groups contain
a given constructor label.  Two or more groups suggest dual participation.
The heuristic uses group size to distinguish: groups with two or fewer labels
are classified as rewrite groups, while larger groups are classified as
equation groups.

## Trigger Conditions

All of the following must hold:

- The grammar defines semantic dependency groups (equations or rewrites
  exist).
- A constructor label appears in **two or more** distinct dependency groups.

One diagnostic is emitted per flagged constructor.  When multiple constructors
are flagged, the grouper consolidates them into a single summary.

## Example

### Grammar

```rust
language! {
    name: ReduceLang,
    types { ![i32] as Expr },
    terms {
        Num . |- <int>         : Expr;
        Add . a:Expr, b:Expr  |- a "+" b : Expr;
        Mul . a:Expr, b:Expr  |- a "*" b : Expr;
    },
    equations {
        |- Add(X, Y) = Add(Y, X);  // G1: {Add}
    },
    rewrites {
        |- Add(X, Mul(Y, Z)) ~> Mul(Add(X, Y), Z);  // G2: {Add, Mul}
    },
}
```

### Output

```
note[A08] (ReduceLang): constructor `Add` appears in 2 dependency groups — an equation may subsume a rewrite
  = hint: check whether the rewrite is redundant given the equation
```

When grouped:

```
note[A08] (RhoCalc): 3 constructors may have equation-subsumed rewrites: Name(NQuote), Proc(PPar, PNew)
```

## Resolution

1. **Remove the redundant rewrite.**  If the equation already provides the
   needed reduction direction, delete the rewrite.  This reduces the Ascent
   struct size and avoids duplicate computation during fixpoint evaluation.

2. **Verify the rewrite is not oriented differently.**  If the equation is
   symmetric (`a = b`) but the rewrite provides a specific reduction direction
   that the grammar relies on for normalization, the rewrite may serve a
   purpose despite the subsumption.  In this case, the note can be safely
   ignored.

3. **Convert the equation to a rewrite.**  If the bidirectional equation is
   not needed and only one direction is desired, replace the equation with a
   rewrite.  This eliminates the reverse direction and makes the intent
   explicit.

## Hint Explanation

The hint **"check whether the rewrite is redundant given the equation"**
asks the author to evaluate whether the rewrite provides any value beyond
what the equation already delivers.  Since equations are bidirectional:

- `a = b` implies `a ~> b` (the same direction as the rewrite).
- If the rewrite only provides `a ~> b`, it is strictly subsumed.
- If the rewrite provides a *different* transformation than the equation
  (same constructor but different context), it is not truly subsumed.

The lint uses a structural heuristic (group participation count) and may
produce false positives when two groups involve the same constructor for
unrelated reasons.

## Related Lints

- [A04](A04-large-equivalence-class.md) -- Removing subsumed rewrites
  reduces the number of dependency groups a constructor participates in,
  potentially lowering A04 risk.
- [A05](A05-self-referential-equation.md) -- A self-referential equation
  trivially subsumes any rewrite for the same identity pattern.
- [G27](../grammar/G27-rule-subsumption-candidate.md) -- Detects structural
  rule subsumption at the syntax level; A08 detects semantic subsumption at
  the equation/rewrite level.
