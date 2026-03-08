# N04: scope-narrowing

**Severity:** Note
**Category:** analysis/concurrency
**Feature Gate:** `nominal`

## Description

Suggests that a `PNew`-style binder's scope can be tightened -- the name binding
currently covers a wider syntactic region than is necessary for all references
to the bound name. Narrowing the scope improves the grammar's clarity, reduces
the support set of intermediate parser states, and can enable more precise
analyses (safety verification, bisimulation, invariant discovery).

The intuition is simple: if a name `x` is bound at the top of a large
syntactic block but only referenced deep inside a small sub-block, the binding
scope can be pushed down to the inner block without changing the language's
semantics. This is the nominal-automata analogue of "move variable declarations
closer to their point of use."

The analysis inspects the orbit structure of the nominal automaton. For each
binder, it computes the *minimal scope* -- the smallest syntactic region that
contains all references to the bound name. If the minimal scope is strictly
smaller than the binder's current scope, the binder is a narrowing candidate.

### Scope narrowing illustration

```
  Before narrowing:

    PNew . x:Name, body:Proc |- "new" x "in" body : Proc

    body = Seq(
             Send(y, IntLit(1)),      -- x not referenced here
             Seq(
               Send(x, IntLit(2)),    -- x referenced here
               Recv(x, z)             -- x referenced here
             )
           )

    Current scope of x:
    ┌─────────────────────────────────────────┐
    │  "new" x "in"                           │
    │  ┌───────────────────────────────────┐  │
    │  │  Send(y, 1)     -- x unused       │  │
    │  │  ┌─────────────────────────────┐  │  │
    │  │  │  Send(x, 2)  -- x used      │  │  │
    │  │  │  Recv(x, z)  -- x used      │  │  │
    │  │  └─────────────────────────────┘  │  │
    │  └───────────────────────────────────┘  │
    └─────────────────────────────────────────┘

  After narrowing:

    Seq(
      Send(y, IntLit(1)),
      PNew . x:Name, inner:Proc |- "new" x "in" inner : Proc
        inner = Seq(Send(x, 2), Recv(x, z))
    )

    Narrowed scope of x:
    ┌─────────────────────────────────┐
    │  "new" x "in"                   │
    │  ┌───────────────────────────┐  │
    │  │  Send(x, 2)  -- x used   │  │
    │  │  Recv(x, z)  -- x used   │  │
    │  └───────────────────────────┘  │
    └─────────────────────────────────┘
```

The narrowed scope is strictly smaller, excluding the `Send(y, 1)` node that
does not reference `x`. This reduces the number of parser states that carry `x`
in their support set, which benefits:
- **Nominal analysis:** Fewer orbits to track.
- **Bisimulation:** Smaller state spaces for the bisimulation game.
- **EWPDS:** Tighter merge function sites with less irrelevant context.

### Formal criterion

For a binder b with bound name n and scope S(b):

  minimal_scope(b, n) = smallest sub-tree T of S(b) such that
    forall s in S(b) . (n in support(s)) implies (s in T)

N04 fires when S(b) strictly contains minimal_scope(b, n):

  minimal_scope(b, n) subset S(b) and minimal_scope(b, n) != S(b)

## Trigger Conditions

A note is emitted **once per narrowing candidate** when **all** of the
following conditions hold:

1. The `nominal` feature is enabled.
2. The pipeline's nominal analysis module (`nominal.rs`) has been executed,
   producing a `NominalAnalysis`.
3. The result's `narrowing_candidates` vector is non-empty.

One diagnostic is emitted for each `(binder, suggestion)` pair in
`narrowing_candidates`, where:
- `binder` is the name of the binder whose scope can be tightened.
- `suggestion` is a description of the proposed narrowing.

The lint is silent when:
- The `nominal` feature is not enabled.
- No `NominalAnalysis` is available (analysis was not run).
- The `narrowing_candidates` vector is empty (all scopes are already minimal).

## Example

### Grammar

```
language! {
    name: LambdaCalc;
    primary: Expr;

    category Expr {
        Lam  = "lam" Name "." Expr;
        App  = Expr Expr;
        Var  = Name;
        Let  = "let" Name "=" Expr "in" Expr;
    }

    category Name {
        Ident = <ident>;
    }
}
```

If the `Let` rule binds `x` over a body that only uses `x` in a deeply
nested sub-expression, the nominal analysis identifies the binder's scope as
a narrowing candidate.

### Output

```
note[N04] (LambdaCalc): `PNew` scope for binder `x` can be tightened: narrow to inner scope
```

## Resolution

N04 is informational. The suggested narrowing is optional but recommended for
grammar clarity and analysis precision:

1. **Apply the narrowing.** Restructure the grammar so that the binder is
   introduced at the innermost scope that covers all references. This may
   involve splitting a large rule into smaller rules or introducing
   intermediate categories.

2. **Keep the wide scope.** If the wide scope is intentional (e.g., the binder
   must be visible for future extensions or for dynamic-scoping semantics),
   the note can be acknowledged without action.

3. **Review the references.** If the narrowing suggestion is surprising (the
   name should be referenced more widely), check whether some references were
   inadvertently removed or commented out.

## Hint Explanation

N04 does not include a hint, as it is a purely informational suggestion. The
`suggestion` field in the diagnostic message provides specific guidance on how
to tighten the scope.

## Related Lints

- [N03](N03-scope-violation.md) -- Scope violation (name used *outside* its scope); the converse problem to N04 (scope *wider* than necessary)
- [S04](../../safety/S04-ewpds-merge-site.md) -- EWPDS merge sites at binder positions; narrowing the scope may reduce the number of merge sites
- [S05](../../safety/S05-ara-invariant.md) -- ARA invariants; narrower scopes can lead to more precise invariant discovery
