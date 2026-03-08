# N03: scope-violation

**Severity:** Warning
**Category:** analysis/concurrency
**Feature Gate:** `nominal`

## Description

Detects names that are used outside the binding scope established by their
binder. In a grammar with name-binding constructs (e.g., `"new" x "in" body`),
each binder introduces a name into a specific scope -- the syntactic region
where the name is valid. A scope violation occurs when a grammar rule references
a name in a context where no enclosing binder has introduced it, or where the
reference is structurally outside the binder's scope.

The analysis is based on nominal automata theory. The grammar is modeled as a
nominal set where:

- **Names** are the atoms (bound variables introduced by binders).
- **Orbits** are equivalence classes of names under permutation (alpha-equivalence).
- **Support** of a state is the set of names that the state depends on.

A scope violation occurs when a name appears in the support of a state but is
not in the support of any enclosing binder scope. Formally, for a name n and a
grammar state s:

  n in support(s) and n not in Union_{b in ancestors(s)} scope(b)

where ancestors(s) is the set of binder states on the path from the root to s,
and scope(b) is the set of names introduced by binder b.

### Scope violation scenario

```
  Grammar rule tree:

    PNew . x:Name, body:Proc |- "new" x "in" body : Proc
                                      │          │
                                      │  scope   │
                                      │<────────>│
                                      │   of x   │

    PSend . ch:Name, msg:Expr |- ch "!" "(" msg ")" : Proc
                                  ^
                                  │
                          if ch = x, then x is used
                          outside the scope of its binder
                          (PSend is not nested inside PNew.body)

  Scope model:
    ┌───────────────────────────────────────┐
    │  PNew scope                           │
    │  binder: x                            │
    │  ┌─────────────────────────────────┐  │
    │  │  body (Proc)                    │  │
    │  │  x is valid here                │  │
    │  └─────────────────────────────────┘  │
    └───────────────────────────────────────┘

    ┌───────────────────────────────────────┐
    │  PSend (separate rule, not in body)   │
    │  ch references x --> SCOPE VIOLATION  │
    └───────────────────────────────────────┘
```

The violation is detected statically by analyzing the grammar's rule structure:
if a name binding is established in one rule and a reference to that name
appears in a rule that is not syntactically nested within the binder's scope,
the nominal analysis flags it.

## Trigger Conditions

A warning is emitted **once per scope violation** when **all** of the following
conditions hold:

1. The `nominal` feature is enabled.
2. The pipeline's nominal analysis module (`nominal.rs`) has been executed,
   producing a `NominalAnalysis`.
3. The result's `scope_violations` vector is non-empty.

One diagnostic is emitted for each `(name, context)` pair in `scope_violations`,
where:
- `name` is the name that escapes its binding scope.
- `context` is a description of the rule or position where the violation occurs.

The lint is silent when:
- The `nominal` feature is not enabled.
- No `NominalAnalysis` is available (analysis was not run).
- The `scope_violations` vector is empty (all names used within their scopes).

## Example

### Grammar

```
language! {
    name: PiCalc;
    primary: Proc;

    category Proc {
        PNew   = "new" Name "in" Proc;
        PSend  = Name "!" "(" Proc ")";
        PRecv  = Name "?" "(" Name ")" Proc;
        PPar   = Proc "|" Proc;
        PZero  = "0";
    }

    category Name {
        Ident = <ident>;
    }
}
```

If the nominal analysis determines that a name `x` introduced by `PNew` is
referenced in a `PSend` rule that is not structurally nested within the
`PNew`'s body, the violation is flagged.

### Output

```
warning[N03] (PiCalc): name `x` used outside its binding scope (rule PSend)
  = hint: ensure the name is only used within the scope of its binder
```

## Resolution

When N03 fires, a name escapes its intended binding scope. The resolution
depends on the grammar's design intent:

1. **Restructure the grammar.** Move the rule that references the escaped name
   so that it is syntactically nested within the binder's scope. For example,
   if `PSend` should only be valid inside a `PNew` scope, make `PSend` a
   sub-rule of `PNew`'s body category.

2. **Add the binding.** If the name should be valid at the reference site,
   introduce an additional binder at a higher scope level that covers both
   the definition and use sites.

3. **Use a different name.** If the reference is to a *different* name that
   happens to share the same string representation, introduce distinct
   identifiers to avoid the false positive.

4. **Accept the violation.** If the grammar intentionally models a language
   with dynamic scoping (where names are resolved at runtime rather than
   statically), scope violations are expected. The warning documents the
   dynamic scoping behavior.

## Hint Explanation

The hint "ensure the name is only used within the scope of its binder" restates
the fundamental principle of lexical scoping: a bound name is valid only within
the syntactic region controlled by its binder. If the grammar intends lexical
scoping, every reference to a bound name must be reachable only through the
binder's body. If the reference is outside this region, either the reference
site or the binder site needs to be restructured to restore the scoping
invariant.

## Related Lints

- [N04](N04-scope-narrowing.md) -- Scope narrowing suggestions; detected when a binder's scope is wider than necessary (the converse of N03)
- [S04](../../safety/S04-ewpds-merge-site.md) -- EWPDS merge sites correspond to the same binder positions that define scopes
- [N05](N05-non-bisimilar.md) -- Non-bisimilar categories; scope violations may contribute to structural differences between categories
