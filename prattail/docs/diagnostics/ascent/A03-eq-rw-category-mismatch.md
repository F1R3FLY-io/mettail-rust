# A03: eq-rw-category-mismatch

**Severity:** Note
**Category:** Ascent / Equation-Rewrite Scope
**Feature Gate:** none (always active)

## Description

Detects categories that have parsing rules but whose constructors are **never
referenced** in any equation or rewrite dependency group.  When the grammar
defines equations and rewrites, these are organized into semantic dependency
groups -- sets of constructor labels that participate in the same equational
reasoning chain.  A category whose constructors appear in no dependency group
is structurally disconnected from the grammar's equational semantics.

This may indicate:

- A **missing equation or rewrite**: the category was intended to participate
  in equational reasoning but the author forgot to add the relevant axioms.
- An **intentionally passive category**: the category provides syntax (e.g.,
  literal tokens, delimiters) but has no equational semantics by design.
- A **stale category**: the category once had equations that were removed
  during refactoring, leaving orphaned parsing rules.

```
  Dependency Groups              Categories
  ┌─────────────────┐           ┌──────┐
  │ {Add, Mul, Sub} │ ──────── │ Expr │ constructors referenced
  └─────────────────┘           └──────┘
  ┌─────────────────┐           ┌──────┐
  │ {NVar, NQuote}  │ ──────── │ Name │ constructors referenced
  └─────────────────┘           └──────┘
                                ┌──────┐
            (none) ──────────── │ Atom │ A03 fires
                                └──────┘
```

This lint only fires when there are dependency groups in the grammar (i.e.,
when at least one equation or rewrite exists).  If no equations or rewrites
are defined at all, every category is trivially outside the scope and no
diagnostic is emitted.

## Trigger Conditions

All of the following must hold:

- At least one semantic dependency group exists (the grammar defines equations
  or rewrites).
- The category has at least one parsing rule (it is not empty).
- No constructor label belonging to this category appears in any semantic
  dependency group.
- The category is **not** the primary (root) category.

One diagnostic is emitted per flagged category.

## Example

### Grammar

```rust
language! {
    name: MathLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . |- <int>          : Expr;
        Add  . a:Expr, b:Expr   |- a "+" b : Expr;
        Lit  . |- <int>          : Atom;
    },
    equations {
        // Add participates, but Atom's Lit does not
        |- Add(X, Y) = Add(Y, X);
    },
}
```

### Output

```
note[A03] (MathLang): category `Atom` has parsing rules but no equations or rewrites reference its constructors
  = hint: if this category should participate in equational reasoning, add equations or rewrites
```

## Resolution

1. **Add equations or rewrites.**  If the category should participate in the
   grammar's equational semantics, define equations or rewrite rules that
   reference its constructors.  This places its labels into dependency groups
   and silences A03.

2. **Accept the note.**  If the category is intentionally passive (e.g., it
   provides lexical tokens, delimiters, or structural syntax without
   equational properties), no action is needed.  A03 is informational.

3. **Remove the category.**  If the category is vestigial from a prior grammar
   revision and serves no current purpose, removing it will eliminate both
   the diagnostic and the dead code.

## Hint Explanation

The hint **"if this category should participate in equational reasoning, add
equations or rewrites"** highlights the disconnect between the category's
syntactic presence and its semantic absence.  Equations and rewrites drive
Ascent's fixpoint computation; a category not in that scope contributes syntax
but no equational semantics.

## Related Lints

- [A02](A02-redundant-congruence.md) -- Detects categories with few rules
  that may have redundant congruence; a structural cousin of the mismatch
  detected by A03.
- [A06](A06-missing-equation-congruence.md) -- Detects constructors in
  equations whose field categories have no equation-participating
  constructors, a finer-grained version of the same concern.
- [G05](../grammar/G05-empty-category.md) -- Detects categories with zero
  rules entirely, a more extreme case than A03.
