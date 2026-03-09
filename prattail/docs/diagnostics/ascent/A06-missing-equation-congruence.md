# A06: missing-equation-congruence

**Severity:** Note
**Category:** Ascent / Congruence Completeness
**Feature Gate:** none (always active)

## Description

Detects constructors that participate in equations but have **field
categories** whose constructors do not participate in any equations.  This
means that congruence propagation through those fields will not take effect:
even if `a = b`, the equality `C(..., a, ...) = C(..., b, ...)` cannot fire
if the field's category has no equational constructors.

Congruence rules in PraTTaIL propagate equalities structurally through
constructor arguments.  For this propagation to be useful, the field
category must itself have constructors that appear in equations -- otherwise
there is nothing for congruence to propagate *through*.

```
  Constructor "Wrap" in equation:  Wrap(x) = Wrap(y) when x = y
  Field category: Atom
  ┌──────────────────────────────────────────┐
  │  Atom has constructors: {Lit}            │
  │  Lit does NOT appear in any equation     │
  │                                          │
  │  Congruence rule: if a = b in Atom       │
  │    then Wrap(a) = Wrap(b)                │
  │                                          │
  │  But a = b can NEVER fire for Atom       │
  │  because Atom has no equations           │
  │  -> congruence through Atom is vacuous   │
  └──────────────────────────────────────────┘
```

This diagnostic is informational.  The generated congruence rules are not
incorrect -- they are simply dead code within the Ascent fixpoint computation
for the specific field category in question.

## Trigger Conditions

All of the following must hold:

- At least one semantic dependency group exists (the grammar has equations or
  rewrites).
- A constructor label appears in at least one dependency group (it
  participates in equations).
- The constructor's syntax contains a `NonTerminal` field whose category
  is different from the constructor's own category.
- That field category has **no** constructors appearing in any dependency
  group.

One diagnostic is emitted per (constructor, field-category) pair.

## Example

### Grammar

```rust
language! {
    name: WrapperLang,
    types { ![i32] as Expr },
    terms {
        Wrap  . x:Atom |- x : Expr;
        Lit   . |- <int>    : Atom;
    },
    equations {
        |- Wrap(X) = Wrap(Y);  // Wrap in dependency group
    },
}
```

### Output

```
note[A06] (WrapperLang): constructor `Wrap` participates in equations but its field category `Atom` has no equation-participating constructors
  = hint: congruence through `Atom` fields may not propagate — consider adding equations for `Atom`
```

## Resolution

1. **Add equations for the field category.**  If equational reasoning should
   propagate through the field, define equations whose constructors belong to
   the field category.  For instance, adding `|- Lit(X) = Lit(Y) when X = Y;`
   places `Lit` into a dependency group and makes congruence through `Atom`
   productive.

2. **Accept the note.**  If the field category is intentionally opaque
   (e.g., it represents atomic values like integers or strings where equality
   is decided by the runtime, not by equational axioms), congruence through it
   is unnecessary and the note can be safely ignored.

3. **Restructure the constructor.**  If the field was intended to be in the
   same category (enabling same-category congruence), change the field's
   category to match the constructor's own category.

## Hint Explanation

The hint **"congruence through `<field-cat>` fields may not propagate --
consider adding equations for `<field-cat>`"** identifies the specific gap:

- **Congruence propagation** requires that equalities exist in the field
  category.  If `a = b` can never hold for terms in `Atom`, then the
  congruence rule `Wrap(a) = Wrap(b)` can never fire.
- **Adding equations** for the field category creates the equalities that
  congruence needs to propagate.

## Related Lints

- [A02](A02-redundant-congruence.md) -- Detects categories with few rules
  whose congruence rules are likely redundant; A06 identifies the specific
  reason (no equation participants in the field category).
- [A03](A03-eq-rw-category-mismatch.md) -- Detects the category-level
  mismatch; A06 is the finer-grained per-constructor-per-field version.
- [A04](A04-large-equivalence-class.md) -- Adding equations to a field
  category (as suggested by A06) may increase the equivalence class sizes
  tracked by A04.
