# A02: redundant-congruence

**Severity:** Note
**Category:** Ascent / Congruence Analysis
**Feature Gate:** none (always active)

## Description

Detects categories whose generated **congruence rules** may be redundant.  In
PraTTaIL's Ascent-based equational reasoning, every category that participates
in equations or rewrites gets congruence rules: if `a = b`, then
`C(a) = C(b)` for every constructor `C` whose syntax references the
category.  These congruence rules ensure that equalities propagate through
term structure.

However, if a category has very few rules of its own (zero or one) and is
only referenced as a nonterminal field in other categories' constructors, the
generated congruence rules may do no useful work.  With only one constructor,
the category is essentially a wrapper -- congruence through it is trivially
satisfied or structurally impossible.

```
┌─────────────────────────────────┐
│  Category Atom (1 rule: "Lit")  │
│  Referenced as field in Expr    │
│  Not a primary category         │
│                                 │
│  Congruence rule generated:     │
│    if a = b then Lit(a) = Lit(b)│
│                                 │
│  But Atom has no equations of   │
│  its own -> congruence is idle  │
└─────────────────────────────────┘
```

This lint is purely informational.  The generated congruence rules are not
incorrect -- they simply contribute nothing to the fixpoint computation,
adding relations and Ascent rules that slow compilation without changing
the result.

## Trigger Conditions

All of the following must hold:

- The category is **not** the primary (root) category.
- The category has at most one rule defined in its syntax.
- The category is referenced as a `NonTerminal` field in at least one other
  category's constructor syntax.

One diagnostic is emitted per flagged category.

## Example

### Grammar

```rust
language! {
    name: SimpleMath,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . n:Atom |- n       : Expr;
        Add  . a:Expr, b:Expr |- a "+" b : Expr;
        Lit  . |- <int>         : Atom;
    },
}
```

### Output

```
note[A02] (SimpleMath): category `Atom` has only 1 rule(s) but is referenced as a field — congruence rules for this category may be redundant
  = hint: consider whether equations/rewrites actually need congruence through this category
```

## Resolution

1. **Suppress the congruence.**  If the category genuinely needs no equational
   reasoning, annotate it to skip congruence generation.  This reduces the
   generated Ascent struct size (fewer relations and rules).

2. **Add equations or rewrites.**  If the category *should* participate in
   equational reasoning but currently lacks equations, adding them will make
   the congruence rules productive and silence this diagnostic.

3. **Merge the category.**  If the category is a trivial wrapper (single rule,
   no independent semantics), consider inlining its constructor into the
   parent category to eliminate the extra congruence overhead entirely.

4. **Ignore the note.**  This is informational.  If the grammar is small
   enough that the extra congruence rules have negligible impact, no action
   is required.

## Hint Explanation

The hint **"consider whether equations/rewrites actually need congruence
through this category"** asks the author to evaluate whether equality
propagation through this specific category has any semantic purpose.
Congruence rules are valuable when:

- The category has constructors appearing on both sides of equations.
- Substitutions within the category can affect equalities in parent
  categories.

If neither condition applies, the congruence rules are dead weight in the
Ascent computation.

## Related Lints

- [A03](A03-eq-rw-category-mismatch.md) -- Detects categories with parsing
  rules but no equations or rewrites referencing their constructors; a related
  structural mismatch.
- [A06](A06-missing-equation-congruence.md) -- The complementary case:
  detects constructors in equations whose field categories lack
  equation-participating constructors, meaning congruence will not propagate.
- [A09](A09-ascent-struct-size.md) -- Redundant congruence contributes to
  large Ascent struct size, which A09 tracks at a higher level.
