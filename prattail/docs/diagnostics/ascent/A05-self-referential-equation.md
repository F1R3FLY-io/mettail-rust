# A05: self-referential-equation

**Severity:** Warning
**Category:** Ascent / Equation Structure
**Feature Gate:** none (always active)

## Description

Detects rules that are **trivial identities** -- rules whose syntax consists
of a single nonterminal whose category is the same as the rule's own category.
Such a rule maps a term to itself (e.g., `Identity . x:Expr |- x : Expr;`).
If this rule participates in an equation, it is always tautologically satisfied
(`x = x` for all `x`), producing no useful equalities while consuming
fixpoint computation cycles.

```
  Rule: Identity . x:Expr |- x : Expr;

  This defines:  Identity(x) = x   for all Expr x

  ┌──────────────────────────────┐
  │  Equation: Identity(x) = x  │
  │  Always true (reflexivity)   │
  │  Contributes nothing to the  │
  │  equivalence relation        │
  └──────────────────────────────┘
```

A self-referential identity rule as a **parsing** rule is legitimate -- it can
serve as a cast or injection (e.g., wrapping a sub-expression for
disambiguation).  The warning specifically concerns its use in **equations**,
where it becomes a reflexivity tautology that wastes Ascent computation.

## Trigger Conditions

All of the following must hold:

- The rule's syntax contains **exactly one** item.
- That single item is a `NonTerminal` whose category matches the rule's own
  category (self-referential).

One diagnostic is emitted per flagged rule.

## Example

### Grammar

```rust
language! {
    name: SimpleLang,
    types { ![i32] as Expr },
    terms {
        Num      . |- <int>          : Expr;
        Add      . a:Expr, b:Expr   |- a "+" b : Expr;
        Identity . x:Expr            |- x      : Expr;
    },
}
```

### Output

```
warning[A05] (SimpleLang): rule `Identity` is a trivial identity (single self-referential nonterminal) — if used as an equation, this is redundant
  = hint: remove this rule if it serves no purpose, or verify it is intentional
```

## Resolution

1. **Remove the rule.**  If the rule was accidentally introduced or is left
   over from refactoring, removing it eliminates the redundant identity and
   reduces the generated Ascent struct size.

2. **Verify intent.**  If the rule serves as a syntactic cast or injection
   (e.g., allowing `Expr` to appear where a `Statement` is expected), it is
   legitimate as a parsing rule.  Ensure it is not also registered as an
   equation participant by removing it from any equational axiom
   declarations.

3. **Rename for clarity.**  If the rule is intentionally a type-level identity
   used for disambiguation (e.g., parenthesized expressions `"(" Expr ")"`),
   add the terminal delimiters to the syntax.  A rule with terminals is not
   self-referential in the sense detected by A05.

## Hint Explanation

The hint **"remove this rule if it serves no purpose, or verify it is
intentional"** acknowledges the dual role of identity rules:

- As **parsing rules**, they may serve as injection/cast constructors between
  categories (though a single-nonterminal same-category rule is unusual).
- As **equation rules**, they contribute the reflexivity axiom `C(x) = x`,
  which is always true and wastes computation.

The hint asks the author to clarify which role the rule plays and take
appropriate action.

## Related Lints

- [A08](A08-equation-subsumes-rewrite.md) -- An identity equation trivially
  subsumes any rewrite for the same constructor, since `C(x) = x` implies
  `C(x) ~> x`.
- [A02](A02-redundant-congruence.md) -- A category with only a single
  self-referential rule may also have redundant congruence.
- [G07](../grammar/G07-identical-rules.md) -- Detects structurally identical
  rules across constructors; A05 is the degenerate single-rule case where the
  rule is identical to its own input.
