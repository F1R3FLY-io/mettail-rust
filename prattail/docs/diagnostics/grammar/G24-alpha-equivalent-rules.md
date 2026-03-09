# G24: alpha-equivalent-rules

**Severity:** Warning
**Category:** Grammar Structure
**Feature Gate:** (none -- always active)

## Description

Detects rules within the same category whose syntax item sequences are
identical up to variable renaming -- that is, they are **alpha-equivalent**.
Two rules are alpha-equivalent when their De Bruijn encounter-order encodings
produce identical byte sequences, even though their concrete variable names
differ.

This lint complements [G07](G07-identical-rules.md), which detects rules with
identical string signatures (exact structural match ignoring field names).
G24 catches a strictly larger class: rules that G07 misses because their
variable names differ but their binding structure is the same.

The De Bruijn encoding works as follows. Variables are assigned sequential
slots in encounter order. The first occurrence of a variable receives tag
`0xC0` (NewVar), and subsequent occurrences receive tag `0x80 | slot`
(VarRef). Terminals and category names are encoded literally. Two rules with
different variable names but identical structure produce identical byte
sequences:

```
  Rule AddA: x "+" y
    De Bruijn: [NewVar, NT(Expr), T(+), NewVar, NT(Expr)]

  Rule AddB: a "+" b
    De Bruijn: [NewVar, NT(Expr), T(+), NewVar, NT(Expr)]

  Identical encoding → alpha-equivalent
```

Crucially, the encoding distinguishes **binding structure**. A rule that
reuses a variable (`x "==" x`) has a different De Bruijn encoding from one
that uses two distinct variables (`a "==" b`):

```
  Rule SelfEq: x "==" x
    De Bruijn: [NewVar, NT(Expr), T(==), VarRef(0), NT(Expr)]

  Rule AnyEq:  a "==" b
    De Bruijn: [NewVar, NT(Expr), T(==), NewVar, NT(Expr)]

  Different encoding → NOT alpha-equivalent
```

## Trigger Conditions

All of the following must hold:

- Two or more rules belong to the same category.
- Their syntax item sequences produce identical De Bruijn byte encodings
  (via `syntax_item_debruijn_bytes()`).
- They have different string signatures (via `syntax_signature()`). If the
  string signatures are also identical, G07 already reports them and G24
  stays silent to avoid double-reporting.

One diagnostic is emitted per group of alpha-equivalent rules within a
category.

## Example

### Grammar

```rust
language! {
    name: Calc,
    types { ![i32] as Expr },
    terms {
        Add  . x:Expr, y:Expr |- x "+" y : Expr;
        Plus . a:Expr, b:Expr |- a "+" b : Expr;
    },
}
```

Here, `Add` and `Plus` have different variable names (`x`/`y` vs `a`/`b`)
but identical De Bruijn structure. The string signatures differ (because
G07's `syntax_signature()` strips field names, making them identical in
that case -- so this example would actually be caught by G07 instead). A
true G24 case requires more subtle differences, such as rules in different
source files with distinct field name patterns that happen to normalize
differently.

### Output

```
warning[G24] (Calc): rules [Add, Plus] in category `Expr` are alpha-equivalent (identical up to variable renaming)
  = hint: these rules differ only in variable names -- consider merging or differentiating their syntax structure
```

## Resolution

1. **Merge the rules.** If both rules serve the same purpose, delete one:

   ```
   Add . x:Expr, y:Expr |- x "+" y : Expr;
   // Remove Plus -- it is alpha-equivalent to Add
   ```

2. **Differentiate the syntax.** If the rules are meant to express different
   operations, add a distinguishing terminal token:

   ```
   Add    . x:Expr, y:Expr |- x "+"  y : Expr;
   Concat . a:Expr, b:Expr |- a "++" b : Expr;
   ```

3. **Differentiate the binding structure.** If one rule should enforce a
   constraint (e.g., both operands must be the same), reuse the variable:

   ```
   Add    . x:Expr, y:Expr |- x "+" y : Expr;  // any two exprs
   Double . x:Expr          |- x "+" x : Expr;  // same expr on both sides
   ```

## Hint Explanation

> these rules differ only in variable names -- consider merging or
> differentiating their syntax structure

The hint points out that the parser cannot distinguish between the rules
because their terminal and non-terminal structure (including binding
patterns) is identical after variable renaming. The WFST dispatch will
assign arbitrary or equal weights to both rules, leading to non-deterministic
selection. The recommended action is to merge them or add a distinguishing
structural element.

## Related Lints

- [G07](G07-identical-rules.md) -- detects rules with identical string
  signatures (a stricter check that fires first); G24 only fires for
  groups that G07 does not already cover
- [G28](G28-alpha-equivalent-groups.md) -- summary-level lint emitted by the
  macro phase reporting the total count of alpha-equivalent groups across
  the entire grammar
- [G04](G04-duplicate-rule-label.md) -- detects duplicate rule labels
  (names), which is a stricter form of duplication (Error severity)
