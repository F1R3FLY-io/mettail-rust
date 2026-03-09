# PAR04: mixfix-ambiguous-delimiter

**Severity:** Warning
**Category:** parser
**Feature Gate:** None

## Description

Warns when a mixfix operator's middle delimiter is also used as an infix
operator in the same grammar. Mixfix operators are multi-part operators like
the ternary conditional `a ? b : c`, where `"?"` and `":"` are the
delimiters separating the operands. If one of these delimiters also serves
as an infix operator (e.g., `":"` as a type ascription operator `x : T`),
the parser faces an ambiguity: when it encounters the delimiter after parsing
a sub-expression, it cannot immediately determine whether the delimiter
belongs to the mixfix operator or begins a new infix expression.

PraTTaIL resolves this via binding power comparison (the mixfix operator and
the infix operator have different BPs), but the result may be surprising. The
warning ensures the grammar author is aware of the collision and has verified
that the precedence relationship produces the intended parse trees.

```
  Mixfix / infix delimiter collision

  Mixfix:  a ? b : c       (":" is a middle delimiter of the ternary)
  Infix:   x : T           (":" is an infix type ascription operator)

  Parse of "a ? b : c : T":

  Interpretation 1:  (a ? b : c) : T
    → ternary first, then type ascription of the result

  Interpretation 2:  a ? b : (c : T)
    → type ascription of c first, then ternary

  The parser resolves via BP comparison:
    if ternary_bp(":") < infix_bp(":")  →  Interpretation 2
    if ternary_bp(":") > infix_bp(":")  →  Interpretation 1
```

## Trigger Conditions

All of the following must hold:

- An operator in the BP table is marked as `is_mixfix`.
- One of its `mixfix_parts` has a `following_terminal` that matches the
  `terminal` of a non-postfix, non-mixfix infix operator in the BP table.

One diagnostic is emitted per colliding delimiter per mixfix operator.

## Example

### Grammar

```rust
language! {
    name: TernaryClash,
    types {
        ![String] as Expr,
        ![String] as Type
    },
    terms {
        Lit      . s:Expr |- s : Expr;
        TypeLit  . s:Type |- s : Type;
        Ternary  . c:Expr, t:Expr, e:Expr |- c "?" t ":" e : Expr;
        Ascribe  . e:Expr, t:Type |- e ":" t : Expr;
        Add      . a:Expr, b:Expr |- a "+" b : Expr;
    },
}
```

### Output

```
warning[PAR04] (TernaryClash): mixfix delimiter `:` in `Ternary` is also used as an infix operator
  = hint: parsing may be ambiguous -- consider using a unique delimiter
```

## Resolution

1. **Use a unique delimiter.** Replace the ambiguous delimiter with a
   distinct token. For example, use `"then"` and `"else"` instead of `"?"`
   and `":"` for the ternary operator: `c "then" t "else" e`.

2. **Verify precedence behavior.** If both uses are intentional, carefully
   verify the BP assignments. The mixfix operator's delimiter BP and the
   infix operator's BP must produce the correct parse tree for all relevant
   inputs, especially nested cases like `a ? b : c : T`.

3. **Add parentheses in documentation.** If the collision is accepted,
   document the precedence behavior for users of the grammar. Recommend
   explicit parentheses in ambiguous cases: `a ? b : (c : T)` vs
   `(a ? b : c) : T`.

4. **Split into separate categories.** If the infix `":"` is used in a
   different syntactic context than the ternary (e.g., type annotations
   only appear in declarations, not expressions), placing them in separate
   categories eliminates the collision.

## Hint Explanation

The hint **"parsing may be ambiguous -- consider using a unique delimiter"**
warns that:

- **Ambiguous parsing** can occur when the same token serves two syntactic
  roles (mixfix delimiter and infix operator). The parser resolves the
  ambiguity deterministically via binding powers, but the result may not
  match the grammar author's intent.

- **A unique delimiter** is the cleanest solution: it eliminates the
  ambiguity entirely. If the grammar can afford a different token for the
  mixfix delimiter, the collision disappears.

## Related Lints

- [PAR03](PAR03-postfix-prefix-collision.md) -- Another form of token role
  collision: the same token used as both prefix and postfix. Both lints
  address the general problem of one token serving multiple syntactic roles.
- [LEX01](../lexer/LEX01-overlapping-token-defs.md) -- Token semantic
  overlap at the lexer level can compound with parser-level delimiter
  collisions.
- [DIS05](../dispatch/DIS05-nfa-try-all-set-size.md) -- Mixfix delimiter
  collisions can increase the number of ambiguous dispatch points, since
  the parser cannot determine the delimiter's role from prefix analysis
  alone.
