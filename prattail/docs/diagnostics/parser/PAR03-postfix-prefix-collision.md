# PAR03: postfix-prefix-collision

**Severity:** Warning
**Category:** parser
**Feature Gate:** None

## Description

Warns when the same token is used as both a prefix operator and a postfix
operator within the same category. This creates a syntactic ambiguity: when
the parser encounters the token in a position where both interpretations are
valid, it must use context and binding power to disambiguate. While PraTTaIL's
parser handles this correctly (the Pratt algorithm disambiguates by position
in the expression), the dual use can surprise grammar authors and produce
unintuitive precedence behavior.

The classic example is `"-"` used as both unary negation (prefix: `-x`) and
some postfix operation, or `"*"` used as both dereference (prefix: `*p`) and
a postfix operator. The parser disambiguates based on whether the token
appears at the start of an expression (prefix position) or after a complete
sub-expression (postfix position), but the resulting precedence relationships
may not match the author's intent.

```
  Token "-" collision in category Expr

  Prefix use:   - x        (unary negation)
  Postfix use:  x -        (hypothetical decrement)

  Parse of "- x -":
    Option 1:  (- x) -     → negate x, then postfix-decrement
    Option 2:  - (x -)     → postfix-decrement x, then negate

  The parser resolves this via binding power comparison:
    prefix_bp("-")  vs  postfix_bp("-")

  If prefix_bp > postfix_bp:  Option 2
  If postfix_bp > prefix_bp:  Option 1
```

## Trigger Conditions

All of the following must hold:

- A token string appears as a prefix operator (a first-position terminal in
  a non-infix, non-variable, non-literal rule) for some category.
- The same token string appears as a postfix operator (in the BP table with
  `is_postfix = true`) for the same category.

One diagnostic is emitted per colliding token per category.

## Example

### Grammar

```rust
language! {
    name: Collision,
    types {
        ![i64] as Expr
    },
    terms {
        Num    . n:Expr |- n : Expr;
        Deref  . a:Expr |- "*" a : Expr;          // prefix: dereference
        Repeat . a:Expr |- a "*" : Expr;           // postfix: Kleene star / repeat
        Add    . a:Expr, b:Expr |- a "+" b : Expr;
    },
}
```

### Output

```
warning[PAR03] (Collision): token `*` is both prefix and postfix in category `Expr` -- surprising precedence
  = hint: review whether the intended semantics are correct; the parser disambiguates by context
```

## Resolution

1. **Review precedence semantics.** Verify that the binding power
   assignments for the prefix and postfix uses produce the correct parse
   trees for all relevant inputs. Pay special attention to expressions
   where the token appears adjacent to itself (e.g., `* * x`).

2. **Use distinct tokens.** If the dual use is unintentional, rename one
   operator to use a different token. For example, use `"deref"` for prefix
   dereference and keep `"*"` for postfix repetition.

3. **Split into sub-categories.** Place the prefix and postfix uses in
   different categories to eliminate the collision. For example, `DerefExpr`
   handles prefix `*` and `RepeatExpr` handles postfix `*`.

4. **Accept the collision.** If both uses are intentional and the
   precedence behavior is correct, acknowledge the warning. The parser's
   context-based disambiguation is correct -- the warning exists to flag
   potentially surprising behavior, not an error.

## Hint Explanation

The hint **"review whether the intended semantics are correct; the parser
disambiguates by context"** clarifies:

- **Context-based disambiguation** means the Pratt parser determines whether
  a token is prefix or postfix based on where it appears in the expression.
  At the start of an expression or after an operator, the token is treated as
  prefix. After a complete sub-expression, it is treated as postfix.

- **"Review whether the intended semantics are correct"** is the key action:
  the parser will produce some parse tree, but it may not be the one the
  grammar author expects. The binding power relationship between the prefix
  and postfix forms determines which interpretation "wins" in ambiguous
  positions.

## Related Lints

- [PAR04](PAR04-mixfix-ambiguous-delimiter.md) -- Another form of token
  role collision, where a mixfix delimiter doubles as an infix operator.
- [PAR02](PAR02-unused-bp-level.md) -- BP level gaps may affect the
  relative precedence of colliding prefix and postfix operators.
- [LEX01](../lexer/LEX01-overlapping-token-defs.md) -- Token-level overlap
  across categories is the lexer-side counterpart of this parser-level
  collision.
- [DIS04](../dispatch/DIS04-backtrack-elimination-coverage.md) -- Prefix/
  postfix collisions can reduce backtracking elimination coverage since the
  dispatch point cannot commit until after trying both interpretations.
