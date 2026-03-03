# G06: shadowed-operator

**Severity:** Note
**Category:** Grammar Structure

## Description

Detects terminals that appear in both the infix operator set (binding power table)
and the FIRST items of unary prefix rules within the same category. This overlap
means the parser must distinguish between the infix and prefix uses of the same
token based on syntactic position (whether a left-hand operand has already been
parsed).

This is intentional by design: PraTTaIL assigns `prefix_bp = max_infix_bp + 2` to
all unary prefix operators so that prefix binding always wins over infix binding
when the parser is in prefix position. The consequence is that expressions like
`-5!` parse as `-(5!)` rather than `(-5)!`, because the postfix `!` binds tighter
than infix `-`, but the prefix `-` binds tighter than everything when it leads a
sub-expression.

This lint is informational only (severity Note). No action is required. It exists
to make the dual usage explicit in the diagnostic output so grammar authors are
aware of the overlap and the binding power resolution strategy.

## Trigger Conditions

The lint fires when **all** of the following conditions hold for a given category:

1. The category has at least one infix operator registered in the `BindingPowerTable`
   (i.e., a rule with syntax `a OP b` classified as infix by PraTTaIL).
2. The category has at least one non-infix, non-variable, non-literal rule whose
   FIRST items include a `FirstItem::Terminal(t)`.
3. The terminal `t` from condition (2) also appears as the `terminal` field of an
   infix operator from condition (1).

The check is per-category: a terminal used as infix in `Int` and prefix in `Float`
does **not** trigger this lint. Both uses must occur within the same category.

## Example

### Grammar

```
language! {
    name: Calc,
    types {
        ![i32] as Int
    },
    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
        Neg    . a:Int        |- "-" a   : Int ![(-a)]   fold;
        Fact   . a:Int        |- a "!"   : Int ![{ (1..=a.max(0)).product::<i32>() }] step;
    }
}
```

Here, `"-"` is used as both the binary infix operator (in `SubInt`) and the unary
prefix operator (in `Neg`). The binding power hierarchy ensures:

- `-5!` parses as `-(5!)` because postfix `!` has `postfix_bp > max_non_postfix_bp`
  and prefix `-` has `prefix_bp = max_infix_bp + 2`, which sits between the two.
- `3 - -5` parses as `3 - (-5)` because the second `-` is in prefix position.

### Output

```
note[G06]: operator `-` is both infix and prefix in category `Int`
  = in category `Int`
  = hint: this is intentional — prefix_bp = max_infix_bp + 2, so `-5!` = `-(5!)`
```

## Resolution

No resolution is required. This is an informational note confirming that the grammar
has a dual-use operator, which is a well-supported and common pattern (e.g., unary
minus). PraTTaIL handles this automatically via the binding power hierarchy:

| Role | Binding Power |
|------|---------------|
| Infix operators | Assigned by `fold`/`step` precedence tiers |
| Unary prefix operators | `max_infix_bp + 2` |
| Postfix operators | `max_non_postfix_bp + 4+` |

If the dual usage is unintentional and you want the terminal to serve only one role:

1. **Remove the infix rule** to make the terminal prefix-only.
2. **Remove the prefix rule** to make the terminal infix-only.
3. **Rename one terminal** (e.g., use `"neg"` for prefix negation instead of `"-"`)
   to eliminate the overlap entirely.

## Hint Explanation

> this is intentional -- prefix_bp = max_infix_bp + 2, so `-5!` = `-(5!)`

The hint reassures the grammar author that the shadowing is by design. The formula
`prefix_bp = max_infix_bp + 2` means that when the Pratt parser encounters a token
like `-` in prefix position, it binds more tightly than any infix operator in the
same category. This ensures that `-5 + 3` parses as `(-5) + 3`, not `-(5 + 3)`.

The example `-(5!)` illustrates the full three-tier binding power hierarchy: postfix
`!` binds tightest to its operand `5`, then prefix `-` applies to the result `5!`,
and finally any surrounding infix operators bind last.

## Related Lints

- [G01](./G01-left-recursion.md) -- left-recursive rules that overlap with infix operator dispatch
- [G03](./G03-ambiguous-prefix.md) -- multiple prefix rules sharing the same first terminal, which can compound with dual infix/prefix usage
- [G10](./G10-ambiguous-associativity.md) -- same-precedence operators with mixed associativity, which interacts with how prefix operators are resolved at parse time
