# G10: ambiguous-associativity

**Severity:** Warning
**Category:** Grammar Structure

## Description

Detects operators at the same precedence level (same `left_bp` value in the binding
power table) that have different associativity. In a Pratt parser, associativity is
encoded in the relationship between `left_bp` and `right_bp`:

| Associativity | Encoding |
|---------------|----------|
| Left | `right_bp = left_bp + 1` |
| Right | `right_bp = left_bp` |

When two operators share the same `left_bp` but one is left-associative and the
other is right-associative, the parser's behavior becomes ambiguous for expressions
that mix these operators. For example, if `+` (left) and `=` (right) both have
`left_bp = 4`, then `a + b = c` could parse as either `(a + b) = c` or
`a + (b = c)` depending on which operator the Pratt parser encounters first in the
infix loop -- and the result may not match the grammar author's intent.

This lint warns about such configurations so the grammar author can assign distinct
precedence levels to operators with different associativity, ensuring deterministic
and intentional parse behavior.

## Trigger Conditions

The lint fires when **all** of the following conditions hold for a given category:

1. The category has two or more infix operators registered in the `BindingPowerTable`.
2. At least two of those operators share the same `left_bp` value (i.e., they are at
   the same precedence level).
3. Within that same-`left_bp` group, the operators have different associativity
   values (some `Left`, some `Right`), as determined by
   `InfixOperator::associativity()`.

The check groups operators by `left_bp` and inspects each group independently. A
group with only one operator is skipped. Operators across different categories are
not compared.

## Example

### Grammar

```
language! {
    name: Assign,
    types {
        ![i32] as Expr
    },
    terms {
        // Addition: left-associative (a + b + c = (a + b) + c)
        Add . a:Expr, b:Expr |- a "+" b : Expr ![a + b] step;
        // Subtraction: left-associative, same precedence as addition
        Sub . a:Expr, b:Expr |- a "-" b : Expr ![a - b] step;
        // Assignment: right-associative, but ACCIDENTALLY at same precedence
        Set . a:Expr, b:Expr |- a "=" b : Expr ![b] step right;
        // Multiplication: left-associative, higher precedence
        Mul . a:Expr, b:Expr |- a "*" b : Expr ![a * b] fold;
    }
}
```

In this grammar, `"+"`, `"-"`, and `"="` are all declared at the `step` precedence
tier. `"+"` and `"-"` are left-associative (the default), while `"="` is
right-associative (via the `right` keyword). Since they share the same `left_bp`,
an expression like `a + b = c` has ambiguous associativity.

### Output

```
warning[G10]: same-precedence operators [+, -, =] in category `Expr` (left_bp=3) have different associativity
  = in category `Expr`
  = hint: use explicit precedence levels to separate operators with different associativity
```

## Resolution

To resolve this warning, assign different precedence levels to operators that have
different associativity. PraTTaIL's precedence tiers (`fold`, `step`, and their
ordering) determine `left_bp` values, so you need to ensure that operators with
different associativity land in different tiers.

1. **Separate precedence tiers.** Place the right-associative operator at a different
   (typically lower) precedence level:

   ```
   // Assignment: lowest precedence, right-associative
   Set . a:Expr, b:Expr |- a "=" b : Expr ![b] step right;
   // Addition/subtraction: higher precedence, left-associative
   Add . a:Expr, b:Expr |- a "+" b : Expr ![a + b] fold;
   Sub . a:Expr, b:Expr |- a "-" b : Expr ![a - b] fold;
   // Multiplication: highest precedence
   Mul . a:Expr, b:Expr |- a "*" b : Expr ![a * b] fold;
   ```

   Now `=` has a lower `left_bp` than `+` and `-`, so `a + b = c` unambiguously
   parses as `(a + b) = c`.

2. **Use the same associativity.** If the operators genuinely belong at the same
   precedence level, make them all left-associative or all right-associative:

   ```
   // All left-associative at the same tier
   Add    . a:Expr, b:Expr |- a "+"  b : Expr ![a + b] step;
   Sub    . a:Expr, b:Expr |- a "-"  b : Expr ![a - b] step;
   Assign . a:Expr, b:Expr |- a ":=" b : Expr ![b]     step;
   ```

3. **Introduce intermediate tiers.** For grammars with many operators, use more
   `fold`/`step` tiers to create fine-grained precedence distinctions. Each
   additional tier creates a new `left_bp` level.

## Hint Explanation

> use explicit precedence levels to separate operators with different associativity

The hint advises the grammar author to restructure the rule declarations so that
operators with different associativity are assigned to different precedence tiers.
In PraTTaIL, precedence is determined by the order and tier keyword (`fold` vs
`step`) of infix rule declarations:

- `fold` operators at the same position share a precedence level.
- `step` operators increment the precedence level.
- Within each level, all operators must share the same associativity for the Pratt
  parser to produce deterministic results.

The Pratt parser resolves `a OP1 b OP2 c` by comparing `OP1.right_bp` with
`OP2.left_bp`. When `left_bp` values are equal but associativity differs, the
comparison yields inconsistent results depending on which operator is `OP1` vs
`OP2`:

- `a + b = c`: `+.right_bp (left_bp+1)` vs `=.left_bp` -- if equal, `+` wins
  (left-assoc behavior).
- `a = b + c`: `=.right_bp (left_bp)` vs `+.left_bp` -- if equal, `=` wins
  (right-assoc behavior).

This asymmetry is exactly what the warning flags. The fix is to ensure that each
`left_bp` group has uniform associativity.

## Related Lints

- [G01](./G01-left-recursion.md) -- left-recursive rules interact with the Pratt parser's infix loop; mixed associativity at the same level can compound with left-recursion to produce unexpected parse trees
- [G06](./G06-shadowed-operator.md) -- dual infix/prefix usage of a terminal also affects binding power resolution; G10 focuses on the infix-only dimension of precedence conflicts
