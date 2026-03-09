# LEX05: float-integer-ambiguity

**Severity:** Note
**Category:** lexer
**Feature Gate:** None

## Description

Detects when the grammar defines both integer and float native types (e.g.,
`i32`/`i64` and `f32`/`f64`) across its categories, which creates a lexical
ambiguity for numeric literals. The string `"123"` is a valid literal for
both an integer and a float category. PraTTaIL's lexer resolves this by
applying **integer-first priority** under longest-match semantics: a bare
digit sequence like `123` always lexes as an integer token, while `123.0`
(with an explicit decimal point) lexes as a float token.

This ambiguity is a common source of confusion in languages with multiple
numeric types. The lint ensures the grammar author is aware of the lexing
convention and can write numeric literals accordingly.

```
  Numeric literal lexing rules

  Input      Token Type    Reason
  ─────      ──────────    ──────
  "123"      Integer       No decimal point → integer-first priority
  "123.0"    Float         Decimal point present → float
  "123."     Float         Trailing dot → float (if grammar allows)
  ".5"       Float         Leading dot → float (if grammar allows)
  "1e10"     Float         Scientific notation → float (if grammar allows)
  "0xFF"     Integer       Hex prefix → integer

  Note: `123` is NEVER a float literal. Use `123.0` explicitly.
```

## Trigger Conditions

All of the following must hold:

- At least one category has a `native_type` of `"i32"` or `"i64"`.
- At least one (possibly different) category has a `native_type` of `"f32"`
  or `"f64"`.

One diagnostic is emitted per grammar (regardless of how many integer/float
category pairs exist).

## Example

### Grammar

```rust
language! {
    name: MixedMath,
    types {
        ![i64] as IntExpr,
        ![f64] as FloatExpr
    },
    terms {
        IntLit    . n:IntExpr |- n : IntExpr;
        FloatLit  . x:FloatExpr |- x : FloatExpr;
        IntAdd    . a:IntExpr, b:IntExpr |- a "+" b : IntExpr;
        FloatAdd  . a:FloatExpr, b:FloatExpr |- a "+." b : FloatExpr;
    },
}
```

### Output

```
note[LEX05] (MixedMath): both integer and float native types present -- `123` always lexes as Integer, never Float
  = hint: use `123.0` for float literals; the lexer uses longest-match with integer-first priority
```

## Resolution

1. **Use explicit float literals.** Always write `123.0` instead of `123`
   when a float value is intended. The decimal point disambiguates the
   literal at the lexer level.

2. **Document the convention.** If the grammar is user-facing, document that
   bare integers like `123` are always integer-typed and that float literals
   require a decimal point.

3. **Add explicit cast rules.** If implicit integer-to-float promotion is
   desired, add a cast rule (e.g., `IntToFloat . n:IntExpr |- n : FloatExpr`)
   that converts integer literals to float values at the AST level.

4. **Use a single numeric type.** If the distinction between integer and
   float is not semantically important, use a single numeric category (e.g.,
   `Number` with `f64` native type) that handles both forms.

## Hint Explanation

The hint **"use `123.0` for float literals; the lexer uses longest-match
with integer-first priority"** conveys:

- **`123.0` for float literals** is the explicit form that the lexer
  unambiguously recognizes as a float. The decimal point `.0` suffix forces
  the lexer to choose the float token type.

- **Integer-first priority** means that when the lexer encounters a bare
  digit sequence, it produces an integer token. This is a deterministic
  rule, not a heuristic -- it applies in all cases where the digit sequence
  is not followed by a decimal point, exponent marker, or other float-
  indicating suffix.

## Related Lints

- [LEX01](LEX01-overlapping-token-defs.md) -- Float/integer ambiguity is a
  specific case of the broader token overlap problem.
- [LEX02](LEX02-unreachable-token-pattern.md) -- The integer pattern can be
  seen as "shadowing" the float pattern for bare digit sequences.
