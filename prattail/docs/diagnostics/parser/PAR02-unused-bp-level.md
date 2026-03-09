# PAR02: unused-bp-level

**Severity:** Note
**Category:** parser
**Feature Gate:** None

## Description

Reports when the binding power (BP) table has significant gaps between
assigned levels -- that is, integer BP values in the range [min_bp, max_bp]
that have no operators assigned to them. A BP level is "used" if at least one
operator's `left_bp` or `right_bp` equals that value. A gap indicates a BP
level that exists in the numeric range but has no operator occupying it.

Gaps in the BP table are not incorrect, but they make the table wider than
necessary. In the generated Pratt parser, BP values are compared numerically
to determine precedence. A wider range with gaps means the match arms or
comparison chains span a larger numeric space without additional semantic
content.

This lint fires only when more than 3 gaps exist in a table with more than 6
total levels, to avoid flagging small grammars where a few gaps are natural.

```
  Binding power table (range [1, 12])

  BP    Operators
  ──    ─────────
   1    (none)         ← gap
   2    ||
   3    (none)         ← gap
   4    &&
   5    (none)         ← gap
   6    ==, !=
   7    (none)         ← gap
   8    <, >, <=, >=
   9    (none)         ← gap
  10    +, -
  11    (none)         ← gap
  12    *, /, %

  6 gaps out of 12 levels → PAR02 fires
  (could be compacted to [1, 6] with no gaps)
```

## Trigger Conditions

All of the following must hold:

- The BP table is non-empty (at least one operator is defined).
- The number of unused levels (total_levels - used_levels) exceeds 3.
- The total number of levels (max_bp - min_bp + 1) exceeds 6.

One diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: GappyPrec,
    types {
        ![i64] as Expr
    },
    terms {
        Num . n:Expr |- n : Expr;
        // BP 2
        Or  . a:Expr, b:Expr |- a "||" b : Expr;
        // BP 5 (gap at 3, 4)
        And . a:Expr, b:Expr |- a "&&" b : Expr;
        // BP 8 (gap at 6, 7)
        Add . a:Expr, b:Expr |- a "+" b : Expr;
        // BP 12 (gap at 9, 10, 11)
        Mul . a:Expr, b:Expr |- a "*" b : Expr;
    },
}
```

### Output

```
note[PAR02] (GappyPrec): BP range [2, 12] has 7 unused levels out of 11 -- BP table wider than necessary
  = hint: consider compacting BP levels to reduce match arm range
```

## Resolution

1. **Compact BP levels.** Reassign operator binding powers to use
   consecutive values. In the example above, remap `||` to BP 1, `&&` to
   BP 2, `+` to BP 3, and `*` to BP 4. This produces a compact table with
   no gaps.

2. **Use PraTTaIL's auto-assignment.** If the grammar uses explicit BP
   values, consider switching to PraTTaIL's automatic BP assignment, which
   packs levels tightly based on declared precedence order.

3. **Reserve gaps intentionally.** If gaps are left for future operators
   (e.g., reserving BP 6-7 for comparison operators to be added later),
   the lint can be acknowledged. The gaps have no runtime cost beyond
   slightly wider numeric ranges in comparison operations.

4. **Ignore for small tables.** The lint only fires when there are more
   than 3 gaps in a table with more than 6 levels, so small grammars are
   already excluded.

## Hint Explanation

The hint **"consider compacting BP levels to reduce match arm range"**
suggests:

- **Compacting BP levels** means renumbering operator binding powers to
  eliminate gaps. This produces a denser numeric range, which can slightly
  improve generated code by reducing the range of values in match arms
  and comparison chains.

- **Match arm range** refers to the Pratt parser's generated code, which
  compares the current BP against operator BPs to decide whether to continue
  parsing. A smaller range may enable the compiler to generate more
  efficient comparison code (e.g., table lookups instead of chains).

## Related Lints

- [PAR01](PAR01-deep-rd-chain.md) -- Deep RD chains often arise from using
  separate categories for precedence levels. Compacting BP levels and using
  Pratt parsing within a single category can eliminate both issues.
- [PAR03](PAR03-postfix-prefix-collision.md) -- BP level assignment affects
  how prefix and postfix operators interact. Compacting levels may change
  the relative precedence of colliding operators.
