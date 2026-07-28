# G10: mixed-associativity-level

**Severity:** Note
**Category:** Grammar Structure

## Description

Reports a precedence **level** that holds operators of both associativities — at least one
right-associative operator beside at least one left-associative one.

This is **legal, unambiguous, and sometimes mandatory.** It is reported because the reading
it produces is easy to misread, not because anything is wrong.

### The encoding

In a Pratt parser, precedence and associativity are carried by one pair of numbers. For an
operator on level `$p$`:

| Associativity | `$(\ell, r)$` | `$\min(\ell, r)$` |
|---|---|---|
| Left  | `$(p,\; p+1)$` | `$p$` |
| Right | `$(p+1,\; p)$` | `$p$` |

Both encodings have the same **minimum**, which is the level; they differ only in the
**order** of the pair, which is the associativity. Precedence and associativity are
therefore independent, and one level may hold operators of both kinds.

That independence is not a curiosity. Rholang's normative grammar
(`rholang-tree-sitter/grammar.js`) declares

```js
matches: $ => prec.right(6, seq($._proc, 'matches', $._proc)),
eq:      $ => prec.left(6,  seq($._proc, '==',      $._proc)),
neq:     $ => prec.left(6,  seq($._proc, '!=',      $._proc)),
```

— three operators, one level, two associativities. A grammar formalism that attached one
associativity to each level could not model Rholang, so MeTTaIL's cannot be one.

### Why it is not ambiguous

In an LR parser, `%left`/`%right` are properties of a precedence *level*, and a
disagreement inside one level is a genuine shift/reduce conflict. A Pratt parser has no
such notion: the `$(\ell, r)$` pair determines exactly one reading for every input. There
is nothing for the parser to be ambiguous about.

### What is worth knowing

A chain that mixes the two nests to the **right in both directions**. Let level `$p$` hold
left-associative `==` and right-associative `matches`.

- `a == b matches c` — `==` is absorbed, then parses its right operand at floor `$p+1$`.
  There it meets `matches` with `$\ell = p+1$`, and `$p+1 \ge p+1$` holds, so `matches` is
  absorbed **into `==`'s right operand**: `a == (b matches c)`.
- `a matches b == c` — `matches` is absorbed, then parses its right operand at floor `$p$`.
  There it meets `==` with `$\ell = p$`, and `$p \ge p$` holds, so `==` is absorbed into
  `matches`'s right operand: `a matches (b == c)`.

The right-associative operator's `$\ell = p+1$` is what clears the floor its
left-associative neighbour installs. If that is the intended reading — as it is in
Rholang — nothing needs to change.

## Trigger Conditions

The lint fires when **all** of the following hold for a category:

1. Two or more **non-postfix** infix operators share a precedence level, where the level
   is `$\min(\ell, r)$`. Postfix operators are excluded: they consume no right operand, so
   they have no associativity to disagree about, and their unused `right_bp` of `0` would
   otherwise collapse every one of them onto a spurious level `0`.
2. Within that level, `InfixOperator::associativity()` is not constant.

Levels are visited in ascending order so that the diagnostic stream is deterministic and
diffable.

> ### Historical note: this lint could not fire before 2026-07-28
>
> G10 previously grouped operators by `left_bp` rather than by level. That predicate was
> unsatisfiable by construction. Levels begin at 2 and advance by 2, so every level is
> **even**; a left-associative operator therefore has an even `$\ell = p$` and a
> right-associative one an odd `$\ell = p+1$`. Two operators sharing a `left_bp` share its
> parity, hence share their associativity, hence never differ.
>
> The lint's two unit tests hand-constructed `left_bp: 2` on both operators with differing
> `right_bp` — a shape `analyze_binding_powers` cannot emit, since a right-associative
> operator at level `$p$` is `$(p+1,\, p)$` and never `$(p,\, p-1)$`. The suite reported a
> dead lint as covered. Both tests now build their tables through the real assigner
> (`prattail/src/lint/tests.rs`), so the coverage is real.
>
> Re-keying to the level made the lint reachable — and its first true positive is Rholang's
> level 6, which is **correct**. That is why the severity moved from `Warning` to `Note`
> and the name from `ambiguous-associativity` to `mixed-associativity-level`: the previous
> wording alleged a defect where the normative grammar mandates the shape.

## Example

### Grammar

```
language! {
    name: Relations,
    types {
        ![bool] as Expr
    },
    terms {
        // Equality: left-associative (the default), opens the level.
        Eq      . a:Expr, b:Expr |- a "=="      b : Expr ![a == b] step;
        // Inequality: joins that level with `same`, also left-associative.
        Ne      . a:Expr, b:Expr |- a "!="      b : Expr ![a != b] step same;
        // Pattern match: joins the SAME level, but right-associative.
        Matches . a:Expr, b:Expr |- a "matches" b : Expr ![a == b] step same right;
    }
}
```

`same` places all three on one level; `right` on `Matches` alone gives that level two
associativities.

### Output

```
note[G10]: precedence level 2 of category `Expr` holds both right-associative [matches] and left-associative [!=, ==] operators
  = in category `Expr`
  = hint: this is legal and unambiguous — every input has one reading. Note that a chain
    mixing them nests to the RIGHT in both directions, because a right-associative
    operator's left binding power exceeds the level. Declare the operators on separate
    levels if that is not intended; keep them together if it is (Rholang's `matches`
    shares level 2 with `==` and `!=` by design).
```

## Resolution

There is nothing to resolve unless the levelling was unintentional. Two options:

1. **Keep them together.** If the operators genuinely belong at one precedence level — as
   `matches`, `==` and `!=` do in Rholang — leave the grammar alone. The note is
   informational.

2. **Separate the levels.** Drop the `same` annotation from the operator that should bind
   differently. Declaration order is precedence order, and an unannotated rule opens the
   next, tighter level:

   ```
   // `matches` on its own, LOOSER level (declared first).
   Matches . a:Expr, b:Expr |- a "matches" b : Expr ![a == b] step right;
   // Equality on a tighter level of its own.
   Eq      . a:Expr, b:Expr |- a "=="      b : Expr ![a == b] step;
   Ne      . a:Expr, b:Expr |- a "!="      b : Expr ![a != b] step same;
   ```

   Now `a matches b == c` reads `a matches (b == c)` because `==` binds tighter, rather
   than because `==` cleared `matches`'s floor.

> **Note on annotations.** Precedence comes from **declaration order** plus the `same`
> annotation. It does **not** come from the evaluation mode: `fold` and `step` select how a
> rule's native body is run and have no effect on binding power whatsoever. An earlier
> revision of this page claimed otherwise.

## Related Lints

- [G01](./G01-left-recursion.md) — left-recursive rules interact with the Pratt parser's
  infix loop; a mixed-associativity level compounds with left-recursion to produce parse
  trees that are correct but surprising.
- [G06](./G06-shadowed-operator.md) — dual infix/prefix usage of a terminal also affects
  binding-power resolution; G10 covers the infix-only dimension.

## See also

- `prattail/docs/design/binding-powers/02-implicit-deduction.md` — the assignment algorithm
  and the level formulas.
- `prattail/docs/design/disambiguation/03-operator-precedence.md` — the worked parse trace.
- `docs/languages/calculator.md` §8 — the same material for a concrete language.
