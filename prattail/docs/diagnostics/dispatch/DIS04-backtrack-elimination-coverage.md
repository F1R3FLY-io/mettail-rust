# DIS04: backtrack-elimination-coverage

**Severity:** Note
**Category:** dispatch
**Feature Gate:** None

## Description

Reports the percentage of dispatch points in a category that have been made
backtrack-free by the G1 (backtracking elimination) optimization pass. When
a dispatch arm is deterministic, the parser can commit to it without saving
and restoring input position -- it knows from compile-time FIRST set analysis
that the lookahead token uniquely identifies the correct rule. When a dispatch
arm is non-deterministic, the parser must use save/restore to tentatively try
the rule and backtrack if it fails.

This lint fires when coverage is less than 100% and the category has more than
2 rules, reporting both the deterministic count and the remaining
non-deterministic count. It serves as a progress indicator for prefix
disambiguation: higher coverage means faster dispatch.

```
  Category `Expr` backtracking elimination coverage

  ┌──────────────┬───────────────┐
  │ Rule         │ Deterministic │
  ├──────────────┼───────────────┤
  │ parse_Num    │      yes      │  ← committed (no save/restore)
  │ parse_Neg    │      yes      │  ← committed
  │ parse_Paren  │      yes      │  ← committed
  │ parse_Add    │      no       │  ← save/restore required
  │ parse_Sub    │      no       │  ← save/restore required
  └──────────────┴───────────────┘
       3/5 rules (60%) deterministic → DIS04 fires
       2 rules still use save/restore
```

## Trigger Conditions

All of the following must hold:

- A `DecisionTree` exists for the category in the lint context.
- The tree has a non-zero `total_rules` count greater than 2.
- The ratio `deterministic_rules / total_rules` is less than 1.0 (not all
  rules are deterministic).

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: PartialCommit,
    types {
        ![i64] as Expr
    },
    terms {
        Num    . n:Expr |- n : Expr;
        Neg    . a:Expr |- "-" a : Expr;
        Paren  . a:Expr |- "(" a ")" : Expr;
        Add    . a:Expr, b:Expr |- a "+" b : Expr;
        Sub    . a:Expr, b:Expr |- a "-" b : Expr;
    },
}
```

### Output

```
note[DIS04] (PartialCommit): category `Expr`: 3/5 rules (60%) have deterministic dispatch -- remaining 2 rules still use save/restore
  = hint: non-deterministic rules share prefixes; consider left-factoring or multi-token lookahead (B1)
```

## Resolution

1. **Left-factor shared prefixes.** When two rules begin with the same
   token (e.g., both `Neg` and `Sub` use `"-"`), extract the shared prefix
   so the parser can commit after one token and branch later.

2. **Enable multi-token lookahead (B1).** The B1 optimization extends
   lookahead from 1 to k tokens, resolving ambiguities that single-token
   FIRST sets cannot distinguish. This can promote non-deterministic arms
   to deterministic.

3. **Add unique prefix tokens.** If possible, redesign rules so each
   alternative begins with a distinct terminal. For example, use `"neg"`
   instead of reusing `"-"` for the unary prefix operator.

4. **Accept partial coverage.** Some grammars intentionally have overlapping
   prefixes (e.g., `-` as both unary prefix and binary infix). In these
   cases, the parser correctly handles the ambiguity via backtracking, and
   partial coverage is expected.

## Hint Explanation

The hint **"non-deterministic rules share prefixes; consider left-factoring
or multi-token lookahead (B1)"** explains:

- **Shared prefixes** are the root cause: two or more rules begin with the
  same token sequence, so single-token lookahead cannot distinguish them.
  The parser must tentatively try one and backtrack if it fails.

- **Left-factoring** eliminates the shared prefix by parsing it once and
  branching at the first divergent token. This is the classic solution from
  LL parsing theory.

- **Multi-token lookahead (B1)** is a PraTTaIL optimization that extends
  the dispatch decision from 1 token to k tokens of lookahead, enabling
  deterministic dispatch even when single-token FIRST sets overlap.

## Related Lints

- [DIS03](DIS03-decision-tree-depth.md) -- Deep decision trees often
  correlate with low backtracking elimination coverage, since long shared
  prefixes prevent early commitment.
- [DIS05](DIS05-nfa-try-all-set-size.md) -- Non-deterministic dispatch
  points with large candidate sets are the most expensive backtracking
  scenarios.
- [DIS01](DIS01-hot-path-misalignment.md) -- When the hot path is
  non-deterministic, misalignment compounds the cost of failed probes.
