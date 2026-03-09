# DIS05: nfa-try-all-set-size

**Severity:** Warning
**Category:** dispatch
**Feature Gate:** None

## Description

Warns when the number of ambiguous dispatch points in a category's decision
tree exceeds a threshold of 5. An ambiguous dispatch point is a node in the
PathMap-based decision tree where the prefix tokens seen so far do not uniquely
identify a single rule -- the parser must "try all" remaining candidates via
NFA-style exploration, attempting each one and backtracking on failure.

Each ambiguous node represents a set of candidate rules that share the same
prefix up to that point. When the number of such nodes is high, the parser
faces many points where it cannot make a deterministic choice. This leads to
increased backtracking, wasted work from failed parse attempts, and poor
worst-case latency. The problem is especially acute when the candidate sets
are large, since each failed attempt incurs the cost of partial parsing plus
state restoration.

```
  Decision tree for category `Expr` with 8 ambiguous nodes

  ┌─ "("
  │  ├─ IDENT → {Tuple, FnCall, Paren, Cast, TypeAscription}  ← AMBIGUOUS
  │  ├─ NUM   → {Tuple, Paren}                                 ← AMBIGUOUS
  │  └─ "("   → {Tuple, Paren, Nested}                         ← AMBIGUOUS
  ├─ IDENT
  │  ├─ "("   → {FnCall, Subscript}                            ← AMBIGUOUS
  │  ├─ "["   → {Index, Slice}                                 ← AMBIGUOUS
  │  └─ "."   → {FieldAccess, MethodCall}                      ← AMBIGUOUS
  ├─ NUM      → {IntLit, FloatLit}                              ← AMBIGUOUS
  └─ "\""     → {StringLit, RawString}                          ← AMBIGUOUS

  8 ambiguous nodes > threshold 5 → DIS05 fires
```

## Trigger Conditions

All of the following must hold:

- A `DecisionTree` exists for the category in the lint context.
- The tree's `stats.ambiguous_nodes` count exceeds 5.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: AmbigExpr,
    types {
        ![String] as Expr
    },
    terms {
        Num      . n:Expr |- n : Expr;
        Ident    . s:Expr |- s : Expr;
        Paren    . a:Expr |- "(" a ")" : Expr;
        Tuple    . a:Expr, b:Expr |- "(" a "," b ")" : Expr;
        FnCall   . f:Expr, a:Expr |- f "(" a ")" : Expr;
        Index    . a:Expr, i:Expr |- a "[" i "]" : Expr;
        Slice    . a:Expr, b:Expr |- a "[" b ":" "]" : Expr;
        Cast     . a:Expr, t:Expr |- "(" a "as" t ")" : Expr;
        Method   . a:Expr, m:Expr |- a "." m "(" ")" : Expr;
        Field    . a:Expr, f:Expr |- a "." f : Expr;
    },
}
```

### Output

```
warning[DIS05] (AmbigExpr): category `Expr` has 7 ambiguous dispatch points (threshold: 5) -- poor prefix disambiguation
  = hint: add unique prefix tokens to rules or enable multi-token lookahead (B1)
```

## Resolution

1. **Add unique prefix tokens.** Give each rule a distinct leading terminal
   so the decision tree can commit after one token. For example, use
   `"tuple("` instead of sharing `"("` between `Paren`, `Tuple`, and
   `Cast`.

2. **Enable multi-token lookahead (B1).** The B1 optimization extends
   prefix analysis to k tokens, resolving ambiguities that single-token
   FIRST sets cannot. For example, `"(" Expr ","` unambiguously identifies
   a `Tuple` while `"(" Expr ")"` identifies `Paren`.

3. **Left-factor overlapping prefixes.** Extract the shared prefix into a
   single rule, then branch at the distinguishing token. For example, parse
   `"(" Expr` first, then dispatch on `","` (Tuple), `"as"` (Cast), or
   `")"` (Paren).

4. **Use intermediate categories.** Break the ambiguous category into
   sub-categories with non-overlapping FIRST sets. For example, separate
   `PostfixExpr` (Index, Slice, Method, Field) from `PrimaryExpr` (Num,
   Ident, Paren, Tuple).

5. **Accept the ambiguity.** Some grammars inherently have overlapping
   prefixes and the NFA try-all fallback is correct (just slower). If
   performance is acceptable, the warning can be acknowledged.

## Hint Explanation

The hint **"add unique prefix tokens to rules or enable multi-token lookahead
(B1)"** recommends two orthogonal strategies:

- **Unique prefix tokens** is the most direct fix: if every rule in a
  category begins with a different terminal, the decision tree has zero
  ambiguous nodes. This requires grammar-level changes.

- **Multi-token lookahead (B1)** is a compiler optimization that
  automatically extends the decision tree to consider multiple tokens of
  prefix. It can resolve ambiguities without grammar changes, at the cost
  of a deeper (but deterministic) decision tree.

## Related Lints

- [DIS03](DIS03-decision-tree-depth.md) -- Large ambiguous sets at deep
  tree levels indicate that both depth and breadth are problematic.
- [DIS04](DIS04-backtrack-elimination-coverage.md) -- Ambiguous nodes are
  the non-deterministic dispatch points that prevent full backtracking
  elimination.
- [DIS02](DIS02-cold-arm-ratio.md) -- If the ambiguous candidate sets
  contain mostly cold arms, the parser wastes time trying rules that almost
  never succeed.
- [LEX01](../lexer/LEX01-overlapping-token-defs.md) -- Token-level
  ambiguity can cause the same input to lex differently, which in turn
  creates decision tree ambiguities at the parser level.
