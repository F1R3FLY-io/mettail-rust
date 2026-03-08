# V04: wta-hot-path

**Severity:** Note
**Category:** analysis/automata
**Feature Gate:** `tree-automata`

## Description

Identifies **frequently weighted term patterns** in the grammar's weighted tree
automaton (WTA) -- term shapes that carry disproportionately high accumulated
weight, making them candidates for **specialization**. Specialization means
generating optimized, pattern-specific code paths for these hot patterns instead
of relying on the general-purpose bottom-up state assignment.

In a weighted tree automaton A = (Q, Sigma, Delta, F, K), each transition
(q₁, ..., q_k, f, q) in Delta carries a weight w in semiring K. The weight
of a run (a complete bottom-up state assignment for a tree) is the semiring
product of all transition weights along the run. When using the tropical
semiring (min, +, inf, 0), the weight represents the cost of the cheapest
derivation for that tree shape.

A **hot path** is a sequence of transitions from leaves to root that
collectively accounts for a significant fraction of the total derivation weight
across the grammar. Hot paths indicate that certain AST shapes dominate the
grammar's structural landscape -- they appear frequently, have low cost, or
both.

```
  WTA Weight Distribution
  ═══════════════════════

  Transition weights (TropicalWeight):

  Num(.)         -> q_num    [w = 0.0]    (free)
  Add(q_num, q_num) -> q_expr  [w = 1.0]
  Mul(q_num, q_num) -> q_expr  [w = 1.0]
  Add(q_expr, q_num) -> q_expr [w = 1.5]    hot path
  Add(q_expr, q_expr) -> q_expr [w = 2.0]   hot path
  Neg(q_expr)    -> q_expr   [w = 0.5]

  Hot path: Add -> q_expr (appears in 73% of derivations)

  ┌─────────────────────────────────────────────┐
  │  Weight distribution by pattern:            │
  │                                             │
  │  Add(q_expr, q_num)  ████████████████ 42%   │  <- V04 fires
  │  Add(q_expr, q_expr) ████████████    31%    │  <- V04 fires
  │  Mul(q_num, q_num)   ████             11%   │
  │  Neg(q_expr)         ███               8%   │
  │  Add(q_num, q_num)   ██                5%   │
  │  Mul(q_expr, q_num)  █                 3%   │
  │                                             │
  └─────────────────────────────────────────────┘
```

The hot-path analysis aggregates transition weights across all possible
derivations and identifies patterns whose cumulative weight exceeds a threshold.
These patterns are reported as specialization candidates because:

1. **Inlining the transition** eliminates the state-lookup overhead for the
   most common tree shapes.
2. **Type-specialized codegen** can avoid boxing, dynamic dispatch, or
   runtime arity checks for known patterns.
3. **Branch prediction** benefits from separating hot paths from cold paths in
   the generated code.

## Trigger Conditions

All of the following must hold:

- The `tree-automata` feature is enabled at compile time.
- A `WtaAnalysis` result is available in the lint context.
- The `hot_paths` list contains at least one entry (at least one term pattern
  exceeds the hot-path weight threshold).

One V04 diagnostic is emitted per hot-path term pattern.

## Example

### Grammar

```rust
language! {
    name: ExprLang,
    types {
        ![i32] as Expr
    },
    terms {
        Num  . |- <int> : Expr;
        Add  . a:Expr, b:Expr |- a "+" b : Expr ![a + b] fold;
        Sub  . a:Expr, b:Expr |- a "-" b : Expr ![a - b] fold;
        Mul  . a:Expr, b:Expr |- a "*" b : Expr ![a * b] fold;
        Neg  . a:Expr |- "-" a : Expr ![{ -a }];
        Call . f:Expr, x:Expr |- f "(" x ")" : Expr;

        // In typical arithmetic expressions, Add(Expr, Num) is by far
        // the most common pattern: "x + 1", "sum + n", etc.
        // The WTA assigns it the highest cumulative weight.
    },
}
```

### Output

```
note[V04] (ExprLang): frequently weighted term pattern: Add->Expr — specialization candidate
```

## Resolution

No action is required. V04 is an informational note highlighting optimization
opportunities. The grammar is correct as-is; V04 simply identifies where the
most performance benefit can be gained from specialization.

If the grammar author or the pipeline's cost-benefit analysis decides to act on
V04:

1. **Enable pattern specialization.** If the pipeline supports it, mark the
   hot-path pattern for specialized code generation. This produces a fast-path
   handler for the common case and falls back to the generic handler for other
   patterns.

2. **Review structural assumptions.** If a pattern is unexpectedly hot (e.g.,
   `Neg(Neg(Expr))` dominates when it should be rare), this may indicate a
   grammar design issue -- perhaps double-negation elimination should be added
   as a rewrite rule (see [T01](../trs/T01-non-joinable-critical-pair.md)).

3. **Use as profiling guidance.** The hot-path list serves as a profiling guide
   for downstream passes (type checking, optimization, code generation). Focus
   optimization effort on the patterns V04 identifies.

## Hint Explanation

This lint has no hint. The information is self-contained: the reported pattern
is a specialization candidate based on its weight distribution in the WTA.

## Related Lints

- [V03](V03-wta-unrecognized-term.md) -- The complementary diagnostic: V03
  finds terms the WTA does not recognize at all, while V04 finds terms the WTA
  recognizes disproportionately often. Together, they provide a complete picture
  of the WTA's coverage and weight distribution.
- [V01](V01-vpa-determinizable.md) -- VPA analysis. Orthogonal to WTA hot-path
  detection.
- [V02](V02-vpa-alphabet-mismatch.md) -- VPA alphabet classification.
  Orthogonal to WTA.
- [D08](../../decision-tree/D08-optimization-suggestion.md) -- Decision tree
  optimization suggestions. V04 hot paths may correlate with high-traffic trie
  paths in the decision tree.
- [P04](../../performance/P04-many-alternatives.md) -- Performance lint for
  many alternatives. Hot paths in V04 may correspond to the most frequently
  exercised alternatives in P04.
