# DIS02: cold-arm-ratio

**Severity:** Note
**Category:** dispatch
**Feature Gate:** None

## Description

Reports when more than 80% of the dispatch arms in a category's WFST action
table are "cold" -- that is, they have a weight of 1.0 or greater, indicating
they are rarely the correct parse alternative for a given input token. A high
cold-arm ratio means that the vast majority of dispatch branches are unlikely
to be taken, and the parser spends most of its time probing a single hot arm
while the remaining arms occupy instruction cache space without contributing
to throughput.

In the tropical semiring used by PraTTaIL's prediction WFST, lower weights
correspond to higher probability. A weight of 0.0 is the "free" path (most
likely), while weights >= 1.0 represent increasingly unlikely alternatives.
When a category has, say, 10 dispatch arms and 9 of them have weight >= 1.0,
90% of the generated match arms are cold code that pollutes the instruction
cache.

```
  Category `Expr` dispatch table
  ┌──────────────┬────────┬────────┐
  │ Action       │ Weight │ Status │
  ├──────────────┼────────┼────────┤
  │ parse_Num    │  0.10  │  HOT   │
  │ parse_Add    │  1.20  │  cold  │
  │ parse_Mul    │  1.50  │  cold  │
  │ parse_Sub    │  1.80  │  cold  │
  │ parse_Div    │  2.00  │  cold  │
  │ parse_Mod    │  2.30  │  cold  │
  │ parse_Pow    │  2.50  │  cold  │
  │ parse_Neg    │  3.00  │  cold  │
  │ parse_Abs    │  3.50  │  cold  │
  │ parse_Sqrt   │  4.00  │  cold  │
  └──────────────┴────────┴────────┘
       9/10 arms (90%) are cold → DIS02 fires
```

The optimization A2 (hot/cold splitting) can restructure the generated code
so that cold arms are placed out-of-line, improving instruction cache
utilization on the hot path.

## Trigger Conditions

All of the following must hold:

- A `PredictionWfst` exists for the category with at least 3 actions.
- More than 80% of actions have `weight.value() >= 1.0`.

One diagnostic is emitted per affected category.

## Example

### Grammar

```rust
language! {
    name: BigExpr,
    types {
        ![i64] as Expr
    },
    terms {
        Num   . n:Expr |- n : Expr;
        Add   . a:Expr, b:Expr |- a "+" b : Expr;
        Sub   . a:Expr, b:Expr |- a "-" b : Expr;
        Mul   . a:Expr, b:Expr |- a "*" b : Expr;
        Div   . a:Expr, b:Expr |- a "/" b : Expr;
        Mod   . a:Expr, b:Expr |- a "%" b : Expr;
        Pow   . a:Expr, b:Expr |- a "^" b : Expr;
        Neg   . a:Expr |- "-" a : Expr;
        Abs   . a:Expr |- "|" a "|" : Expr;
    },
}
```

### Output

```
note[DIS02] (BigExpr): category `Expr`: 8/9 dispatch arms (89%) are cold (weight >= 1.0)
  = hint: most arms are rarely taken -- hot/cold splitting (A2) may improve i-cache utilization
```

## Resolution

1. **Enable hot/cold splitting (A2).** The codegen optimization A2
   restructures dispatch code so that cold arms are placed in a separate
   function or code section, keeping the hot path compact and cache-friendly.

2. **Reduce the number of alternatives.** If many rules exist for a
   category but most are rarely used, consider refactoring the grammar to
   group related alternatives under a sub-category. This reduces the fan-out
   of any single dispatch point.

3. **Retrain WFST weights.** If the weight distribution seems wrong (e.g.,
   all weights are near 1.0 when some alternatives should be common), ensure
   the training corpus is representative of real-world inputs.

4. **Accept the ratio.** For grammars where most alternatives genuinely are
   rare (e.g., a language with one dominant expression form and many exotic
   operators), a high cold ratio is expected and harmless.

## Hint Explanation

The hint **"most arms are rarely taken -- hot/cold splitting (A2) may improve
i-cache utilization"** explains that:

- **Hot/cold splitting** is a code layout optimization (documented as A2 in
  the codegen optimization catalog) that separates frequently-executed code
  from rarely-executed code. The CPU instruction cache benefits because the
  hot path fits in fewer cache lines.

- **i-cache utilization** refers to the efficiency of the CPU's instruction
  cache. When cold code is interleaved with hot code, cache lines are wasted
  on instructions that are almost never executed.

## Related Lints

- [DIS01](DIS01-hot-path-misalignment.md) -- If the hot path is also
  misaligned, the one remaining hot arm may not even be tried first,
  compounding the cold-arm problem.
- [DIS04](DIS04-backtrack-elimination-coverage.md) -- Cold arms that also
  require save/restore backtracking are doubly expensive.
- [DIS05](DIS05-nfa-try-all-set-size.md) -- Large ambiguous sets combined
  with many cold arms indicate poor prefix disambiguation overall.
