# C04: wide-cross-overlap

**Severity:** Note
**Category:** Cross-Category

## Description

Detects pairs of categories whose FIRST sets (the set of tokens that can legally begin a parse of that category) overlap by 80% or more of the smaller set, with at least 2 overlapping tokens. High FIRST-set overlap between two categories means that when the parser encounters one of the shared tokens during cross-category dispatch, it cannot determine which category to parse without save/restore backtracking: it must speculatively try one category, and if that fails, restore the lexer position and try the other.

This backtracking is correct but expensive. Each save/restore cycle captures and restores the full lexer state (cursor position, line/column tracking, buffered tokens). When the overlap ratio approaches 100%, almost every token in the grammar triggers this two-attempt dispatch pattern, degrading parse throughput proportionally to the frequency of cross-category calls.

The overlap ratio is computed as `|FIRST(A) intersect FIRST(B)| / min(|FIRST(A)|, |FIRST(B)|)`, measured against the smaller set to avoid penalizing categories that happen to have many unique tokens alongside the shared ones.

## Trigger Conditions

A note is emitted when **all** of the following hold for a pair of categories `(A, B)`:

1. Both `FIRST(A)` and `FIRST(B)` are non-empty.
2. The intersection `FIRST(A) intersect FIRST(B)` contains at least 2 tokens (`overlap_count >= 2`).
3. The overlap ratio `overlap_count / min(|FIRST(A)|, |FIRST(B)|)` is >= 0.8 (80%).

Each unordered pair `{A, B}` is checked exactly once (the iteration uses `i < j` over the sorted category list). If a grammar has N categories, at most N*(N-1)/2 pairs are checked.

## Example

### Grammar

```
language! {
    name: RhoPiLike,
    types {
        ![i32] as Int
        ![String] as Str
        ![()] as Proc
        ![bool] as Bool
    },
    terms {
        // Int rules
        NumLit  . |- @integer : Int;
        IntVar  . |- @ident : Int;
        Neg     . a:Int |- "-" a : Int fold;
        Add     . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        IntPar  . a:Int |- "(" a ")" : Int step;

        // Proc rules -- note significant overlap with Int FIRST tokens
        PVar    . |- @ident : Proc;
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;
        PPar    . a:Proc |- "(" a ")" : Proc step;
        PNeg    . a:Proc |- "-" a : Proc step;
        PNum    . |- @integer : Proc;

        // String rules
        StrLit  . |- @string : Str;

        // Bool rules
        BTrue   . |- "true" : Bool;
        BFalse  . |- "false" : Bool;

        // Casts
        CastIntToProc . a:Int |- a : Proc step;
    },
}
```

In this grammar:
- `FIRST(Int)` = {`@integer`, `@ident`, `"-"`, `"("`}
- `FIRST(Proc)` = {`@ident`, `"stdout"`, `"("`, `"-"`, `@integer`}
- Overlap = {`@integer`, `@ident`, `"-"`, `"("`} = 4 tokens
- `min_size` = min(4, 5) = 4
- Ratio = 4/4 = 100%

Since 100% >= 80% and 4 >= 2, the lint fires.

### Output

```
note[C04]: cross-category overlap between `Int` and `Proc`: 4/4 tokens (100%) — mostly save/restore dispatch
  = hint: high FIRST-set overlap means many tokens need save/restore backtracking in cross-category dispatch
```

## Resolution

1. **Reduce token ambiguity by adding unique prefix tokens.** If a category's rules can be rewritten to start with a category-specific keyword, the overlap decreases:

   ```
   // Instead of bare PNum and PNeg that overlap with Int:
   PNum . a:Int |- "proc" "(" a ")" : Proc step;  // unique "proc" prefix
   // Remove PNeg from Proc; use CastIntToProc for negated ints in Proc contexts
   ```

2. **Merge categories if the overlap is inherent.** If two categories share almost all their FIRST tokens by design, they may be better modeled as a single category with discriminating rules:

   ```
   // Merge Int and Proc into a single Expr category with type-discriminating rules
   types {
       ![Expr] as Expr
   },
   ```

3. **Accept the overhead** if the grammar semantics require the overlap. Some language designs (e.g., process calculi where any expression can appear in a process context) inherently produce high overlap. In such cases, the WFST-weighted dispatch minimizes the cost by trying the higher-weight category first.

4. **Use beam pruning.** If the WFST prediction weights clearly favor one category over the other for most shared tokens, beam pruning (configured via `RecoveryConfig::beam_width`) can reduce the number of alternatives explored.

## Hint Explanation

The hint "high FIRST-set overlap means many tokens need save/restore backtracking in cross-category dispatch" explains the performance mechanism behind this lint. Cross-category dispatch in PraTTaIL works as follows:

1. When a rule references a NonTerminal from a different category (e.g., a `Proc` rule containing an `Int` operand), the generated parser calls the other category's parse function.
2. If the current token appears in both categories' FIRST sets, the parser cannot statically determine which category will succeed. It must save the lexer state, attempt one parse, and restore if it fails.
3. The save/restore overhead includes copying the lexer cursor position, line/column counters, and any buffered lookahead tokens. While each individual save/restore is O(1), the aggregate cost across a full parse can be significant when the overlap ratio is high.

The ratio is measured against the smaller FIRST set because that represents the "worst case" from the perspective of the less-common category: if 80% of its starting tokens also start parses in the more-common category, then 80% of its parse attempts will require backtracking through the more-common category first (since WFST weights typically favor the larger category).

## Related Lints

- [C01](C01-cast-cycle.md) -- cast cycles can amplify cross-category overlap by creating mutual coercion paths that increase the effective FIRST set of each category
- [P04](../performance/P04-many-alternatives.md) -- high overlap often co-occurs with many alternatives per token, since shared tokens may dispatch to rules in multiple categories
