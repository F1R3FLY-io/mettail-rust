# P04: many-alternatives

**Severity:** Note
**Category:** Performance

## Description

Detects tokens in a category's FIRST set for which the WFST prediction engine returns more than 4 dispatch actions. Each dispatch action represents a candidate rule that could match when the parser sees that token in that category's context. The parser must evaluate each candidate using save/restore backtracking: it saves the lexer state, attempts to parse the candidate rule, and restores the state if the attempt fails before trying the next candidate.

The WFST prediction engine orders candidates by weight (lower tropical weight = higher priority), and WFST beam pruning can reduce the number of candidates explored at runtime. However, the static count of dispatch targets reflects the worst case -- the number of alternatives the parser must be prepared to try if all higher-priority candidates fail.

More than 4 alternatives per token indicates significant prefix ambiguity: the grammar has many rules in the same category that can begin with the same token, and the WFST cannot statically eliminate any of them. This is a grammar design signal, not necessarily a performance crisis, but it identifies tokens where parse throughput will be lower due to speculative execution.

## Trigger Conditions

A note is emitted for each `(token, category)` pair where:

1. The `token` appears in the FIRST set of the `category`.
2. `prediction_wfst.predict(token)` returns a `Vec<&WeightedAction>` with length > 4 (counts all dispatch targets, not just the top-weighted one).

Each offending `(token, category)` pair produces a separate diagnostic.

## Example

### Grammar

```
language! {
    name: AmbiguousExpr,
    types {
        ![i32] as Int
        ![String] as Str
        ![()] as Proc
    },
    terms {
        // 6 rules in Int that start with @ident
        IntVar     . |- @ident : Int;
        IntFnCall  . |- @ident "(" Int ")" : Int step;
        IntIndex   . |- @ident "[" Int "]" : Int step;
        IntField   . |- @ident "." @ident : Int step;
        IntMethod  . |- @ident "." @ident "(" Int ")" : Int step;
        IntSlice   . |- @ident "[" Int ":" Int "]" : Int step;

        // Other Int rules (unique prefixes, no issue)
        NumLit . |- @integer : Int;
        Neg    . a:Int |- "-" a : Int fold;
        Add    . a:Int, b:Int |- a "+" b : Int ![a + b] fold;

        // Str rules
        StrLit . |- @string : Str;

        // Proc rules
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;

        // Casts
        CastIntToProc . a:Int |- a : Proc step;
    },
}
```

In this grammar, the token `@ident` dispatches to 6 rules in category `Int`:
1. `IntVar` (bare identifier)
2. `IntFnCall` (identifier + `(`)
3. `IntIndex` (identifier + `[`)
4. `IntField` (identifier + `.` + identifier)
5. `IntMethod` (identifier + `.` + identifier + `(`)
6. `IntSlice` (identifier + `[` + int + `:`)

Since 6 > 4, the lint fires.

### Output

```
note[P04]: token `@ident` dispatches to 6 rules in category `Int` — save/restore overhead
  = in category `Int`
  = hint: reduce prefix ambiguity or use beam pruning to limit alternatives
```

## Resolution

1. **Left-factor the grammar to reduce prefix sharing.** Group rules that share a prefix into a single rule that dispatches on the distinguishing token:

   ```
   // Instead of 6 separate rules starting with @ident:
   IntRef . |- @ident : Int;                            // bare variable
   IntAccess . |- @ident "(" Int ")" : Int step;        // function call
   IntIndex  . |- @ident "[" Int "]" : Int step;        // indexing
   IntField  . |- @ident "." @ident : Int step;         // field access
   ```

   Left-factoring cannot fully eliminate the ambiguity (all 4 still start with `@ident`), but it can reduce the count by merging related forms (e.g., `IntMethod` as a post-parse rewrite of `IntField` when followed by `(`).

2. **Use distinguishing prefix keywords.** If the grammar's syntax allows it, add unique starting tokens:

   ```
   // Method calls use a distinct syntax:
   IntMethod . |- "call" @ident "." @ident "(" Int ")" : Int step;
   ```

3. **Configure beam pruning to limit runtime exploration.** The WFST prediction weights determine the order in which alternatives are tried. If the first 2-3 candidates succeed in the vast majority of cases, beam pruning can skip the remaining candidates:

   ```
   // In RecoveryConfig or grammar annotation:
   beam_width: 3,  // Try at most 3 candidates per token
   ```

   Note: Beam pruning trades completeness for speed. If the correct rule is ranked 4th or lower by WFST weight, beam pruning will miss it and trigger error recovery.

4. **Accept the overhead** for tokens that inherently dispatch to many rules. Some language designs (e.g., identifier-heavy languages where variables, function calls, field access, and method calls all start with an identifier) will always have high alternative counts for `@ident`. The WFST weight ordering ensures the most common rule is tried first, amortizing the cost.

## Hint Explanation

The hint "reduce prefix ambiguity or use beam pruning to limit alternatives" presents two complementary strategies:

- **Reduce prefix ambiguity** addresses the root cause. When fewer rules share the same first token, the WFST dispatches to fewer candidates, and each parse attempt has a higher probability of succeeding on the first try. Grammar-level changes (left-factoring, unique prefixes, rule merging) are the most effective approach but require modifying the language's concrete syntax.

- **Use beam pruning** addresses the symptom at runtime. Beam pruning limits the number of candidates the parser explores for any given token by cutting off alternatives below a weight threshold or beyond a fixed count. This reduces the worst-case save/restore count but may cause the parser to miss valid parses that are ranked low by the WFST.

The threshold of 4 is chosen because save/restore cycles have approximately linear cost: 5+ alternatives means 4+ potential restore operations per token occurrence. For tokens that appear frequently (e.g., `@ident` in a typical program), the aggregate overhead scales with both the alternative count and the token frequency. The WFST `predict()` function returns all actions whose input token matches, sorted by tropical weight, providing a complete picture of the dispatch fan-out for each token.

## Related Lints

- [W03](../wfst/W03-high-ambiguity-token.md) -- fires at a lower threshold (> 3 rules) and reports the same underlying issue from the WFST perspective; W03 and P04 may both fire for the same token, with W03 focusing on WFST weight analysis and P04 focusing on performance impact
- [P02](P02-high-nfa-spillover.md) -- many alternatives per token often co-occurs with NFA spillover needs, since both result from prefix ambiguity; resolving P04 by left-factoring also reduces NFA spillover
