# P02: high-nfa-spillover

**Severity:** Note
**Category:** Performance

## Description

Detects grammars where more than 3 categories require NFA spillover buffers. NFA spillover occurs when a category has prefix ambiguity that cannot be resolved by a single-token lookahead DFA: multiple rules share the same first token, and the NFA disambiguation engine must buffer tokens into a spillover region to determine which rule to apply. Each category with NFA spillover requires a dedicated thread-local storage (TLS) buffer (`Cell<Vec<(Token, Range)>>`) that persists across parse calls.

When many categories need spillover buffers, the aggregate TLS overhead becomes noticeable:

- **Memory.** Each spillover buffer is a `Vec` that grows to accommodate the longest ambiguous prefix in that category. With K categories needing spillover, the parser maintains K TLS buffers simultaneously.
- **Cache pressure.** TLS access involves indirection through the thread-local storage block. With many active TLS slots, cache locality degrades.
- **Initialization cost.** Each buffer must be initialized on first use per thread, adding startup latency in multi-threaded parsing scenarios.

The threshold of 3 is chosen because most practical grammars have 1-2 categories with prefix ambiguity (typically the expression and statement categories). More than 3 suggests that the grammar's token design may benefit from disambiguation improvements.

## Trigger Conditions

A note is emitted when:

1. `nfa_spillover_categories.len() > 3`, where `nfa_spillover_categories` is the set of category names identified during the NFA disambiguation phase as requiring spillover buffers.

The diagnostic message lists all affected categories in sorted alphabetical order.

## Example

### Grammar

```
language! {
    name: AmbiguousLang,
    types {
        ![i32] as Int
        ![f64] as Float
        ![String] as Str
        ![bool] as Bool
        ![()] as Proc
    },
    terms {
        // Int rules -- @ident prefix ambiguity (IntVar vs IntFnCall)
        NumLit     . |- @integer : Int;
        IntVar     . |- @ident : Int;
        IntFnCall  . |- @ident "(" @integer ")" : Int step;

        // Float rules -- @ident prefix ambiguity (FloatVar vs FloatFnCall)
        FloatLit   . |- @float : Float;
        FloatVar   . |- @ident : Float;
        FloatFnCall . |- @ident "(" @float ")" : Float step;

        // Str rules -- @ident prefix ambiguity (StrVar vs StrFnCall)
        StrLit     . |- @string : Str;
        StrVar     . |- @ident : Str;
        StrFnCall  . |- @ident "(" @string ")" : Str step;

        // Bool rules -- @ident prefix ambiguity (BoolVar vs BoolFnCall)
        BTrue      . |- "true" : Bool;
        BFalse     . |- "false" : Bool;
        BoolVar    . |- @ident : Bool;
        BoolFnCall . |- @ident "(" "true" ")" : Bool step;

        // Proc rules
        POutput . a:Str |- "stdout" "!" "(" a ")" : Proc step;

        // Casts
        CastIntToProc  . a:Int |- a : Proc step;
        CastBoolToProc . a:Bool |- a : Proc step;
    },
}
```

In this grammar, `Int`, `Float`, `Str`, and `Bool` all have prefix ambiguity on `@ident` (the variable rule and the function-call rule share the same first token). Each requires an NFA spillover buffer to disambiguate by looking at the second token.

### Output

```
note[P02]: 4 categories need NFA spillover buffers: [Bool, Float, Int, Str] — increases TLS overhead
  = hint: reduce prefix ambiguity to lower the number of categories needing NFA spillover
```

## Resolution

1. **Add distinguishing prefix tokens.** If function calls can use a category-specific syntax, the NFA spillover is eliminated for that category:

   ```
   // Instead of: IntFnCall . |- @ident "(" @integer ")" : Int step;
   // Use a keyword prefix:
   IntFnCall . |- "int_call" @ident "(" @integer ")" : Int step;
   ```

2. **Unify the ambiguous rules into a single rule with post-parse discrimination.** If the variable and function-call forms share semantics:

   ```
   // Single rule handles both cases; post-parse logic distinguishes
   IntRef . |- @ident : Int;
   IntCall . |- @ident "(" @integer ")" : Int step;
   // The NFA can now use forced-prefix replay on the second token "("
   ```

   Note: This may still require spillover, but the NFA disambiguation engine uses forced-prefix replay to minimize the buffer size.

3. **Merge categories.** If four categories all have the same ambiguity pattern (`@ident` as both variable and function call), consider a single `Expr` category with type-discriminating rules:

   ```
   types { ![Expr] as Expr },
   terms {
       Var    . |- @ident : Expr;
       FnCall . |- @ident "(" Expr ")" : Expr step;
       NumLit . |- @integer : Expr;
       // ...
   },
   ```

   This reduces the spillover category count from 4 to 1.

4. **Accept the overhead** if the grammar's type system inherently requires separate categories with shared prefix tokens. The NFA spillover engine is optimized for this case (TLS `Cell<Vec<T>>` with take/set reuse), so the overhead is primarily cache-related rather than allocation-related.

## Hint Explanation

The hint "reduce prefix ambiguity to lower the number of categories needing NFA spillover" identifies the root cause: prefix ambiguity within a category. NFA spillover buffers exist because the DFA-based lexer and single-token-lookahead dispatch cannot resolve which rule to apply when multiple rules in the same category start with the same token. The NFA disambiguation engine buffers additional tokens (the "spillover") to extend the lookahead until the ambiguity is resolved.

Each category with spillover adds a TLS buffer that is allocated once per thread and reused across parse calls via `Cell::take()` / `Cell::set()`. The buffers themselves are cheap (empty `Vec` on first use, then reused), but the TLS indirection and cache-line pollution from multiple active buffers can measurably affect throughput in tight parsing loops. The threshold of 3 is based on empirical observation that most grammars require spillover in at most 2-3 categories (typically the main expression and statement categories), and exceeding this threshold often indicates a grammar design that could benefit from restructuring.

## Related Lints

- [W02](../wfst/W02-nfa-ambiguous-prefix.md) -- identifies the specific rules within each category that contribute to NFA ambiguity; resolving W02 warnings directly reduces the number of categories needing spillover
- [P04](P04-many-alternatives.md) -- many alternatives per token often co-occurs with NFA spillover, since both result from prefix ambiguity in the grammar
