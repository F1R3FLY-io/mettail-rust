# R02: sparse-recovery

**Severity:** Note
**Category:** Recovery

## Description

Detects categories whose recovery WFST has exactly 1 sync token. While this is strictly better than having zero sync tokens (which triggers the more severe R01 warning), a single sync token provides only one resynchronization point for error recovery. With just one sync token, the recovery system can only resume parsing at occurrences of that single terminal, which may be sparsely distributed in the token stream. If the one sync token does not appear near the error site, the recovery algorithm must skip a large number of tokens before finding it, potentially discarding valid code and masking downstream errors.

Effective error recovery generally benefits from 2 or more sync tokens so that the recovery system has multiple candidate resynchronization points to choose from. The Viterbi minimum-cost search evaluates all reachable sync tokens and selects the one with the lowest repair cost; more candidates give the algorithm more opportunities to find a low-cost repair that preserves as much of the original input as possible.

## Trigger Conditions

A note is emitted when **all** of the following conditions hold:

1. A `RecoveryWfst` exists for the category.
2. The `sync_tokens()` set has exactly 1 element (i.e., `count > 0 && count < 2`).

## Example

### Grammar

```
language! {
    name: SimpleExpr,
    types {
        ![i32] as Expr
    },
    terms {
        Lit   . n:Expr |- n                : Expr ![n];
        Neg   . a:Expr |- "-" a            : Expr ![- a];
        Add   . a:Expr, b:Expr |- a "+" b  : Expr ![a + b];
        Mul   . a:Expr, b:Expr |- a "*" b  : Expr ![a * b];
        // The only structural delimiter is the semicolon terminator.
        // No parentheses, no braces, no brackets -- just one sync token.
        Stmt  . e:Expr |- e ";"            : Expr ![e];
    },
}
```

In this grammar, `Expr`'s FOLLOW set contains only `";"` (from the `Stmt` rule where `";"` follows the `Expr` NonTerminal). No other structural delimiters appear in any rule referencing `Expr`. The recovery WFST for `Expr` therefore has exactly 1 sync token: `Semicolon`.

### Output

```
note[R02]: category `Expr` has only 1 sync token -- limited recovery options
  = in category `Expr`
  = hint: add more structural delimiters to improve error recovery quality
```

## Resolution

Add additional structural delimiters to the grammar rules that involve the category:

1. **Add a parenthesized grouping rule.** This introduces `RParen` (`)`) into the category's FOLLOW set via the closing parenthesis:

   ```
   Group . a:Expr |- "(" a ")" : Expr ![a];
   ```

2. **Add comma-separated lists or tuples.** Rules like `Pair . a:Expr, b:Expr |- "(" a "," b ")"` add both `RParen` and `Comma` to the sync set.

3. **Add block-structured rules.** If the language supports blocks, introduce braces:

   ```
   Block . body:Expr |- "{" body "}" : Expr ![body];
   ```

4. **Review cross-category references.** If other categories reference `Expr` as a NonTerminal, the tokens that follow those references in the outer rules contribute to `Expr`'s FOLLOW set. Adding more rules in consuming categories can indirectly grow the sync set.

After any of these additions, the sync set will contain 2+ tokens, and this note will no longer be emitted.

## Hint Explanation

The hint "add more structural delimiters to improve error recovery quality" directs the grammar author to enrich the category's syntax with standard bracketing and separator tokens. Structural delimiters -- parentheses, braces, brackets, commas, and semicolons -- serve as natural recovery landmarks because they appear at well-defined syntactic boundaries. The more distinct sync tokens available, the shorter the average skip distance during recovery, and the more downstream errors the parser can detect in a single pass. A sync set of 3-5 tokens is typical for well-structured grammars and provides robust recovery behavior.

## Related Lints

- [R01](./R01-empty-sync-set.md) -- the zero-sync-token case, which is strictly worse than having 1 sync token; R01 is a Warning while R02 is only a Note
- [R05](./R05-missing-bracket-sync.md) -- if the category uses an opening bracket but the corresponding closing bracket is missing from the sync set, fixing R05 will also increase the sync token count and may resolve R02
