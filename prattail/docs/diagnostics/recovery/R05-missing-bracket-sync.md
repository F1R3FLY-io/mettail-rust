# R05: missing-bracket-sync

**Severity:** Warning
**Category:** Recovery

## Description

Detects categories that use an opening bracket delimiter (`(`, `{`, or `[`) in at least one rule's syntax but whose recovery WFST does not contain the corresponding closing bracket variant (`RParen`, `RBrace`, or `RBracket`) in its `sync_tokens()` set. This is a significant recovery quality issue because opening brackets create nesting expectations: when the parser encounters an opening bracket, it expects a matching close. If the closing bracket is not a sync token, the recovery system cannot use it as a resynchronization point when a parse error occurs inside the bracketed construct. The result is that errors within parenthesized groups, brace-delimited blocks, or bracket-enclosed lists may cause the recovery system to skip past the closing bracket entirely, losing the syntactic boundary and potentially cascading into errors in surrounding code.

The lint checks three bracket pairs:
- `(` requires `RParen` (`)`) in the sync set
- `{` requires `RBrace` (`}`) in the sync set
- `[` requires `RBracket` (`]`) in the sync set

Each pair is checked independently, so a category that uses both `(` and `{` but is missing only `RBrace` will emit one warning (for the `{`/`RBrace` pair).

## Trigger Conditions

A warning is emitted for each bracket pair `(open, close_variant)` when **all** of the following conditions hold:

1. The category has at least one rule whose syntax items contain a `SyntaxItemSpec::Terminal(t)` where `t` matches the opening bracket (`"("`, `"{"`, or `"["`).
2. A `RecoveryWfst` exists for the category.
3. No token in the `sync_tokens()` set has a `token_name()` equal to the expected closing variant (`"RParen"`, `"RBrace"`, or `"RBracket"`).

## Example

### Grammar

```
language! {
    name: FuncCall,
    types {
        ![String] as Name,
        ![i32] as Expr
    },
    terms {
        // Name rules
        Ident . s:Name |- s : Name ![s];

        // Expr rules
        Lit   . n:Expr |- n              : Expr ![n];
        Neg   . a:Expr |- "-" a          : Expr ![- a];
        Add   . a:Expr, b:Expr |- a "+" b : Expr ![a + b];

        // This rule uses "(" but the corresponding ")" only appears
        // in Call's own syntax. If no other rule places ")" after an
        // Expr NonTerminal, then RParen may not be in Expr's sync set.
        Call  . f:Name, arg:Expr |- f "(" arg ")" : Expr ![{
            format!("{}({})", f, arg)
        }];

        // Array indexing uses "[" but if no rule has "]" following Expr
        // in a consuming position, RBracket may be absent from Expr's
        // sync set.
        Index . arr:Expr, idx:Expr |- arr "[" idx "]" : Expr ![arr + idx];
    },
}
```

Suppose the FOLLOW set computation places `RParen` into `Expr`'s sync set (from the `Call` rule's `")"` following the `arg:Expr` position) but does **not** place `RBracket` (because the `"]"` in `Index` follows a same-category infix position that the FOLLOW analysis does not propagate). The lint will fire for the `[`/`RBracket` pair but not for `(`/`RParen`.

### Output

```
warning[R05]: category `Expr` uses `[` delimiter but closing `RBracket` is absent from sync set
  = in category `Expr`
  = hint: ensure the closing bracket is in the category's FOLLOW set or structural delimiters
```

## Resolution

There are several ways to ensure the closing bracket enters the sync set:

1. **Add a rule where the closing bracket follows a NonTerminal of the category.** The most direct approach: create a rule (or modify an existing one) so that the closing bracket appears immediately after a NonTerminal of the target category in a consuming rule. This causes the FOLLOW set analysis to include the closing bracket.

   ```
   // Before: arr "[" idx "]" -- "]" follows idx (same-cat infix, may not propagate)
   // Fix: Add a standalone indexing rule where "]" follows Expr in a wrapper category
   ArrayAccess . arr:Expr, idx:Expr |- arr "[" idx "]" : Expr ![arr + idx];
   ```

2. **Add a standalone bracket-grouping rule.** For example, adding `Bracket . a:Expr |- "[" a "]" : Expr ![a]` ensures `RBracket` appears in `Expr`'s FOLLOW set because `"]"` directly follows the `a:Expr` NonTerminal.

   ```
   BracketGroup . a:Expr |- "[" a "]" : Expr ![a];
   ```

3. **Reference the category from another rule that uses the closing bracket.** If a higher-level category has a rule like `ListItem . e:Expr |- e "]"`, the `"]"` will enter `Expr`'s FOLLOW set.

4. **Check for asymmetric grammar structure.** Sometimes the opening bracket is used in the category but the closing bracket only appears in a different category's rule. Restructuring so that both brackets are visible in the same category's rule set resolves the issue.

## Hint Explanation

The hint "ensure the closing bracket is in the category's FOLLOW set or structural delimiters" identifies the two mechanisms by which a token enters the sync set. The FOLLOW set is computed by the prediction pipeline's fixed-point analysis: a token `t` is in `FOLLOW(Cat)` if there exists a rule in any category where a `NonTerminal(Cat)` is immediately followed by `t` (or transitively, by a category whose FIRST set contains `t`). Structural delimiters are a hardcoded set of tokens (`(){}[],;`) that the recovery system recognizes as universal sync points -- but only if those tokens actually appear somewhere in the grammar. The fix is to ensure the grammar structure allows the closing bracket to be reachable via one of these paths, typically by having at least one rule where the closing bracket follows a NonTerminal of the affected category.

## Related Lints

- [G09](../grammar/G09-unbalanced-delimiters.md) -- detects mismatched open/close brackets within a single rule's syntax; G09 is about syntactic well-formedness while R05 is about recovery effectiveness
- [R01](./R01-empty-sync-set.md) -- if the entire sync set is empty (not just missing one bracket), R01 fires instead; R05 is a more targeted check for specific bracket pairs that should be present
