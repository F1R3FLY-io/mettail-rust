# X01: composition-ambiguity-introduction

**Severity:** Warning
**Category:** Composition
**Feature Gate:** (none -- always active when composition lints run)

## Description

Detects FIRST set ambiguity growth introduced by merging two grammars. When
two source grammars A and B are composed into a single merged grammar, new
derivation paths may appear that did not exist in either source grammar
individually. These new paths manifest as tokens in the merged grammar's FIRST
sets that are absent from the union of A's and B's FIRST sets.

For a shared category C (present in both grammars), the lint computes:

    FIRST_A(C) -- tokens that begin valid parses of C in grammar A
    FIRST_B(C) -- tokens that begin valid parses of C in grammar B
    FIRST_M(C) -- tokens that begin valid parses of C in the merged grammar

    new_tokens = FIRST_M(C) \ (FIRST_A(C) ∪ FIRST_B(C))

When `new_tokens` is non-empty, the composition has introduced derivation
paths that neither source grammar supported on its own. This typically occurs
when cross-category casts or nonterminal references in the merged grammar
create new reachability edges that expose previously unreachable token
prefixes.

```
  Grammar A            Grammar B           Merged
 ┌─────────┐         ┌─────────┐        ┌──────────┐
 │ FIRST_A │         │ FIRST_B │        │ FIRST_M  │
 │ {+, -}  │         │ {*, /}  │        │ {+,-,*,/,│
 └─────────┘         └─────────┘        │  ^}      │
                                         └──────────┘
         FIRST_A ∪ FIRST_B = {+, -, *, /}
         new_tokens = {^}   ← introduced by composition
```

The pre-composition overlap count (|FIRST_A(C) ∩ FIRST_B(C)|) is also
reported to help gauge the existing level of ambiguity before the merge.

## Trigger Conditions

All of the following must hold:

- Two grammars A and B are composed via the composition lint framework.
- A `CompositionLintContext` is provided with pre-merge and post-merge FIRST
  sets.
- At least one shared category C exists (present in both grammars).
- For that category, the merged FIRST set contains tokens not in the union
  of A's and B's FIRST sets (i.e., `new_tokens` is non-empty).

One diagnostic is emitted per shared category with newly introduced tokens.

## Example

### Grammar

```rust
// Grammar A
language! {
    name: ArithA,
    types { ![i32] as Expr },
    terms {
        Add . a:Expr, b:Expr |- a "+" b : Expr;
        Sub . a:Expr, b:Expr |- a "-" b : Expr;
    },
}

// Grammar B
language! {
    name: ArithB,
    types { ![i32] as Expr },
    terms {
        Mul . a:Expr, b:Expr |- a "*" b : Expr;
        Pow . a:Expr, b:Expr |- a "^" b : Expr;  // new token "^"
    },
}

// Composition introduces a cross-category cast that makes "^" reachable
// in contexts where only A's tokens were expected.
```

### Output

```
warning[X01] (MergedArith): composition introduces 1 new FIRST set token(s) in category `Expr` not in either source grammar: [^] (pre-composition overlap: 0 token(s))
  = hint: add unique prefix tokens to disambiguate; WFST auto-assigns weights by declaration order when prefixes overlap
```

## Resolution

1. **Add unique prefix tokens.** If the newly introduced tokens create
   ambiguity with existing rules, differentiate them by adding a distinctive
   leading terminal:

   ```
   Pow . a:Expr, b:Expr |- a "**" b : Expr;  // distinct from "*"
   ```

2. **Restrict the composition scope.** Narrow the set of shared categories
   so that only categories intended for cross-grammar interaction are merged.
   This prevents unintended token leakage.

3. **Accept the growth.** If the new tokens represent intentional
   cross-grammar functionality (e.g., an extension grammar adding new
   operators), the warning is informational and can be acknowledged.

## Hint Explanation

> add unique prefix tokens to disambiguate; WFST auto-assigns weights by
> declaration order when prefixes overlap

The first part recommends adding distinguishing terminal prefixes so that the
parser can unambiguously select the correct rule without consulting WFST
weights. The second part explains that when prefixes do overlap, the WFST
prediction layer assigns weights based on declaration order -- rules declared
earlier receive lower (better) tropical weights. This automatic assignment
resolves ambiguity deterministically but may not match the author's intent.

## Related Lints

- [X02](X02-composition-priority-shadowing.md) -- detects when a rule from
  one grammar is shadowed (lower priority) by a rule from the other grammar
  for the same token
- [X03](X03-composition-dead-rule-creation.md) -- detects rules that become
  dead after composition, which can be a consequence of the ambiguity X01
  reports
- [G03](../grammar/G03-ambiguous-prefix.md) -- single-grammar ambiguous
  prefix detection (the non-composition counterpart)
