# LEX01: overlapping-token-defs

**Severity:** Warning (placeholder -- not yet active)
**Category:** lexer
**Feature Gate:** None

## Description

Detects when two or more terminal definitions in the grammar match the same
input string with different semantic intent across different categories. In
PraTTaIL, terminals are string literals that the lexer matches during
tokenization. When the same terminal string appears in rules of different
categories with non-overlapping FIRST sets, it may indicate that the grammar
author intended different tokens that happen to share a spelling.

This is distinct from the normal case where shared delimiters like `"("`,
`"+"`, or `";"` appear across many categories -- those are expected. LEX01
targets the situation where a terminal like `"in"` is used as a keyword in
one category (e.g., `for x in list`) and as an identifier-like operator in
another (e.g., `x in S` for set membership), creating a potential semantic
collision.

```
  Terminal overlap analysis

  Category  Rule       Terminal  Semantic Role
  ────────  ─────────  ────────  ─────────────
  ForStmt   ForIn      "in"     loop keyword
  SetExpr   MemberOf   "in"     membership operator

  Same string "in", different semantics → LEX01 would fire
  (currently placeholder: requires terminal semantic tracking)
```

Note: LEX01 is currently a **placeholder** lint. The implementation requires
terminal semantic tracking infrastructure that is not yet in place. The lint
function body is a no-op. When implemented, it will collect all fixed
terminals from rules and check for exact duplicates across categories with
different semantic roles.

## Trigger Conditions

When fully implemented, all of the following would hold:

- The same terminal string appears in rules of at least two different
  categories.
- The categories have non-overlapping FIRST sets, suggesting the terminal
  has different semantic roles in each context.
- The overlap is not a common shared delimiter (parentheses, commas,
  semicolons, standard operators).

Currently, no diagnostics are emitted (placeholder implementation).

## Example

### Grammar

```rust
language! {
    name: KeywordClash,
    types {
        ![String] as Stmt,
        ![bool] as BoolExpr,
        ![Vec<String>] as List
    },
    terms {
        Lit     . s:BoolExpr |- s : BoolExpr;
        ListLit . l:List |- l : List;
        ForIn   . x:Stmt, l:List, body:Stmt |- "for" x "in" l "{" body "}" : Stmt;
        MemberOf . x:BoolExpr, s:List |- x "in" s : BoolExpr;
        // "in" serves as a loop keyword in ForIn but as a
        // set-membership operator in MemberOf
    },
}
```

### Output (projected -- not currently emitted)

```
warning[LEX01] (KeywordClash): terminal `in` appears in categories `Stmt` and `BoolExpr` with non-overlapping FIRST sets -- potential semantic collision
  = hint: consider using distinct tokens (e.g., `in` vs `elem`) to avoid lexer-level ambiguity
```

## Resolution

1. **Use distinct terminal strings.** Rename one of the colliding terminals
   to a unique string. For example, use `"elem"` for set membership and
   reserve `"in"` for the loop keyword.

2. **Rely on context disambiguation.** If the grammar is unambiguous at the
   parser level (i.e., the two uses of `"in"` never appear in the same
   parse context), the collision is harmless. The parser will select the
   correct interpretation based on the surrounding syntax.

3. **Add a keyword table.** Register `"in"` as a keyword so the lexer can
   assign it a dedicated token type. Keyword recognition prevents it from
   being confused with an identifier or generic operator.

## Hint Explanation

The hint (when implemented) would explain that **terminals with the same
spelling but different semantic roles** can confuse both human readers and
tooling. Even when the parser resolves the ambiguity correctly, code
highlighters, formatters, and error messages may present the wrong
interpretation.

## Related Lints

- [LEX02](LEX02-unreachable-token-pattern.md) -- Overlapping tokens can
  also create shadowing situations where one token pattern makes another
  unreachable.
- [LEX05](LEX05-float-integer-ambiguity.md) -- A specific case of token
  overlap where integer and float literal patterns match the same input.
- [PAR03](../parser/PAR03-postfix-prefix-collision.md) -- A parser-level
  analog where the same token serves as both prefix and postfix operator.
