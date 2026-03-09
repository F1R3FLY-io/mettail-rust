# LEX02: unreachable-token-pattern

**Severity:** Note
**Category:** lexer
**Feature Gate:** None

## Description

Detects when a terminal string in the grammar is a proper prefix of another,
longer terminal string. Under longest-match lexing semantics, the longer
terminal always wins when both could match the input. This means the shorter
terminal is effectively "shadowed" -- it can never match an input that starts
with the longer terminal's full spelling.

For example, if the grammar defines both `"="` and `"=="`, the input `==`
will always lex as a single `"=="` token, never as two `"="` tokens. This is
usually the correct behavior (longest-match is the standard lexing strategy),
but the lint notes it so the grammar author is aware of the precedence
relationship.

This lint only fires for multi-character terminals. Single-character terminals
like `"+"` or `"-"` are not checked because prefix relationships between
single characters and multi-character tokens (e.g., `"+"` vs `"++"`) are
extremely common and expected.

```
  Longest-match precedence

  Input: "==>"

  Candidate matches:
    "="   matches at position 0 (length 1)
    "=="  matches at position 0 (length 2)   ← longest match wins
    "==>" matches at position 0 (length 3)   ← if defined, wins over both

  Token produced: "==>" (or "==" if "==>" is not a terminal)

  LEX02 notes: `=` is a prefix of `==`
               `==` is a prefix of `==>` (if both are terminals)
```

## Trigger Conditions

All of the following must hold:

- Two distinct terminal strings exist in the grammar.
- Both terminals have length > 1.
- One terminal is a proper prefix of the other (i.e., the longer starts
  with the shorter).

One diagnostic is emitted per ordered prefix pair.

## Example

### Grammar

```rust
language! {
    name: CompareOps,
    types {
        ![bool] as BoolExpr,
        ![i64] as Expr
    },
    terms {
        Num     . n:Expr |- n : Expr;
        Eq      . a:Expr, b:Expr |- a "==" b : BoolExpr;
        Assign  . a:Expr, b:Expr |- a "=" b : Expr;
        Arrow   . a:Expr, b:Expr |- a "=>" b : Expr;
        // "=" is a prefix of "==" and "=>"
        // "=>" is not a prefix of "==" (different second char)
    },
}
```

### Output

```
note[LEX02] (CompareOps): terminal `=>` is a prefix of `==>` -- longest-match semantics apply
  = hint: input `==>` will always lex as `==>`, never as `=>`
```

(In the actual grammar above, the output would be about `=` vs `==` etc.,
depending on which terminals exceed length 1.)

## Resolution

1. **Understand the precedence.** Longest-match is almost always the
   desired behavior. The shorter terminal will still match inputs where the
   longer terminal does not apply (e.g., `"= "` matches `"="` because the
   space prevents `"=="` from matching).

2. **No action needed.** This lint is informational. If you intended the
   prefix relationship, no changes are required.

3. **Use distinct spellings.** If the shadowing is unintentional (e.g., you
   expected the shorter terminal to match even when the longer one could),
   rename one terminal to avoid the prefix relationship.

4. **Remove the unreachable terminal.** If the shorter terminal is never
   used independently (every occurrence is actually part of the longer
   terminal), consider removing it from the grammar.

## Hint Explanation

The hint **"input `<longer>` will always lex as `<longer>`, never as
`<shorter>`"** makes the longest-match rule explicit for the specific
terminal pair. It clarifies that:

- When the lexer sees the full spelling of the longer terminal, it will
  always produce a single token of that longer type.
- The shorter terminal can only match inputs where the longer terminal's
  additional characters are absent (e.g., followed by whitespace or a
  different character).

## Related Lints

- [LEX01](LEX01-overlapping-token-defs.md) -- Semantic overlap between
  same-spelled terminals across categories (a broader form of token
  collision).
- [LEX05](LEX05-float-integer-ambiguity.md) -- Float/integer ambiguity is a
  specific case where numeric literal patterns shadow each other.
- [PAR04](../parser/PAR04-mixfix-ambiguous-delimiter.md) -- Mixfix
  delimiters that are prefixes of infix operators create a parser-level
  analog of this problem.
