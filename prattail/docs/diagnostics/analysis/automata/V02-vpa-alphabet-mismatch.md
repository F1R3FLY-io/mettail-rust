# V02: vpa-alphabet-mismatch

**Severity:** Warning
**Category:** analysis/automata
**Feature Gate:** `vpa`

## Description

Detects a **delimiter classification inconsistency** in the grammar's token
alphabet: a single token appears as both a **call** (opening/push) symbol and a
**return** (closing/pop) symbol in different rules. This violates the
fundamental requirement of visibly pushdown automata (VPAs), which demand that
the input alphabet be partitioned into three mutually disjoint classes.

For a VPA, the alphabet Sigma must satisfy:

    Sigma = Sigma_c  union  Sigma_r  union  Sigma_i
    Sigma_c  cap  Sigma_r = emptyset
    Sigma_c  cap  Sigma_i = emptyset
    Sigma_r  cap  Sigma_i = emptyset

The critical invariant is Sigma_c cap Sigma_r = emptyset: no token may act as
both an opening delimiter (pushing onto the stack) and a closing delimiter
(popping from the stack). When this invariant is violated, the stack behavior
is no longer determined solely by the input token -- it depends on parsing
context, which breaks the "visible" pushdown property.

```
  Alphabet Partition Violation
  ════════════════════════════

  ┌──────────┐   ┌──────────┐
  │ Sigma_c  │   │ Sigma_r  │
  │  (call)  │   │ (return) │
  │          │   │          │
  │    (     ├───┤    )     │
  │    [     │ ┌─┤    ]     │
  │          │ │ │          │
  │   "|"  ◄─┼─┘ │   "|"   │    V02 fires: "|" in
  │          │   │          │    both Sigma_c and Sigma_r
  └──────────┘   └──────────┘
```

In the diagram, the token `|` is used in one rule as an opening delimiter
(e.g., `| params | body`) and in another as a closing delimiter (e.g.,
`case | pattern`). This dual classification prevents the VPA from being
deterministic -- the stack action for `|` is ambiguous.

## Trigger Conditions

All of the following must hold:

- The `vpa` feature is enabled at compile time.
- A `VpaAnalysis` result is available in the lint context.
- The `alphabet_mismatches` list contains at least one entry (at least one
  token was classified as both a call and a return symbol).

One V02 diagnostic is emitted per mismatched token.

## Example

### Grammar

```rust
language! {
    name: PipeConfusion,
    types {
        ![String] as Expr,
        ![String] as Pattern
    },
    terms {
        // "|" acts as opening delimiter (call) for closures:
        Lambda . body:Expr |- "|" <ident> "|" body : Expr;

        // "|" acts as closing delimiter (return) for match arms:
        Var    . |- <ident> : Expr;
        Match  . e:Expr, p:Pattern, b:Expr |- "match" e "{" p "=>" b "}" : Expr;
        PatOr  . a:Pattern, b:Pattern |- a "|" b : Pattern;
    },
}
```

### Output

```
warning[V02] (PipeConfusion): delimiter classification inconsistency: token `|` classified as both call and return
  = hint: ensure each delimiter token is used consistently as either opening or closing
```

## Resolution

1. **Use distinct tokens for distinct roles.** Replace one use of the ambiguous
   token with a different delimiter. For instance, use `||` for closure
   parameter delimiters and reserve `|` for pattern alternation:
   ```
   Lambda . body:Expr |- "||" <ident> "||" body : Expr;
   ```

2. **Reclassify as internal.** If the token does not truly act as a delimiter
   in both contexts, reclassify one use so that it is treated as an internal
   symbol (Sigma_i). Internal symbols do not affect the stack, so the partition
   remains valid. This requires restructuring the grammar so the token's rule
   does not imply push/pop semantics.

3. **Accept the non-VPA property.** If the grammar intentionally uses the same
   token as both an opener and closer (e.g., `|` in Rust-like closures and
   match arms), acknowledge that the grammar's structured sublanguage is not a
   visibly pushdown language. The general Pratt parser will still handle it
   correctly through binding-power disambiguation, but the VPA-specific
   optimizations (zero-backtracking delimiter matching) will not apply.

## Hint Explanation

The hint **"ensure each delimiter token is used consistently as either opening
or closing"** restates the disjointness invariant of the VPA alphabet partition:

    Sigma_c  cap  Sigma_r = emptyset

For the VPA analysis to succeed, every delimiter token must have a single,
unambiguous role:

- **Opening (call/push):** The token pushes a stack frame. It signals the start
  of a nested structure. Examples: `(`, `[`, `{`, `begin`.

- **Closing (return/pop):** The token pops a stack frame. It signals the end of
  a nested structure. Examples: `)`, `]`, `}`, `end`.

- **Internal (no stack effect):** The token neither pushes nor pops. It is
  processed within the current nesting level. Examples: `+`, `-`, `*`, `,`.

When a token appears in both the call and return sets, the VPA cannot determine
whether to push or pop when it encounters that token. The resolution is always
to disambiguate: either by using different tokens for different roles, or by
reclassifying one usage as internal.

## Related Lints

- [V01](V01-vpa-determinizable.md) -- The positive counterpart: fires when the
  VPA is determinizable. V01 typically cannot fire when V02 fires (the alphabet
  inconsistency prevents clean determinization).
- [V03](V03-wta-unrecognized-term.md) -- WTA term analysis. Orthogonal to VPA
  alphabet classification.
- [G09](../../grammar/G09-unbalanced-delimiters.md) -- Detects mismatched
  open/close brackets in rule syntax. A structural precursor: if delimiters
  are already unbalanced in individual rules, the VPA alphabet classification
  will likely also be inconsistent.
