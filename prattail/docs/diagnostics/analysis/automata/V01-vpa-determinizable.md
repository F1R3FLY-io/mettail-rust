# V01: vpa-determinizable

**Severity:** Note
**Category:** analysis/automata
**Feature Gate:** `vpa`

## Description

Confirms that the grammar's **structured sublanguage** -- the fragment involving
matched delimiters such as parentheses, brackets, and braces -- admits a
deterministic **visibly pushdown automaton** (VPA) with zero backtracking.

A VPA is a restricted form of pushdown automaton where the input alphabet is
partitioned into three disjoint classes:

    Sigma = Sigma_c  union  Sigma_r  union  Sigma_i

- **Sigma_c (call/push):** Tokens that push a symbol onto the stack (opening
  delimiters: `(`, `[`, `{`, `<`, etc.).
- **Sigma_r (return/pop):** Tokens that pop from the stack (closing delimiters:
  `)`, `]`, `}`, `>`, etc.).
- **Sigma_i (internal):** Tokens that leave the stack unchanged (operators,
  identifiers, literals, keywords).

The key property of VPAs is that the stack behavior is determined entirely by
the input symbol -- unlike general pushdown automata where the same symbol can
push, pop, or leave the stack unchanged depending on the current state. This
"visibility" constraint makes VPAs closed under complementation, intersection,
and determinization, unlike general CFGs.

```
  VPA Alphabet Partition
  ══════════════════════

  ┌──────────────────────────────────────────────┐
  │               Sigma (all tokens)             │
  │                                              │
  │  ┌──────────┐  ┌──────────┐  ┌────────────┐ │
  │  │ Sigma_c  │  │ Sigma_r  │  │  Sigma_i   │ │
  │  │  (call)  │  │ (return) │  │ (internal) │ │
  │  │  (  [  { │  │  )  ]  } │  │  +  -  id  │ │
  │  │  push    │  │  pop     │  │  no-op     │ │
  │  └──────────┘  └──────────┘  └────────────┘ │
  │                                              │
  │  disjoint: Sigma_c cap Sigma_r = emptyset    │
  │  disjoint: Sigma_c cap Sigma_i = emptyset    │
  │  disjoint: Sigma_r cap Sigma_i = emptyset    │
  └──────────────────────────────────────────────┘
```

When the analysis determines that the grammar's delimiter structure admits a
deterministic VPA, V01 fires with the resulting state count. A deterministic VPA
means that the structured sublanguage can be parsed without any backtracking or
speculation -- each token uniquely determines the next state and stack action.

This is a strong positive signal: the grammar's nesting structure is
well-formed, and delimiter-driven parsing is efficient.

## Trigger Conditions

All of the following must hold:

- The `vpa` feature is enabled at compile time.
- A `VpaAnalysis` result is available in the lint context.
- The `is_determinizable` field is `true` (the constructed nondeterministic VPA
  can be determinized without exponential blowup, and the resulting DVPA has
  `state_count` states).

Exactly one V01 diagnostic is emitted per grammar.

## Example

### Grammar

```rust
language! {
    name: SimpleExpr,
    types {
        ![i32] as Expr
    },
    terms {
        Num    . |- <int> : Expr;
        Add    . a:Expr, b:Expr |- a "+" b : Expr ![a + b] fold;
        Paren  . e:Expr |- "(" e ")" : Expr;
        Index  . a:Expr, i:Expr |- a "[" i "]" : Expr;
        Block  . e:Expr |- "{" e "}" : Expr;
    },
}
```

### Output

```
note[V01] (SimpleExpr): grammar's structured sublanguage admits zero-backtracking VPA (5 states)
```

## Resolution

No action is required. V01 is an informational note confirming that the
grammar's delimiter structure is clean and deterministic.

The state count provides a measure of the structural complexity of the
delimiter-driven fragment. A lower state count indicates a simpler nesting
structure; a higher count may suggest that multiple delimiter types interact in
nuanced ways (but still deterministically).

## Hint Explanation

This lint has no hint. The grammar's structured sublanguage is determinizable
and no corrective action is needed.

## Related Lints

- [V02](V02-vpa-alphabet-mismatch.md) -- Fires when a token is classified as
  both a call (opening delimiter) and a return (closing delimiter), violating
  the disjointness requirement of the VPA alphabet partition. If V02 fires, V01
  typically will not (the alphabet inconsistency prevents determinization).
- [V03](V03-wta-unrecognized-term.md) -- WTA analysis of the term structure.
  Orthogonal to VPA analysis but part of the same automata framework.
- [V04](V04-wta-hot-path.md) -- WTA hot-path detection. Orthogonal to VPA.
