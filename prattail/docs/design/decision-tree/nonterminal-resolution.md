# PraTTaIL Decision Tree — Nonterminal Resolution

| Metadata | Value                                                                    |
|----------|--------------------------------------------------------------------------|
| Date     | 2026-03-06                                                               |
| Updated  | 2026-03-06                                                               |
| Source   | `prattail/src/decision_tree.rs` (L719-864), `prattail/src/prediction.rs` |

---

## Table of Contents

- [§1 Problem Statement](#1-problem-statement)
- [§2 FIRST Set Expansion at NT Boundaries](#2-first-set-expansion-at-nt-boundaries)
- [§3 Three Resolution Strategies](#3-three-resolution-strategies)
- [§4 The resolve_nonterminal_boundaries Algorithm](#4-the-resolve_nonterminal_boundaries-algorithm)
- [§5 Disjointness Analysis](#5-disjointness-analysis)
- [§6 Correctness Argument](#6-correctness-argument)
- [§7 Worked Examples](#7-worked-examples)
- [§8 Interaction with Dispatch Strategy](#8-interaction-with-dispatch-strategy)

---

## §1 Problem Statement

When the trie is split at a nonterminal boundary (see
[trie-construction.md §4](trie-construction.md#4-segment-splitting-at-nt-boundaries)),
the parser reaches a point where it must decide which nonterminal to enter.
Consider the trie node at byte path `[id_float, id_lparen]` in the Float
category:

```
  Rule A: float ( <Ident> )     ← IDENT_CAPTURE at position 2
  Rule B: float ( <Int> )       ← NonTerminal("Int") at position 2
```

Both rules share the terminal prefix `float (`.  After consuming these two
tokens, the parser sees the next token and must choose:

- If the next token can **only** start an `Int` expression → commit to Rule B
- If the next token is an `Ident` that cannot start `Int` → commit to Rule A
- If the next token is ambiguous (e.g., `Ident` is in both FIRST(Int) and
  FIRST(IdentCapture)) → NFA try-all is required

This decision is made by **FIRST set expansion** at nonterminal boundaries.

---

## §2 FIRST Set Expansion at NT Boundaries

At each nonterminal boundary, the resolver expands the nonterminal's FIRST set
to determine which tokens can appear immediately after the shared terminal
prefix.

### §2.1 FIRST Set Definition

For a syntactic category C, `FIRST(C)` is the set of terminal tokens that can
appear as the first token of any derivation from C:

```
  FIRST(C) = { t ∈ Terminals | ∃ derivation C ⟹* t α }
```

FIRST sets are computed during the pipeline's analysis phase
(`compute_first_sets()` in `prediction.rs`) before the decision tree is built.

### §2.2 Expansion at Boundary

When the trie reaches a nonterminal boundary for category C at some path P,
the tokens that can follow P are:

```
  next_tokens(P, C) = FIRST(C)
```

For an `IdentCapture` at the same boundary:

```
  next_tokens(P, IdentCapture) = { Ident }
```

For a `BinderCapture`:

```
  next_tokens(P, BinderCapture) = { Ident }
```

The union of these sets across all options at the boundary determines the total
token space the parser might encounter.

---

## §3 Three Resolution Strategies

Based on FIRST set analysis, each nonterminal boundary resolves into one of
three strategies:

### §3.1 Strategy 1: Pre-NT Split (Deterministic)

**Condition:** The FIRST sets of all options at the boundary are pairwise
disjoint.

```
  ∀ i ≠ j: FIRST(option_i) ∩ FIRST(option_j) = ∅
```

**Result:** The parser peeks the next token and deterministically selects the
correct option.  No backtracking is needed.

```
  Trie structure at boundary:

            shared prefix P
                  │
          ┌───────┼───────┐
          ▼       ▼       ▼
     FIRST(A)  FIRST(B)  FIRST(C)
     disjoint  disjoint  disjoint
          │       │       │
    Segment k  Segment m  Segment n
    (cont. A)  (cont. B)  (cont. C)
```

**Code generation:** The trampoline emits a `match` on the peeked token:

```
  match peek_token() {
      t if t in FIRST(A) => enter_A(),   // segment k
      t if t in FIRST(B) => enter_B(),   // segment m
      t if t in FIRST(C) => enter_C(),   // segment n
      _ => error("unexpected token"),
  }
```

### §3.2 Strategy 2: Post-NT Continuation (Deterministic, Deferred)

**Condition:** The FIRST sets overlap, but the **continuation segments** after
each option have disjoint FIRST sets.

```
  FIRST(option_i) ∩ FIRST(option_j) ≠ ∅
  but
  FIRST(continuation_i) ∩ FIRST(continuation_j) = ∅
```

**Result:** The parser speculatively enters a nonterminal, then checks the
token after the nonterminal returns.  The continuation segment's first token
disambiguates.

```
  Trie structure:

            shared prefix P
                  │
                  ▼
            NT boundary
           (overlapping FIRST)
                  │
          ┌───────┼───────┐
          ▼       ▼       ▼
       cont_A   cont_B   cont_C
       FIRST    FIRST    FIRST
     disjoint  disjoint  disjoint
```

**Example:** Rules `float ( <Int> )` and `float ( <Int> ]` (hypothetical).
Both enter `Int`, but the continuation tokens `)` vs `]` are disjoint.  After
parsing `Int`, the parser peeks `)` or `]` to choose the rule.

### §3.3 Strategy 3: FIRST Overlap (Ambiguous) → NFA Try-All

**Condition:** FIRST sets overlap and cannot be resolved by continuation
analysis.

```
  ∃ i ≠ j: FIRST(option_i) ∩ FIRST(option_j) ≠ ∅
  and continuation analysis does not resolve the overlap
```

**Result:** The boundary is marked `Ambiguous`.  The parser must use NFA
try-all dispatch: save state, try each candidate in weight order, and
accept the first that succeeds.

```
  Trie structure:

            shared prefix P
                  │
                  ▼
        ╔═══════════════════╗
        ║    AMBIGUOUS      ║
        ║  candidates:      ║
        ║    Rule A (w=0.0) ║
        ║    Rule B (w=0.0) ║
        ╚═══════════════════╝
```

**Code generation:** The trampoline emits save/restore backtracking:

```
  let save = save_state();
  // Try candidate with lowest weight first
  if let Ok(result) = try_rule_A() { return result; }
  restore_state(save);
  if let Ok(result) = try_rule_B() { return result; }
  restore_state(save);
  error("no candidate matched")
```

---

## §4 The resolve_nonterminal_boundaries Algorithm

The resolver function `resolve_nonterminal_boundaries()` (L728-779) implements
FIRST set disjointness checking for all NT boundaries in a tree.

### §4.1 Algorithm Pseudocode

```
fn resolve_nonterminal_boundaries(tree, first_sets):
    for segment in tree.segments:
        updates ← []
        for (path, action) in segment.iter():
            if action is NonterminalBoundary { options }:
                all_first_tokens ← {}
                has_overlap ← false
                for opt in options:
                    for tok_id in opt.first_tokens:
                        if tok_id ≤ MAX_TERMINAL_ID:
                            if tok_id already in all_first_tokens:
                                has_overlap ← true
                            insert tok_id into all_first_tokens
                if has_overlap:
                    candidates ← options.map(opt → AmbiguousCandidate {
                        label: opt.kind.name(),
                        weight: opt.weight,
                    })
                    updates.push((path, Ambiguous { candidates }))
                // If no overlap, boundary stays deterministic
        for (path, action) in updates:
            segment.insert(path, action)
```

### §4.2 Key Properties

1. **Conservative:** If any overlap is detected, the entire boundary is
   marked ambiguous.  No partial resolution is attempted.

2. **Per-segment:** Each segment is resolved independently.  A boundary in
   segment 0 does not affect resolution of boundaries in continuation segments.

3. **Idempotent:** Running the resolver multiple times produces the same
   result.  Once a boundary is converted to `Ambiguous`, re-running does not
   change it (the action is no longer `NonterminalBoundary`).

### §4.3 Complexity

The resolver iterates all (path, value) pairs in each segment once, performing
a set-intersection check per boundary.  For a tree with S segments and N total
entries:

```
  Time: O(N × max_options_per_boundary)
  Space: O(max_FIRST_set_size) for the overlap check set
```

In practice, `max_options_per_boundary` is small (2-4).

---

## §5 Disjointness Analysis

### §5.1 Pairwise Disjointness

Two FIRST sets F_i and F_j are disjoint if they share no terminal token:

```
  disjoint(F_i, F_j) ⟺ F_i ∩ F_j = ∅
```

For N options at a boundary, full disjointness requires all pairs to be
disjoint:

```
  fully_disjoint(F₁, ..., F_N) ⟺ ∀ i ≠ j: F_i ∩ F_j = ∅
```

Equivalently, the union has no duplicates:

```
  fully_disjoint ⟺ |F₁ ∪ ... ∪ F_N| = |F₁| + ... + |F_N|
```

The resolver uses the duplicate-insertion check (L744-746) which is equivalent
to the union cardinality test.

### §5.2 Terminal vs Non-Terminal Bytes

Only bytes in the terminal range (`0x00..0x7F`) participate in disjointness
analysis.  Capture markers (`0x80`, `0x81`) and optional markers (`0xC0`,
`0xC1`) are not FIRST set elements — they represent structural positions, not
tokens.

```
  ∀ tok_id in boundary.first_tokens:
      tok_id ≤ 0x7F ⟹ participates in disjointness check
      tok_id > 0x7F ⟹ ignored (structural marker)
```

### §5.3 Ident Overlap

The `Ident` token is a common source of FIRST set overlap.  Both
`IdentCapture` and many nonterminal categories include `Ident` in their FIRST
sets.  This makes `Ident`-related boundaries frequently ambiguous:

```
  FIRST(IdentCapture) = { Ident }
  FIRST(Int)          = { Integer, Ident, LParen, ... }
  FIRST(Expr)         = { Integer, Ident, LParen, KwIf, ... }

  FIRST(IdentCapture) ∩ FIRST(Int) = { Ident } ≠ ∅
      → AMBIGUOUS
```

---

## §6 Correctness Argument

### §6.1 Soundness

**Claim:** If the resolver marks a boundary as deterministic (no overlap), then
the parser can always choose the correct option by peeking one token.

**Argument:** Let options O₁, ..., O_N have pairwise disjoint FIRST sets
F₁, ..., F_N.  At runtime, the parser peeks token `t`.

- Case 1: `t ∈ F_i` for exactly one i.  The parser enters option O_i.  Since
  `t ∈ FIRST(O_i)`, the option can produce a derivation starting with `t`.
  Since `t ∉ F_j` for j ≠ i, no other option can produce a derivation starting
  with `t`.  The choice is correct.

- Case 2: `t ∉ F_i` for any i.  The token does not match any option's FIRST
  set.  This is a parse error, correctly detected.

- Case 3: `t ∈ F_i ∩ F_j`.  This contradicts the disjointness assumption.
  The resolver would have marked the boundary as ambiguous, so this case does
  not arise under a deterministic boundary.

### §6.2 Completeness

**Claim:** If the resolver marks a boundary as ambiguous, then there exists at
least one token that genuinely requires backtracking.

**Argument:** The resolver finds `t ∈ FIRST(O_i) ∩ FIRST(O_j)`.  This means
both O_i and O_j can produce derivations starting with `t`.  The parser cannot
distinguish O_i from O_j by peeking `t` alone.

Note: This is sound but not tight.  The overlap token `t` might not lead to a
complete parse under one of the options (the FIRST set is an overapproximation
of reachable first tokens).  A tighter analysis would require full LL(k)
lookahead or semantic analysis, which is beyond the scope of this mechanism.
The decision tree conservatively falls back to NFA try-all, preserving
correctness.

### §6.3 Termination

The resolver iterates each segment's entries exactly once.  The inner loop
iterates each option's FIRST tokens.  Both are bounded by grammar size.  The
resolver terminates in finite time.

---

## §7 Worked Examples

### §7.1 Example: Deterministic Boundary (Pre-NT Split)

**Grammar:**

```
  Category: Stmt
    WhileStmt:  while <BoolExpr> do <Stmt>
    ForStmt:    while <IntExpr> step <Stmt>
    // (hypothetical: "while" dispatches to two rules with different NT types)
```

Assume `FIRST(BoolExpr) = { KwTrue, KwFalse }` and
`FIRST(IntExpr) = { Integer, LParen }`.

After encoding, both rules share prefix `[id_while]` and reach an NT boundary.
The resolver checks:

```
  FIRST(BoolExpr) ∩ FIRST(IntExpr) = { KwTrue, KwFalse } ∩ { Integer, LParen }
                                    = ∅
```

Result: **Deterministic.**  The trie node remains a `NonterminalBoundary` with
disjoint options.

```
  Trie at boundary:

           [id_while]
               │
       ┌───────┼───────┐
       ▼               ▼
  KwTrue/KwFalse    Integer/LParen
  → enter BoolExpr  → enter IntExpr
  → resume seg 1    → resume seg 2
```

### §7.2 Example: Ambiguous Boundary (FIRST Overlap)

**Grammar:**

```
  Category: Float
    FloatId:     float ( <Ident> )
    IntToFloat:  float ( <Int> )
```

Assume `FIRST(IdentCapture) = { Ident }` and
`FIRST(Int) = { Integer, Ident, LParen }`.

The resolver checks:

```
  FIRST(IdentCapture) ∩ FIRST(Int) = { Ident } ∩ { Integer, Ident, LParen }
                                    = { Ident }
                                    ≠ ∅
```

Result: **Ambiguous.**  The boundary is converted to:

```
  Ambiguous {
    candidates: [
      { label: "ident_capture", weight: 0.0 },
      { label: "NT:Int",        weight: 0.0 },
    ]
  }
```

The `dispatch_strategy()` query for `KwFloat` will return `NfaTryAll`.

### §7.3 Example: Post-NT Continuation Resolution

**Grammar:**

```
  Category: Container
    ArrayLit:  [ <Expr> ]
    SetLit:    [ <Expr> }
    // (hypothetical: both enter Expr, but closing delimiter differs)
```

Both rules share prefix `[id_lbracket]` and enter `NonTerminal("Expr")`.
Their FIRST sets overlap (`FIRST(Expr) = FIRST(Expr)` trivially).

However, the continuation segments differ:

```
  ArrayLit continuation: [id_rbracket]    (token "]")
  SetLit continuation:   [id_rbrace]      (token "}")
```

Since `{ RBracket } ∩ { RBrace } = ∅`, the parser can:

1. Enter `Expr` (same for both rules).
2. After `Expr` returns, peek the next token.
3. If `]` → commit to `ArrayLit`.
4. If `}` → commit to `SetLit`.

This post-NT continuation strategy avoids NFA try-all by deferring the
disambiguation to the first differing terminal after the shared nonterminal.

---

## §8 Interaction with Dispatch Strategy

The resolution of nonterminal boundaries feeds into the `dispatch_strategy()`
query (L1674-1798).  The mapping is:

| Boundary Resolution           | DispatchStrategy Result                                               |
|-------------------------------|-----------------------------------------------------------------------|
| Fully disjoint FIRST sets     | `DisjointSuffix` (if suffixes are terminal) or deterministic NT entry |
| Post-NT continuation disjoint | `DisjointSuffix` with `shared_prefix_len` covering the NT             |
| FIRST overlap → Ambiguous     | `NfaTryAll` with all candidates from the boundary                     |
| Single option at boundary     | `Singleton` (no disambiguation needed)                                |

The `dispatch_strategy()` function checks whether the branch byte after the
shared prefix is a terminal (`≤ MAX_TERMINAL_ID`).  If the branch byte is a
non-terminal or capture marker (`> MAX_TERMINAL_ID`), the function cannot
determine suffix disjointness from the trie alone and falls back to
`NfaTryAll`:

```rust
// From dispatch_strategy (L1749-1752):
let branch_byte = path[shared_len];
if branch_byte > MAX_TERMINAL_ID {
    is_disjoint = false;
    break;
}
```

This conservative check ensures that nonterminal boundaries are never
incorrectly treated as deterministic by the trie-walk logic.  The actual
determinism of an NT boundary depends on FIRST set resolution (§4), not on
trie path structure alone.
