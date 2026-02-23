# WFST Error Recovery

**Feature gate:** `wfst`

**Date:** 2026-02-22

When the Pratt or recursive-descent parser encounters a token it cannot
consume, it must recover and continue rather than aborting. The unweighted
recovery strategy is "skip to the nearest synchronization token." The
WFST recovery subsystem replaces that single heuristic with a small set of
repair actions each carrying a tropical cost. Recovery is then a minimum-cost
selection problem rather than a fixed-policy skip.

Three tiers of context-awareness stack on top of the base cost model: the
parse frame that triggered the error (Tier 1), the bracket balance at the
error site (Tier 2), and a lightweight simulation of whether a proposed repair
leads to a valid continuation (Tier 3). Each tier multiplies the base cost of
individual repair actions, giving the recovery engine progressively more
precise guidance without requiring a full re-parse.

---

## Table of Contents

1. [RecoveryWfst Construction](#1-recoverywfst-construction)
2. [Repair Actions and Costs](#2-repair-actions-and-costs)
3. [Single-Step Recovery](#3-single-step-recovery)
4. [Viterbi Recovery](#4-viterbi-recovery)
5. [Beam-Pruned Viterbi Recovery](#5-beam-pruned-viterbi-recovery)
6. [Tier 1 — Frame Context](#6-tier-1--frame-context)
7. [Tier 2 — Bracket Balance](#7-tier-2--bracket-balance)
8. [Tier 3 — Parse Simulation](#8-tier-3--parse-simulation)
9. [Worked Example](#9-worked-example)
10. [Source Reference](#10-source-reference)

---

## 1. RecoveryWfst Construction

A `RecoveryWfst` is built per grammar category by `build_recovery_wfsts` in
`recovery.rs`. The builder collects sync tokens from three sources and
annotates each with an `AnnotatedSyncToken` carrying a `SyncSource` tag and a
`weight_multiplier` that discounts recovery actions that target that token.

**Sync token sources:**

1. **EOF** (`SyncSource::Eof`) — always included; the strongest sync point
   because it is unambiguous. Multiplier: 0.6 (applied where relevant).
2. **Structural delimiters** (`SyncSource::StructuralDelimiter`) — closing
   brackets, semicolons, and commas that appear in the grammar's terminal set:
   `)`, `}`, `]`, `;`, `,`. These are unambiguous boundaries. Multiplier: 0.8.
3. **FOLLOW set tokens** (`SyncSource::FollowSet`) — tokens that legitimately
   follow the category in the grammar, computed during pipeline FIRST/FOLLOW
   analysis. Multiplier: 1.0 (no discount).

The check for structural delimiters is grammar-sensitive: a delimiter is only
added as a sync token if the corresponding terminal (`")"`, `"}"`, etc.) is
present in the grammar's terminal set. This prevents the recovery engine from
syncing to delimiters that cannot appear in the input.

The `TokenIdMap` (from `token_id.rs`) converts token name strings to compact
integer IDs for `O(1)` membership tests on the `BTreeSet<TokenId>` inside
`RecoveryWfst`.

---

## 2. Repair Actions and Costs

All repair costs live in the `costs` submodule of `recovery.rs` as
`TropicalWeight` constants.

| Action            | Cost                  | Description                                                                                                           |
|-------------------|-----------------------|-----------------------------------------------------------------------------------------------------------------------|
| `SkipToSync`      | 0.5 per token skipped | Skip unexpected tokens until a sync point is reached. The cost accumulates: skipping 3 tokens costs 1.5.              |
| `DeleteToken`     | 1.0                   | Ignore exactly one unexpected token and try again. The parser advances by one.                                        |
| `SubstituteToken` | 1.5                   | Replace the current token with an expected sync token. The parser advances by one.                                    |
| `InsertToken`     | 2.0                   | Fabricate a missing sync token at the current position without consuming input. The parser position does not advance. |

`MAX_SKIP_LOOKAHEAD = 32` tokens is the bound on how far the skip search
looks. Beyond that bound, no `SkipToSync` option is proposed for tokens past
position 32.

**Rationale for ordering.** Skip is cheapest because it mirrors what unweighted
panic-mode recovery already does — advance past noise until a safe boundary.
Delete is slightly more expensive because it commits to removing exactly one
token, which may be wrong. Substitute penalizes token replacement further.
Insert is most expensive because fabricating a token adds information to the
stream that was not there, increasing the risk of a cascade of secondary errors.

---

## 3. Single-Step Recovery

`RecoveryWfst::find_best_recovery` evaluates all four repair strategies at the
current position and returns the one with the minimum tropical cost:

```
parse error at pos P in category C
        │
        ├─ SkipToSync: scan [P, P+1, ..., P+31] for first sync token
        │   cost = skip_count × 0.5   (if sync at P: cost = 0.0)
        │   → RepairResult { SkipToSync, new_pos = P + skip_count }
        │
        ├─ DeleteToken (if P < len):
        │   cost = 1.0
        │   → RepairResult { DeleteToken, new_pos = P + 1 }
        │
        ├─ InsertToken for each sync_id in sync_tokens:
        │   cost = 2.0
        │   → RepairResult { InsertToken(sync_id), new_pos = P }
        │
        └─ SubstituteToken for each sync_id (if P < len):
            cost = 1.5
            → RepairResult { SubstituteToken(sync_id), new_pos = P + 1 }
```

The function picks the globally minimum cost across all candidates using
`pick_better`, which simply returns the lower-cost `RepairResult` of two. Ties
break in favour of the first candidate (stable ordering).

The `SkipToSync` search stops at the first sync token it finds. Once a sync
token is encountered at distance `k`, the cost is `k × 0.5`. A sync at the
next position (k=1) costs 0.5, which is less than Delete (1.0) and much less
than Insert (2.0). Skipping 3 tokens (cost 1.5) ties with Substitute; 5
tokens (cost 2.5) exceeds Insert. This means Insert is preferred over long
skip chains in grammars where sync tokens are sparse.

---

## 4. Viterbi Recovery

`viterbi_recovery` builds an implicit directed acyclic graph (DAG) over the
lookahead window and finds the minimum-cost path to a sync token using dynamic
programming:

**Lattice structure:**

```
  Nodes: 0, 1, 2, ..., max_lookahead (= sink)

  Edges from node i:
    ─ if token[i] is a sync token:
        i → sink  (cost = 0.0, accumulated from dist[i])
    ─ skip edge:
        i → i+1   (cost += SKIP_PER_TOKEN = 0.5)

  dist[0] = 0.0 (zero cost at start)
  dist[j] = +∞  (unreachable) for j > 0 initially
```

The forward pass processes nodes left to right; each node updates its
successors. `dist[sink]` receives the accumulated skip cost of the best path
to any sync token. The backtrace recovers the skip count from `pred[]`.

This is equivalent to Dijkstra's algorithm on a DAG, which simplifies to a
single left-to-right scan since all edge costs are non-negative and the DAG
is topologically ordered by position.

The Viterbi function returns `None` if no sync token is reachable within
`MAX_SKIP_LOOKAHEAD` positions.

---

## 5. Beam-Pruned Viterbi Recovery

`viterbi_recovery_beam` extends `viterbi_recovery` with an optional beam
threshold. At each position, if the accumulated path cost to that position
already exceeds `dist[sink] + beam_width` — meaning the path cannot improve
on the best known sync cost within the beam — that position is skipped.

The pruning is safe because the sink's best known cost monotonically
decreases as better sync tokens are discovered. A path that cannot beat
`dist[sink] + beam_width` at position `i` also cannot beat it at `i+j` for
any `j > 0` (since further skips only increase cost).

When `beam_width` is `None`, `viterbi_recovery_beam` is identical to
`viterbi_recovery`.

---

## 6. Tier 1 — Frame Context

**Tier 1** adjusts the base repair costs by multiplying them with context
factors derived from where in the parse tree the error occurred.

The `RecoveryContext` struct captures:

- `frame_kind: FrameKind` — the parse frame type
- `depth: usize` — nesting depth in the parse stack
- `binding_power: u8` — current Pratt binding power

The `FrameKind` enum covers all frame types that arise during trampoline
parsing:

| Variant      | Description                                |
|--------------|--------------------------------------------|
| `Prefix`     | Pratt prefix handler (atom, unary prefix)  |
| `InfixRHS`   | Right-hand side of a binary infix operator |
| `Postfix`    | Postfix operator position                  |
| `Collection` | Collection body (list, set, map)           |
| `Group`      | Parenthesized or bracketed group           |
| `Mixfix`     | Multi-part operator position (e.g., `? :`) |
| `Lambda`     | Lambda binder body                         |
| `Dollar`     | Dollar application body                    |
| `CastWrap`   | Cross-category cast wrapper                |
| `Other`      | Generic / unknown context                  |

The three multiplier methods on `RecoveryContext`:

**`skip_multiplier()`** — scales `SkipToSync` and `DeleteToken` costs:

| Condition                | Multiplier                                          |
|--------------------------|-----------------------------------------------------|
| `depth > 1000`           | × 0.5 — deep nesting; noise is likely, skip is safe |
| `depth < 10`             | × 2.0 — shallow; precise repair preferred           |
| `frame_kind == InfixRHS` | × 0.75 — bad operand; skip to next statement        |
| `binding_power < 4`      | × 0.75 — loose binding; skipping is safe            |

Multiple conditions compound multiplicatively. For example, a shallow InfixRHS
frame with neutral binding power gives skip multiplier `2.0 × 0.75 = 1.5`.

**`insert_multiplier()`** — scales `InsertToken` costs:

| Condition                  | Multiplier                                         |
|----------------------------|----------------------------------------------------|
| `frame_kind == Collection` | × 0.5 — missing element/separator is common        |
| `frame_kind == Group`      | × 0.5 — missing closing delimiter is common        |
| `binding_power > 20`       | × 1.5 — deep tight-binding context; precise repair |

**`substitute_multiplier()`** — scales `SubstituteToken` costs:

| Condition              | Multiplier                                  |
|------------------------|---------------------------------------------|
| `frame_kind == Mixfix` | × 0.75 — wrong token in multi-part operator |

---

## 7. Tier 2 — Bracket Balance

**Tier 2** tracks whether any bracket tokens are unmatched at the error site.
`RecoveryContext` carries three counters: `open_parens`, `open_braces`, and
`open_brackets`. These are maintained by the generated parser code and passed
into recovery.

`bracket_insert_multiplier(token_name)` returns:

| Condition                                          | Multiplier |
|----------------------------------------------------|------------|
| `token_name == "RParen"` and `open_parens > 0`     | × 0.3      |
| `token_name == "RBrace"` and `open_braces > 0`     | × 0.3      |
| `token_name == "RBracket"` and `open_brackets > 0` | × 0.3      |
| All other cases                                    | × 1.0      |

The 0.3 multiplier strongly discounts inserting a closing bracket when there
is a matching unmatched open bracket. This captures the common error pattern
of a missing closing delimiter in a nested expression.

Tier 2 multipliers apply only to `InsertToken` actions. The total insert cost
for a sync token `s` in `find_best_recovery_contextual` is:

```
insert_cost(s) = 2.0 × insert_multiplier() × bracket_insert_multiplier(name(s)) × tier3_mult(s)
```

---

## 8. Tier 3 — Parse Simulation

**Tier 3** uses a lightweight `ParseSimulator` to check whether a proposed
repair leads to a plausible parse continuation. It does not actually parse —
it checks a simplified state machine against FIRST, FOLLOW, and infix token
sets over a `lookahead_depth`-token window (default 5).

**Simulation algorithm** (`simulate_after_repair`):

```
for offset in 0..lookahead_depth:
    token = input[pos + offset]
    if token ∈ FIRST(category)  → consume, continue
    if token ∈ infix_tokens(category) → valid continuation, continue
    if token ∈ FOLLOW(category) → category ends here → ValidContinuation
    else → FailedAt { position: offset }
end-of-input or lookahead exhausted → ValidContinuation
```

**Cost multiplier from simulation result:**

| Result                     | Multiplier                                                               |
|----------------------------|--------------------------------------------------------------------------|
| `ValidContinuation`        | × 0.5 — repair leads to good continuation                                |
| `FailedAt { position: n }` | × (1.0 + (lookahead\_depth − n) × 0.2) — earlier failures penalized more |

For example, with `lookahead_depth = 5`, a failure at position 4 (near the
end of the window) gives multiplier `1.0 + (5 − 4) × 0.2 = 1.2`. A failure
at position 0 (the repair itself immediately fails) gives multiplier
`1.0 + 5 × 0.2 = 2.0`.

The `ParseSimulator` is optional. When `simulator` is `None`, Tier 3
multipliers default to 1.0 (no adjustment).

---

## 9. Worked Example

**Input:** `a + * b`

**Error:** the parser is in `parse_Expr`, positioned after consuming `a +`,
expecting an expression but seeing `*`.

**Context:** `FrameKind::InfixRHS`, `depth = 3`, `binding_power = 10`,
`open_parens = 0`, `open_braces = 0`. Simulator available with
`FIRST(Expr) = {Integer, Ident, LParen}`, `FOLLOW(Expr) = {Semi, RParen, Eof}`,
`infix_tokens(Expr) = {Plus, Minus, Star, Slash}`.

**Sync tokens for Expr:** `{Eof, Semi}` (no structural delimiters in grammar
for this example).

**Repair candidates:**

```
SkipToSync:
  next sync token in [*, b, …] — none in first 32 tokens except EOF
  (assume: Semi at position 4, skip_count = 3)
  base cost = 3 × 0.5 = 1.5
  Tier 1 skip_multiplier = 0.75 (InfixRHS) × 1.0 (neutral depth) = 0.75
  Tier 3: simulate after pos+3 (at "b"): Ident ∈ FIRST(Expr) → ValidContinuation → 0.5×
  adjusted = 1.5 × 0.75 × 0.5 = 0.5625

DeleteToken:
  base cost = 1.0
  Tier 1 skip_multiplier = 0.75 (InfixRHS)
  Tier 3: simulate after pos+1 (at "b"): Ident ∈ FIRST(Expr) → ValidContinuation → 0.5×
  adjusted = 1.0 × 0.75 × 0.5 = 0.375

InsertToken(Semi):
  base cost = 2.0
  Tier 1 insert_multiplier = 1.0 (no Collection/Group frame)
  Tier 2 bracket_insert_multiplier("Semi") = 1.0 (no open brackets)
  Tier 3: simulate at pos (at "*"): * ∈ infix_tokens → ValidContinuation → 0.5×
  adjusted = 2.0 × 1.0 × 1.0 × 0.5 = 1.0

InsertToken(Eof):
  (similar — cost ≥ 1.0)

SubstituteToken(Semi):
  base cost = 1.5
  Tier 1 substitute_multiplier = 1.0 (no Mixfix frame)
  Tier 3: simulate after pos+1 (at "b"): ValidContinuation → 0.5×
  adjusted = 1.5 × 1.0 × 0.5 = 0.75
```

**Winner:** `DeleteToken` at effective cost 0.375.

Interpretation: deleting `*` and continuing at `b` is the cheapest repair. The
parser removes the spurious `*` operator, then parses `b` as the right-hand
operand of `+`. The result is the expression `a + b`.

---

## 10. Worked Diagrams

### 10.1 Repair Lattice (Single-Step View)

```
  input: [ a ][ + ][ * ][ b ][ ; ]
                       ↑
                  error at pos P

  repair lattice from pos P:

  ┌────────────────────────────────────────────────────────────┐
  │                                                            │
  │   skip 1 (0.5)    skip 2 (1.0)    sync at ;                │
  │   P ─────────── P+1 ──────────── P+2 ─────────── P+3       │
  │   │              │                │               │        │
  │   │ delete(1.0)  │ delete(1.0)    │ delete(1.0)   │        │
  │   │              │                │               │        │
  │   P+1            P+2              P+3             P+4      │
  │                                                            │
  │   insert at P (2.0):  fabricate missing token, stay at P   │
  │   substitute at P (1.5): replace *, advance to P+1         │
  │                                                            │
  └────────────────────────────────────────────────────────────┘
```

### 10.2 Three-Tier Cost Pyramid

```
  ┌─────────────────────────────────────────────────────┐
  │                  Tier 3                             │
  │           Parse Simulation                          │
  │    (simulate_after_repair, lookahead 5 tokens)      │
  │    cost multiplier: 0.5× (valid) .. 2.0× (failed)   │
  │    ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈      │
  │                  Tier 2                             │
  │            Bracket Balance                          │
  │   (open_parens / open_braces / open_brackets)       │
  │   insert matching closer: 0.3× (strongly preferred) │
  │   ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈       │
  │                  Tier 1                             │
  │           Frame Context                             │
  │   (FrameKind, depth, binding_power)                 │
  │   skip_mult / insert_mult / substitute_mult         │
  │   ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈ ┈       │
  │              Base Costs                             │
  │     Skip 0.5/tok · Delete 1.0 · Sub 1.5 · Ins 2.0   │
  └─────────────────────────────────────────────────────┘
```

Tier 1 is always applied (cheapest: simple multiplications from struct fields).
Tier 2 is applied for `InsertToken` when bracket counters are populated.
Tier 3 is applied only when a `ParseSimulator` is provided (optional).
Each tier multiplies the cost from the tier below it.

---

## 11. Runtime Reconstruction and Codegen Integration

### 11.1 `RecoveryWfst::from_flat()`

The pipeline serializes recovery WFSTs as static arrays in generated code
via `emit_recovery_wfst_static()`. At runtime, `RecoveryWfst::from_flat()`
reconstructs the struct from these arrays:

```rust
pub fn from_flat(
    category: &str,
    sync_token_ids: &[u16],
    _sync_sources: &[(u16, u8)],
    token_names: &[&str],
) -> Self
```

This reconstructs the `BTreeSet<TokenId>` of sync tokens and the
`TokenIdMap` for name lookups.

### 11.2 `ParseSimulator::from_flat()`

```rust
pub fn from_flat(
    first_set_tokens: &[(&str, &[u16])],
    follow_set_tokens: &[(&str, &[u16])],
    infix_tokens: &[(&str, &[u16])],
    lookahead_depth: usize,
) -> Self
```

Reconstructs the FIRST/FOLLOW/infix sets from flat arrays of
(category_name, token_id_slice) pairs.

### 11.3 Full 4-Strategy Codegen

The generated `wfst_recover_Cat()` function now evaluates all four repair
strategies with context parameters:

```rust
fn wfst_recover_Cat<'a>(
    tokens: &[(Token<'a>, Span)],
    pos: &mut usize,
    depth: usize,
    binding_power: u8,
    open_parens: u16,
    open_braces: u16,
    open_brackets: u16,
) -> bool
```

**Bracket balance estimation:** The recovering trampoline scans tokens
consumed so far to estimate bracket balance before calling recovery:

```rust
let mut op: u16 = 0; let mut ob: u16 = 0; let mut ok: u16 = 0;
for i in 0..*pos {
    match &tokens[i].0 {
        Token::LParen => op = op.saturating_add(1),
        Token::RParen => op = op.saturating_sub(1),
        Token::LBrace => ob = ob.saturating_add(1),
        Token::RBrace => ob = ob.saturating_sub(1),
        Token::LBracket => ok = ok.saturating_add(1),
        Token::RBracket => ok = ok.saturating_sub(1),
        _ => {}
    }
}
```

This is O(pos) but only runs on error paths — zero overhead on the happy
path.

---

## 12. Source Reference

| Symbol                      | Location                   |
|-----------------------------|----------------------------|
| `RecoveryWfst`              | `prattail/src/recovery.rs` |
| `RepairAction`              | `prattail/src/recovery.rs` |
| `RepairResult`              | `prattail/src/recovery.rs` |
| `FrameKind`                 | `prattail/src/recovery.rs` |
| `RecoveryContext`           | `prattail/src/recovery.rs` |
| `AnnotatedSyncToken`        | `prattail/src/recovery.rs` |
| `SyncSource`                | `prattail/src/recovery.rs` |
| `ParseSimulator`            | `prattail/src/recovery.rs` |
| `SimulationResult`          | `prattail/src/recovery.rs` |
| `viterbi_recovery`          | `prattail/src/recovery.rs` |
| `viterbi_recovery_beam`     | `prattail/src/recovery.rs` |
| `build_recovery_wfsts`      | `prattail/src/recovery.rs` |
| `RecoveryWfst::from_flat`   | `prattail/src/recovery.rs` |
| `ParseSimulator::from_flat` | `prattail/src/recovery.rs` |
| `emit_recovery_wfst_static` | `prattail/src/pipeline.rs` |
| `costs` submodule           | `prattail/src/recovery.rs` |

Test count: 34 (in `prattail/src/recovery.rs` `#[cfg(test)]` module).

See also:
- [prediction.md](prediction.md) — prediction WFST (uses the same `TokenIdMap`)
- [../theory/viterbi-and-forward-backward.md](../theory/viterbi-and-forward-backward.md) — Viterbi algorithm correctness
- [weight-training.md](weight-training.md) — log-semiring training that can tune recovery weights
