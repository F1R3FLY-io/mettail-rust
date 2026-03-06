# NFA Spillover Thread-Local Architecture

**Date:** 2026-03-01

---

## Table of Contents

1. [Overview](#1-overview)
2. [Memory Layout](#2-memory-layout)
3. [Cell Take/Set Protocol](#3-cellltvectgtgt-takeset-protocol)
4. [Lifetime and Re-Entrancy](#4-lifetime-and-re-entrancy)
5. [Zero-Overhead Analysis](#5-zero-overhead-analysis)
6. [Data Flow Diagram](#6-data-flow-diagram)

---

## 1. Overview

When multiple grammar rules within a single category share the same dispatch
token, the parser cannot determine which rule applies from lookahead alone.
PraTTaIL resolves this through **NFA disambiguation** (Layer 2.5): the
generated parser tries all candidate rules for the ambiguous token, collects
successful parses, and defers final resolution to semantic disambiguation.

This architecture requires communicating parse results **across call
boundaries** --- the NFA merged prefix arm inside `parse_Cat()` produces N
alternatives, but the replay and final disambiguation happen in
`parse_preserving_vars()`, a separate function that orchestrates cross-category
parsing. Thread-local storage (TLS) provides the communication channel.

Four `Cell<>` thread-locals per category enable:

- **Zero-allocation spillover**: the best alternative is returned normally;
  the remaining N-1 are buffered in a reusable `Vec` for later replay.
- **Forced-prefix replay**: each spilled alternative is injected back into the
  parser via an `Option` override, bypassing the NFA try-all so it receives
  its own infix context (e.g., `float(x) + 1.0`).
- **Weight tracking**: WFST tropical weights accompany each alternative through
  spillover and replay, enabling weight-aware tiebreaking in
  `from_alternatives()`.

**Source files:**

- `prattail/src/trampoline.rs` --- thread-local declarations, NFA merged arm
  codegen, forced-prefix check
- `macros/src/gen/runtime/language.rs` --- drain loop in
  `parse_preserving_vars()`, `AMBIGUOUS_WEIGHTS`, weight-aware
  `from_alternatives()`
- `prattail/src/wfst.rs` --- `PredictionWfst::nfa_alternative_order()`

---

## 2. Memory Layout

Each grammar category `Cat` receives four thread-locals, emitted by
`trampoline.rs:write_trampoline_parser()` (lines 1143--1173). They are emitted
for **all** categories --- not only those with NFA ambiguity --- so that
`parse_preserving_vars()` can unconditionally drain without conditional
compilation. Operating on empty `Cell` contents is essentially free (see
[Section 5](#5-zero-overhead-analysis)).

### 2.1 Thread-Local Declarations

```rust
thread_local! {
    // Spillover buffer: N-1 alternatives from the NFA merged arm.
    // Each entry: (parsed_value, end_position, tropical_weight)
    static NFA_PREFIX_SPILL_CAT: Cell<Vec<(Cat, usize, f64)>> =
        Cell::new(Vec::new());

    // Forced-prefix override: set before replay so the parser
    // skips NFA try-all and uses this value directly as lhs.
    static NFA_FORCED_PREFIX_CAT: Cell<Option<(Cat, usize, f64)>> =
        Cell::new(None);

    // Primary result weight: the WFST tropical weight of the best
    // (returned) NFA result. Read by parse_preserving_vars to
    // populate the success_weights vector.
    static NFA_PRIMARY_WEIGHT_CAT: Cell<f64> =
        Cell::new(0.5);

    // B2 accumulated dispatch confidence: sum of tropical weights
    // along the parse path. Higher = more ambiguous. Used by
    // error recovery to select repair strategy.
    static RUNNING_WEIGHT_CAT: Cell<f64> =
        Cell::new(0.0);
}
```

### 2.2 Per-Variable Semantics

| Thread-Local             | Type                              | Default     | Written By                      | Read By                                      |
|--------------------------|-----------------------------------|-------------|---------------------------------|----------------------------------------------|
| `NFA_PREFIX_SPILL_CAT`   | `Cell<Vec<(Cat, usize, f64)>>`    | Empty `Vec` | NFA merged arm (spillover)      | `parse_preserving_vars()` (drain loop)       |
| `NFA_FORCED_PREFIX_CAT`  | `Cell<Option<(Cat, usize, f64)>>` | `None`      | Drain loop (before replay)      | Prefix block entry (forced check)            |
| `NFA_PRIMARY_WEIGHT_CAT` | `Cell<f64>`                       | `0.5`       | NFA merged arm (best weight)    | `parse_preserving_vars()` (weight recording) |
| `RUNNING_WEIGHT_CAT`     | `Cell<f64>`                       | `0.0`       | Dispatch decisions (accumulate) | Recovery code via `running_weight_cat()`     |

### 2.3 Tuple Layout: `(Cat, usize, f64)`

Each spilled alternative is a 3-tuple:

```
(Cat, usize, f64)
  ▲     ▲     ▲
  │     │     └── Tropical weight from PredictionWfst
  │     │         (lower = more likely; 0.0 = deterministic)
  │     │
  │     └── End position: number of tokens consumed by the
  │         prefix parse (used to advance *pos on replay)
  │
  └── Parsed prefix value: the AST node produced by this
      alternative's prefix handler (e.g., Float::IntToFloat(...))
```

The `usize` position is critical: different NFA alternatives may consume
different numbers of tokens (e.g., when one rule has an optional suffix). The
forced-prefix replay restores `*pos` to this value so the infix loop begins at
the correct token.

---

## 3. `Cell<Vec<T>>` Take/Set Protocol

### 3.1 Why `Cell` and Not `RefCell`

Standalone parse functions can cause **re-entrancy**: `parse_preserving_vars()`
calls `Cat::parse(input)`, which calls `parse_cat()`, which may recursively
invoke the same function through cross-category dispatch or forced-prefix
replay. With `RefCell`, a borrow acquired in the outer call would conflict with
a borrow in the inner call, causing a runtime panic.

`Cell` avoids this entirely by transferring **ownership** rather than borrowing:

```rust
// Cell::take() — moves the Vec out, replacing with Vec::new()
let spill_buf = cell.take();  // cell now contains empty Vec

// Cell::set() — moves the Vec back in, dropping the old value
cell.set(spill_buf);          // cell now contains the buffer
```

There is no borrow to conflict with. The inner (re-entrant) call sees an empty
`Cell`, allocates a fresh `Vec` if needed, and returns it via `set()`. The
outer call's `Vec` lives on its stack frame, unaffected.

### 3.2 Take/Set Cost Model

Both `Cell::take()` and `Cell::set()` compile down to pointer-width stores:

| Operation                          | Implementation                                         | Cost                                |
|------------------------------------|--------------------------------------------------------|-------------------------------------|
| `Cell::take()` on empty `Vec`      | Store `(ptr=dangling, len=0, cap=0)`                   | 3 pointer stores                    |
| `Cell::set()` with empty `Vec`     | Store `(ptr=dangling, len=0, cap=0)`, drop old (no-op) | 3 pointer stores                    |
| `Cell::take()` on populated `Vec`  | Store empty, return owned `Vec`                        | 3 pointer stores                    |
| `Cell::set()` with populated `Vec` | Store new, drop old (dealloc if non-empty)             | 3 pointer stores + optional dealloc |
| `Cell::get()` on `f64`             | Copy the `f64` value                                   | 1 `f64` load                        |
| `Cell::set()` on `f64`             | Store the `f64` value                                  | 1 `f64` store                       |

### 3.3 Pool Semantics

The `Cell<Vec<T>>` pattern doubles as a **pool**: the `Vec`'s heap allocation
survives across parse calls. After the first NFA ambiguity allocates a buffer,
subsequent calls reuse the same allocation:

```
Call 1: take(empty) → alloc → push N-1 entries → set(vec with cap >= N-1)
Call 2: take(vec with cap >= N-1) → push N-1 entries (no realloc) → set(same vec)
Call 3: take(vec with cap >= N-1) → push N-1 entries (no realloc) → set(same vec)
```

For categories without NFA ambiguity, the `Vec` is never populated: take/set
is a no-op pair of pointer stores.

---

## 4. Lifetime and Re-Entrancy

### 4.1 Static Frame Types

The trampoline parser stores continuation frames in a `Vec<Frame_Cat>`. These
frames must be `'static` because they live in a thread-local pool:

```rust
// Frames store position indices, not token references
enum Frame_Cat {
    InfixRHS {
        op_pos: usize,       // index into tokens[], NOT Token<'a>
        saved_bp: u8,
        lhs: Cat,            // owned AST node
    },
    // ... other variants
}
```

By storing `op_pos: usize` instead of `op_token: Token<'a>`, frames avoid
carrying a lifetime parameter. The token is re-read from `tokens[op_pos]` when
the frame is unwound.

### 4.2 Cell Contents Are Owned

All four thread-locals store owned values, not borrows:

- `Vec<(Cat, usize, f64)>` --- `Cat` is an owned enum, `usize` and `f64` are `Copy`
- `Option<(Cat, usize, f64)>` --- same
- `f64` --- `Copy`

No lifetime parameter appears in any thread-local type. This makes the entire
spillover mechanism compatible with `thread_local!` (which requires `'static`).

### 4.3 Re-Entrancy Behavior

When a forced-prefix replay triggers a re-entrant call to `parse_cat()`:

```
parse_preserving_vars()
  │
  ├── Cat::parse(input)                  ← primary parse
  │     └── parse_cat(tokens, pos, 0)
  │           └── NFA merged arm
  │                 ├── best → return
  │                 └── N-1 → NFA_PREFIX_SPILL_CAT.set(...)
  │
  ├── drain NFA_PREFIX_SPILL_CAT.take()  ← owns spilled vec
  │
  └── for each spilled (alt, pos, w):
        │
        ├── NFA_FORCED_PREFIX_CAT.set(Some((alt, pos, w)))
        │
        └── Cat::parse(input)            ← replay parse (re-entrant)
              └── parse_cat(tokens, pos, 0)
                    ├── NFA_FORCED_PREFIX_CAT.take() → Some(...)
                    │     → skip NFA try-all, use forced value
                    │     → continue to infix loop
                    └── NFA merged arm NOT reached
                          (forced prefix bypassed it)
```

The key invariant: the re-entrant call takes the forced prefix from the `Cell`
(setting it to `None`), so it never re-enters the NFA try-all. Any nested
spillover from the replay is cleared explicitly:

```rust
// macros/src/gen/runtime/language.rs:1151-1152
/* Clear any nested spillover from forced-prefix replay */
NFA_PREFIX_SPILL_CAT.with(|cell| { cell.take(); });
```

### 4.4 Outermost-Wins Pool Policy

When re-entrancy occurs with the frame pool (`FRAME_POOL_CAT`), only the
**outermost** call's `Vec` survives in the thread-local. The inner call sees
an empty `Cell`, allocates a fresh `Vec`, uses it, and sets it back. When the
outer call finishes, its `set()` overwrites the inner call's `Vec`. Since the
outer call's `Vec` typically has the largest capacity (it processed the full
token stream), this is the optimal allocation to retain.

---

## 5. Zero-Overhead Analysis

### 5.1 Cost by Scenario

| Scenario                                       | NFA_PREFIX_SPILL                     | NFA_FORCED_PREFIX                     | NFA_PRIMARY_WEIGHT                  | RUNNING_WEIGHT             | Total          |
|------------------------------------------------|--------------------------------------|---------------------------------------|-------------------------------------|----------------------------|----------------|
| No NFA ambiguity (unambiguous token)           | Untouched                            | take(None) → 1 ptr store              | Untouched                           | +w via set() → 1 f64 store | ~1 ptr + 1 f64 |
| Single NFA success (only 1 alternative parsed) | Untouched                            | take(None) → 1 ptr store              | set(w) → 1 f64 store                | +w via set() → 1 f64 store | ~1 ptr + 2 f64 |
| NFA with N successes, spillover                | take + push(N-1) + set → O(N-1)      | take(None) → 1 ptr store              | set(w) → 1 f64 store                | +w via set() → 1 f64 store | O(N-1) pushes  |
| Forced-prefix replay (per spilled alt)         | take() to clear nested → 1 ptr store | set(Some) + take(Some) → 2 ptr stores | Untouched (weight carried in tuple) | reset(0.0) + reaccumulate  | ~3 ptr stores  |
| Error path (parse failure)                     | take() to clear → 1 ptr store        | Untouched                             | Untouched                           | Untouched                  | ~1 ptr store   |

### 5.2 Overhead for Unambiguous Grammars

For grammars with no NFA ambiguity (every dispatch token maps to exactly one
rule), the per-category overhead is:

- `NFA_FORCED_PREFIX_CAT`: one `Cell::take()` per `parse_cat()` call
  (always returns `None`, costs 1 pointer-width store)
- `NFA_PREFIX_SPILL_CAT`: one `Cell::take()` in `parse_preserving_vars()`
  (always returns empty `Vec`, costs 3 pointer-width stores)
- `NFA_PRIMARY_WEIGHT_CAT`: one `Cell::get()` + one `Cell::set()` in
  `parse_preserving_vars()` (2 f64 operations)
- `RUNNING_WEIGHT_CAT`: one `Cell::set(0.0)` at entry, one `Cell::set()` per
  dispatch decision (f64 add + store)

Total: approximately 4 pointer stores + a few f64 operations per parse --- well
within noise for any nontrivial grammar.

### 5.3 Beam Pruning Reduces Replay Cost

When a `PredictionWfst` has a beam width configured, spillover is filtered at
the NFA merged arm:

```rust
// Generated code — only spill alternatives within beam of best weight
if alt_pos == nfa_positions[0] && alt_w <= nfa_weights[0] + BEAM_WIDTH {
    spill_buf.push((alt, alt_pos, alt_w));
}
```

Alternatives outside the beam are never spilled and never replayed, reducing
the O(N-1) replay cost to O(k-1) where k <= N is the number of alternatives
within beam width of the best.

### 5.4 F2 Early Termination

When the first alternative has weight 0.0 (the tropical identity for the
times-operator, indicating deterministic/unambiguous) and the category does NOT
need NFA spillover, remaining alternatives are skipped entirely:

```rust
// Generated code — remaining alternatives guarded by F2 check
if nfa_results.is_empty() {
    // Try alternative 2...
    // Try alternative 3...
    // ...
}
// F2: deterministic hit (w=0.0) — remaining alternatives skipped if first succeeded
```

F2 is disabled when `needs_nfa_spillover` is true because disambiguation
requires all alternatives, even if the first is weight-0.0.

### 5.5 Demand-Driven Replay (F3)

The drain loop in `parse_preserving_vars()` uses three optimizations to minimize
replay cost when the primary parse is not accepting:

**1. Weight-ordered spill buffer**: The push site in `trampoline.rs` sorts the
spill buffer by weight (ascending) before `cell.set()`. This ensures that when
the drain loop iterates, alternatives are replayed in optimal order (best weight
first).

```rust
// Generated code in NFA merged arm
spill_buf.sort_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal));
cell.set(spill_buf);
```

**2. Weight-threshold pruning**: The drain loop computes a threshold
`primary_weight + REPLAY_WEIGHT_SLACK` (where slack = 2.0 tropical units ≈ 7.4×
likelihood ratio). Since the buffer is weight-sorted, once an alternative exceeds
the threshold, all remaining are worse --- the loop breaks early.

**3. Acceptance short-circuit**: If a replayed alternative produces an accepting
(ground) term, it is the weight-best accepting candidate (due to sorted order).
The loop immediately breaks, clearing the remaining spill buffer. No further
replays are attempted.

```
  Drain Loop Algorithm:
  ┌────────────────────────────────────────────────────────────┐
  │  spilled = NFA_PREFIX_SPILL_CAT.take()  [weight-sorted]    │
  │  primary_w = NFA_PRIMARY_WEIGHT_CAT.get()                  │
  │  threshold = primary_w + 2.0                               │
  │                                                            │
  │  for (alt, pos, w) in spilled:                             │
  │    ├── w > threshold? ──── yes ──▶ break (all worse)       │
  │    │                                                       │
  │    ├── replay via forced-prefix                            │
  │    │                                                       │
  │    ├── result accepting? ── yes ──▶ break (optimal found)  │
  │    │                                                       │
  │    └── continue to next alternative                        │
  └────────────────────────────────────────────────────────────┘
```

**Correctness argument**: Weight-sorted replay with acceptance short-circuit
produces the same semantic result as exhaustive replay because
`from_alternatives()` selects the weight-best accepting alternative. Since the
buffer is sorted ascending by weight, the first accepting replay IS that
weight-best candidate. All remaining alternatives are either (a) higher-weight
accepting (would be discarded by `from_alternatives()`) or (b) non-accepting
(would be discarded by the accepting-preference rule).

**Edge case — all non-accepting**: When no alternative is accepting, the
short-circuit never triggers. The threshold may still prune high-weight
alternatives, but the loop replays all alternatives within the threshold. The
resulting `Ambiguous(Vec<Inner>)` is then deferred to Ascent for semantic
resolution, identical to the exhaustive behavior.

**Combined effect**: For a grammar with K NFA spillover categories and average M
alternatives per spillover, the typical case drops from M−1 replays to 0−1
replays (short-circuit on first accepting), saving O(K×M) forced-prefix
re-parses per multi-category parse.

---

## 6. Data Flow Diagram

### 6.1 End-to-End Data Flow

```
                              COMPILE TIME
 ┌──────────────────────────────────────────────────────────────────────┐
 │                                                                      │
 │  categories_needing_nfa_spillover()                                  │
 │       │                                                              │
 │       ▼                                                              │
 │  group_rd_by_dispatch_token()                                        │
 │       │                                                              │
 │       ▼                                                              │
 │  Token group has >1 rule? ─── no ──▶ Direct dispatch (no spillover)  │
 │       │                                                              │
 │      yes                                                             │
 │       │                                                              │
 │       ▼                                                              │
 │  nfa_alternative_order()  ──▶  Sort by tropical weight               │
 │       │                                                              │
 │       ▼                                                              │
 │  write_nfa_merged_prefix_arm()  ──▶  Generate try-all + spillover    │
 │       │                                                              │
 │       ▼                                                              │
 │  Emit thread-local declarations (4 per category)                     │
 │  Emit forced-prefix check at prefix block entry                      │
 │  Emit drain loop in parse_preserving_vars()                          │
 │                                                                      │
 └──────────────────────────────────────────────────────────────────────┘


                               RUNTIME
 ┌──────────────────────────────────────────────────────────────────────┐
 │                                                                      │
 │  parse_preserving_vars(input)                                        │
 │       │                                                              │
 │       ▼                                                              │
 │  ┌─────────────────────────────────────────────────────────────┐     │
 │  │  Cat::parse(input)  [PRIMARY PARSE]                         │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  parse_cat(tokens, pos, 0)                                  │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  ┌────────────────────────────────────────────────────────┐ │     │
 │  │  │  'prefix block                                         │ │     │
 │  │  │       │                                                │ │     │
 │  │  │       ▼                                                │ │     │
 │  │  │  NFA_FORCED_PREFIX_CAT.take()                          │ │     │
 │  │  │       │                                                │ │     │
 │  │  │    None (first call)                                   │ │     │
 │  │  │       │                                                │ │     │
 │  │  │       ▼                                                │ │     │
 │  │  │  match token {                                         │ │     │
 │  │  │    Token::KwFloat => {  [NFA MERGED ARM]               │ │     │
 │  │  │       │                                                │ │     │
 │  │  │       ▼                                                │ │     │
 │  │  │    ┌──────────────────────────────────────┐            │ │     │
 │  │  │    │  Try alt[0] (w=0.50): FloatId        │            │ │     │
 │  │  │    │  Try alt[1] (w=1.00): IntToFloat     │            │ │     │
 │  │  │    │  Try alt[2] (w=1.50): BoolToFloat    │            │ │     │
 │  │  │    │  Try alt[3] (w=2.00): StrToFloat     │            │ │     │
 │  │  │    │       │                              │            │ │     │
 │  │  │    │       ▼                              │            │ │     │
 │  │  │    │  nfa_results = [FloatId, IntToFloat] │            │ │     │
 │  │  │    │  nfa_weights = [0.50, 1.00]          │            │ │     │
 │  │  │    │       │                              │            │ │     │
 │  │  │    │       ▼                              │            │ │     │
 │  │  │    │  match nfa_results.len() {           │            │ │     │
 │  │  │    │    _ => {                            │            │ │     │
 │  │  │    │      best = FloatId(x) [idx 0]       │            │ │     │
 │  │  │    │                                      │            │ │     │
 │  │  │    │      NFA_PRIMARY_WEIGHT_CAT          │            │ │     │
 │  │  │    │        .set(0.50)                    │            │ │     │
 │  │  │    │                                      │            │ │     │
 │  │  │    │      RUNNING_WEIGHT_CAT              │            │ │     │
 │  │  │    │        .set(get() + 0.50)            │            │ │     │
 │  │  │    │                                      │            │ │     │
 │  │  │    │      NFA_PREFIX_SPILL_CAT.take()     │            │ │     │
 │  │  │    │        → push (IntToFloat, pos, 1.0) │            │ │     │
 │  │  │    │        → set(spill_buf)              │            │ │     │
 │  │  │    │                                      │            │ │     │
 │  │  │    │      break 'prefix best              │            │ │     │
 │  │  │    │    }                                 │            │ │     │
 │  │  │    │  }                                   │            │ │     │
 │  │  │    └──────────────────────────────────────┘            │ │     │
 │  │  │    }  // end Token::KwFloat arm                        │ │     │
 │  │  │  }  // end match                                       │ │     │
 │  │  │       │                                                │ │     │
 │  │  │       ▼                                                │ │     │
 │  │  │  lhs = FloatId(x)                                      │ │     │
 │  │  │       │                                                │ │     │
 │  │  └───────┼────────────────────────────────────────────────┘ │     │
 │  │          ▼                                                  │     │
 │  │     infix loop (processes + 1.0 etc.)                       │     │
 │  │          │                                                  │     │
 │  │          ▼                                                  │     │
 │  │     return Ok(Float::Add(FloatId(x), NumLit(1.0)))          │     │
 │  └─────────────────────────────────────────────────────────────┘     │
 │       │                                                              │
 │       ▼                                                              │
 │  Record primary success + weight:                                    │
 │    successes.push(Inner::Float(result))                              │
 │    success_weights.push(NFA_PRIMARY_WEIGHT_CAT.get())  → 0.50        │
 │       │                                                              │
 │       ▼                                                              │
 │  ┌─────────────────────────────────────────────────────────────┐     │
 │  │  DRAIN LOOP (F3 demand-driven)                              │     │
 │  │                                                             │     │
 │  │  spilled = NFA_PREFIX_SPILL_CAT.take()  [weight-sorted ↑]   │     │
 │  │    → [(IntToFloat(x), 5, 1.0)]                              │     │
 │  │  primary_w = NFA_PRIMARY_WEIGHT_CAT.get() → 0.50            │     │
 │  │  threshold = 0.50 + 2.0 = 2.50                              │     │
 │  │                                                             │     │
 │  │  for (alt_prefix, alt_pos, alt_weight) in spilled:          │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  alt_weight (1.0) > threshold (2.50)? → no, continue        │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  NFA_FORCED_PREFIX_CAT.set(Some((IntToFloat(x), 5, 1.0)))   │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  ┌──────────────────────────────────────────────────────┐   │     │
 │  │  │  Cat::parse(input)  [REPLAY PARSE]                   │   │     │
 │  │  │       │                                              │   │     │
 │  │  │       ▼                                              │   │     │
 │  │  │  parse_cat(tokens, pos, 0)                           │   │     │
 │  │  │       │                                              │   │     │
 │  │  │       ▼                                              │   │     │
 │  │  │  NFA_FORCED_PREFIX_CAT.take() → Some(...)            │   │     │
 │  │  │       │                                              │   │     │
 │  │  │       ▼                                              │   │     │
 │  │  │  *pos = forced_pos (= 5)                             │   │     │
 │  │  │  lhs = IntToFloat(x)   [skip NFA try-all]            │   │     │
 │  │  │       │                                              │   │     │
 │  │  │       ▼                                              │   │     │
 │  │  │  infix loop (processes + 1.0 etc.)                   │   │     │
 │  │  │       │                                              │   │     │
 │  │  │       ▼                                              │   │     │
 │  │  │  return Ok(Float::Add(IntToFloat(x), NumLit(1.0)))   │   │     │
 │  │  └──────────────────────────────────────────────────────┘   │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  wrapped = Inner::Float(result)                             │     │
 │  │  wrapped.is_accepting()? → check for F3 short-circuit       │     │
 │  │  successes.push(wrapped)                                    │     │
 │  │  success_weights.push(1.0)                                  │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  F3: accepting → clear spill buf + break (short-circuit)    │     │
 │  │  F3: not accepting → clear nested spillover + continue      │     │
 │  └─────────────────────────────────────────────────────────────┘     │
 │       │                                                              │
 │       ▼                                                              │
 │  match successes.len() {                                             │
 │    1 => return Ok(Term(successes[0]))    [unambiguous]               │
 │    _ => {                                [N > 1 successes]           │
 │       │                                                              │
 │       ▼                                                              │
 │  ┌─────────────────────────────────────────────────────────────┐     │
 │  │  DISAMBIGUATION                                             │     │
 │  │                                                             │     │
 │  │  AMBIGUOUS_WEIGHTS.set(success_weights)                     │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  from_alternatives(successes)                               │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  1. Flatten nested Ambiguous variants                       │     │
 │  │  2. Filter to is_accepting() alternatives (ground terms)    │     │
 │  │       │                                                     │     │
 │  │       ▼                                                     │     │
 │  │  ┌────────────────────────────────────────────────────┐     │     │
 │  │  │  0 accepting → Ambiguous(all)  [defer to Ascent]   │     │     │
 │  │  │  1 accepting → return it       [unique ground]     │     │     │
 │  │  │  N accepting → min-weight wins [WFST tiebreak]     │     │     │
 │  │  └────────────────────────────────────────────────────┘     │     │
 │  │       │                                                     │     │
 │  │       ▼  (for N accepting, WFST tiebreak)                   │     │
 │  │  AMBIGUOUS_WEIGHTS.take()                                   │     │
 │  │  weights.len() == n_alts?                                   │     │
 │  │    yes → best_idx = argmin(weights[accepting_indices])      │     │
 │  │    no  → return first accepting (length mismatch fallback)  │     │
 │  └─────────────────────────────────────────────────────────────┘     │
 │    }                                                                 │
 │  }                                                                   │
 │                                                                      │
 └──────────────────────────────────────────────────────────────────────┘
```

### 6.2 Thread-Local State Machine

Each `Cell` follows a simple state machine during one parse cycle:

```
NFA_PREFIX_SPILL_CAT:
 ┌───────────┐    take()     ┌──────────┐   push(N-1)   ┌────────────┐
 │ Empty Vec │──────────────▶│ Owned by │──────────────▶│ Owned by   │
 │ (in Cell) │               │ NFA arm  │               │ NFA arm    │
 └───────────┘               │ (stack)  │               │ (populated)│
      ▲                      └──────────┘               └─────┬──────┘
      │                                                       │
      │                                                       │
      │  ┌────────────────┐       set(populated_vec)          │
      │  │ Populated Vec  │◀──────────────────────────────────┘
      │  │ (in Cell)      │
      │  └───────┬────────┘
      │          │ take() by drain loop
      │          ▼
      │  ┌────────────────┐
      │  │ Owned by drain │ → iterate → replay each → clear nested
      │  │ loop (stack)   │
      │  └───────┬────────┘
      │          │ Vec dropped (or returned empty)
      └──────────┘


NFA_FORCED_PREFIX_CAT:
 ┌──────┐   set(Some(...))   ┌───────────┐   take()   ┌───────────────┐
 │ None │───────────────────▶│ Some(...) │───────────▶│ Some(...) on  │
 │      │                    │ (in Cell) │            │ stack; Cell   │
 └──┬───┘                    └───────────┘            │ reset to None │
    │                                                 └──────┬────────┘
    │                                                        │
    └────────────────────────────────────────────────────────┘
                     (replay consumes; cell returns to None)


NFA_PRIMARY_WEIGHT_CAT:
 ┌──────┐    set(w)    ┌──────┐    get()     ┌──────┐   set(0.5)   ┌──────┐
 │ 0.5  │─────────────▶│  w   │─────────────▶│  w   │─────────────▶│ 0.5  │
 │(init)│  (NFA arm)   │      │  (drain loop)│(read)│  (reset)     │      │
 └──────┘              └──────┘              └──────┘              └──────┘


RUNNING_WEIGHT_CAT:
 ┌──────┐   set(0.0)   ┌──────┐   set(get()+w)   ┌─────────────┐
 │  0.0 │─────────────▶│ 0.0  │─────────────────▶│ accumulated │
 │(init)│  (parse_cat  │      │  (each dispatch  │ weight      │
 └──────┘   entry)     └──────┘   decision)      └─────┬───────┘
                                                       │
                                              running_weight_cat()
                                              reads on error path
```

### 6.3 Worked Example: `float(x) + 1.0`

Given input `float(x) + 1.0` in a Calculator grammar with categories
`{Int, Float, Bool, Str}`:

**Step 1: Primary parse (`Float::parse`)**

```
parse_cat("Float", tokens=[KwFloat, LParen, Ident("x"), RParen, Plus, NumLit(1.0)], pos=0)

NFA_FORCED_PREFIX_FLOAT.take() → None (first call)

Enter NFA merged arm for Token::KwFloat:
  nfa_saved = 0

  Try FloatId (w=0.50):    *pos=0 → parse "float" "(" Float ")" → Ok(FloatId(FreeVar(x))), pos=4
  Try IntToFloat (w=1.00): *pos=0 → parse "float" "(" Int ")"   → Ok(IntToFloat(FreeVar(x))), pos=4
  Try BoolToFloat (w=1.50): *pos=0 → parse "float" "(" Bool ")" → Err (x not a bool literal)
  Try StrToFloat (w=2.00): *pos=0 → parse "float" "(" Str ")"   → Err (x not a string literal)

  nfa_results  = [FloatId(FreeVar(x)), IntToFloat(FreeVar(x))]
  nfa_positions = [4, 4]
  nfa_weights  = [0.50, 1.00]

  Match: _ (len=2) → {
    *pos = 4
    NFA_PRIMARY_WEIGHT_FLOAT.set(0.50)
    RUNNING_WEIGHT_FLOAT.set(0.0 + 0.50)
    NFA_PREFIX_SPILL_FLOAT.take() → empty vec
      push (IntToFloat(FreeVar(x)), 4, 1.00)  ← within beam
    NFA_PREFIX_SPILL_FLOAT.set([(IntToFloat(FreeVar(x)), 4, 1.00)])
    break 'prefix FloatId(FreeVar(x))
  }

lhs = FloatId(FreeVar(x))

Infix loop: Token::Plus at pos=4 → lhs = Float::Add(FloatId(FreeVar(x)), NumLit(1.0))

return Ok(Float::Add(FloatId(FreeVar(x)), NumLit(1.0)))
```

**Step 2: Drain loop in `parse_preserving_vars`**

```
successes = [Inner::Float(Add(FloatId(FreeVar(x)), NumLit(1.0)))]
success_weights = [0.50]

spilled = NFA_PREFIX_SPILL_FLOAT.take()
  → [(IntToFloat(FreeVar(x)), 4, 1.00)]

Replay: NFA_FORCED_PREFIX_FLOAT.set(Some((IntToFloat(FreeVar(x)), 4, 1.00)))
  Float::parse("float(x) + 1.0")
    parse_cat → NFA_FORCED_PREFIX_FLOAT.take() → Some(...)
      *pos = 4
      lhs = IntToFloat(FreeVar(x))
      infix loop: Token::Plus → lhs = Float::Add(IntToFloat(FreeVar(x)), NumLit(1.0))
      return Ok(Float::Add(IntToFloat(FreeVar(x)), NumLit(1.0)))

successes = [
  Inner::Float(Add(FloatId(FreeVar(x)), NumLit(1.0))),
  Inner::Float(Add(IntToFloat(FreeVar(x)), NumLit(1.0))),
]
success_weights = [0.50, 1.00]

NFA_PREFIX_SPILL_FLOAT.take() → empty (clear nested)
```

**Step 3: Disambiguation**

```
successes.len() = 2 → enter disambiguation

AMBIGUOUS_WEIGHTS.set([0.50, 1.00])

from_alternatives([
  Inner::Float(Add(FloatId(FreeVar(x)), NumLit(1.0))),     ← not accepting (FreeVar)
  Inner::Float(Add(IntToFloat(FreeVar(x)), NumLit(1.0))),  ← not accepting (FreeVar)
])

Flatten: no nested Ambiguous → flat.len() = 2
Filter is_accepting(): 0 accepting (both contain FreeVar)

→ return Ambiguous([...])  [deferred to Ascent for semantic resolution]
```

If `x` were bound (e.g., `float(42) + 1.0`):

```
  FloatId(NumLit(42))     → not accepting (FloatId on a NumLit is identity, but non-ground)
  IntToFloat(IntLit(42))  → accepting (ground conversion)

Filter is_accepting(): 1 accepting → return IntToFloat(IntLit(42)) directly
```

### 6.4 Source References

| Component                          | File            | Location                                                        |
|------------------------------------|-----------------|-----------------------------------------------------------------|
| Thread-local declarations          | `trampoline.rs` | `write_trampoline_parser()`, lines 1143--1173                   |
| `running_weight_cat()` accessor    | `trampoline.rs` | lines 1178--1184                                                |
| NFA spillover codegen              | `trampoline.rs` | `write_nfa_merged_prefix_arm()`, lines 367--412                 |
| Forced-prefix check                | `trampoline.rs` | `write_trampoline_body()`, lines 1343--1356                     |
| Recovery-mode forced-prefix check  | `trampoline.rs` | lines 3144--3154                                                |
| NFA ambiguity detection            | `trampoline.rs` | `group_rd_by_dispatch_token()`, lines 77--116                   |
| Spillover category detection       | `trampoline.rs` | `categories_needing_nfa_spillover()`, lines 136--151            |
| Weight ordering                    | `trampoline.rs` | `write_nfa_merged_prefix_arm()`, lines 225--257                 |
| F2 early termination               | `trampoline.rs` | lines 253--304                                                  |
| Drain loop (F3 demand-driven)      | `language.rs`   | `generate_language_impl()`, lines 1208--1245                    |
| Weight-ordered spill sort          | `trampoline.rs` | `write_prefix_match_arms()`, spill_block + CSL spill_block_lazy |
| `AMBIGUOUS_WEIGHTS` declaration    | `language.rs`   | lines 1529--1535                                                |
| Weight-aware `from_alternatives()` | `language.rs`   | lines 284--326                                                  |
| `parse_preserving_vars()`          | `language.rs`   | lines 1544--1569                                                |
