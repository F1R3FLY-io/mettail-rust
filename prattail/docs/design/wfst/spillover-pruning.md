# Weight-Based Spillover Pruning (F1)

**Date:** 2026-03-01

---

## Table of Contents

1. [Problem](#1-problem)
2. [Mechanism](#2-mechanism)
3. [Generated Code](#3-generated-code)
4. [Correctness](#4-correctness)
5. [Interaction with F2 (Early Termination)](#5-interaction-with-f2-early-termination)
6. [Complexity](#6-complexity)

---

## 1. Problem

When multiple grammar rules within the same category share a dispatch token,
PraTTaIL's NFA disambiguation (Layer 2.5) resolves the ambiguity by trying
all N alternatives and selecting the best.  The primary result (lowest WFST
weight) is returned immediately from the prefix match, while the remaining
N-1 alternatives are **spilled** into a thread-local buffer
(`NFA_PREFIX_SPILL_CAT`) for **forced-prefix replay**.  During replay, each
spilled alternative is injected into a fresh `parse_Cat_preserving_vars`
call so that `substitute_env` and `from_alternatives` can resolve the
ambiguity semantically.

The problem: every spilled alternative triggers a full parser invocation --
prefix dispatch, the entire infix loop, and environment substitution.  When
some alternatives carry very high WFST weights (indicating unlikely parses),
the replay work is wasted.  Those alternatives cannot win the final
disambiguation in `from_alternatives()`, which selects the lowest-weight
accepting result.  Replaying them adds latency proportional to the number
of unlikely alternatives times the cost of a full parse.

### Concrete example

Consider the Calculator language's `Float` category with four rules sharing
`Token::KwFloat`:

| Rule          | WFST Weight | Likelihood |
|---------------|-------------|------------|
| `FloatId`     | 0.0         | identity (most common)  |
| `IntToFloat`  | 0.3         | integer promotion       |
| `BoolToFloat` | 0.8         | boolean coercion        |
| `StrToFloat`  | 1.5         | string parsing (rare)   |

Without pruning, all three non-primary alternatives are spilled and each
triggers a full parser replay.  With a beam width of 1.0, only `IntToFloat`
(0.3) and `BoolToFloat` (0.8) are spilled -- `StrToFloat` (1.5) exceeds
0.0 + 1.0 = 1.0 and is discarded at spill time.

---

## 2. Mechanism

Spillover pruning operates at **compile time** within
`write_nfa_merged_prefix_arm()` in `trampoline.rs`.  The codegen template
for the spill loop conditionally includes a weight filter based on the
`PredictionWfst`'s beam width.

### Two-stage filtering

The spill loop already applies a **position filter**: only alternatives
whose final cursor position matches the primary result's position are
spilled (alternatives that consumed a different number of tokens cannot
participate in semantic disambiguation).  F1 adds a second filter:

```
Stage 1 (existing): alt_pos == nfa_positions[0]         // position match
Stage 2 (F1):       alt_w  <= nfa_weights[0] + beam     // weight within beam
```

Both filters are conjunctive -- an alternative must pass both to be spilled.

### Beam width source

The beam width is extracted from the `PredictionWfst` at pipeline time:

```rust
// trampoline.rs:369-373
let beam_threshold = config
    .prediction_wfst
    .as_ref()
    .and_then(|wfst| wfst.beam_width())   // Option<TropicalWeight>
    .map(|bw| bw.value());                  // Option<f64>
```

`PredictionWfst::beam_width()` returns `Option<TropicalWeight>`, set either
by `PredictionWfstBuilder::with_beam_width()` or
`PredictionWfst::set_beam_width()`.  When `None`, no beam is configured
and F1 falls back to position-only filtering (backward compatible).

**Source:** `wfst.rs:beam_width()` (line 226), `trampoline.rs:write_nfa_merged_prefix_arm()` (lines 367-406)

### Codegen decision tree

```
                    ┌──────────────────────────┐
                    │ needs_nfa_spillover?      │
                    └────────────┬─────────────┘
                          yes    │    no
                    ┌────────────┴────┐
                    │                 │
              ┌─────▼─────┐   ┌──────▼──────────────┐
              │ beam_width │   │ No spill loop.      │
              │ configured?│   │ Take first result,  │
              └──┬─────────┘   │ break 'prefix.      │
            yes  │   no        └─────────────────────┘
         ┌───────┴────────┐
         │                │
   ┌─────▼──────┐  ┌─────▼──────────┐
   │ Emit spill │  │ Emit spill     │
   │ with pos + │  │ with pos-only  │
   │ weight     │  │ filter         │
   │ filter     │  │ (all matching) │
   └────────────┘  └────────────────┘
```

---

## 3. Generated Code

### Before F1 (position filter only)

When no beam width is configured, the generated spill loop filters only on
cursor position:

```rust
// Generated code (no beam):
_ => {
    *pos = nfa_positions[0];
    let mut iter = nfa_results.into_iter();
    let best = iter.next().expect("nfa_results non-empty");
    NFA_PRIMARY_WEIGHT_FLOAT.with(|cell| cell.set(nfa_weights[0]));
    RUNNING_WEIGHT_FLOAT.with(|cell| cell.set(cell.get() + nfa_weights[0]));
    NFA_PREFIX_SPILL_FLOAT.with(|cell| {
        let mut spill_buf = cell.take();
        for ((alt, &alt_pos), &alt_w) in iter
            .zip(nfa_positions[1..].iter())
            .zip(nfa_weights[1..].iter())
        {
            // Position filter only:
            if alt_pos == nfa_positions[0] {
                spill_buf.push((alt, alt_pos, alt_w));
            }
        }
        cell.set(spill_buf);
    });
    break 'prefix best;
},
```

### After F1 (position + weight filter)

When beam width is configured (e.g., 1.0), the generated filter adds a
weight comparison.  The beam value is embedded as a **compile-time f64
literal**:

```rust
// Generated code (beam = 1.0):
_ => {
    *pos = nfa_positions[0];
    let mut iter = nfa_results.into_iter();
    let best = iter.next().expect("nfa_results non-empty");
    NFA_PRIMARY_WEIGHT_FLOAT.with(|cell| cell.set(nfa_weights[0]));
    RUNNING_WEIGHT_FLOAT.with(|cell| cell.set(cell.get() + nfa_weights[0]));
    NFA_PREFIX_SPILL_FLOAT.with(|cell| {
        let mut spill_buf = cell.take();
        for ((alt, &alt_pos), &alt_w) in iter
            .zip(nfa_positions[1..].iter())
            .zip(nfa_weights[1..].iter())
        {
            // Position + weight filter (F1):
            if alt_pos == nfa_positions[0] && alt_w <= nfa_weights[0] + 1.0 {
                spill_buf.push((alt, alt_pos, alt_w));
            }
        }
        cell.set(spill_buf);
    });
    break 'prefix best;
},
```

The only difference is the added condition `&& alt_w <= nfa_weights[0] + 1.0`
in the inner `if`.  The `1.0` is the beam width, baked into the generated code
as a constant -- no runtime lookup is needed.

### Codegen implementation

The spill filter string is constructed in `trampoline.rs` (lines 374-387):

```rust
let spill_filter = if let Some(beam) = beam_threshold {
    // Runtime check: alt_w <= nfa_weights[0] + beam
    format!(
        "if alt_pos == nfa_positions[0] && alt_w <= nfa_weights[0] + {beam:?} {{ \
            spill_buf.push((alt, alt_pos, alt_w)); \
        }}"
    )
} else {
    // No beam -- spill all position-matching alternatives
    "if alt_pos == nfa_positions[0] { \
        spill_buf.push((alt, alt_pos, alt_w)); \
    }"
    .to_string()
};
```

The `{beam:?}` format specifier emits the f64 with enough precision to
round-trip (e.g., `1.0` stays `1.0`, not `1`).

---

## 4. Correctness

### Theorem: Pruning cannot discard the winning alternative

**Claim:** If alternative `a` has weight `w_a > w_best + beam`, then `a`
cannot win disambiguation in `from_alternatives()`.

**Proof:**

Let `w_best` = `nfa_weights[0]`, the weight of the primary (best-weight)
result from the NFA try-all phase.  The alternatives are sorted by weight
(lowest first) via `PredictionWfst::nfa_alternative_order()`.

1. **Weight ordering invariant.**  After NFA try-all, `nfa_weights[0]` is
   the minimum weight among all successfully parsed alternatives.  For any
   alternative `a` at index `i > 0`, `nfa_weights[i] >= nfa_weights[0]`.

2. **Tropical semiring properties.**  In the tropical semiring
   `(R+ union {+inf}, min, +, +inf, 0.0)`:
   - `plus(a, b) = min(a, b)` -- selects the lower-weight path.
   - `times(a, b) = a + b` -- accumulates weights along a path.
   - `one() = 0.0` -- identity for `times` (zero cost).
   - `zero() = +inf` -- identity for `plus` (unreachable).

3. **Replay cannot decrease weight.**  When a spilled alternative
   `(alt, alt_pos, alt_w)` is replayed via forced-prefix injection, the
   replay runs `parse_Cat_preserving_vars`, which accumulates additional
   weight via `RUNNING_WEIGHT_CAT`.  Since tropical `times` is addition
   and all weights are non-negative, the replayed parse's total weight is
   `alt_w + delta` where `delta >= 0`.

4. **Disambiguation selects minimum.**  `from_alternatives()` reads
   `AMBIGUOUS_WEIGHTS` and selects the accepting alternative with the
   lowest weight (lines 307-316 of `language.rs`).  The primary result
   has weight `w_best`.  Any pruned alternative has weight `w_a > w_best + beam`.
   After replay, its total weight is `w_a + delta >= w_a > w_best + beam > w_best`.
   Therefore, the pruned alternative's total weight strictly exceeds
   `w_best`, and it cannot be selected by `min`.

5. **Conclusion.**  The pruned alternative cannot win.  F1 is sound. **QED**

### Edge cases

| Case | Behavior |
|------|----------|
| No beam configured (`beam_width = None`) | F1 is a no-op; all position-matching alternatives are spilled (backward compatible) |
| Beam = 0.0 | Only alternatives with weight exactly equal to `w_best` are spilled |
| Beam = +inf | Equivalent to no beam; all alternatives pass the filter |
| Single alternative (`N = 1`) | No spillover occurs; F1 is never reached |
| All alternatives have identical weight | All pass the filter (difference is 0.0 <= beam for any beam >= 0.0) |

---

## 5. Interaction with F2 (Early Termination)

F1 (Spillover Pruning) and F2 (Early Termination) are complementary
optimizations that target different phases of NFA disambiguation:

| Property | F1: Spillover Pruning | F2: Early Termination |
|----------|----------------------|----------------------|
| **Phase** | After NFA try-all (spill loop) | During NFA try-all (inner loop) |
| **Trigger** | `beam_width` configured on `PredictionWfst` | First alternative has weight 0.0 |
| **Effect** | Fewer alternatives replayed | Fewer alternatives tried |
| **Guard** | `needs_nfa_spillover` (only applies when spillover is active) | `!needs_nfa_spillover` (incompatible with spillover) |
| **Scope** | Compile-time literal in spill filter | Compile-time `if nfa_results.is_empty()` guard |

### Mutual exclusivity of F2 and spillover

F2 is gated by `!config.needs_nfa_spillover` (line 253-254):

```rust
let first_is_deterministic = ordered_inlineable.len() > 1
    && !config.needs_nfa_spillover      // <-- F2 disabled when spillover active
    && ordered_inlineable
        .first()
        .map_or(false, |(_, w)| *w == 0.0);
```

When `needs_nfa_spillover` is true, F2 is disabled because
`from_alternatives` requires all successfully parsed alternatives --
even if the first has weight 0.0 -- to perform semantic disambiguation.
F1 is the only optimization that applies in this case, and it safely
reduces the replay set without affecting semantic resolution.

### Combined scenario

For a category **without** spillover (simple dispatch):
- F2 applies: if the first alternative (weight 0.0) succeeds, remaining
  alternatives are skipped entirely.
- F1 does not apply (no spill loop exists).

For a category **with** spillover (NFA disambiguation):
- F2 does not apply (all alternatives must be tried).
- F1 applies: after all alternatives are tried, only those within the
  beam are spilled for replay.

The two optimizations therefore never conflict.

### Data flow

```
NFA Try-All Phase                         Spill Phase
  ┌─────────┐                            ┌────────────┐
  │ Alt 1   │─── F2: if w=0.0 and       │            │
  │ (w=0.0) │    !spillover, skip ────── │            │
  │         │    rest                     │            │
  ├─────────┤                            │            │
  │ Alt 2   │──── tried regardless ────► │ F1: spill  │
  │ (w=0.3) │    when spillover active   │ if w <=    │
  ├─────────┤                            │ best+beam  │──► replay
  │ Alt 3   │──── tried regardless ────► │            │
  │ (w=0.8) │                            │            │──► replay
  ├─────────┤                            │            │
  │ Alt 4   │──── tried regardless ────► │            │
  │ (w=1.5) │                            │            │──► pruned (1.5 > 0.0+1.0)
  └─────────┘                            └────────────┘
```

---

## 6. Complexity

### Compile-time cost

| Operation | Cost |
|-----------|------|
| Beam width extraction (`beam_width()`) | O(1) -- field read |
| Spill filter string construction | O(1) -- one `format!` call with literal |
| Per-alternative filter condition | O(1) -- single `<=` comparison in template |
| Total codegen overhead | O(A) where A = number of alternatives in the merged arm |

The generated code size changes by exactly one `&& alt_w <= nfa_weights[0] + <beam>`
clause per merged NFA arm -- typically 1-3 arms per category.

### Runtime cost

| Operation | Cost |
|-----------|------|
| Weight comparison (`alt_w <= nfa_weights[0] + beam`) | O(1) -- single f64 comparison |
| Per spill iteration | O(1) -- existing position check + one added comparison |
| Total spill loop | O(N-1) where N = number of NFA alternatives |

The overhead of F1 is one additional f64 comparison per spilled alternative.
On modern architectures, this is a single `ucomisd` instruction on the
critical path of the spill loop (which already performs an integer comparison
for position matching).

### Space cost

Zero additional allocations.  The beam width is a compile-time literal,
not a stored value.  The spill buffer (`Vec<(Cat, usize, f64)>`) is the
same structure with or without F1 -- F1 simply adds fewer elements to it.

### When beam is not configured

When `beam_width()` returns `None`, the codegen falls through to the
position-only filter.  The generated code is **identical** to the pre-F1
output.  There is no conditional branch, no dead code, and no runtime
cost -- the beam comparison is simply absent from the generated source.

**Source:** `trampoline.rs:write_nfa_merged_prefix_arm()` (lines 367-418),
`wfst.rs:beam_width()` (line 226-228),
`language.rs:from_alternatives()` (lines 284-326)
