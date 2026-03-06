# Extended Recovery Strategies

**Date:** 2026-03-01

Design document covering the three new repair actions (SwapTokens,
CategorySwitch, Composite), the multi-step Viterbi lattice, and the
full 7-strategy evaluation order in `wfst_recover_Cat()`. This
document builds on [error-recovery.md](error-recovery.md) which covers
the original 4 strategies and the 3-tier cost model.

---

## Table of Contents

1. [Overview](#1-overview)
2. [SwapTokens (Transposition Repair)](#2-swaptokens-transposition-repair)
3. [CategorySwitch (Cross-Category Recovery)](#3-categoryswitch-cross-category-recovery)
4. [Composite (Multi-Step Repair Sequence)](#4-composite-multi-step-repair-sequence)
5. [The Full Viterbi Lattice](#5-the-full-viterbi-lattice)
6. [Strategy Evaluation Order](#6-strategy-evaluation-order)
7. [Worked Example: Complete 7-Strategy Evaluation](#7-worked-example-complete-7-strategy-evaluation)
8. [Cost Hierarchy Table](#8-cost-hierarchy-table)
9. [Source Reference](#9-source-reference)

---

## 1. Overview

The WFST error recovery system described in [error-recovery.md](error-recovery.md)
evaluates 4 repair strategies: SkipToSync, DeleteToken, InsertToken,
SubstituteToken. The 15-sprint error recovery expansion added 3 new
strategies and a multi-step evaluation mechanism:

| # | Strategy               | Original or New | When Introduced |
|---|------------------------|-----------------|-----------------|
| 1 | SkipToSync             | Original        | Sprint 1        |
| 2 | DeleteToken            | Original        | Sprint 1        |
| 3 | InsertToken            | Original        | Sprint 1        |
| 4 | SubstituteToken        | Original        | Sprint 1        |
| 5 | **SwapTokens**         | **New**         | Sprint 8        |
| 6 | **CategorySwitch**     | **New**         | Sprint 10       |
| 7 | **viterbi_multi_step** | **New**         | Sprint 9        |

Strategies 1–4 are documented in [error-recovery.md §4](error-recovery.md#4-single-step-recovery).
This document covers strategies 5–7 and the 7-strategy evaluation order.

---

## 2. SwapTokens (Transposition Repair)

### 2.1 Motivation

Adjacent transposition is a common typo pattern in infix-heavy grammars:

```
Intended:   a + b * c
Typed:      a b + * c        ("+b" transposed to "b+")
                ╰───╯
              swap these
```

Without SwapTokens, the recovery system must delete `b` (cost 1.0) or
skip to `+` (cost 0.5), both of which lose the `b` token. SwapTokens
reorders `b` and `+` without losing information.

### 2.2 Activation

SwapTokens is evaluated when:

1. `remaining.len() ≥ 2` — at least two tokens remain after the error.
2. `remaining[1] ∈ sync_tokens` — swapping puts a sync token at the
   front.

Condition 2 ensures the swap produces an immediately useful result: after
swapping, the parser sees a sync token and can resume. Without this
guard, arbitrary swaps would rarely lead to valid continuations.

### 2.3 Cost

```
Base cost: config.swap_cost    (default: 1.25)
Edit cost: EditWeight(1)       (single edit operation)
```

The base cost 1.25 sits between delete (1.0) and substitute (1.5),
reflecting that swap preserves all tokens.

### 2.4 Position Effect

```
pos → pos + 2    (consumes both tokens in swapped order)
```

Both the transposed tokens are consumed. The parser resumes at
`pos + 2`.

### 2.5 Tier Interaction

SwapTokens is treated as a mild reorder (similar to skip):

- **Tier 1:** `skip_multiplier()` is applied (same as SkipToSync).
- **Tier 3:** ParseSimulator evaluates continuation from `pos + 2`.
- **Final cost:** `config.swap_cost × skip_mult × tier3_mult`.

### 2.6 Worked Example

Grammar: `Int → Int "+" Int | Int "*" Int | Integer`

Input: `3 2 + 5` (error: `2` is not an infix operator after `3`)

```
Tokens:  Integer(3)  Integer(2)  Plus  Integer(5)  Eof
         pos=0       pos=1       pos=2 pos=3       pos=4
```

Error at pos=1: expected infix operator, found `Integer(2)`.

```
remaining = [Integer(2), Plus, Integer(5), Eof]
             [0]         [1]   [2]          [3]
```

**Swap check:** remaining[1] = Plus. Is Plus a sync token? Yes (Plus ∈
FOLLOW(Int)). SwapTokens is available.

```
Swap: cost = 1.25 × skip_mult × tier3_mult
      pos → pos + 2 = 3
      After swap: parser sees Plus at conceptual position, then Integer(5)
```

Tier 3 simulates from pos=3: Integer(5) ∈ FIRST(Int) → valid
continuation. tier3_mult = 0.5.

**Final swap cost:** 1.25 × 1.0 × 0.5 = 0.625

Compare with delete (cost = 1.0 × 1.0 × tier3_mult). After deleting
Integer(2), parser sees Plus at pos=2 → valid continuation.
delete cost = 1.0 × 1.0 × 0.5 = 0.5.

Winner: DeleteToken (0.5) beats SwapTokens (0.625). This is correct:
deleting `2` and keeping `3 + 5` is a better repair than swapping
`2 +` to get `+ 2 5` (which would produce `3 + 2 5` — still malformed).

---

## 3. CategorySwitch (Cross-Category Recovery)

### 3.1 Motivation

In multi-category grammars, an error token may be valid in a different
category. If a cast rule connects that category to the current one, the
parser can switch categories rather than reporting an error.

```
Grammar:
  Int → Int "+" Int | Integer
  Bool → Bool "&&" Bool | "true" | "false"
  Int → Bool   (cast: BoolToInt)

Input: true + 5
       ╰───╯
       "true" is a Bool, not an Int — but BoolToInt cast exists
```

### 3.2 Static Data: CROSS_CAT_CASTS_Cat

At compile time, the pipeline emits a per-category static array:

```rust
static CROSS_CAT_CASTS_Int: &[(&str, &[u16])] = &[
    ("Bool", &[5_u16, 6_u16]),   // Bool's FIRST set token IDs
];
```

Each entry is `(source_category, source_first_token_ids)`. The recovery
function checks whether the error token's ID is in any source category's
FIRST set.

### 3.3 Activation

CategorySwitch is only emitted for multi-category grammars that have cast
rules to the current category. Single-category grammars skip this
strategy entirely (no overhead).

### 3.4 Cost

```
Base cost: config.substitute_cost × 0.5 = 1.5 × 0.5 = 0.75
Edit cost: EditWeight(2)   (semantic substitution)
```

The cost is low because a cast rule exists — the semantic intent is
preserved. The 0.5 discount reflects that the token is valid in some
category and a formal cast connects it to the target.

### 3.5 Position Effect

```
pos → pos   (no advancement — context switch, not token consumption)
```

The parser does not advance past the error token. Instead, it
conceptually delegates to the source category's parser, which will
consume the token via its normal prefix handler.

### 3.6 Worked Example

Grammar as in §3.1. Input: `true + 5`.

```
Parsing Int: prefix handler expects Integer or open-paren.
Found: Token::Boolean(true) at pos=0.
Error: unexpected token.
```

Recovery evaluates CROSS_CAT_CASTS_Int:
- `("Bool", &[token_id_of("Boolean")])` — is `token_to_id(Boolean(true))`
  in the Bool FIRST set? Yes.

```
CategorySwitch: cost = 0.75
                desc = "try parsing as Bool (cast Bool → Int)"
                pos → pos (no advancement)
```

Compare with other strategies:
- Skip: no sync token nearby → cost ≫ 0.75
- Delete: cost 1.0 → loses the `true` token
- Substitute: cost 1.5 → worse than cast

Winner: CategorySwitch (0.75). The parser logs the recovery and
continues with the BoolToInt cast path.

### 3.7 Missing Cast Rule Diagnostics

When the error token belongs to another category's FIRST set but **no
cast rule** connects them, the generated trampoline prefix handler emits
a hint:

```
"Hint: this is a Proc expression, but no Proc → Float cast rule exists."
```

These hints use the `cast_suggestions` data emitted per-category:

```rust
let cast_suggestions: &[(&str, &str)] = &[
    ("at", "Proc"),   // token "at" is in Proc's FIRST set
];
```

The hint appears in the `UnexpectedToken` error's `expected` field via
`Cow<'static, str>`.

---

## 4. Composite (Multi-Step Repair Sequence)

### 4.1 Produced by viterbi_multi_step()

`Composite` is not an independently evaluated strategy. It is the output
of `viterbi_multi_step()` when the optimal repair requires more than one
atomic action. The Viterbi search over the repair lattice may find that a
sequence like "delete, skip, skip, sync" is cheaper than any single
action.

### 4.2 Structure

```rust
RepairAction::Composite {
    steps: Vec<RepairAction>,  // ordered sequence of atomic actions
}
```

Each element in `steps` is an atomic action (SkipToSync, DeleteToken,
InsertToken, SubstituteToken, SwapTokens). Composites do not nest.

### 4.3 Display

The `describe()` method joins component descriptions with ", ":

```
"delete unexpected token, skip 2 token(s) to ';'"
"swap adjacent tokens, skip 1 token(s) to ')'"
```

### 4.4 EditWeight

The edit cost of a Composite is the sum of its components:

```rust
fn edit_cost(&self) -> EditWeight {
    let total = steps.iter().map(|s| s.edit_cost().0).sum::<u32>();
    EditWeight::new(total)
}
```

### 4.5 When Composite Beats Single-Step

Composite is most valuable when:

1. The error requires multiple corrections (e.g. two adjacent typos).
2. A single skip would overshoot a nearby sync point.
3. Delete+skip reaches a sync point cheaper than pure skip (when Tier 3
   multipliers differ).

See [multi-step-viterbi-recovery.md §8](../../theory/wfst/multi-step-viterbi-recovery.md#8-composite-repairs)
for the break-even analysis.

---

## 5. The Full Viterbi Lattice (viterbi_multi_step)

### 5.1 All 6 Edge Types

The multi-step Viterbi lattice in `viterbi_multi_step()` evaluates all
six edge types simultaneously. For a 5-token window:

```
  ┌────┐  skip   ┌────┐  skip   ┌────┐  skip   ┌────┐  skip   ┌────┐
  │ t₀ ├────────▶│ t₁ ├────────▶│ t₂ ├────────▶│ t₃ ├────────▶│ t₄ │
  └─┬──┘  0.5    └─┬──┘  0.5    └─┬──┘  0.5    └─┬──┘  0.5    └─┬──┘
    │ del          │ del          │ del          │ del          │
    │ 1.0          │ 1.0          │ 1.0          │ 1.0          │
    │──────▶t₁     │──────▶t₂     │──────▶t₃     │──────▶t₄     │
    │              │              │              │              │
    │ swap 1.25    │ swap 1.25    │ swap 1.25    │              │
    │──────────▶t₂ │──────────▶t₃ │──────────▶t₄ │              │
    │              │              │              │              │
    │ sub          │ sub          │ sub          │ sub          │
    │ 1.5          │ 1.5          │ 1.5          │ 1.5          │
    │──────▶t₁     │──────▶t₂     │──────▶t₃     │──────▶t₄     │
    │              │              │              │              │
    ├─ins──▶SINK   ├─ins──▶SINK   ├─ins──▶SINK   ├─ins──▶SINK   │
    │  2.0         │  2.0         │  2.0         │  2.0         │
    │              │              │              │              │
    │              │              │              │       sync   │
    │              │              │              │       0.0    │
    │              │              │              │──────▶SINK   ├──▶SINK
    │              │              │              │              │
```

(Substitute edges only when token[*i*] ∉ sync_tokens.)

### 5.2 Forward Pass with Beam Pruning

See [multi-step-viterbi-recovery.md §4](../../theory/wfst/multi-step-viterbi-recovery.md#4-viterbi-on-the-repair-lattice)
for the formal algorithm.

### 5.3 Insert Guard

The `inserted[i]` boolean array limits inserts to one per position:

```rust
let mut inserted = vec![false; max_lookahead];
// ...
if !inserted[i] {
    for &sync_id in sync_tokens {
        // Insert edge: i → SINK
        inserted[i] = true;
    }
}
```

### 5.4 Backtrace Reconstruction

See [multi-step-viterbi-recovery.md §5](../../theory/wfst/multi-step-viterbi-recovery.md#5-backtrace-and-sequence-reconstruction)
for the backtrace algorithm.

### 5.5 RepairSequence Output

```rust
RepairSequence {
    actions: Vec<RepairAction>,      // ordered repair actions
    new_pos: usize,                  // final parser position
    total_cost: TropicalWeight,      // tropical cost sum
    total_edits: EditWeight,         // edit distance sum
}
```

### 5.6 All Costs Parameterized

Every cost in the lattice comes from `RecoveryConfig`:

| Edge       | Config Field      | Default |
|------------|-------------------|---------|
| Skip       | `skip_per_token`  | 0.5     |
| Delete     | `delete_cost`     | 1.0     |
| Substitute | `substitute_cost` | 1.5     |
| Insert     | `insert_cost`     | 2.0     |
| Swap       | `swap_cost`       | 1.25    |
| Sync       | (fixed)           | 0.0     |

---

## 6. Strategy Evaluation Order in wfst_recover_Cat

The generated `wfst_recover_Cat()` function evaluates all 7 strategies
and selects the one with the minimum cost.

### 6.1 Strategy 1: SkipToSync

Scan forward up to `max_skip_lookahead` tokens for the nearest sync
token. Cost: `skip_count × 0.5 × combined_skip_mult`.

See [error-recovery.md §4](error-recovery.md#4-single-step-recovery).

### 6.2 Strategy 2: DeleteToken

Delete one token (cost 1.0 × combined_skip_mult). Parser advances
by 1.

### 6.3 Strategy 3: InsertToken

Insert a missing sync token. Cost: 2.0 × frame_insert_mult ×
bracket_insert_mult. Bracket balance strongly discounts closing
delimiters (0.3× when unmatched brackets exist).

### 6.4 Strategy 4: SubstituteToken

Replace current token with a sync token. Cost: 1.5 × sub_mult
(Mixfix frames get 0.75×).

### 6.5 Strategy 5: SwapTokens (NEW)

Swap two adjacent tokens. Cost: 1.25 × combined_skip_mult ×
tier3_mult. Only when remaining ≥ 2 and remaining[1] ∈ sync_tokens.

See §2 above.

### 6.6 Strategy 6: CategorySwitch (NEW)

Switch to parsing via a different category with a cast rule. Cost:
1.5 × 0.5 = 0.75. Only when `CROSS_CAT_CASTS_Cat` contains the error
token's ID.

See §3 above.

### 6.7 Strategy 7: viterbi_multi_step (NEW)

Build the full repair lattice and run Viterbi. The resulting
`RepairSequence` may be a single action or a `Composite`. The
`total_cost` competes directly with the single-step strategies.

See §5 above.

### 6.8 Winner Selection

```
best_strategy = argmin(cost_1, cost_2, ..., cost_7)
```

If all strategies produce cost = ∞, recovery fails and the original
error is reported unchanged. Otherwise, the parser position is updated
to `best_pos` and the repair description is pushed as a
`ParseError::RecoveryApplied`.

**Tier 3 rescoring.** After the initial min-cost selection from
strategies 1–6, the ParseSimulator rescores the winner by simulating
continuation from the repair position. The rescored cost may change the
ranking relative to strategy 7 (multi-step Viterbi).

---

## 7. Worked Example: Complete 7-Strategy Evaluation

### 7.1 Setup

Grammar: `Int → Int "+" Int | Int "*" Int | Integer`

Input: `3 + @ * 5 ;`

```
Tokens:  Integer(3)  Plus  Error(@)  Star  Integer(5)  Semi  Eof
         pos=0       pos=1 pos=2     pos=3 pos=4       pos=5 pos=6
```

Error at pos=2: expected operand, found `@`.

```
remaining = [Error(@), Star, Integer(5), Semi, Eof]
sync_tokens = {Plus, Star, Semi, RParen, Eof}
```

Context: depth=2, binding_power=2 (RHS of `+`), frame_kind=InfixRHS.
Brackets: all balanced (0, 0, 0).

### 7.2 Strategy Evaluation

**Tier 1 multipliers:**
- skip_mult = 1.0 (depth < 1000, depth ≥ 10: no adjustment)
- bp_mult = 0.75 (bp=2 < 4)
- frame_skip_mult = 0.75 (InfixRHS)
- combined_skip_mult = 1.0 × 0.75 × 0.75 = 0.5625

| # | Strategy        | Computation                                     | Raw Cost | Adjusted Cost |
|---|-----------------|-------------------------------------------------|----------|---------------|
| 1 | SkipToSync      | nearest sync: Star at skip=1 → 1 × 0.5 × 0.5625 | 0.5      | 0.281         |
| 2 | DeleteToken     | 1.0 × 0.5625                                    | 1.0      | 0.5625        |
| 3 | InsertToken     | 2.0 × 1.0 (no frame discount) × 1.0 (balanced)  | 2.0      | 2.0           |
| 4 | SubstituteToken | 1.5 × 1.0 (not Mixfix)                          | 1.5      | 1.5           |
| 5 | SwapTokens      | remaining[1]=Star ∈ sync → 1.25 × 0.5625        | 1.25     | 0.703         |
| 6 | CategorySwitch  | @ not in any cast source FIRST set              | ∞        | ∞             |
| 7 | MultiStep       | Viterbi: skip(0.5) → sync at Star               | 0.5      | 0.5           |

**Tier 3 rescoring** of strategy 1 (the current winner at 0.281):
- Simulate from pos=3 (Star): Star ∈ infix(Int) → valid continuation.
- tier3_mult = 0.5.
- Final cost: 0.281 × 0.5 = 0.141.

**Multi-step (strategy 7)** cost 0.5 > rescored strategy 1 cost 0.141.

### 7.3 Winner

**Strategy 1: SkipToSync** with adjusted cost 0.141.

Repair: "skip 1 token(s) to '*'" — the `@` token is skipped, and
parsing resumes at the `*` operator.

Result: `ParseError::RecoveryApplied` wrapping the original
`UnexpectedToken` error, with description "skip 1 token(s) to '*'".

---

## 8. Cost Hierarchy Table

| # | Action          | Base Cost | Config Field      | Edit Distance | Position Effect  |
|---|-----------------|-----------|-------------------|---------------|------------------|
| 1 | SkipToSync      | 0.5/token | `skip_per_token`  | 1 per skipped | pos + skip_count |
| 2 | DeleteToken     | 1.0       | `delete_cost`     | 1             | pos + 1          |
| 3 | InsertToken     | 2.0       | `insert_cost`     | 2             | pos (phantom)    |
| 4 | SubstituteToken | 1.5       | `substitute_cost` | 2             | pos + 1          |
| 5 | SwapTokens      | 1.25      | `swap_cost`       | 1             | pos + 2          |
| 6 | CategorySwitch  | 0.75      | sub_cost × 0.5    | 2             | pos (switch)     |
| 7 | Composite       | Σ steps   | (per-step config) | Σ step edits  | per-step         |

**Ordering by default base cost:**
```
SkipToSync(1) ≤ CategorySwitch(0.75) ≤ DeleteToken(1.0)
≤ SwapTokens(1.25) ≤ SubstituteToken(1.5) ≤ InsertToken(2.0)
```

Note: SkipToSync cost depends on skip_count. For skip=1, cost = 0.5.
For skip=2, cost = 1.0 (matching delete). CategorySwitch (0.75) is
cheaper than single-token skip (0.5) for skip ≥ 2.

---

## 9. Source Reference

| Symbol                            | Location                             |
|-----------------------------------|--------------------------------------|
| `RepairAction::SwapTokens`        | `prattail/src/recovery.rs:266–271`   |
| `RepairAction::Composite`         | `prattail/src/recovery.rs:277–280`   |
| `RepairAction::CategorySwitch`    | `prattail/src/recovery.rs:288–293`   |
| `RepairAction::describe()`        | `prattail/src/recovery.rs:332–361`   |
| `RepairAction::edit_cost()`       | `prattail/src/recovery.rs:374–388`   |
| `find_best_recovery()`            | `prattail/src/recovery.rs:487–567`   |
| `find_best_recovery_contextual()` | `prattail/src/recovery.rs:1528–1679` |
| `viterbi_multi_step()`            | `prattail/src/recovery.rs:840–1072`  |
| `generate_wfst_recovery_fn()`     | `prattail/src/pipeline.rs:1831–2060` |
| `CROSS_CAT_CASTS_Cat`             | `prattail/src/pipeline.rs:1180`      |
| `cast_suggestions`                | `prattail/src/trampoline.rs:677`     |

**Cross-references:**

- [error-recovery.md](error-recovery.md) — original 4 strategies, 3-tier
  cost model
- [multi-step-viterbi-recovery.md](../../theory/wfst/multi-step-viterbi-recovery.md) —
  formal Viterbi foundations
- [cascade-suppression.md](../../theory/wfst/cascade-suppression.md) —
  absorbing-state cascade prevention
- [recovery-config.md](recovery-config.md) — all 19 parameters
- [recovery-state-propagation.md](../../architecture/wfst/recovery-state-propagation.md) —
  thread-local state infrastructure
