# Incremental Parsing Guide

## Overview

`IncrementalSession` manages checkpoint-based incremental parsing for LSP integration. On file open, a full parse creates checkpoints. On edits, only the affected region is re-parsed.

## Initial Parse

```rust
use mettail_prattail::cek::IncrementalSession;

// Create session with token-level checkpoints
let mut session = IncrementalSession::new(0, 1);

// During initial parse, record checkpoints
// (done by the generated parser via CekTraceEntry emission)
```

## Handling Edits

When the user edits the buffer:

```rust
// 1. Invalidate stale checkpoints
session.invalidate_after(edit_position);

// 2. Find nearest valid checkpoint
let (cp_pos, cp_state) = session
    .checkpoint_at_or_before(edit_position)
    .expect("checkpoint at position 0 always exists");

// 3. Resume parsing from checkpoint
// (feed modified token stream starting from cp_pos)

// 4. Check for convergence at each token
// if is_convergent(&current_state, &surviving_checkpoint) → stop
```

## Convergence

Two states are convergent when their stacks and binding powers match:

```rust
use mettail_prattail::cek::is_convergent;

// After processing the edited region, compare against surviving checkpoints
// If convergent → the rest of the parse is unchanged
```

## Checkpoint Granularity

| Interval | Memory | Reparse Speed | Use Case |
|----------|--------|---------------|----------|
| 1 (every token) | ~400 KB/file | ~100-300 ns/edit | Real-time IDE |
| 10 | ~40 KB/file | ~1-10 μs/edit | Medium-size files |
| 50 | ~8 KB/file | ~10-100 μs/edit | Large files |

## VPA-Bounded Reparse (Enhancement B)

When available, Visibly Pushdown Automata analysis tightens the reparse region:

```
Edit at position 15 inside "( 1 + 2 )"
                             ^^^
VPA identifies innermost matched pair: positions 0..8
Only reparse positions 0..8 (not the entire file)
```

## Tree Automata Validation (Enhancement A)

After incremental reparse, only the changed-node-to-root path needs re-validation:

```
Before edit:  Add(Lit(1), Mul(Lit(2), Lit(3)))
Edit: change 2 → 4
After edit:   Add(Lit(1), Mul(Lit(4), Lit(3)))

Only re-validate: Lit(4) → Mul → Add
Skip: Lit(1), Lit(3)
```
