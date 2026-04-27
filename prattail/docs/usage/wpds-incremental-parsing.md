# WPDS Incremental Parsing Guide

W7 Stage 11 deliverable (plan v5.1). Successor to
`incremental-parsing-guide.md` for the WPDS-runtime parser.

## Overview

[`WpdsIncrementalSession`] (defined in `prattail/src/wpds_session.rs`)
manages checkpoint-based incremental parsing for LSP integration. On file
open, a full parse seeds checkpoints at configurable granularity. On
edits, only the affected region is re-parsed by resuming the walker from
the nearest checkpoint at-or-before the edit position.

## Initial parse

```rust
use mettail_prattail::wpds_session::WpdsIncrementalSession;
use mettail_prattail::wpds_walker::{WalkerConsumer, WpdsWalker};
use mettail_prattail::wpds_runtime::{
    CheckpointReason, WpdsControl, WpdsEvent, WpdsTransition,
};
use mettail_prattail::automata::lex_weight::LexicographicWeight;

// Create session with token-level checkpoints.
let mut session: WpdsIncrementalSession<LexicographicWeight> =
    WpdsIncrementalSession::new(1);

// Drive an initial parse, recording a checkpoint every N tokens.
let mut walker = WpdsWalker::new(my_engine, /* min_bp */ 0);
struct Recorder<'s> {
    session: &'s mut WpdsIncrementalSession<LexicographicWeight>,
}
impl<'s> WalkerConsumer<LexicographicWeight> for Recorder<'s> {
    fn on_event(&mut self, _event: &WpdsEvent<LexicographicWeight>, _state: &_) -> WpdsControl {
        WpdsControl::Checkpoint
    }
    fn on_checkpoint(
        &mut self,
        config: &mettail_prattail::wpds_runtime::WpdsConfiguration<LexicographicWeight>,
    ) {
        self.session.record_checkpoint(config.pos, config.clone());
    }
}
let mut recorder = Recorder { session: &mut session };
let _final_state = walker.run_with_consumer(&mut recorder, 100_000);
```

## Handling edits

```rust
// 1. Invalidate stale checkpoints downstream of the edit.
session.invalidate_after(edit_position);

// 2. Reparse from the nearest at-or-before checkpoint.
let final_state = session.reparse(
    edit_position,
    my_engine,
    /* max_steps */ 100_000,
)?;
```

## Convergence

Two configurations are convergent when their `state`, `stack`, and `pos`
fields all match (per `WpdsIncrementalSession::is_convergent`). When the
walker reaches a configuration that matches a surviving checkpoint, the
remainder of the parse is unchanged and reparsing can stop.

```rust
use mettail_prattail::wpds_session::WpdsIncrementalSession;

if WpdsIncrementalSession::is_convergent(&current_config, &surviving_checkpoint) {
    // The rest of the parse is unchanged. Stop reparsing; reuse the existing
    // parse tree downstream of `edit_position`.
}
```

## Checkpoint granularity

| Interval | Memory | Reparse Speed | Use Case |
|----------|--------|---------------|----------|
| 1 (every token) | ~400 KB/file | ~100-300 ns/edit | Real-time IDE |
| 10 | ~40 KB/file | ~1-10 µs/edit | Medium-size files |
| 50 | ~8 KB/file | ~10-100 µs/edit | Large files |

(Estimates based on the survey contract R12; absolute numbers depend on
the grammar's stack depth and the efficiency of the host platform's
allocator. Profile your workload before tuning.)

## Differences from the legacy `IncrementalSession`

The legacy `IncrementalSession` in `cek.rs` provided checkpoint storage
but **no `reparse` method** (survey gap class B). The WPDS analogue:

- Adds the documented-but-missing `reparse(edit_pos, engine, max_steps)`.
- Uses integer-indexed `StackSymbolV2` and the typed `WpdsConfiguration<W>`
  (~8 bytes per stack frame) instead of `String`-tagged tags.
- Carries a typed weight (`LexicographicWeight`) so reparse decisions can
  consult the same tiebreak semantics as the live walker.
- Generic over `W: Semiring`, so non-default weights (TropicalWeight only,
  CountingWeight, etc.) work without API changes.

## Future enhancements (not yet implemented)

The survey's R15 listed five enhancement directions as informational:

- **A**: Tree-automata incremental validation (re-validate only the
  changed-node-to-root path).
- **B**: VPA-bounded reparse (tighter reparse region via call/return matching).
- **C**: WFST-guided ambiguity resolution (bias toward previously-selected alternative).
- **D**: WPDS checkpoint density optimization (poststar classifies positions at compile time).
- **E**: Symbolic guard caching (skip re-evaluation if referenced atoms unchanged).

These are documented as future work; they are not required for LSP
correctness.

## Source files

| File | Content |
|---|---|
| `prattail/src/wpds_session.rs` | `WpdsIncrementalSession`, `ReparseError`, tests |
| `prattail/src/wpds_walker.rs` | `WpdsWalker::seeded_from(engine, config)` (resume from checkpoint) |
| `prattail/src/wpds_runtime.rs` | `WpdsConfiguration<W>` snapshot type |
