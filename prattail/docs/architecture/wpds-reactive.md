# WPDS Reactive State Machine Architecture

This document is the WPDS-runtime analogue of `reactive-state-machine.md`.
It documents the reactive contract that external consumers (LSP, DAP,
REPL, nREPL) attach to when driving the WPDS-based runtime parser.

W7 Stage 11 deliverable (plan v5.1).

## Pattern

The WPDS walker follows the same MeTTaTron-style reactive state machine
pattern that the legacy CEK parser was designed around:

```
State × Event → Transition
```

The core driver is a pure function. External consumers provide the event
loop. The walker does no I/O, no side effects, no global state of its
own — all observability flows through `WalkerConsumer` (Stage 5).

## Component overview

```
┌─────────────────────────────────────────────────────────┐
│                  WpdsWalker<W, E>                        │
│                                                          │
│  ┌──────────┐   ┌───────────┐   ┌──────────────────┐   │
│  │ WpdsState│   │ WpdsGss<W>│   │ WpdsStepEngine E │   │
│  │ (FSM)    │   │ (stack)   │   │ (per-language)   │   │
│  └────┬─────┘   └─────┬─────┘   └────────┬─────────┘   │
│       │               │                  │              │
│       └───────────────┼──────────────────┘              │
│                       │                                 │
│             process_event(WpdsEvent<W>)                 │
│                       │                                 │
│                       ▼                                 │
│             WpdsTransition<W>                           │
│             ├─ NoChange                                 │
│             ├─ Transition { new_state, trace }          │
│             ├─ Checkpoint { config }                    │
│             └─ Done { state }                           │
│                                                         │
└─────────────────────────────────────────────────────────┘
          ▲                              │
          │                              │
     WpdsEvent                    WpdsTraceEntry
     (from consumer)              (to consumer)
```

## Types

### WpdsState

The control component — which phase of WPDS-driven parsing the walker is in.

| Variant | Description |
|---|---|
| `Ready { min_bp }` | Initial state at category entry |
| `PrefixDispatch { pos, cur_bp }` | Matching on the current token to choose a prefix rule |
| `InfixLoop { cur_bp }` | Looking for an infix/postfix operator with BP > `cur_bp` |
| `AmbiguityFanout { branches }` | Multiple GSS branches active; awaiting resolution |
| `Saturating { delta_size }` | WPDS poststar/prestar saturation in progress |
| `Unwinding` | Popping continuation frames after a value was produced |
| `Accepted` | Parse complete |
| `Error { message }` | Parse failed |

### WpdsEvent

Events that drive the walker forward.

| Event | Effect |
|---|---|
| `Step` | Advance one transition (the canonical pulse) |
| `TokenConsumed { pos, token }` | Token was consumed at the given position |
| `BranchForked { parent, children }` | GSS branch fork; multiple stack tops |
| `BranchResolved { winner, weight }` | Ambiguity resolved to a single winning branch |
| `SemanticActionFired { action_id, args }` | Semantic action executed during AST assembly |
| `Checkpoint { reason }` | Request the walker to record a checkpoint |
| `Inspect` | Read state without mutation |

### WpdsTransition

The output of processing an event.

| Variant | Description |
|---|---|
| `NoChange` | Inspect event or terminal-state absorption |
| `Transition { new_state, trace }` | State changed; optional trace entry |
| `Checkpoint { config }` | Checkpoint recorded at the current configuration |
| `Done { state }` | Parse complete (terminal state reached) |

### WpdsControl

Returned by `WalkerConsumer::on_event` to direct the walker.

| Variant | Effect |
|---|---|
| `Continue` | Proceed to the next transition |
| `Checkpoint` | Snapshot, then continue |
| `Abort` | Halt; walker enters `Error { message: "consumer aborted" }` |
| `Pause` | Suspend awaiting external resumption (DAP/REPL pause) |

The `Pause` variant exists per Rholang §13.1 affordance (mandate M6 of
the migration survey).

## Consumer integration

### Batch parser

```rust
let mut walker = WpdsWalker::new(MyLangWpdsEngine, 0);
let final_state = walker.run_to_completion(10_000);
```

### DAP server (step debugging)

```rust
let mut walker = WpdsWalker::new(MyLangWpdsEngine, 0);
loop {
    let transition = walker.process_event(WpdsEvent::Step);
    if breakpoint_hit(walker.state(), walker.position()) {
        send_dap_stopped_event(&walker);
        wait_for_dap_continue();
    }
    if walker.state().is_terminal() {
        break;
    }
    let _ = transition;
}
```

### LSP server (incremental reparse)

```rust
let mut session: WpdsIncrementalSession<LexicographicWeight> =
    WpdsIncrementalSession::new(/* checkpoint_interval */ 1);

// On didOpen: drive parser, recording checkpoints at every token.
// (See `wpds-incremental-parsing.md` for the seed loop.)

// On didChange at edit_pos:
session.invalidate_after(edit_pos);
let final_state = session.reparse(edit_pos, MyLangWpdsEngine, 10_000)?;
```

### REPL (with consumer)

```rust
let mut walker = WpdsWalker::new(MyLangWpdsEngine, 0);
let mut consumer = TracingConsumer::<LexicographicWeight>::new();
let final_state = walker.run_with_consumer(&mut consumer, 10_000);
for (event_tag, state_after) in &consumer.events {
    println!("{:?} → {:?}", event_tag, state_after);
}
```

### nREPL session

Identical to REPL but reuses the same `WpdsWalker` across requests by
calling `WpdsWalker::seeded_from(engine, saved_config)` to restart
without losing memoized analysis state.

## Layering: reactive FSM is primary

Per survey mandate M1, the **reactive `process_event` API is the primary
external contract**. `run_to_completion`, `run_with_consumer`, and
`run_to_saturation` are convenience wrappers built atop it.

`WalkerConsumer` (mandate M2) is the **secondary** side-effect contract —
attached to the walker for tracing, breakpoints, and protocol-message
emission. It does not drive the walker; it observes.

The two layers are symmetric with the legacy CEK design (per the survey
§3.7 layering diagram), preserving the user's original MeTTaTron-style
mandate end-to-end.

## MeTTaTron comparison

| MeTTaTron | PraTTaIL CEK (legacy) | PraTTaIL WPDS (current) |
|---|---|---|
| `ReplState` | `CekState` | `WpdsState` |
| `ReplEvent` | `CekEvent` | `WpdsEvent` |
| `StateTransition` | `CekTransition` | `WpdsTransition` |
| `ReplStateMachine` | `CekMachine` (planned) | `WpdsWalker<W, E>` |
| `process_event()` | `process_event()` (planned) | `process_event()` (live) |

## Source files

| File | Content |
|---|---|
| `prattail/src/wpds_runtime.rs` | `WpdsState`/`Event`/`Transition`/`Control`, `StackSymbolV2`, `CheckpointReason` |
| `prattail/src/wpds_walker.rs` | `WpdsWalker`, `WpdsStepEngine`, `WalkerConsumer`, `TracingConsumer`, `NullConsumer`, `AbortAfterConsumer` |
| `prattail/src/wpds_session.rs` | `WpdsIncrementalSession`, `ReparseError` |
| `prattail/src/gss.rs` | `WpdsGss<W>`, `WpdsGssNode`, `WpdsGssEdge<W>`, iterative path enumeration |
| `prattail/src/automata/lex_weight.rs` | `LexicographicWeight` (left-projection times semantics) |
