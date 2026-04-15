# Reactive State Machine Architecture

## Pattern

The CEK machine follows the **reactive state machine** pattern from MeTTaTron:

```
State × Event → Transition
```

The core driver is a pure function. External consumers (DAP, LSP, REPL) provide the event loop.

## Component Overview

```
┌─────────────────────────────────────────────────────┐
│                  CekMachine<Cat>                     │
│                                                     │
│  ┌──────────┐   ┌──────────┐   ┌────────────────┐  │
│  │ CekState │   │ ParseState│   │ CekEnvironment │  │
│  │ (C)      │   │ (K+C+pos)│   │ (E)            │  │
│  └────┬─────┘   └─────┬────┘   └───────┬────────┘  │
│       │               │                │            │
│       └───────────────┼────────────────┘            │
│                       │                             │
│              process_event(CekEvent)                │
│                       │                             │
│                       ▼                             │
│              CekTransition                          │
│              ├─ NoChange                            │
│              ├─ Transition { new_state, trace }     │
│              └─ Checkpoint { pos, depth, bp }       │
│                                                     │
└─────────────────────────────────────────────────────┘
          ▲                          │
          │                          │
     CekEvent                  CekTraceEntry
     (from consumer)           (to consumer)
```

## Types

### CekState

The control component — which phase of parsing we're in.

| Variant | Description |
|---------|-------------|
| `Ready { min_bp }` | Initial state |
| `PrefixDispatch { pos, cur_bp }` | Matching on current token |
| `InfixLoop { cur_bp }` | Checking for operators |
| `Unwinding` | Popping continuation frames |
| `Accepted` | Parse complete |
| `Error { message }` | Parse failed |

### CekEvent

Events that drive the machine forward.

| Event | Effect |
|-------|--------|
| `Step` | One CEK transition |
| `ValueProduced { display }` | Record value emission |
| `FramePushed { variant }` | Record frame push |
| `FramePopped { variant }` | Record frame pop |
| `OperatorConsumed { op_pos }` | Record infix operator |
| `Inspect` | Read state, no change |

### CekTransition

The output of processing an event.

| Variant | Description |
|---------|-------------|
| `NoChange` | Inspect event, no mutation |
| `Transition { new_state, trace }` | State change with optional trace |
| `Checkpoint { pos, depth, bp }` | Incremental reparse checkpoint |

## Consumer Integration

### Batch Parser

```rust
let mut machine = CekMachine::new(tokens, min_bp);
let result = machine.run_to_completion();
```

### DAP Server

```rust
loop {
    let transition = machine.process_event(CekEvent::Step);
    if breakpoint_hit(&machine.parse_state()) {
        send_dap_stopped_event(&machine);
        wait_for_dap_continue();
    }
    if machine.state().is_terminal() { break; }
}
```

### LSP Server

```rust
let mut session = IncrementalSession::new(0, 1);
// On file open: parse full
session.parse_full(tokens);
// On edit: incremental reparse
let result = session.reparse(edit_range, new_tokens);
```

### REPL

```rust
let mut env = CekEnvironment::new();
loop {
    let input = read_input();
    let mut machine = CekMachine::new(tokenize(input), 0);
    machine.parse_state().environment = env.clone();
    let result = machine.run_to_completion();
    // Update env with any assignments
    env = machine.parse_state().environment.clone();
}
```

## MeTTaTron Comparison

| MeTTaTron | PraTTaIL CEK |
|-----------|-------------|
| `ReplState` | `CekState` |
| `ReplEvent` | `CekEvent` |
| `StateTransition` | `CekTransition` |
| `ReplStateMachine` | `CekMachine` |
| `process_event()` | `process_event()` |
