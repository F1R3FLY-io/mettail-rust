# CEK-6: Online Parsing Infrastructure

## Intuition

The reactive CEK machine externalizes parse state as a **suspendable, inspectable state machine**. Any consumer (DAP server, LSP server, REPL, railroad annotator) can drive it at its own pace via `process_event()`.

The key insight is that PraTTaIL's trampoline already has all the ingredients of a CEK machine — the explicit continuation stack, the binding power control, and the accumulated capture environment. Formalizing this as a reactive state machine makes these ingredients accessible to external tools.

## Reactive Architecture

Follows MeTTaTron's reactive state machine pattern:

```
State × Event → Transition
```

The core driver is a pure function: no I/O, no side effects, no global state. External consumers provide the event loop.

### State Machine Diagram

```
                    ┌─────────┐
                    │  Ready  │
                    └────┬────┘
                         │ Step
                         ▼
              ┌──────────────────────┐
              │   PrefixDispatch     │◄─────────────┐
              │  (match on token)    │               │
              └──────────┬───────────┘               │
                   ┌─────┴─────┐                     │
                   │           │                     │
                   ▼           ▼                     │
           ┌───────────┐  ┌─────────┐               │
           │ InfixLoop │  │ (push   │               │
           │ (check    │  │  frame, │───────────────┘
           │  for ops) │  │  drive) │
           └─────┬─────┘  └─────────┘
                 │
           ┌─────┴─────┐
           │           │
           ▼           ▼
    ┌───────────┐  ┌──────────┐
    │ Unwinding │  │ Accepted │
    │ (pop      │  └──────────┘
    │  frame)   │
    └─────┬─────┘
          │
    ┌─────┴──────────┐
    │                │
    ▼                ▼
  (back to        ┌──────────┐
   Infix/Drive)   │  Error   │
                  └──────────┘
```

## Incremental Parsing

### Token-Level Checkpoints

Default granularity: **every token** (`checkpoint_interval = 1`). Each checkpoint stores a `ParseState` snapshot.

Memory overhead: ~200-400 KB per file via persistent continuation stacks (CoW).

### Reparse Algorithm

1. **Invalidate**: Find latest checkpoint at position ≤ `edit_range.start`. Discard stale checkpoints.
2. **Resume**: Create a `CekMachine` from the checkpoint's `ParseState`.
3. **Converge**: Compare current state against surviving checkpoints. If convergent → stop.
4. **Yield**: Return newly-parsed AST nodes in the changed region.

### Convergence Detection

Two `ParseState`s are convergent if:
- Same stack depth
- Same binding power
- Same frame variant tags at every stack position

```rust
fn is_convergent(a: &ParseState, b: &ParseState) -> bool {
    a.stack_tags.len() == b.stack_tags.len()
        && a.cur_bp == b.cur_bp
        && a.stack_tags.iter().zip(b.stack_tags.iter()).all(|(ta, tb)| ta == tb)
}
```

## Automata Enhancements

### A: Tree Automata Incremental Validation

Bottom-up tree automata re-evaluate only the changed-node-to-root path:
1. Cache automaton state at each AST node
2. Re-compute only along changed path
3. If state unchanged at ancestor → stop propagating

### B: VPA Minimal Reparse Region

Visibly Pushdown Automata determine the smallest reparse region:
1. Find innermost matched call-return pair containing edit
2. Only reparse within that pair
3. Tighter than "reparse until convergence"

### C: WFST-Guided Ambiguity Resolution

Prediction WFST weights guide incremental reparse through ambiguous regions:
1. Bias toward previously-selected alternative
2. `running_weight` detects divergence → trigger broader reparse

### D: WPDS Checkpoint Density Optimization

Poststar analysis classifies positions at compile time:
- **High density**: ambiguous dispatch, cross-category calls
- **Low density**: deterministic prefix, invariant stack contexts

### E: Symbolic Guard Caching

For predicated types:
1. Track which atoms each guard depends on
2. If edit doesn't change referenced atoms → skip re-evaluation

## Consumer Patterns

### DAP Server

| DAP Concept | CEK Mapping |
|-------------|-------------|
| Breakpoints | Predicates on `ParseState` |
| `stepIn` | One `process_event(Step)` |
| `stepOver` | Step until stack depth ≤ current |
| `stepOut` | Step until stack depth < current |
| Stack frames | `parse_state.stack_tags` |
| Variables | Captures in each frame |

### LSP Server

| LSP Feature | CEK Mapping |
|-------------|-------------|
| `textDocument/didChange` | `IncrementalSession::reparse()` |
| `textDocument/documentSymbol` | `CompletedNode` stream |
| Semantic tokens | Trace entries |
| Error diagnostics | `CekState::Error` |

### REPL

| REPL Feature | CEK Mapping |
|-------------|-------------|
| Execute | `CekMachine::run_to_completion()` with persistent `CekEnvironment` |
| Assign | `env.set(category, name, value)` |
| Step | `CekMachine::process_event(Step)` |

## References

- Wagner, T. A. & Graham, S. L. (1998). *Efficient and flexible incremental parsing.* TOPLAS.
- Alur, R. & Madhusudan, P. (2004). *Visibly pushdown languages.* STOC.
