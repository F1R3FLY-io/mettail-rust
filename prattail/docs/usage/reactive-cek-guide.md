# Reactive CEK Machine Usage Guide

## Overview

The reactive CEK machine provides three driving modes for the trampolined parser:

1. **Batch**: `run_to_completion()` — equivalent to the current `parse_Cat()`
2. **Step**: `process_event(Step)` — one CEK transition at a time
3. **Checkpoint**: `run_to_checkpoint()` — pause at natural boundaries

## Batch Mode (Default)

For standard parsing, batch mode is equivalent to the existing `parse_Cat()`:

```rust
// The generated parser already uses batch mode internally.
// No changes needed for existing code.
let result = parse_Expr(tokens, &mut pos, 0)?;
```

## Step Mode (Debugging)

For DAP integration or parser debugging:

```rust
use mettail_prattail::cek::*;

// Create a trace collector for recording transitions
let mut collector = TraceCollector::new();

// Step through parsing "1 + 2 * 3"
let mut state = ParseState::new(0);
state.pos = 0;

// Each step advances one CEK transition
// The generated parser exposes step-by-step execution
// via CekTraceEntry emission.
```

## Checkpoint Mode (LSP)

For incremental parsing after edits:

```rust
use mettail_prattail::cek::*;

let mut session = IncrementalSession::new(0, 1); // min_bp=0, every-token checkpoints

// Initial parse: creates checkpoints throughout
// session.parse_full(&tokens);

// After user edits at position 15:
// session.invalidate_after(15);
// Find nearest checkpoint before the edit
if let Some((cp_pos, cp_state)) = session.checkpoint_at_or_before(15) {
    // Resume parsing from checkpoint
    // Re-parse until convergence with surviving checkpoints
}
```

## Environment Persistence (REPL)

For REPL sessions with persistent bindings:

```rust
use mettail_prattail::cek::*;

let mut env = CekEnvironment::new();

// First submission: x = 5
env.set("Int", "x", "5".to_string());

// Second submission: x + 3 → looks up x from env
let value = env.get("Int", "x"); // Some("5")
```

## Trace Collection (Railroad Annotation)

For grammar visualization:

```rust
use mettail_prattail::cek::*;
use mettail_prattail::railroad::*;

let mut collector = TraceCollector::new();

// After parsing, annotate diagrams
let spec = /* your LanguageSpec */;
let mut diagrams = generate_railroad_diagrams(&spec);
annotate_diagrams(&mut diagrams, &collector);

// Print ASCII railroad for "Expr" category
if let Some(diagram) = diagrams.get("Expr") {
    println!("{}", diagram_to_text(&diagram.root));
}
```

## Convergence Detection

For incremental reparsing, two states are convergent when:

```rust
use mettail_prattail::cek::is_convergent;

let state_a = /* checkpoint state */;
let state_b = /* reparsed state */;

if is_convergent(&state_a, &state_b) {
    // Parse will proceed identically from here
    // Stop re-parsing, reuse existing parse tree
}
```
