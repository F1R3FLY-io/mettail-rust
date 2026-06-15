# Simulation Invariants

## What Is It?

An invariant is a predicate that must hold at every step of a simulation. If an invariant fails at any step, the simulation records the violation (with full context: step index, term state, error message) and reports it as a `SimulationFailure`. Invariants are the primary mechanism for expressing **safety properties**: conditions that must always be true.

Located in `simulation/src/invariant.rs`.

## What Does It Do?

The invariant system provides:

1. A trait (`Invariant`) for defining custom invariants.
2. Four built-in invariants covering common safety properties.
3. Integration with the `SimulationRunner`, which checks invariants after every parse and rewrite step.

## Why Was It Chosen?

Safety properties are the most common type of correctness condition in language implementations. "The term should never grow beyond 10,000 nodes." "The pretty-printer's output should always be re-parseable." "Rewriting should always terminate." These are invariants.

By factoring invariants into a trait, the framework supports both built-in checks and user-defined domain-specific checks, without modifying the runner.

## The Invariant Trait

```rust
pub trait Invariant: Send + Sync {
    /// Human-readable name of this invariant.
    fn name(&self) -> &str;

    /// Check the invariant against the current state.
    /// Returns Ok(()) if it holds, Err(message) if violated.
    fn check(&self, state: &InvariantState) -> Result<(), String>;
}
```

The `Send + Sync` bounds allow invariants to be stored in the `SimulationConfig` (which may be shared across threads in future parallel campaigns).

### InvariantState

Each invariant receives an `InvariantState` snapshot of the current simulation step:

```rust
pub struct InvariantState<'a> {
    pub current_term_display: &'a str,  // display string of the term
    pub step_index: usize,               // 0-based step number
    pub term_size: usize,                // approximate AST node count
    pub term_depth: usize,               // maximum nesting depth
    pub language: &'a dyn Language,       // the language being simulated
}
```

The `language` field allows invariants to invoke language-specific operations (e.g., re-parsing the display string to check parseability).

## Built-In Invariants

### BoundedSize

**What it checks:** The term's approximate node count must not exceed a fixed bound.

**Why it matters:** Unbounded term growth is a symptom of non-terminating rewrite systems. If a rewrite rule like `a → f(a, a)` doubles the term size at each step, the term will exceed any bound within logarithmically many steps. `BoundedSize` catches this early.

```rust
pub struct BoundedSize {
    pub max_nodes: usize,
}
```

```
PROCEDURE BoundedSize.check(state):
    IF state.term_size > max_nodes THEN
        RETURN Err("Term size {state.term_size} exceeds bound {max_nodes}
                     at step {state.step_index}")
    RETURN Ok(())
```

**Typical configuration:** `BoundedSize { max_nodes: 10_000 }` for production languages, `max_nodes: 100` for unit tests.

### BoundedDepth

**What it checks:** The term's maximum nesting depth must not exceed a fixed bound.

**Why it matters:** Even if total node count remains small, unbounded depth can cause stack overflows in recursive traversals and indicates pathological nesting (e.g., deeply right-nested `PPar` compositions).

```rust
pub struct BoundedDepth {
    pub max_depth: usize,
}
```

```
PROCEDURE BoundedDepth.check(state):
    IF state.term_depth > max_depth THEN
        RETURN Err("Term depth {state.term_depth} exceeds bound {max_depth}
                     at step {state.step_index}")
    RETURN Ok(())
```

**Typical configuration:** `BoundedDepth { max_depth: 50 }`.

### AlwaysParseable

**What it checks:** The term's display string is always parseable by the language's parser.

**Why it matters:** This is a fundamental soundness property of the language definition. If `parse(display(term))` fails, then either the pretty-printer produces invalid output or the parser has a bug. This invariant checks that the parse-display roundtrip is always valid.

```rust
pub struct AlwaysParseable;
```

```
PROCEDURE AlwaysParseable.check(state):
    clear_var_cache()
    MATCH state.language.parse_term(state.current_term_display):
        Ok(_)  → RETURN Ok(())
        Err(e) → RETURN Err("Term display {state.current_term_display}
                              is not parseable at step {state.step_index}: {e}")
```

Note the `clear_var_cache()` call: MeTTaIL languages use a global variable name cache that must be reset before parsing to avoid stale variable ID conflicts.

**Typical configuration:** Always include `AlwaysParseable` in simulation campaigns. It has no parameters.

### NormalFormReachable

**What it checks:** The rewriting process terminates within the step limit.

**Why it matters:** Termination is the most important liveness property. If rewriting does not terminate, the language definition has a bug (e.g., a non-decreasing rewrite cycle).

Unlike the other invariants, `NormalFormReachable` is **not checked at each step**. Its `check()` method is intentionally a no-op. Instead, the `SimulationRunner` checks it at the end of the simulation by inspecting the selected backend report and trace outcome:

```rust
pub struct NormalFormReachable {
    pub max_steps: usize,
}
```

```
PROCEDURE NormalFormReachable.check(state):
    RETURN Ok(())    // no-op per step

PROCEDURE NormalFormReachable.check_completion(report, total_steps, reached_nf):
    IF report is Complete DovetailRunReport with at least one root THEN
        RETURN Ok(())
    IF report is BoundedByCycleCut DovetailRunReport THEN
        RETURN Err("Dovetail report is non-exhaustive")
    IF report is RuntimeObservations THEN
        RETURN Err("runtime observations are not rewrite-result evidence")
    IF NOT reached_nf AND total_steps ≥ max_steps THEN
        RETURN Err("Normal form not reached after {total_steps} steps
                     (limit: {max_steps})")
    RETURN Ok(())
```

The runner detects `NormalFormReachable` by its `name()` returning `"NormalFormReachable"` and calls the completion check:

```
IF outcome is NormalForm THEN
    RETURN Ok(())
IF outcome is RuntimeReport for Complete DovetailRunReport with roots THEN
    RETURN Ok(())
ELSE
    FOR inv in invariants WHERE inv.name() == "NormalFormReachable":
        RETURN Err(SimulationFailure {
            error: precise backend-report reachability error
        })
```

This makes Dovetail a first-class rewrite backend in simulation. The invariant
does not require an Ascent-shaped BFS path when Dovetail has already produced a
complete checked extraction report. It still rejects `BoundedByCycleCut`
because a cycle-bounded report is honest partial evidence, not proof of
termination or exhaustive reachability. It also rejects Rho observation reports
because those are substrate runtime observations, not rewrite-result evidence.

**Typical configuration:** `NormalFormReachable { max_steps: 1000 }`.

## How Invariant Checking Works in the Runner

The `SimulationRunner` calls `check_invariants_at_step()` at two points:

1. **After parsing**: the initial term is checked before any rewrites.
2. **After each rewrite step**: every intermediate term in the BFS path is checked.

```
PROCEDURE check_invariants_at_step(term_display, step, metrics, ...):
    state ← InvariantState {
        current_term_display: term_display,
        step_index: step,
        term_size: metrics.node_count,
        term_depth: metrics.depth,
        language: self.language,
    }

    FOR invariant in config.invariants:
        MATCH invariant.check(&state):
            Err(msg):
                RETURN Err(SimulationFailure {
                    trace: ExecutionTrace {
                        outcome: InvariantViolation {
                            step, invariant: invariant.name(), message: msg
                        }
                    },
                    error: "Invariant '{invariant.name()}' violated: {msg}"
                })
            Ok(()):
                continue

    RETURN Ok(())
```

Note: invariant violations **do not stop the current simulation run** from being recorded in the campaign results. The failure is collected and the campaign continues with the next test case (fail-slow semantics).

## Writing Custom Invariants

To create a custom invariant, implement the `Invariant` trait:

```rust
use mettail_simulation::invariant::{Invariant, InvariantState};

/// Invariant: the term must not contain the "UNSAFE" substring.
struct NoUnsafeTerms;

impl Invariant for NoUnsafeTerms {
    fn name(&self) -> &str {
        "NoUnsafeTerms"
    }

    fn check(&self, state: &InvariantState) -> Result<(), String> {
        if state.current_term_display.contains("UNSAFE") {
            Err(format!(
                "Term contains 'UNSAFE' at step {}: {}",
                state.step_index, state.current_term_display
            ))
        } else {
            Ok(())
        }
    }
}
```

Then add it to the configuration:

```rust
let config = SimulationConfig {
    invariants: vec![
        Box::new(BoundedSize { max_nodes: 1000 }),
        Box::new(NoUnsafeTerms),
    ],
    ..Default::default()
};
```

### Guidelines for Custom Invariants

1. **Keep `check()` fast.** It is called at every step of every simulation run. Avoid O(n^2) string operations or complex computations.

2. **Use `state.language` sparingly.** Calling `language.parse_term()` (as `AlwaysParseable` does) is relatively expensive. Only do this if the invariant specifically requires re-parsing.

3. **Provide clear error messages.** Include the step index, the term (or a truncated version), and the specific bound or condition that was violated. These messages appear in `SimulationFailure.error` and in the JSONL trace.

4. **Consider stateful invariants.** The current API is stateless (each `check()` call receives an independent snapshot). For invariants that need to track state across steps (e.g., "the term size must be non-increasing"), use `Arc<Mutex<...>>` inside the invariant struct, or use the `MorphologyTracker` for trend detection instead.
