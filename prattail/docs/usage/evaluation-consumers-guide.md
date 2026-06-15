# Evaluation Consumers Guide

> **Status: historical CEK consumer guide.** The production REPL/runtime path
> now calls `Language::run_default_backend_report` and consumes
> `RuntimeBackendReport`. The old `Language::decompose_into_cek` bridge has
> been removed from the production trait and from generated `language!`
> implementations. The examples below describe the retired CEK consumer shape
> for archival/prattail-internal context only.

## Why does this exist?

The CEK evaluator is a generic state machine. Historical consumers drove it
in different ways: the REPL runs it to completion in one shot, a debugger
steps through transitions one at a time, the DAP protocol maps each step
to a protocol message. This guide documents the retired consumer integration
with `CekEvaluator` and `decompose_into_cek`, with pseudocode, sequence
diagrams, and example sessions.

## 1. REPL `exec`

### 1.1 Why does this exist?

The REPL is the primary interactive consumer. In the current production
runtime, `exec` dispatches through the selected backend report. The older
three-tier path below is retained only as historical CEK documentation.

### 1.2 Pseudocode

```
fn exec_term(language, term_str, env):
    term = language.parse_term_for_env(term_str)

    if env is non-empty:
        term = language.substitute_env(term, env)

    term = language.normalize_term(term)

    // Tier 1: direct eval
    if result = language.try_direct_eval(term):
        display(result)
        return

    // Tier 2: CEK decomposition
    evaluator = CekEvaluator::new(display(term))
    if language.decompose_into_cek(term, evaluator):
        observer = NullEvalObserver
        match evaluator.run_to_completion(observer):
            Ok(result_str):
                result_term = language.parse_term(result_str)
                display(result_term)
                return
            Err(_):
                pass  // fall through

    // Tier 3: Ascent rewrite graph
    results = language.run_ascent(term)
    nf = results.normal_form_reachable_from(term.id)
    display(nf)
```

### 1.3 Example Session

```
mettail> lang calculator
Loading language: calculator
Language loaded successfully!

calculator> exec 1 + 2
Parsing... done
Direct eval... Time taken: 1.2us
Done!

Current term (result):
  3

calculator> exec (1 + 2) * (3 + 4)
Parsing... done
CEK eval... Time taken: 3.8us
Done!

Current term (result):
  21

calculator> x = 5
Saved x = 5

calculator> exec x + 10
Parsing... done
Substituting environment... done
Direct eval... Time taken: 0.9us
Done!

Current term (result):
  15
```

### 1.4 Key Behaviors

- `NullEvalObserver` is used -- zero tracing overhead.
- Environment substitution happens before evaluation (pre-substitution).
- `parse_term_for_env` does NOT clear the variable cache, preserving
  bindings across submissions.
- When CEK eval succeeds, the result string is re-parsed to obtain a
  typed AST node for the REPL state.

## 2. nREPL Server

### 2.1 Why does this exist?

An nREPL server provides a network-accessible evaluation endpoint. IDE
plugins (Emacs, VS Code, Neovim) connect over TCP and send evaluation
requests. The server maintains a persistent session with environment
state across requests.

### 2.2 Session Lifecycle

```
  Client                        nREPL Server
    │                                │
    │  connect()                     │
    ├───────────────────────────────▶│ create session
    │                                │ evaluator = CekEvaluator::new("")
    │                                │ env = language.create_env()
    │                                │
    │  eval("x = 5")                 │
    ├───────────────────────────────▶│ language.add_to_env(env, "x", parse("5"))
    │                    ack         │
    │◀───────────────────────────────┤
    │                                │
    │  eval("x + 3")                 │
    ├───────────────────────────────▶│ parse → substitute_env → decompose
    │                                │ evaluator.reset_with_term("8")
    │                                │ evaluator.run_to_completion()
    │              result: "8"       │
    │◀───────────────────────────────┤
    │                                │
    │  disconnect()                  │
    ├───────────────────────────────▶│ drop session
    │                                │
```

### 2.3 Pseudocode

```
struct NreplSession:
    language: &dyn Language
    evaluator: CekEvaluator
    env: Box<dyn Any>

fn handle_eval(session, code):
    term = session.language.parse_term_for_env(code)
    term = session.language.substitute_env(term, session.env)
    term = session.language.normalize_term(term)

    // Tier 1
    if result = session.language.try_direct_eval(term):
        return format(result)

    // Tier 2: reuse evaluator (preserves memo cache)
    session.evaluator.reset_with_term(display(term))
    if session.language.decompose_into_cek(term, session.evaluator):
        observer = NullEvalObserver
        match session.evaluator.run_to_completion(observer):
            Ok(result): return result
            Err(_): pass

    // Tier 3
    results = session.language.run_ascent(term)
    return results.normal_form_reachable_from(term.id).display
```

### 2.4 Key Difference from REPL

The nREPL server calls `evaluator.reset_with_term()` instead of creating
a new `CekEvaluator` each time. This preserves:
- The memo cache (ground terms evaluated in previous requests are not
  re-evaluated)
- The environment (variable bindings persist across requests)

## 3. CLI Debugger

### 3.1 Why does this exist?

A CLI debugger lets developers step through term evaluation transition by
transition, inspecting the control term, environment, and continuation
stack at each point. It uses `evaluator.step()` instead of
`run_to_completion()`.

### 3.2 Pseudocode

```
fn debug_term(language, term_str):
    term = language.parse_term(term_str)
    evaluator = CekEvaluator::new(display(term))
    language.decompose_into_cek(term, evaluator)

    observer = TracingEvalObserver::with_event_recording()
    step_num = 0

    loop:
        print_state(step_num, evaluator)
        cmd = read_command()

        match cmd:
            "step" | "s":
                result = evaluator.step(observer)
                step_num += 1
                match result:
                    StepResult::Accepted:
                        print("Accepted: ", evaluator.control())
                        break
                    StepResult::Error { message }:
                        print("Error: ", message)
                        break
                    StepResult::Continue:
                        continue

            "run" | "r":
                result = evaluator.run_to_completion(observer)
                print("Result: ", result)
                break

            "env" | "e":
                for (name, value) in evaluator.environment():
                    print("  ", name, " = ", value)

            "stack" | "k":
                for frame in evaluator.continuation():
                    print("  ", frame)

            "quit" | "q":
                break

fn print_state(step, evaluator):
    print("[Step ", step, "]")
    print("  State:   ", evaluator.state())
    print("  Control: ", evaluator.control())
    print("  |E|:     ", evaluator.env_size())
    print("  |K|:     ", evaluator.stack_depth())
```

### 3.3 Example Debugger Session

```
$ mettail debug calculator "let x = (1 + 2) in x * 10"

[Step 0]
  State:   Ready
  Control: let x = (1 + 2) in x * 10
  |E|:     0
  |K|:     1   [LetBody(x, "x * 10")]

debug> step
[Step 1]
  State:   Reducing
  Control: (1 + 2)
  |E|:     0
  |K|:     1   [LetBody(x, "x * 10")]

debug> step
[Step 2]
  State:   Reducing
  Control: (1 + 2)
  |E|:     0
  |K|:     1   [LetBody(x, "x * 10")]
  Transition: REDUCE (cache miss, stack non-empty → ASCEND)

debug> step
[Step 3]
  State:   Reducing
  Control: x * 10
  |E|:     1   { x = "(1 + 2)" }
  |K|:     0

debug> env
  x = (1 + 2)

debug> run
Result: Ok("(x * 10)")

debug> quit
```

### 3.4 Key Behaviors

- `TracingEvalObserver::with_event_recording()` captures every transition
  for post-mortem analysis.
- The debugger shows the full CEK triple at each step.
- `stack` command displays the continuation stack bottom-to-top.

## 4. DAP Server

### 4.1 Why does this exist?

The Debug Adapter Protocol (DAP, v1.65) is a standard for IDE debugging.
A DAP server maps CEK evaluator concepts to DAP protocol messages, enabling
VS Code and other IDEs to step through term evaluation with breakpoints,
variable inspection, and stack frame display.

### 4.2 CEK → DAP Concept Mapping

| CEK Concept | DAP Protocol Concept | DAP Message |
|-------------|---------------------|-------------|
| `evaluator.state()` | Thread state | `ThreadEvent` |
| `evaluator.step()` | Step execution | `StepInResponse` |
| `evaluator.continuation()` | Stack frames | `StackTraceResponse` |
| `EvalFrame` variant fields | Variables | `VariablesResponse` |
| `evaluator.control()` | Current expression | `EvaluateResponse` |
| `CekControl::Abort` | Pause request | `PauseResponse` |
| `StepResult::Accepted` | Thread exit | `TerminatedEvent` |
| `EvalStepEvent` | Stopped event | `StoppedEvent` |

### 4.3 Sequence Diagram

```
  IDE (DAP Client)              DAP Server              CekEvaluator
      │                            │                        │
      │  InitializeRequest         │                        │
      ├───────────────────────────▶│                        │
      │  InitializeResponse        │                        │
      │◀───────────────────────────┤                        │
      │                            │                        │
      │  LaunchRequest(term)       │                        │
      ├───────────────────────────▶│  new(term)             │
      │                            ├───────────────────────▶│
      │                            │  decompose_into_cek    │
      │                            ├───────────────────────▶│
      │  StoppedEvent(entry)       │                        │
      │◀───────────────────────────┤                        │
      │                            │                        │
      │  StackTraceRequest         │                        │
      ├───────────────────────────▶│  continuation()        │
      │                            ├───────────────────────▶│
      │  StackTraceResponse        │  [frame₁, frame₂, ...]│
      │◀───────────────────────────┤◀───────────────────────┤
      │                            │                        │
      │  VariablesRequest(frame₁)  │                        │
      ├───────────────────────────▶│  environment()         │
      │                            ├───────────────────────▶│
      │  VariablesResponse         │  {x: "5", y: "10"}    │
      │◀───────────────────────────┤◀───────────────────────┤
      │                            │                        │
      │  StepInRequest             │                        │
      ├───────────────────────────▶│  step(dap_observer)    │
      │                            ├───────────────────────▶│
      │  StoppedEvent(step)        │  CekControl::Continue  │
      │◀───────────────────────────┤◀───────────────────────┤
      │                            │                        │
      │  ContinueRequest           │                        │
      ├───────────────────────────▶│  run_to_completion()   │
      │                            ├───────────────────────▶│
      │  TerminatedEvent           │  Ok(result)            │
      │◀───────────────────────────┤◀───────────────────────┤
```

### 4.4 DAP Observer Implementation

```
struct DapObserver:
    sender: DapMessageSender
    breakpoints: Vec<BreakpointPredicate>

impl EvalObserver for DapObserver:
    fn on_eval_event(event):
        // Check breakpoints
        for bp in breakpoints:
            if bp.matches(event):
                sender.send(StoppedEvent {
                    reason: "breakpoint",
                    thread_id: 1,
                })
                return CekControl::Abort

        // Emit stopped event for step requests
        if stepping_mode:
            sender.send(StoppedEvent {
                reason: "step",
                thread_id: 1,
            })
            return CekControl::Abort  // pause after each step

        return CekControl::Continue
```

### 4.5 Stack Frame Generation

Each `EvalFrame` on the continuation stack maps to a DAP `StackFrame`:

```
fn frames_to_dap(evaluator) -> Vec<DapStackFrame>:
    frames = []
    for (i, frame) in evaluator.continuation().enumerate():
        frames.push(DapStackFrame {
            id: i,
            name: frame.variant_name(),
            source: Source { name: "eval" },
            line: 0,
            column: 0,
        })
    // Add the current control as the top frame
    frames.insert(0, DapStackFrame {
        id: evaluator.stack_depth(),
        name: format!("control: {}", evaluator.control()),
        ...
    })
    return frames
```

## 5. LSP Integration

### 5.1 Why does this exist?

The parsing CEK machine (not the evaluation CEK) integrates with the
Language Server Protocol (LSP, v3.17) for incremental reparsing. When a
user edits a file, the LSP server does not re-parse from scratch. Instead,
it uses checkpointed parse states to resume from the nearest valid point
before the edit.

### 5.2 Sequence Diagram

```
  Editor (LSP Client)         LSP Server           IncrementalSession
      │                          │                        │
      │  didOpen(file)           │                        │
      ├─────────────────────────▶│  parse_full()          │
      │                          ├───────────────────────▶│
      │                          │  record checkpoints    │
      │  diagnostics             │  at each token         │
      │◀─────────────────────────┤◀───────────────────────┤
      │                          │                        │
      │  didChange(edit@pos)     │                        │
      ├─────────────────────────▶│  invalidate_after(pos) │
      │                          ├───────────────────────▶│
      │                          │  checkpoint_at_or_     │
      │                          │  before(pos)           │
      │                          ├───────────────────────▶│
      │                          │  resume parse from     │
      │                          │  checkpoint            │
      │                          │                        │
      │                          │  step until convergent │
      │                          │  with surviving        │
      │                          │  checkpoint            │
      │  diagnostics (updated)   │                        │
      │◀─────────────────────────┤                        │
```

### 5.3 Key Types

- `IncrementalSession`: Manages checkpoint cache for a single source buffer
- `ParseState`: Complete CEK parse state (stack tags, binding power, position)
- `is_convergent(a, b)`: Two states are convergent if their continuation
  stacks and binding powers match (the parse will proceed identically)

### 5.4 Checkpoint Placement

Default: every token (`checkpoint_interval = 1`) for sub-microsecond edits.
Memory: ~200--400 KB per file with token-level checkpoints and copy-on-write
stacks.

## 6. Custom Observers

### 6.1 Implementing `EvalObserver`

To create a custom observer, implement the `EvalObserver` trait:

```rust
use mettail_prattail::cek::CekControl;
use mettail_prattail::cek_eval::{EvalObserver, EvalStepEvent};

struct MyObserver {
    // ... your state ...
}

impl EvalObserver for MyObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl {
        // Inspect the event, do something, return control directive
        CekControl::Continue
    }
}
```

### 6.2 Example: Logging Observer

```rust
struct LoggingObserver;

impl EvalObserver for LoggingObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl {
        eprintln!(
            "[{}] term={} depth={} env={}",
            event.rule,
            event.term_display,
            event.stack_depth,
            event.env_size,
        );
        CekControl::Continue
    }
}
```

Usage:

```rust
let mut evaluator = CekEvaluator::new("1 + 2".to_string());
language.decompose_into_cek(term, &mut evaluator);
let mut obs = LoggingObserver;
let result = evaluator.run_to_completion(&mut obs);
```

Output:

```
[REDUCE] term=2 depth=1 env=0
[ASCEND] term=2 depth=1 env=0
[REDUCE] term=(1 + 2) depth=0 env=0
[ACCEPT] term=(1 + 2) depth=0 env=0
```

### 6.3 Example: Profiling Observer

```rust
use std::time::Instant;

struct ProfilingObserver {
    start: Instant,
    step_times: Vec<f64>,
}

impl ProfilingObserver {
    fn new() -> Self {
        Self {
            start: Instant::now(),
            step_times: Vec::new(),
        }
    }

    fn report(&self) {
        let total: f64 = self.step_times.iter().sum();
        let mean = total / self.step_times.len() as f64;
        eprintln!("Total: {:.3}ms, Steps: {}, Mean: {:.3}us/step",
            total * 1000.0,
            self.step_times.len(),
            mean * 1_000_000.0,
        );
    }
}

impl EvalObserver for ProfilingObserver {
    fn on_eval_event(&mut self, _event: &EvalStepEvent<'_>) -> CekControl {
        let now = Instant::now();
        self.step_times.push(now.duration_since(self.start).as_secs_f64());
        self.start = now;
        CekControl::Continue
    }
}
```

### 6.4 Example: Breakpoint Observer

```rust
struct BreakpointObserver {
    /// Stop when control term contains this substring
    term_pattern: String,
    /// Stop when stack depth exceeds this limit
    max_depth: Option<usize>,
}

impl EvalObserver for BreakpointObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl {
        // Term-content breakpoint
        if event.term_display.contains(&self.term_pattern) {
            eprintln!("Breakpoint: term contains '{}'", self.term_pattern);
            return CekControl::Abort;
        }

        // Depth breakpoint
        if let Some(max) = self.max_depth {
            if event.stack_depth > max {
                eprintln!("Breakpoint: depth {} > {}", event.stack_depth, max);
                return CekControl::Abort;
            }
        }

        CekControl::Continue
    }
}
```

Usage:

```rust
let mut obs = BreakpointObserver {
    term_pattern: "error".to_string(),
    max_depth: Some(100),
};
let result = evaluator.run_to_completion(&mut obs);
match result {
    Ok(value) => println!("Result: {}", value),
    Err(msg) => println!("Stopped: {}", msg),
}
```

### 6.5 Combining Observers

Since `EvalObserver` is a trait, observers can be composed:

```rust
struct CompositeObserver {
    observers: Vec<Box<dyn EvalObserver>>,
}

impl EvalObserver for CompositeObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl {
        for obs in &mut self.observers {
            match obs.on_eval_event(event) {
                CekControl::Abort => return CekControl::Abort,
                CekControl::Checkpoint => return CekControl::Checkpoint,
                CekControl::Continue => continue,
            }
        }
        CekControl::Continue
    }
}
```

## 7. Parsing CEK vs Evaluation CEK

MeTTaIL has two distinct CEK machines. Consumers should use the correct one:

| Aspect | Parsing CEK (`cek.rs`) | Evaluation CEK (`cek_eval.rs`) |
|--------|----------------------|-------------------------------|
| **Purpose** | Token consumption → AST construction | Term rewriting → normal form |
| **Control** | Token stream position + binding power | Current term (string display) |
| **Environment** | Frame captures (field values) | Variable bindings (HashMap) |
| **Kontinuation** | `Vec<Frame_Cat>` (generated per-category) | `Vec<EvalFrame>` (6 generic variants) |
| **Observer trait** | `CekObserver` (feature = `cek-runtime`) | `EvalObserver` (feature = `cek-runtime`) |
| **Consumers** | DAP (parse debugging), LSP (incremental), Railroad | REPL exec, nREPL, CLI debugger, DAP (eval) |
| **Feature gate** | Always available (base types); `cek-runtime` for observer | `cek-runtime` |

## References

- DAP Specification v1.65: https://microsoft.github.io/debug-adapter-protocol/
- LSP Specification v3.17: https://microsoft.github.io/language-server-protocol/
- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
  and the lambda-calculus.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University
  Press.

## Source Files

| File | Content |
|------|---------|
| `prattail/src/cek.rs` | Parsing CEK, CekObserver, TracingObserver, NullObserver |
| `prattail/src/cek_eval.rs` | CekEvaluator, EvalFrame, EvalObserver, EvalTrace |
| `runtime/src/language.rs` | Production runtime trait and selected backend report dispatch |
| `repl/src/repl.rs` | REPL execution through the selected runtime backend report |
| `prattail/src/green_thread.rs` | GreenThread with persistent CEK triple |
| `prattail/src/scheduler.rs` | Scheduler FSM driving green thread execution |
