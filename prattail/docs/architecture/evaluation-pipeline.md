# Evaluation Pipeline Architecture

## Why does this exist?

MeTTaIL languages need to reduce terms to semantic results. A Rholang program
`(1 + 2) + (3 + 4)` must evaluate to `10`, and a process-calculus program may
need rewrite evidence or RSpace observations rather than a single scalar normal
form.

The production user-facing execution boundary is now the selected runtime
backend:

```text
parsed term
  -> Language::run_default_backend_report(default_backend)
  -> RuntimeBackendReport
```

That report may be Ascent-shaped, Dovetail-report-shaped, or Rho-observation-
shaped. The legacy direct evaluator and CEK evaluator remain useful explicit
tools for tests, debugging, and specialized consumers, but REPL `exec` must not
silently bypass the selected backend by trying direct evaluation or CEK first.
Ascent likewise remains a graph oracle/reference path, not the unconditional
production fallback once a language has selected Dovetail or Rho.

## 1. Runtime Backend Boundary

### 1.1 Production Flowchart

```
         ┌──────────────┐
         │  Parsed term  │
         └──────┬───────┘
                │
                ▼
    ┌────────────────────────────────────┐
    │ selected RuntimeBackend capability │
    └──────────────┬─────────────────────┘
                   │
                   ▼
    ┌────────────────────────────────────┐
    │ Language::run_default_backend_     │
    │ report(term, backend)              │
    └──────────────┬─────────────────────┘
                   │
        ┌──────────┴───────────┬────────────────┐
        ▼                      ▼                ▼
 ┌──────────────┐      ┌────────────────┐ ┌────────────────┐
 │ Ascent graph │      │ Dovetail report│ │ Rho observations│
 └──────────────┘      └────────────────┘ └────────────────┘
```

### 1.2 Explicit Helper: `try_direct_eval`

**When it fires.** The term is a fully-ground expression whose value can be
computed by native Rust operations. Examples:

- `1 + 2` -- integer addition, returns `Int(3)`
- `true && false` -- boolean conjunction, returns `Bool(false)`
- `"hello" ++ " world"` -- string concatenation

**Why it exists.** These cases require zero rewrite steps. The `language!`
macro generates a recursive match over the AST that evaluates operators
in-place. No continuation stack, no environment, no observer overhead.

**Cost.** O(n) in the size of the ground sub-expression tree, but with
minimal constant factors (no allocation beyond the result term).

**Signature.** `Language::try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>>`

Returns `None` when the term contains free variables, unknown operators,
or constructs that require rewriting (e.g., `new x in { ... }`).

### 1.3 Explicit Helper: CEK Decomposition + Evaluation

**Status.** This helper is retired from the production `Language` trait.
Generated `language!` implementations no longer emit `decompose_into_cek`;
Dovetail/Rho execution enters through checked `RuntimeBackendReport` values.
The notes below remain as historical/prattail-internal context for the CEK
evaluator.

**When it fired historically.** The term was structurally complex (nested binary operators,
let-bindings, parallel compositions) but does not require the full Ascent
rewrite graph. The retired `decompose_into_cek` method successfully pushed frames
onto the evaluator's continuation stack, and `run_to_completion` reaches
the `Accepted` state without error.

**Why it existed.** Many terms fall between "trivially ground" and "needs
full rewriting." A nested expression like `(1 + 2) + (3 + 4)` requires
descending into sub-expressions, evaluating them, and combining results.
The CEK machine handles this with an explicit continuation stack, without
building a rewrite graph.

**Cost.** O(n) in term size, with per-step observer callback overhead (zero
for `NullEvalObserver`). Step limit (default 10,000) prevents divergence.

**Historical signature.**

```rust
Language::decompose_into_cek(
    &self,
    term: &dyn Term,
    evaluator: &mut CekEvaluator,
) -> bool
```

Returns `true` if frames were pushed; `false` if the language has no CEK
decomposition for this term shape.

### 1.4 Explicit Reference Path: Ascent Rewrite Graph

**When it fires.** Ascent is available when the caller explicitly selects the
Ascent runtime backend or asks for graph/oracle behavior. It is used for terms
with rewrite rules, process-algebraic constructs (`P | Q` with channel
communication), differential checks, graph navigation, and rollout comparison
against Dovetail.

**Why it exists.** Some terms genuinely need the full rewrite graph. A
Rholang process `for (@x <- ch) { x!(42) } | ch!(true)` involves channel
communication, name substitution, and structural equivalence -- none of
which the CEK evaluator handles directly.

**Cost.** O(|reachable terms| x |rules|). Builds the complete rewrite
graph and returns all normal forms reachable from the initial term.

**Signature.** `Language::run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String>`

### 1.5 Concrete Examples

| Input | Production backend result | Explicit helper/oracle use |
|-------|------|-----|
| `1 + 2` | selected backend report | `try_direct_eval` can test native ground arithmetic |
| `(1 + 2) + (3 + 4)` | selected backend report | CEK can inspect continuation-stack evaluation |
| `let x = 5 in x + 1` | selected backend report | CEK can inspect environment and body evaluation |
| `{P \| Q}` with rewrite rules | selected backend report | Ascent can provide a graph oracle/reference |
| `x + 1` (x free) | selected backend report or backend rejection | Ascent/Dovetail can report rewrite evidence; CEK may decline |

## 2. Why a CEK Machine?

### 2.1 Formal Definition

The CEK machine (Felleisen & Friedman, 1986) is a triple:

    C = ⟨control, environment, kontinuation⟩

- **Control (C)**: The current term under focus.
- **Environment (E)**: A finite map from variable names to values.
- **Kontinuation (K)**: An explicit stack of evaluation contexts.

Small-step operational semantics:

    ⟨c, ρ, κ⟩ → ⟨c', ρ', κ'⟩

Each step inspects the control term, consults the environment, and
manipulates the continuation stack. The machine halts when the control
is a value and the stack is empty.

### 2.2 CekEvaluator as Reactive FSM

`CekEvaluator` implements the CEK machine as a reactive finite state
machine following MeTTaTron's `State x Event → State' x Actions` pattern:

```
  ┌───────┐  step(Reduce)  ┌──────────┐  step(Descend)  ┌─────────────┐
  │ Ready ├───────────────▶│ Reducing ├────────────────▶│ Descending  │
  └───────┘                └────┬─────┘                 └──────┬──────┘
                                │                              │
                         Accept │                    step(Reduce)
                                ▼                              │
                          ┌──────────┐                         ▼
                          │ Accepted │◀────── Ascend ── ┌─────────────┐
                          └──────────┘     (stack empty)│ Ascending   │
                                                       └─────────────┘
```

### 2.3 Transition Rules

The evaluator has 6 transition rules that define its small-step semantics:

| Rule | From State | Condition | To State | Stack Effect |
|------|-----------|-----------|----------|-------------|
| **Reduce** | Ready | -- | Reducing | -- |
| **Descend** | Reducing | Term has unevaluated subterms | Reducing | Push frame |
| **Ascend** | Reducing | Subterm is in normal form | Reducing | Pop frame, integrate result |
| **Bind** | (external) | Pattern variable matched | Reducing | Update environment |
| **Apply** | (external) | Rewrite rule fires | Reducing | Replace control term |
| **Accept** | Reducing | No rules match, stack empty | Accepted | -- |

### 2.4 Transition Diagram

```
  Reduce ──────▶ Descend ──────▶ Reduce (recursive subterm)
    │                 │
    │                 └──▶ Ascend ──▶ Apply ──▶ Reduce (re-check)
    │                                      │
    └──▶ Bind ──▶ Apply                    └──▶ Accept (normal form)
    │
    └──▶ Accept (no rules match)
```

### 2.5 Memoization

Ground terms (terms with no free variables) are cached in a memo table:

```
  memo_cache : HashMap<String, String>
```

When the evaluator encounters a ground term it has previously reduced, it
returns the cached normal form immediately. This is effective for Rholang's
parallel composition where identical processes appear multiple times
(e.g., `P | P | P` where `P` is ground).

Cache statistics are tracked in `EvalTrace` via `cache_hits` / `cache_misses`
and exposed through `cache_hit_rate()`.

## 3. The Reactive Observer Pattern

### 3.1 Why Observers?

The evaluator is a **pure state machine** -- it should not know about
logging, breakpoints, protocol messages, or profiling. But all of these
need to intercept every transition. The observer pattern externalizes
side-effects through a single callback interface.

### 3.2 The EvalObserver Trait

```rust
pub trait EvalObserver {
    fn on_eval_event(&mut self, event: &EvalStepEvent<'_>) -> CekControl;
}
```

The observer receives a borrowed `EvalStepEvent` at each transition (zero
allocation on the hot path) and returns a `CekControl` directive:

| Return Value | Meaning |
|--------------|---------|
| `CekControl::Continue` | Proceed to the next transition |
| `CekControl::Checkpoint` | Record the current PDA configuration, then continue |
| `CekControl::Abort` | Halt evaluation immediately |

### 3.3 Observer Dataflow

```
    ┌──────────────────┐     EvalStepEvent      ┌──────────────────┐
    │   CekEvaluator   ├───────────────────────▶│   EvalObserver   │
    │                  │                         │                  │
    │  step() fires    │     CekControl          │  on_eval_event() │
    │  transition      │◀───────────────────────┤  returns control │
    └──────────────────┘                         └──────────────────┘
```

### 3.4 Provided Implementations

| Observer | Purpose | Overhead |
|----------|---------|----------|
| `NullEvalObserver` | Discards all events | Zero (inlined away) |
| `TracingEvalObserver` | Collects `EvalTrace` statistics | Low (counter increments) |
| `TracingEvalObserver::with_event_recording()` | Full event log for replay | Moderate (String clones) |
| `AbortAfterObserver(n)` | Aborts after n steps | Minimal (counter check) |

### 3.5 How One Interface Serves Explicit Consumers

- **Focused CEK tests/tools**: `NullEvalObserver` + `run_to_completion()`
- **Tracing/profiling**: `TracingEvalObserver` with aggregate statistics
- **Breakpoints (debugger)**: Custom observer returning `CekControl::Abort`
  when a breakpoint predicate matches
- **DAP protocol**: Observer emitting `StoppedEvent` DAP messages on each step
- **Step limit**: `AbortAfterObserver(10_000)` prevents divergent rewrites

## 4. Structural Sharing and Fork

### 4.1 Why Persistent Data Structures?

When evaluating `P | Q` concurrently, each sub-process needs its own
environment and continuation stack. Naive deep cloning is O(n) per fork.
With persistent data structures from the `im` crate, forking is O(1):

| Operation | `HashMap` | `im::HashMap` |
|-----------|-----------|---------------|
| Clone | O(n) | O(1) (path copy) |
| Insert | O(1) amortized | O(log n) |
| Lookup | O(1) amortized | O(log n) |

### 4.2 Green Thread Integration

Each `GreenThread` carries its own CEK triple using persistent types:

```
environment:  im::HashMap<String, im::HashMap<String, String>>
continuation: im::Vector<EvalFrame>
```

Forking a green thread clones both in O(1). The parent and child share
the underlying tree structure, diverging only at mutation points (structural
sharing via path copying).

## 5. References

- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
  and the lambda-calculus. *Formal Description of Programming Concepts III*,
  pp. 193--219.
- Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge
  University Press.
- Reppy, J. H. (1999). *Concurrent Programming in ML*. Cambridge University
  Press.
- Reynolds, J. C. (1972). Definitional interpreters for higher-order
  programming languages. *Proceedings of the ACM Annual Conference*,
  pp. 717--740.

## Source Files

| File | Content |
|------|---------|
| `prattail/src/cek.rs` | Parsing CEK: states, events, transitions, observer |
| `prattail/src/cek_eval.rs` | Evaluation CEK: CekEvaluator, EvalFrame, EvalObserver |
| `prattail/src/green_thread.rs` | Green thread with persistent CEK triple |
| `runtime/src/language.rs` | Production runtime trait and selected backend report dispatch |
| `macros/src/gen/runtime/language.rs` | Code generation for selected backend reports and runtime metadata |
| `repl/src/repl.rs` | `exec` dispatch through the selected runtime backend report |
