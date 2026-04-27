# W7 Stage 0 Survey: Reactive Design Audit

This document is the deliverable of W7 Stage 0 of the WPDS-Runtime full parser
migration (plan v5.1). It surveys the reactive design contracts that already
exist for the parser CEK, classifies what is implemented vs aspirational, and
specifies what the WPDS migration must preserve, replace, or add.

The survey gates Stages 1–11. All design decisions in subsequent stages must
trace back to a contract recorded here.

---

## 1. Reactive Design Contracts (Authoritative Sources)

The following seven documents constitute the authoritative reactive design
intent for the parser and its consumers. They were read verbatim during
Stage 0; this section quotes the binding contracts.

### 1.1. `prattail/docs/architecture/reactive-state-machine.md`

> "The CEK machine follows the **reactive state machine** pattern from
> MeTTaTron: `State × Event → Transition`. The core driver is a pure
> function. External consumers (DAP, LSP, REPL) provide the event loop."

**Binding contracts:**
- (R1) Parser is a pure transition function: `State × Event → Transition`.
- (R2) External consumers drive via `process_event(event)`.
- (R3) Three transition outcomes: `NoChange | Transition { new_state, trace } | Checkpoint { pos, depth, bp }`.
- (R4) MeTTaTron mapping: `ReplState ≅ CekState`, `ReplEvent ≅ CekEvent`,
  `StateTransition ≅ CekTransition`, `process_event() ≅ process_event()`.

### 1.2. `prattail/docs/usage/reactive-cek-guide.md`

> "Three driving modes for the trampolined parser:
> 1. **Batch**: `run_to_completion()` — equivalent to the current `parse_Cat()`
> 2. **Step**: `process_event(Step)` — one CEK transition at a time
> 3. **Checkpoint**: `run_to_checkpoint()` — pause at natural boundaries"

**Binding contracts:**
- (R5) Batch mode is convenience wrapper over reactive driver, not a separate path.
- (R6) Step mode emits `CekTraceEntry` per transition (DAP).
- (R7) Checkpoint mode pauses at natural boundaries (LSP).

### 1.3. `prattail/docs/usage/evaluation-consumers-guide.md`

This document covers BOTH the parser CEK and the evaluator CEK. The
parser-relevant section is §5 (LSP Integration).

**Binding contracts:**
- (R8) LSP consumers use `IncrementalSession::reparse(edit_range, new_tokens)`.
- (R9) `IncrementalSession` holds checkpoint cache for a single source buffer.
- (R10) `is_convergent(a, b)` halts reparse when stacks/binding-powers match.
- (R11) Default checkpoint granularity: every token (interval = 1).
- (R12) Memory budget: ~200–400 KB per file with token-level checkpoints
  (assumes copy-on-write stacks).

### 1.4. `prattail/docs/usage/incremental-parsing-guide.md`

> "On file open, a full parse creates checkpoints. On edits, only the
> affected region is re-parsed."

**Binding contracts:**
- (R13) Reparse algorithm: invalidate → find checkpoint → resume → converge.
- (R14) Tunable `checkpoint_interval`: 1 (real-time IDE), 10 (medium), 50 (large).
- (R15) Future enhancements (informational, not binding): VPA-bounded reparse,
  tree-automata validation, WFST-guided ambiguity, WPDS density optimization,
  symbolic guard caching.

### 1.5. `prattail/docs/design/online-parsing.md` (CEK-6)

> "The reactive CEK machine externalizes parse state as a **suspendable,
> inspectable state machine**. Any consumer (DAP server, LSP server, REPL,
> railroad annotator) can drive it at its own pace via `process_event()`."

**Binding contracts:**
- (R16) Parse state is suspendable AND inspectable.
- (R17) State-machine diagram: `Ready → PrefixDispatch → InfixLoop → Unwinding → Accepted | Error`.
- (R18) DAP mappings: breakpoints = predicates on `ParseState`; `stepIn` = one
  `process_event(Step)`; `stepOver/stepOut` = step until depth ≤/< current;
  stack frames = `parse_state.stack_tags`; variables = captures per frame.
- (R19) LSP mappings: `didChange` → `IncrementalSession::reparse()`;
  `documentSymbol` → `CompletedNode` stream; semantic tokens → trace entries;
  diagnostics → `CekState::Error`.
- (R20) REPL mappings: execute → `run_to_completion()` with persistent
  `CekEnvironment`; assign → `env.set(category, name, value)`; step →
  `process_event(Step)`.

### 1.6. `prattail/docs/architecture/evaluation-pipeline.md`

This document is mostly evaluator (Tier 2) but §3 articulates the observer
philosophy that applies to both parser and evaluator.

> "The evaluator is a **pure state machine** — it should not know about
> logging, breakpoints, protocol messages, or profiling. But all of these
> need to intercept every transition. The observer pattern externalizes
> side-effects through a single callback interface."

**Binding contracts:**
- (R21) Pure state machine + observer trait is the canonical layering.
- (R22) Observer trait returns `CekControl::Continue | Checkpoint | Abort`.
- (R23) `NullObserver` zero-cost (inlined away).
- (R24) Observer is the SECONDARY contract; reactive FSM (`process_event`)
  is the PRIMARY contract for external consumers.

### 1.7. `docs/design/made/rholang-target/design.md` §13 ("Integration Affordances")

> "The migration does not implement any LSP, DAP, nREPL, or REPL server.
> Those are a separate, future track of work. What the migration *does*
> guarantee is that the following affordances — the hooks that a future
> server would attach to — are preserved or added."

**Binding contracts:**
- (R25) `CekObserver`/`CekEvent`/`CekControl` preserved verbatim.
- (R26) New control variant `CekControl::Pause` for halt-awaiting-controller.
- (R27) `RhoEvaluator::checkpoint() -> RSpaceHandle` and `restore(handle)`
  for bidirectional stepping. (Evaluator-side; parser-side is `IncrementalSession`.)
- (R28) Source map: `Par → (file, line, column)` table; every emitted `Par`
  gets a stable id. Basis for breakpoint-to-line mapping.
- (R29) One green thread = one session. Inter-session events via
  `ChannelId::InterSession`.
- (R30) `Theory::run_ascent()` retires in favour of
  `Theory::rho_evaluate(term, n_steps)`. (Evaluator-side; parser stays.)
- (R31) No new REPL commands implemented in the migration; affordances are
  exposed so commands are *implementable later*.

---

## 2. Implementation State (What Exists Today)

### 2.1. Files and sizes

| File | Lines | Purpose |
|---|---|---|
| `prattail/src/cek.rs` | 1,309 | Parser CEK types + observer + IncrementalSession |
| `prattail/src/cek_eval.rs` | 2,420 | Evaluator CEK + observer (UNCHANGED by W7) |
| `prattail/src/wpds.rs` | 4,008 | WPDS infrastructure (offline analysis only today) |
| `prattail/src/gss.rs` | 406 | GSS skeleton; references aspirational `reactive-cek` feature |
| `prattail/src/trampoline.rs` | 7,278 | Current trampolined parser (TO BE REPLACED) |
| `prattail/src/dispatch.rs` | 2,001 | Cross-cat dispatch (TO BE REPLACED) |
| `prattail/src/pratt.rs` | 2,172 | Pratt BP analysis (TO BE PRESERVED, drives WPDS rule emission) |

### 2.2. Reactive contracts: implemented vs aspirational

| Contract | State | Evidence |
|---|---|---|
| (R1) Pure `State × Event → Transition` | **Aspirational** | Type definitions exist (`CekState`, `CekEvent`, `CekTransition` in `cek.rs`); `process_event` is documented but no method on `CekMachine` actually drives the trampoline reactively. The trampoline is its own loop. |
| (R2) External consumer driving | **Aspirational** | No `process_event` callsites outside the documentation. |
| (R3) Three transition outcomes | **Implemented (types)** | Enum exists; not actually emitted at runtime. |
| (R4) MeTTaTron mapping | **Documented** | Conceptual mapping; not load-bearing in code. |
| (R5) Batch as wrapper | **Inverted** | The `parse_<Cat>` batch path IS the only path. Reactive driver does not exist. |
| (R6) `parse_<Cat>_traced` for DAP | **Implemented but unused** | Generated for every category; **zero callsites** in workspace. |
| (R7) Checkpoint mode | **Aspirational** | `IncrementalSession` exists with all methods + tests, but is never called outside its own test module. |
| (R8) `IncrementalSession::reparse(edit, tokens)` | **Missing method** | Methods exist: `new`, `record_checkpoint`, `checkpoint_at_or_before`, `invalidate_after`, `clear`. **No `reparse` method exists** despite being documented. |
| (R9) Per-buffer checkpoint cache | **Implemented (type)** | `BTreeMap<usize, ParseState>` skeleton in place. |
| (R10) `is_convergent(a, b)` | **Implemented** | Function exists in `cek.rs`. |
| (R11)–(R14) Checkpoint granularity | **Implemented (parameter)** | `checkpoint_interval` is plumbed; no consumer sets it. |
| (R15) VPA/tree-automata/WFST/WPDS density / symbolic-guard caching | **Aspirational** | Future enhancements; no hooks today. |
| (R16) Suspendable + inspectable | **Partial** | `ParseState` is inspectable; not suspendable (no resumption from arbitrary state). |
| (R17) State machine diagram | **Aspirational** | The trampoline does not transition through these named states; the diagram is a target. |
| (R18) DAP mappings | **Aspirational** | No DAP server attaches to anything. |
| (R19) LSP mappings | **Aspirational** | No LSP server attaches to anything. |
| (R20) REPL mappings | **Partial** | REPL exists and uses the batch parser; does NOT use `process_event` or `CekEnvironment`. |
| (R21) Pure FSM + observer layering | **Inverted on parser side** | The trampoline is impure (mutates pos, work-stack, output). Observer trait exists but the only emission point is `parse_<Cat>_traced`, which is unused. |
| (R22) `CekControl` directives | **Implemented (type)** | Enum exists; never returned to a driver. |
| (R23) `NullObserver` zero-cost | **Implemented** | Marker struct with `#[inline(always)]`. |
| (R24) Reactive primary, observer secondary | **Inverted** | Observer is the only documented hook; reactive driver is documented but absent. |
| (R25) Preserve `CekObserver`/`CekEvent`/`CekControl` | **Migration mandate** | Plan v5 deletes parser-side `CekObserver`; replacement (`WalkerConsumer`) must subsume its capabilities. |
| (R26) `CekControl::Pause` | **New** | Add during migration. |
| (R27) Evaluator checkpoint/restore | **Out of scope for W7** | Evaluator side; W7 is parser-only. |
| (R28) Source map | **Partial** | Spans tracked at parse time but not packaged as `(file, line, column)` table. Out of scope for W7 unless trivial. |
| (R29) Session identity | **Implemented** | One `GreenThread` = one session via `green_thread.rs`. |
| (R30) `Theory::rho_evaluate` | **Out of scope for W7** | Evaluator side. |
| (R31) Affordances exposed for future implementation | **Migration mandate** | W7 must expose at least: reactive `process_event`, `WpdsIncrementalSession`, `WalkerConsumer`. |

### 2.3. External consumer audit

Confirmed by Explore agent during pre-Stage-0 investigation:

| Component | Production consumers | Test-only consumers |
|---|---|---|
| `CekObserver` (parser) | **0** | `TracingObserver`, `NullObserver` (in `cek.rs` tests) |
| `parse_<Cat>_traced` codegen | **0** | None |
| `IncrementalSession` | **0** | 4 unit tests in `cek.rs` |
| `EvalObserver` (evaluator) | **1** (REPL via `NullEvalObserver`) | `TracingEvalObserver`, `AbortAfterObserver` |
| `CekEvaluator::run_to_completion` | **1** (REPL) | many |
| `process_event` (any) | **0 on parser**; scheduler/pool_fsm have it | scheduler has tests |

The picture: the parser-side reactive contract is ENTIRELY aspirational
infrastructure. The evaluator-side observer trait is real (REPL uses it) but
also primarily through the null-observer convenience path. Neither parser nor
evaluator has a live external consumer driving the reactive FSM.

### 2.4. WPDS infrastructure today

`prattail/src/wpds.rs` (4,008 lines) provides:

- `StackSymbol` (current; will become `StackSymbolV2` in Stage 1)
- `Wpds<W>`, `WpdsRule<W>`, `PAutomaton<W>`
- `build_wpds`, `poststar`, `prestar`, `stringsum`
- Tropical and Boolean weight types

Used today **only for offline analysis** — never as a runtime parser. The
migration's task is to lift this from analysis machinery to live execution.

### 2.5. Aspirational features in `gss.rs`

The header comment references:
- `gll-parsing` feature — does not exist in `Cargo.toml`
- `reactive-cek` feature — does not exist in `Cargo.toml`

The `Cargo.toml` only defines one feature: `ascent-parallel`, currently
broken. So the GSS skeleton is staged for activation once a `reactive-cek`
substrate exists. **Stage 3 of the migration will activate it without the
feature gate** (per the "no feature gating" mandate from plan v5).

---

## 3. Gap Classification

This is the load-bearing output of Stage 0. Every gap below is addressed by
a specific migration stage.

### 3.1. Gap class A: Inverted layering (most critical)

The original mandate is:

```
CONSUMER → process_event(event) → reactive FSM → optional observer callback
```

The implementation is:

```
CONSUMER → run_to_completion() → trampoline loop → optional traced variant → unused observer
```

**Migration response**: Stage 4 (`WpdsWalker::process_event`) restores
reactive driver as primary; Stage 5 (`WalkerConsumer`) makes the observer
secondary; Stage 10 deletes `parse_<Cat>_traced`.

### 3.2. Gap class B: Missing methods promised in docs

- `IncrementalSession::reparse(edit, tokens)` — documented in §1.3, §1.4;
  missing in `cek.rs`. Stage 5 implements `WpdsIncrementalSession::reparse`.
- `CekMachine::process_event` — documented in §1.1, §1.5; not present on any
  parser type today. Stage 4 implements `WpdsWalker::process_event`.
- `CekMachine::run_to_checkpoint` — documented in §1.2; not present.
  Stage 4/5 implements (likely as `process_event` loop with checkpoint break).
- `CekControl::Pause` — promised by Rholang §13.1; not in current enum.
  Stage 1 adds.

### 3.3. Gap class C: Unused codegen artifacts

- `parse_<Cat>_traced` functions — generated for every category, called by
  no one. Stage 10 removes from emission.
- `CekState`/`CekEvent`/`CekTransition` enums in parser-side `cek.rs` — types
  defined; never instantiated. Stage 1 introduces `WpdsState`/`WpdsEvent`/
  `WpdsTransition`; Stage 10 deletes parser-side `cek.rs` analogues.

### 3.4. Gap class D: WPDS substrate not lifted to runtime

- `Wpds<W>` exists for offline analysis. No runtime parser consumes it.
- `PAutomaton<W>::poststar` not in any hot path.
- `LexicographicWeight` does not exist; current parser uses ad-hoc tiebreaks
  (declaration order, source-cat order, longest-match) scattered across
  `dispatch.rs` and `trampoline.rs`. Stage 2 introduces single semiring.

### 3.5. Gap class E: GSS staged but not active

- `gss.rs` skeleton (406 lines) compiles but has no callers.
- References two aspirational features (`gll-parsing`, `reactive-cek`).
- Stage 3 activates GSS as the WPDS branch-sharing substrate.

### 3.6. Gap class F: Display under ambiguity unspecified

- Current `Ambiguous(alts) => write!(f, "{}", alts[0])` in
  `macros/src/gen/runtime/language.rs:685` silently picks lex-best.
- No diagnostic emitted.
- Stage 7 implements Display Option D: emit `[LANG-D11]` warning,
  canonicalize to lex-best primary.

### 3.7. Gap class G: Parity testing absent

- No test suite proves new parser produces same AST as old parser.
- Stage 8 builds Model A (dual codegen) and Model B (postcard golden ASTs).

### 3.8. Gap class H: Test coverage of ambiguity-prone paths thin

- No systematic tests for cross-cat ambiguity, Pratt BP boundaries, binder
  shadowing under ambiguity, recovery corruption, ambiguity-exposure
  diagnostics, or parity replay.
- Stage 9 adds 6 new test_gen modules (≥10 tests each, 60+ new tests).

---

## 4. Migration Mandates (Derived from Survey)

Stages 1–11 must satisfy ALL of:

| Mandate | Source | Stage |
|---|---|---|
| M1: Reactive `process_event` is primary external API | (R1)–(R5), (R24) | 4 |
| M2: Observer trait is secondary side-effect callback | (R21)–(R23) | 5 |
| M3: `NullConsumer` monomorphizes to zero-cost | (R23) | 5 |
| M4: `WpdsIncrementalSession` provides LSP affordances | (R8)–(R14) | 5 |
| M5: `process_event` returns `WpdsTransition` | (R3) | 1, 4 |
| M6: `WpdsControl::Pause` exists | (R26) | 1 |
| M7: Five-state machine: Ready/PrefixDispatch/InfixLoop/Unwinding/Accepted/Error + AmbiguityFanout/Saturating extensions for WPDS | (R17) | 1 |
| M8: GSS active substrate for ambiguity branching | aspirational `gll-parsing` | 3 |
| M9: `LexicographicWeight` unifies all tiebreak ordering | (gap D) | 2 |
| M10: Display Option D emits `D11` diagnostic | (gap F) | 7 |
| M11: Parity verified via dual codegen + postcard goldens | (gap G) | 8 |
| M12: ≥60 new ambiguity-prone tests across 6 modules | (gap H) | 9 |
| M13: Old parser CEK deleted; evaluator CEK untouched | plan v5 | 10 |
| M14: New `wpds-reactive.md` mirrors `reactive-state-machine.md` | (R1)–(R5) | 11 |

---

## 4A. 📌 Prominent long-term note — recovery as WPDS edges

Stage 6's recovery integration (Decision #3 of the Stage 6 implementation
plan v2) wires recovery at the **wrapper level**: `parse_<Cat>_via_wpds`
calls `mettail_prattail::recovery::find_best_recovery` (the existing
WFST-based min-cost repair) when the walker terminates in
`WpdsState::Error`. The walker itself has no recovery branching.

**Long-term ideal:** recovery should be encoded as alternate WPDS edges —
Skip/Delete/Substitute/Insert rules weighted so `LexicographicWeight`
lex-min selects them only when no primary rule matches. That makes
recovery a first-class WPDS feature; the wrapper plumbing is deleted once
it lands.

This note is replicated in:
- `prattail/src/wpds_runtime.rs` module doc comment
- `prattail/docs/design/wpds-stage-10-audit.md` as "post-Stage-10 follow-up"
- (Future) `wpds_codegen/mod.rs` module doc comment once the sub-tree
  refactor lands (Stage 6 Phase A.1)

Tracking: no ticket yet; opened as follow-up when Stage 10's deletion
completes and the recovery-as-WPDS-edges prototype can be scheduled.

---

## 5. Out of Scope

The following are confirmed out of scope for W7 (and tracked elsewhere):

- **W1**: Multi-stratum Ascent split (separate task #12).
- **W5**: Map-test verification post-W1+W2 (separate task #5).
- **W6**: Final workspace build + REPL smoke + merge commit (separate task #6).
- **W4c**: Bool display idempotence (task #14, parked, will be subsumed by Stage 7).
- **Evaluator CEK**: All of `cek_eval.rs` (R27, R30) — preserved verbatim.
- **Source map** (R28): Spans already tracked; full `(file, line, column)`
  table not required for W7. Stage 11 docs note this as future work.
- **DAP/LSP/nREPL servers themselves** (R31): W7 exposes affordances; servers
  are separate work tracks.

---

## 6. Risks and Mitigations Surfaced by Survey

| Risk | Source | Mitigation |
|---|---|---|
| Reactive granularity wrong → consumer can't pace at preferred rate | (R6), (R18) | Stage 4 spec: "single token = one Step event" guarantee + DAP/LSP example tests in Stage 9 |
| `is_convergent` semantics drift from CEK definition | (R10) | Stage 5: keep current `cek.rs:is_convergent` definition; port verbatim |
| Display canonicalization breaks roundtrip tests | (gap F) | Stage 7: D11 warning + roundtrip tests assert primary stable |
| Codegen format split (debug/release) creates two code paths | (M11) | Stage 6/8: parity test verifies same parse output across both formats |
| WPDS poststar saturation is too coarse for incremental reparse | (R7), (R8) | Stage 5: incremental session uses checkpoint-resume, not full poststar; only reparse region drives WPDS |
| GSS activation introduces nondeterminism in test outputs | (gap E) | Stage 3: GSS yields are sorted by `LexicographicWeight` for deterministic enumeration |
| `LexicographicWeight` left-projection times semantics unclear | (gap D) | Stage 2 deliverable: design doc + comparison vs full-product times |
| Postcard format drift across rustc versions breaks goldens | (M11) | Stage 8: pin postcard schema via `#[derive]` lock; provide regenerate script |

---

## 7. Stage 0 Sign-Off Checklist

- [x] All 7 reactive design docs read verbatim
- [x] All 31 binding contracts (R1–R31) classified
- [x] All 8 gap classes (A–H) identified and mapped to stages
- [x] All 14 mandates (M1–M14) traced to source
- [x] Out-of-scope items confirmed
- [x] Risks surfaced and pre-mitigations specified
- [x] postcard already in `prattail/Cargo.toml` (1.x with `alloc` feature)
- [x] No `reactive-cek` or `gll-parsing` feature gates needed (per plan v5 mandate)

**Stage 0 complete. Stages 1–11 are unblocked.**
