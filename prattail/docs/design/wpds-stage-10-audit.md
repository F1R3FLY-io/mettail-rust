# W7 Stage 10 Audit: Old CEK Parser Deletion (deferred)

This document is the deliverable of W7 Stage 10 of plan v5.1. Stage 10
mandates deleting the legacy CEK parser-side types (`CekState`, `CekEvent`,
`CekTransition`, `CekObserver`, `TracingObserver`, `NullObserver`,
`IncrementalSession`, `parse_<Cat>_traced` codegen). The actual deletion
is **deferred** because the user's "no feature loss" mandate requires
Stage 6 codegen to reach feature parity with the existing trampoline
parser before deletion is safe.

This audit documents:

1. The current usage map of the items targeted for deletion.
2. The cleanly-deletable subset (none today; all items have live consumers).
3. The Stage 6 milestones that unblock Stage 10.
4. The deletion procedure once unblocked.

---

## 1. Current usage map

| Item | Defined in | Used by |
|---|---|---|
| `CekState` (parser) | `prattail/src/cek.rs` | `trampoline.rs`, `railroad.rs`, `cek_eval.rs` (re-uses some variants), `cost_benefit.rs` |
| `CekEvent` | `prattail/src/cek.rs` | `trampoline.rs`, `cek_eval.rs`, `cost_benefit.rs` |
| `CekTransition` | `prattail/src/cek.rs` | `trampoline.rs`, `railroad.rs`, `cek_eval.rs` |
| `CekControl` | `prattail/src/cek.rs` | `cek.rs::tests`, `cek_eval.rs` (evaluator side; KEEP), `trampoline.rs`, `runtime/src/lib.rs` |
| `CekObserver` (trait) | `prattail/src/cek.rs` | `trampoline.rs` (codegen target for `parse_<Cat>_traced`), `cek.rs::tests` |
| `TracingObserver` | `prattail/src/cek.rs` | `cek.rs::tests` only |
| `NullObserver` | `prattail/src/cek.rs` | `cek.rs::tests` only |
| `IncrementalSession` | `prattail/src/cek.rs` | `cek.rs::tests` only |
| `parse_<Cat>_traced` | macros codegen → `target/generated/<lang>/parser.rs` | None outside generated code itself |

## 2. Cleanly-deletable subset (today)

**None.** Every item in the table above has at least one consumer outside
its own test module:

- `CekObserver` is the trait the codegen-emitted `parse_<Cat>_traced`
  functions are generic over. Even though no external code calls those
  generated traced parsers, removing the trait would force the codegen
  to also drop the traced parser emission, which is itself wired into
  the macro pipeline.
- `TracingObserver`, `NullObserver`, `IncrementalSession` appear
  test-only at the API level, but they exercise the public surface that
  has been promised for LSP/DAP/REPL integration in
  `prattail/docs/usage/evaluation-consumers-guide.md`. Until the
  WPDS-runtime equivalents (`TracingConsumer`, `NullConsumer`,
  `WpdsIncrementalSession` — all landed in W7 Stage 5) replace them in
  the documented public API, deleting them would be a documented
  feature loss.
- `CekState`/`CekEvent`/`CekTransition` are still hot-path types in
  the trampoline parser.

## 3. Stage 6 milestones that unblock Stage 10

Stage 10 unblocks when **all** of the following land:

- **Stage 6.1** — WPDS engine emits per-rule `Push`/`Replace`/`Pop`
  actions for every grammar rule in every shipped language (Calculator,
  RhoCalc, Lambda, Ambient, LedTest, BaseMath, ExtMath, MixedMath,
  ImportedMath, RhoCalc-casting, Calculator-casting).
- **Stage 6.2** — Parity tests (W7 Stage 8 Model A) confirm WPDS
  output matches trampoline output across the full
  `languages/tests/` corpus.
- **Stage 6.3** — `runtime/src/lib.rs` re-exports
  `mettail_prattail::wpds_runtime::WpdsControl` instead of
  `mettail_prattail::cek::CekControl`.
- **Stage 6.4** — `cek_eval.rs` migrates from the parser-side
  `CekControl` to the WPDS-runtime `WpdsControl` (or both unify on a
  shared `Control` type).
- **Stage 6.5** — `railroad.rs` migrates from `CekTraceEntry` to
  `WpdsTraceEntry`.
- **Stage 6.6** — `cost_benefit.rs` references to parser-CEK types
  switch to WPDS-runtime equivalents.

## 4. Deletion procedure once unblocked

When Stage 6.1–6.6 are all green:

```bash
# 1. Remove parser-side items from cek.rs (keep evaluator items used by cek_eval.rs)
$EDITOR prattail/src/cek.rs   # delete: CekState, CekEvent, CekTransition,
                              # CekControl (only if cek_eval migrates first),
                              # CekObserver, TracingObserver, NullObserver,
                              # IncrementalSession, all *_traced helpers

# 2. Remove parse_*_traced emission from macros codegen
$EDITOR macros/src/gen/runtime/language.rs   # delete the traced emission block

# 3. Drop the *_traced functions from the generated parser
cargo clean -p languages
cargo build -p languages              # regenerates parser.rs without traced

# 4. Delete the dead documentation references
rm prattail/docs/usage/reactive-cek-guide.md
rm prattail/docs/usage/incremental-parsing-guide.md   # superseded by wpds-incremental-parsing.md
$EDITOR prattail/docs/usage/evaluation-consumers-guide.md   # rewrite §1 to use WPDS

# 5. Verify
cargo test --workspace
```

Until the milestones land, the items remain in `cek.rs` with
`#[deprecated]` annotations would be appropriate — but per plan v5.1's
"no feature gating, no shadow mode" mandate, we deliberately do not add
deprecation markers because there is no replacement for users to migrate
to yet (the WPDS engine is not feature-complete).

## 5. Tracking

- Follow-up task: see #30 (open) — "W7 Stage 10 deferred deletion".
- Survey contract: M13 ("delete old CEK parser; keep evaluator").
- Memory note: `wpds-migration.md` records Stage 10 as "audit complete,
  deletion deferred pending Stage 6 feature parity."

## 6. 📌 Post-Stage-10 follow-up — recovery as WPDS edges

After Stage 10 removes the trampoline emission, a separate follow-up track
should migrate recovery from the wrapper-level
`mettail_prattail::recovery::find_best_recovery` invocation (which Stage 6
Phase A.1 wires into `parse_<Cat>_via_wpds`) into **native WPDS edges**.

Proposed mechanism:
- Every `PrefixDispatch` arm in the emitted engine returns
  `WpdsStepAction::Fork` with a primary expected branch plus recovery
  branches (Skip/Delete/Substitute/Insert) weighted with
  `LexicographicWeight` at high-cost primary values.
- Lex-min then selects recovery only if the expected branch's parse fails
  entirely (primary cost = `inf` via `TropicalWeight::infinity`).
- The wrapper's `apply_recovery_and_continue` plumbing is deleted; the
  walker handles recovery natively.

This is **post-Stage-10 work** — it requires the trampoline to be gone
(so recovery.rs's current wrapper use doesn't constrain the design) and
the WPDS walker to be the sole parser. Tracking opens when Stage 10
completes.

Cross-references:
- `prattail/src/wpds_runtime.rs` module doc (the prominent note)
- `prattail/docs/design/wpds-migration-survey.md` §4A
