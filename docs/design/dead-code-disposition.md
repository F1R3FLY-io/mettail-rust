# Dead-Code Disposition — `prattail` speculative modules

**Original:** 2026-06-21 (production-readiness Phase 2) · **Updated:** 2026-06-22 · **Branch:** `feature/wfst-architecture`

This note records the disposition of three large `prattail/src` modules that a metric
sweep flagged as possibly-dead, and the **evidence** that decided each. It exists so the
call can be reconstructed (and re-audited) without re-deriving the analysis.

## Summary

| Module | Lines | Verdict | Action |
|--------|------:|---------|--------|
| `prattail/src/presburger.rs` | 2,807 | **LIVE** | none — untouched |
| `prattail/src/cek.rs` | 1,301 | dead (orphaned codegen target) | **physically removed 2026-06-22** |
| `prattail/src/channel.rs` | 1,802 | dead (uncalled consumer) | **physically removed 2026-06-22** |

## Evidence

### `presburger.rs` — LIVE (do not touch)
Earlier reconnaissance mis-flagged this as "near-dead (only a bench)". Direct grep refuted that:
- `pipeline.rs:1834` and `pipeline.rs:2194` call `crate::presburger::analyze_from_bundle(...)` on the live pipeline path; the result is stored at `pipeline.rs:1587` (`PipelineState::presburger_result`).
- Consumed downstream by `lint.rs:510` / `lint.rs:9672` and `cost_benefit.rs` (`Optimization::PresburgerAnalysis`).
- Backed by a dedicated zero-admission proof: `formal/rocq/presburger/` (Makefile target `rocq-presburger`).

⇒ Removing or gating it would break the math-analysis pipeline. **No change.**

### `cek.rs` / `channel.rs` — physically removed (2026-06-22)
Both were first **parked** behind off-by-default features (`cek-runtime` / `green-threads`) in the
production-readiness pass (2026-06-21), then **physically removed** on 2026-06-22 by explicit request
(the project's gate-don't-delete default is overridden by an explicit deletion request).

- `cek.rs` was a reactive CEK-machine view of the trampoline parser (suspend/step/checkpoint), an
  **orphaned codegen target**: the traced-parser codegen that once emitted `cek::*` had already been
  removed, leaving only doc-comments. It is **superseded** by the live WPDA recognizer — which *is* the
  parsing CEK machine structurally (see `prattail/docs/architecture/cek-machine.md`,
  `wpds-cek-bijection.md`).
- `channel.rs` was a **parse-time** green-thread / channel concurrency experiment (orthogonal to the
  runtime rewrite backend), whose sole consumer `pipeline::analyze_green_thread_safety` was itself
  uncalled. The runtime-parse work measured that parallelizing the parser is Amdahl-bounded and not
  worth pursuing.

Removed together with these now-orphaned satellites:
- the `cek-runtime` / `green-threads` Cargo features + their 4 optional deps (`dashmap`,
  `crossbeam-channel`, `crossbeam-deque`, `num_cpus`);
- the uncalled `GreenThreadAnalysis` + `analyze_green_thread_safety` (`pipeline/state.rs`);
- the orphaned `GT01–GT06` lints (`lint/lints.rs`) + their `DiagnosticId` variants
  (`lint/diagnostic.rs`) + the `cost_benefit` `GreenThreadForkJoin` (GT01) optimization;
- the parked-feature CI rot-check (`.github/workflows/ci.yml`);
- the 13 green-thread design docs + 7 orphaned CESK-**evaluator** docs (the CESK *evaluator* was
  deleted in P6; these documented it).
- `control.rs` (`CekControl`) — a 32-line vestige whose only consumer was `cek.rs` (it served the
  P6-deleted `cek_eval.rs`).

**Retained** (live, not the deleted code): the parser-CEK-isomorphism recognizer
(`wpda_walker`/`wpds.rs`, `CekWpdsBijection`, `WpdaControl`) and its docs — the recognizer, not the
evaluator; and the grammar-level `channels {}` guard DSL (`mettail_runtime::ChannelDef`), which is
unrelated to the deleted parse-time `channel.rs`.
