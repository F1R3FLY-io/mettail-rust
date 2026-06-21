# Dead-Code Disposition — `prattail` speculative modules

**Date:** 2026-06-21 · **Scope:** production-readiness campaign, Phase 2 · **Branch:** `feature/wfst-architecture`

This note records the disposition of three large `prattail/src` modules that a metric
sweep flagged as possibly-dead, the **evidence** that decided each one, and how to
reverse the decision. It exists so the call can be reconstructed (and re-audited)
without re-deriving the analysis.

## Summary

| Module | Lines | Verdict | Action |
|········|······:|·········|········|
| `prattail/src/presburger.rs` | 2,807 | **LIVE** | none — untouched |
| `prattail/src/cek.rs` | 1,301 | apparently-dead (orphaned codegen target) | parked behind `cek-runtime` (off by default) |
| `prattail/src/channel.rs` | 1,802 | apparently-dead (uncalled consumer) | parked behind `green-threads` (off by default) |

## Evidence

### `presburger.rs` — LIVE (do not touch)
Earlier reconnaissance mis-flagged this as "near-dead (only a bench)". Direct grep refuted that:
- `pipeline.rs:1834` and `pipeline.rs:2194` call `crate::presburger::analyze_from_bundle(...)` on the live pipeline path; the result is stored at `pipeline.rs:1587` (`PipelineState::presburger_result`).
- Consumed downstream by `lint.rs:510` / `lint.rs:9672` and `cost_benefit.rs` (`Optimization::PresburgerAnalysis`).
- Backed by a dedicated zero-admission proof: `formal/rocq/presburger/` (Makefile target `rocq-presburger`).

⇒ Removing or gating it would break the math-analysis pipeline. **No change.**

### `cek.rs` — orphaned codegen target → parked behind `cek-runtime`
A reactive CEK-machine view of the trampoline parser (suspend/step/checkpoint for DAP/LSP/REPL).
- No hand-written caller: the only `mettail_prattail::cek::*` references in `src/` are **doc-comments** (`railroad.rs:260,489` document a *decoupling* from it).
- The traced-parser codegen that once emitted `cek::*` into generated parsers
  (`write_trampolined_parser_traced` / `emit_observer_call` / `TracingMode::Traced`, in a
  `recursive.rs` that no longer exists) has been **removed**; those identifiers return zero
  hits at this commit. A stale March-2026 agent transcript under `docs/design/exploring/`
  still shows the old emission and is the source of the "cek is a live codegen target" claim —
  it is out of date.

### `channel.rs` — uncalled consumer → parked behind `green-threads`
Green-thread (concurrent-parsing) infrastructure: lock-free MPMC channels (`crossbeam_channel`),
`DashMap` channel maps, join patterns — modeled **by analogy** on Rholang pi-calculus channel
semantics (it does *not* use the F1r3node Rho machine; the parser is single-threaded per parse session).
- Sole consumer is `pipeline::analyze_green_thread_safety` (`pipeline.rs:5237`), whose only caller in
  turn is … nothing: grep finds the definition + a doc-comment and no invocation.
- The `GT01–GT06` cost-model labels survive in `cost_benefit.rs` (`Optimization::GreenThreadForkJoin`)
  as **diagnostic-only** status; the analysis that would populate them is the uncalled function above.

> **Layer note (a common conflation):** "green threads" here are a *parse-time* concurrency
> experiment, orthogonal to the *runtime/rewrite-execution* backend (CESK → Dovetail report +
> F1r3node Rho machine). The backend replacement neither used nor retired them; they were simply
> never wired into the live parser.

## Mechanism (reversible, non-destructive — code is NOT deleted)

`prattail/Cargo.toml`:
```toml
cek-runtime  = []
green-threads = ["cek-runtime", "dep:dashmap", "dep:crossbeam-channel", "dep:crossbeam-deque", "dep:num_cpus"]
```
The four deps `dashmap`, `crossbeam-channel`, `crossbeam-deque`, `num_cpus` were made `optional`
(they are used **only** by cek/channel; `crossbeam-deque` is currently unreferenced). `im` stays
non-optional — it is used by the live walker (`cursor_store`, `wpda_walker`, `cohort_lazy`, `tomita_frontier`).

`prattail/src/lib.rs`: `#[cfg(feature = "cek-runtime")] pub mod cek;` and
`#[cfg(feature = "green-threads")] pub mod channel;` (with an inline rationale banner).
`pipeline.rs`: `GreenThreadAnalysis` + `analyze_green_thread_safety` gated under `green-threads`.

## Verification (this commit)

| Check | Result |
|·······|········|
| `cargo build --workspace` (default) | ✅ exit 0 — no downstream consumer referenced the gated items |
| `cargo build -p prattail --features green-threads` | ✅ exit 0 — parked code still compiles |
| `cargo nextest run -p prattail` (default) | ✅ **3725 passed, 0 failed** |
| `cargo nextest run -p prattail --features green-threads` | ✅ **3795 passed, 0 failed** (= 3725 + cek 26 + channel 44) |

The exact `+70` delta proves the only tests removed from the default build were the cek/channel
in-module tests, that they still pass under the feature, and that nothing else moved.

## To re-enable or remove
- **Re-enable:** build/test with `--features green-threads` (pulls in `cek-runtime` transitively).
- **Physically remove** `cek.rs`/`channel.rs` (and their deps): a separate, **explicitly approved**
  step — not done here, per the project's comment-out/gate-don't-delete rule.

CI guards this with a `cargo check -p prattail --features green-threads` feature-rot job (added in the
campaign's CI-finalization phase).
