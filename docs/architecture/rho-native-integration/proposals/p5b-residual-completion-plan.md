# P5b Residual Completion Plan (survey + design)

Status: working plan. Produced by a code-grounded survey (2026-06-16) after CAMP-0
verified the M-RHO bridge green against the now-building f1r3node-rust. The four P5b
target languages are **Calculator, RhoCalc, Ambient, GuardedRho** (MiniRho is a doc
example, not a generated language; lambda/led_test/class2*/optsmoke are not Rho-flip
targets).

## Per-language completion state (vs doc-08 12-step checklist)

- **Calculator** — COMPLETE. Scalar lowering + native-fold dispositions; executes on
  RhoRuntime (`lowered_calculator_{int,bool,string}_ops_compute_correctly_on_rho_runtime`);
  differential vs Ascent (`rho_vs_ascent.rs:86`).
- **RhoCalc** — COMPLETE. Host COMM lowering (`rhocalc_ast.rs`); executes parsed
  processes as AST calls (`rho_rhocalc_ast.rs`, 17 tests); COMM oracle (`rho_comm_oracle`, 8).
- **Ambient** — COMPLETE (in-engine). Flips to `RuntimeBackend::Dovetail` (host-less AC),
  Complete reports (`ambient_dovetail_flip.rs`).
- **GuardedRho** — plans end-to-end through the guard-quality gate
  (`guarded_rho_rho_backend.rs`, 2 tests, all qualities non-`Unknown`); guards execute on
  host RSpace via `rho_guard_oracle.rs` (4 tests). **Open item: B1** (below).

## Genuine residual (ordered)

- **B1 — GuardedRho completion bar.** Either (B1-A) build a generated-AST install+execute
  path (`mettail-rho-runtime/src/guarded_rho_ast.rs`, mirroring `rhocalc_ast.rs`; lower
  `PGuardedInput`→`Receive` with the `?guard` predicate as a `where`/pattern body) and an
  install helper + an end-to-end `run_default_backend_report` test; or (B1-B) declare the
  flip "planned + host-routed, execution-proven via `rho_guard_oracle`" (the `RhoNativeJoin`
  disposition's defining evidence per doc-08). **Risk:** GuardedRho's guards call external
  relations (`halts`/`safe`) populated by user code — undecidable in-engine (hence
  `RejectSafeApprox`). The channel/join legs are AST-first-able; the external-relation leg
  may need a host relation provider, and if it cannot be executed AST-first it is a
  documented `RejectSafeApprox` boundary (a plan-defined skip on that leg only).
- **B2 — MiniRho/stale-note doc reconciliation** (decision-free, done first):
  remove/relabel the `◐ MiniRho` row (not a generated language) and the now-false
  `@1!(Nil)` OOS note (that term parses + passes today) in
  `07-verification-and-rollout.md`.
- **B3 — Coverage-matrix reconciliation.** Fold the B1 outcome into the doc-07 per-language
  table and add a per-language flip-status line to `prattail/docs/theory/formal-verification/coverage-matrix.md`
  (the "updated together" doc gate). `references.md#coverage-matrix` only points to the
  prattail file — no separate grid.
- **B4 — (optional) Calculator differential honesty.** Point `rho_vs_ascent.rs`'s Rho side
  at the reconstructed real `CalculatorLanguage` plan (it already lowers a synthetic
  `CALC_RUN_FRAGMENT`; the Ascent side already uses the real def).

## Plan-defined skips (gates working as designed — do NOT chase)

- **C1** Ambient flips to Dovetail, not RhoMachine (in-engine, host-less, by the discharge rule).
- **C2 (load-bearing)** No differential-vs-Ascent for RhoCalc/Ambient/GuardedRho — Ascent is
  an INVALID oracle for them: capture-unsound on Ambient binders (proven,
  `ambient_binder_handler.rs`), and no model for host COMM or external guard relations. The
  COMM oracle (RhoCalc) and guard oracle (GuardedRho) ARE the correct differentials; step-9
  "differential-vs-Ascent" is a Calculator-specific scalar-fold gate.
- **C3** `castbigrat` (RhoCalc) is a pre-existing big-rational cast smoke residual, not a
  flip blocker; `@1!(Nil)` (GuardedRho) actually passes now (stale note).
- **C4** `rho_guard_oracle` being `source-oracle`-gated is the sanctioned guard-regression
  oracle (doc-08 source boundary), not a stub.

## P6 (retire Ascent/CESK) — gating + inventory

Separately-confirmed destructive step, gated on all in-scope flips landing (met under B1-B;
met under B1-A once the GuardedRho wrapper lands). Removes: the `oracle-ascent` feature +
gated targets/structs/`ascent_source!`/`eqrel`; the `legacy-cesk-runtime` feature +
prattail/testkit CESK modules. Retains the WPDA-side CEK/observer parser modules and the
differential harness while any language still uses it (Calculator). Nothing removed without
explicit user approval; git history is the archive.

## Risks

- **R-patch** — the build depends on the temporary `rholang_parser` `[patch]` to the
  cost-accounting worktree (`Cargo.toml`, held local). B1-A's `Receive`/`where` lowering
  inherits that WIP `rholang` `Par`/`ReceiveBind` surface; pin construction to `rhoapi`
  types (as `rhocalc_ast.rs` does) and re-run CAMP-0 after B1. Remove the patch once
  cost-accounting merges to rholang-rs master.
- **R-Ascent-oracle-invalidity** — see C2; do not build Ambient/RhoCalc/GuardedRho-vs-Ascent
  oracles.
- **R-doc-status-overclaim** — declaring P5b complete requires B2/B3 in the same pass, else
  the matrix claims both "complete" and "in rollout."
