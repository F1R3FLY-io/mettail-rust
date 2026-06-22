# P5b Residual Completion Plan (survey + design)

> **Status (reconciled post-P6):** executed. All four P5b target languages were
> flipped (Calculator, RhoCalc, Ambient, GuardedRho), and P6 then retired the
> Ascent/CESK paths. Two artifacts this 2026-06-16 survey references as live were
> subsequently removed in P6 and now read as historical: the `rho_vs_ascent.rs`
> differential test (deleted with the `oracle-ascent` feature, `c9cea652`) and the
> temporary `rholang_parser` `[patch]` under **R-patch** (resolved). Retained as
> the survey-of-record.

Original survey status (2026-06-16): working plan. Produced by a code-grounded survey
after CAMP-0 verified the M-RHO bridge green against the now-building f1r3node-rust. The four P5b
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

- **B1 — GuardedRho completion bar. RESOLVED (2026-06-16): host-routed is derived-correct;
  a sound generated-AST guarded-receive lowering is impossible.** The resolution is a
  derivation, not a preference:
  - `rhoapi::ReceiveBind` has EXACTLY `{patterns, source, remainder, free_count}` — no guard
    field (proven by the struct literal at `rholang-runtime/src/rhocalc_ast.rs:413-418`,
    which specifies all fields with no `..default`). RSpace matching is purely structural.
  - GuardedRho's `?guard` is a `BehavioralPred::RelationQuery` over the **external relations**
    `halts`/`safe`, "populated by user code" (`languages/src/guarded_rho.rs:33-34,92-95`).
    These are not Rholang-computable and not structural patterns, so they cannot be encoded in
    a `ReceiveBind` pattern, nor evaluated in a desugared `Par` body.
  - Therefore lowering `PGuardedInput` to a plain `rhoapi` `Receive` would have to DROP the
    guard `⇒` consume-on-false `⇒` semantically UNSOUND (a guarded receive that ignores its
    guard). That is exactly the "hack/pragmatic decision" the mandate forbids.
  - Hence the guarded receive is *semantically* a host-routed `RhoNativeJoin` / external-relation
    disposition — which the guard-quality seam already classifies (`RejectSafeApprox`,
    `guard_quality.rs`) and which `rho_guard_oracle` executes on the real host RSpace
    (non-consuming-on-failed-guard semantics, 4 tests). Per doc-08:386-388 the host RSpace
    mechanism IS the `RhoNativeJoin` disposition's defining evidence.
  - **Completion:** GuardedRho's flip is COMPLETE — it plans end-to-end through the gate
    (`guarded_rho_rho_backend.rs`, all qualities non-`Unknown`) and its guarded-receive
    semantics execute on the host RSpace (`rho_guard_oracle`). The behavioral guard being
    host-routed is a gate working as designed, not a deferral. Doc-07 cell `→` ✅ host-routed.
  - (A generated-AST wrapper could lower GuardedRho's *guard-free* structural fragment
    — `POutput`/`PPar`/`NQuote`/`PDrop`/`CastInt` — like RhoCalc, but that fragment excludes
    the language's defining `PGuardedInput`, so it adds no real coverage. Not built.)
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
