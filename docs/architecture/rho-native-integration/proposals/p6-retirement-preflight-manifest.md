# P6 — Retire Ascent/CESK: pre-flight manifest (REQUIRES EXPLICIT APPROVAL)

Status: **EXECUTED** (P6-full, approved) — Stage 1 `9d889894`, Stage 2 `c9cea652`, CESK `0a93ee39`; `rho_vs_ascent.rs`, `rho_language_backend_report.rs`, and the `oracle-ascent` feature were removed. Retained as the decision record; the original staging note follows. P6 is a destructive step (it deletes code from the
live tree). Per the campaign plan (R7) and the standing "no destructive actions without
explicit approval" rule, **nothing below is removed until you approve it**. Git history is
the archive. P5b is complete (all four target languages flipped + verified, CAMP-0 green),
which is P6's gating precondition.

## What P6 removes (the legacy production runtime backends being replaced)

These are already *fenced behind features and fail-closed by default* (proven by
`RuntimeBackendDispatch.v`); P6 deletes the fenced code itself. Verified surfaces:

| Surface | Location | Notes |
|---|---|---|
| `oracle-ascent` feature + deps (`ascent`, `ascent-byods-rels`, `hashbrown`, `rustc-hash`) | `languages/Cargo.toml:46-51`; `ascent-parallel` `:54` (already broken upstream) | the Ascent reference/oracle build surface |
| generated Ascent code | `macros/src/gen/**` (`ascent_source!`, `eqrel`, generated `run_ascent*` impls, dual-indexed BYODS relation provider) — part of the **72** `ascent_source!`/`eqrel`/`run_ascent`/CESK matches in `macros/src`+`prattail/src`+`testkit/src` | generated only under `oracle-ascent` |
| `legacy-cesk-runtime` feature + CESK modules | `prattail/Cargo.toml:48`; the `cek_eval`/`cesk_store`/`gc`/`abstract_cesk`/`green_thread`/`scheduler`/`global_pool`/`pool_fsm`/`worker_pool`/`coordinator` cluster; gated targets `prattail/Cargo.toml:158,163` | the CESK runtime backend being replaced by the Rho machine |
| `testkit` CESK/green-thread analytical modules | `testkit/Cargo.toml:11` re-export + gated modules | behind `testkit/legacy-cesk-runtime` |

## What P6 RETAINS (not the legacy runtime)

- **WPDA-side CEK/observer parser modules** — the active parser/recognizer is not the
  legacy runtime backend (plan + doc-07:716-721). Keep.
- **The Dovetail/Rho production path** (the replacement) — untouched.

## DECISION REQUIRED — the differential-oracle (`rho_vs_ascent`)

`rho_vs_ascent` (Calculator's differential, just hardened in P5b/B4 to run real-vs-real)
**depends on `oracle-ascent`** — it runs `CalculatorLanguage::run_ascent` as the reference.
So does `rho_language_backend_report` (oracle-ascent-gated). Removing the Ascent reference
breaks them. The plan says: *"Retain the differential-oracle harness only as long as the
coverage matrix shows a language still using it for rollout evidence."* Calculator still
uses it. Two options:

- **(P6-keep-oracle)** Remove the legacy Ascent/CESK **production** path + the CESK runtime,
  but **retain `oracle-ascent`** as the reference/oracle surface (it is already non-production,
  fail-closed). `rho_vs_ascent`/`rho_language_backend_report` keep running. Smallest, safest.
- **(P6-full)** Also retire `oracle-ascent` entirely (delete `rho_vs_ascent`, the Ascent
  reference, all 72 surfaces). Calculator then loses its Ascent differential — but its flip
  is otherwise proven by the end-to-end RhoRuntime tests + `OracleQuotientEquivalence.v`
  (the exactness proof) + the COMM/guard oracles. Fully removes Ascent from the tree.

## Pre-flight + post-removal gates (run on the approved scope)

1. Pre-flight: re-list the exact files/symbols to delete (this manifest expanded to a precise
   file+line checklist) for your final review.
2. Remove only the approved scope.
3. Re-run: `validate.sh` (both doc suites) · claim-hygiene · proof-hole ·
   `rocq-critical-zero-admission` · the full Rust gate matrix (CAMP-0 set) · a dependency-tree
   check that no production build pulls `ascent`/`ascent-byods-rels`/the CESK cluster.
4. Update doc-07/08 + both coverage matrices together (Evidence-Loop step 7).
5. Commit with the complete removal ledger.

## Precise file-level removal checklist (verified surface)

The two scopes differ by ONE axis: CESK (`legacy-cesk-runtime`) has **no remaining use** and is
removed in both; Ascent (`oracle-ascent`) is **still the differential-oracle reference**
(`rho_vs_ascent`, `rho_language_backend_report`) so it is kept under P6-keep-oracle and removed
under P6-full. (The Ascent code is already compiled *only* under `oracle-ascent`, fail-closed by
default — there is no separate always-on "Ascent production path" left to peel; the production
default is Dovetail/Rho, proven by `RuntimeBackendDispatch.v`.)

### Both scopes remove — the CESK runtime backend (no remaining consumer)
- `prattail/src/{cek_eval,cesk_store,gc,abstract_cesk,green_thread,scheduler,global_pool,pool_fsm,worker_pool,coordinator}.rs` — 10 standalone modules.
- `prattail/Cargo.toml:48` `legacy-cesk-runtime` feature + its gated test targets (`:158,163`); the 10 `#[cfg(feature="legacy-cesk-runtime")]` gates + `mod` decls in `prattail/src`.
- `testkit/Cargo.toml:11` re-export + the 3 `legacy-cesk-runtime` gates/modules in `testkit/src` (`analytical/green_thread_tests.rs`, `analytical/cesk_coverage.rs`).
- **VERIFIED (2026-06-16):** the only consumers outside `prattail/src` are those two `testkit/src/analytical/*` files, and they are themselves `legacy-cesk-runtime`-gated — so there is **no consumer outside the feature**; removal under the feature is clean. (The WPDA-side CEK/observer parser modules are a *different* path — KEEP them.)

### P6-full additionally removes — the Ascent reference/oracle
- `languages/Cargo.toml:46-51` `oracle-ascent` feature + the `ascent`/`ascent-byods-rels`/`hashbrown`/`rustc-hash` optional deps + `ascent-parallel` (`:54`, already broken upstream); the `oracle-ascent`-`required-features` test targets (`:138,143,238`); the 31 `oracle-ascent` cfg-gates in `languages/src` + the Ascent oracle test files.
- `macros/src/logic/**` — the Ascent RUNTIME generator only (`generate_ascent`/`format_ascent`/the `ascent::ascent!` Datalog emitter) + the `ascent_output` runtime wiring in `macros/src/lib.rs`; the generated `run_ascent*`/`eqrel` surfaces under the 15 macros cfg-gates. **Do NOT remove `macros/src/logic/antipattern.rs`'s `parse_ascent_program_tokens` use** (it is logic-block *parsing*, the active path — see next item).
- **`ascent_syntax_export/` crate — RETAIN. VERIFIED (2026-06-16) it is NOT oracle-only:** it is used *unconditionally* by the active macro/parser path — `ast/src/language.rs` (`parse_ascent_program_tokens` parses the `logic { relation … }` block of every `language!` definition), `macros/src/logic/antipattern.rs`, and `query/src/parse/ascent_parse.rs`. Deleting it would break the macro for ALL languages (it parses the predicate/relation declarations, e.g. GuardedRho's `halts`/`safe`). Keep the crate and its `ast`/`macros`/`query` Cargo.toml deps. P6 removes the Ascent *runtime* (the generated Datalog backend), not the Ascent-*syntax* parser.
- `rholang-runtime/Cargo.toml:27-32` `oracle-ascent` feature + the `rho_vs_ascent.rs` and `rho_language_backend_report.rs` test targets (`:79,84`).
- `runtime` / generated `Language::run_ascent` trait surface (already fail-closed by default).
- After removal Calculator's flip is still proven by the end-to-end RhoRuntime tests + `OracleQuotientEquivalence.v` + the COMM/guard oracles; only the *live* Ascent differential is gone.

## Status: PREPPED — awaiting explicit scope + approval

P6 is now staged to the brink: the surface is mapped, the scope fork is exact, the post-removal
gate sweep is defined. **One destructive step remains — the deletion itself — and it is NOT taken
until you explicitly approve a scope** (`P6-keep-oracle` or `P6-full`). This is the
separately-confirmed pre-flight the plan (R7) and the standing "no destructive action without
explicit approval" rule require. Git history is the archive.
