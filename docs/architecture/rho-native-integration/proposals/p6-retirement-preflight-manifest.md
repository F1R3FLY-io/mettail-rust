# P6 — Retire Ascent/CESK: pre-flight manifest (REQUIRES EXPLICIT APPROVAL)

Status: STAGED, **not executed**. P6 is a destructive step (it deletes code from the
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
| `testkit` CESK/green-thread analytical modules | `testkit/Cargo.toml:11` re-export + gated modules | behind `mettail-testkit/legacy-cesk-runtime` |

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

## Gating statement

Nothing is removed without your explicit approval; git history is the archive. This manifest
is the separately-confirmed pre-flight the plan (R7) requires.
