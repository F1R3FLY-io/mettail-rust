# P6 STAGE 2 — Ascent runtime removal surgery (execution plan)

Approved scope: P6-full. CESK already removed (commit `0a93ee39`). This is the Ascent half.
Designed by a code-grounded survey (2026-06-16). Checkpoint: `0a93ee39`.

**Status: EXECUTED** — Stage 1 (engine-generator excision) `9d889894`; Stage 2 (oracle-ascent test + feature surface) `c9cea652`. Retained as the execution record.

## Decisive correction (do NOT over-remove)

`AscentResults` (runtime/src/language.rs:1179) and `Language::run_ascent`/`run_ascent_with_facts`
(runtime/src/language.rs:944,1045) are the **production rewrite-graph result type + trait surface**,
already engine-decoupled (the `runtime` crate has ZERO `ascent` dep) and **fail-closed by default**.
They back `RuntimeBackendOutput::Ascent`, the `*ReachableNormalForms` iterators, and ~20
`normal_forms_reachable_from_*` methods used by query/simulation/repl/testkit/Dovetail/Rho.
**RETAIN them.** "Retire Ascent" = delete the **engine generation** + the **generated trait-impl
overrides that call the engine**; every language then falls back to the fail-closed default.

## RETAIN (must not touch)
- `ascent_syntax_export` crate (parses `logic { relation … }` for EVERY language) + its ast/macros/query deps.
- `generate_freshness_functions` + the unconditional freshness include (Dovetail binder path).
- `AscentResults` + `run_ascent*` trait defaults + `RuntimeBackendOutput::Ascent` (production rewrite-graph surface).
- `logic::stratification::analyze` (grammar well-formedness gate, not the engine).
- WPDA-side `cek`/observer modules.

## Ordered, build-verifiable stages

**Stage 1 — stop generating the Ascent engine + run_ascent overrides (macros only):**
- `macros/src/gen/runtime/language.rs`: delete `generate_ascent_struct`, `spill_ascent_struct`; drop ascent
  params from `generate_language_impl`/`generate_language_struct`/`generate_language_struct_multi` (delete the
  `prog_struct_def`/`pre_stratum_struct_def`/`ground_seed_block`/`pre_stratum_phase` locals + the
  `run_ascent_typed` methods); delete the two `run_ascent`/`run_ascent_with_facts` overrides in
  `generate_language_trait_impl` + `_multi`; remove `generate_cek_fast_path`/`generate_green_thread_dispatch`.
- `macros/src/gen/compose_gen.rs`: delete `ascent_arms` + the composed `run_ascent` override.
- `macros/src/lib.rs`: drop `generate_ascent_source` import + call + 6 bindings + `ascent_include` +
  `#[cfg(oracle-ascent)] #ascent_include`; change `generate_language_impl` to 1-arg.
- `macros/src/logic/mod.rs`: delete `generate_ascent_source`, `AscentOutput`, `StratumContent`, now-unused helpers; keep `stratification::analyze`.
- `macros/src/gen/test_gen/mod.rs`: remove op-section emission + the oracle-ascent header; stub/remove `generate_op_section` + `operational_tests/*` emitters.
- CHECKPOINT: `cargo check -p macros` then `cargo check -p languages` (default features).

**Stage 2 — drop Cargo features + engine deps:**
- `languages/Cargo.toml`: delete `oracle-ascent` + `ascent-parallel` features + `ascent`/`ascent-byods-rels`/`hashbrown`/`rustc-hash` optional deps.
- `prattail/Cargo.toml`: delete `ascent-parallel`. `rholang-runtime/Cargo.toml`: delete `oracle-ascent`.
- workspace `Cargo.toml`: delete `ascent`/`ascent-byods-rels` workspace deps (KEEP `ascent_syntax_export`).
- `languages/src/lib.rs`: delete the 6 `#[cfg(oracle-ascent)]` items (eqrel re-export, `pub mod dual_indexed`, 4 `*_source` re-exports); delete `languages/src/dual_indexed.rs`.
- CHECKPOINT: `cargo check --workspace`.

**Stage 3 — delete oracle-only example/bench targets:**
- `languages/Cargo.toml`: delete examples `demo_supply_chain`, `ev0_probe`, bench `rhocalc_bench` + their files.
- `rholang-runtime/Cargo.toml`: delete `[[test]] rho_vs_ascent`, `[[test]] rho_language_backend_report`.
- CHECKPOINT: `cargo check --workspace --all-targets`.

**Stage 4 — delete the oracle-ascent test files + edit the partially-gated one:**
- Delete 15 whole-file `#![cfg(oracle-ascent)]` tests in `languages/tests/` (ambient_tests, auto_inject_cong_propagation,
  calculator, casting_example_files, composition_tests, edge_case_tests, exec_empty_collection, h3_chain_correctness,
  led_delegation_tests, numeric_bigint_cast_regressions, probe_neg_zero, recovery_bounded_dispatch, rhocalc_tests,
  run_ascent_dedup, trampoline_tests).
- Delete 8 `gen_*_op.rs` artifacts (basemath, calculator, extmath, importedmath, ledtest, mixedmath, optsmoke, rhocalc).
- Delete `rholang-runtime/tests/{rho_vs_ascent,rho_language_backend_report}.rs`.
- EDIT `languages/tests/runtime_backend_metadata.rs`: strip the two `#[cfg(not(oracle-ascent))]` attrs (keep as the permanent fail-closed proof).
- FINAL CHECKPOINT: `cargo check --workspace --all-targets`; `cargo build --workspace`; `cargo tree -p languages | grep -i ascent` shows ONLY `ascent_syntax_export`.

## Risks (from the survey)
- Over-removal of `AscentResults`/`run_ascent`/`ascent_syntax_export`/`freshness` → cascade. The stages touch only the engine + generated overrides; verify the retained surface compiles unchanged at each checkpoint.
- Regeneration race: do Stage 1 (stop emission) BEFORE Stage 4 (delete `gen_*_op`).
- `ground_rewrite_seeds` non-Ascent use: verified none (all consumers are the removed generator / deleted run_ascent_typed).
