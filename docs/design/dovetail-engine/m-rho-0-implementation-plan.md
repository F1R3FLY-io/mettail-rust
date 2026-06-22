# M-RHO.0 — Implementation Design (Rho-bridge bring-up)

> **Status (reconciled post-P6):** shipped. M-RHO.0 began as the *inert* milestone
> — the three Rho-bridge crates present but carrying no live caller — and that
> framing is retained below as the design-of-record. The bridge is now live: the
> renamed `rholang-codegen` / `rholang-runtime` / `rholang-adapter` crates drive
> the production Rho lane, and the generated Ascent differential oracle was retired
> in P6. Read the original "(INERT)" phrasing as historical milestone language.

> Grounded against f1r3node-rust `@ feature/cost-accounted-rho` and mettail-rust
> `@ feature/wfst-architecture` (2026-06-09, via a Plan agent over pgmcp). This is
> the authoritative substage breakdown for M-RHO.0; each substage is independently
> completable and pairs a zero-admission Rocq obligation. Parent plan:
> `~/.claude/plans/codex-was-cleaning-up-ethereal-kettle.md` §"Engine epic — FINAL
> DESIGN". pgmcp: `m-rho-0-inert-crates-adapter-calculator-oracle` (#280).

## Base-verification verdict

Base verified; three corrections that reshape the plan text (none block .0):

1. **The `FakeGslt`/`FakeLogic` conformance template lives in `#[cfg(test)]`**
   (`resource_logic.rs:221-270`), and the 4 conformance laws
   (`law_sound`/`law_reject_underfunded`/`law_supply_monotone`/`law_decidable`,
   `resource_logic.rs:137-200`) are **private `#[cfg(test)] fn`s** — not
   cross-crate importable. `⇒` the adapter cannot literally call the host's laws;
   it **re-hosts** a faithful transcription (decision **B1-a**, below).
2. **The differential-oracle baseline is `lang.run_ascent(term)?.normal_forms()`**
   (`languages/tests/gen_calculator_op.rs:228+`) — there is no separate `eval`
   entrypoint.
3. **f1r3node-rust's cost-accounted-rho Rocq corpus is NOT globally axiom-free**
   (`MultiSignerRefinement.v`, `LLIdentities.v` each have one `Admitted.`) — but
   the adapter's reuse path (`GSLTOSLFCapstone.v`, `LinearLogicResources.v`) IS
   `Qed`-closed, so the *reused* obligations are clean. Do not advertise the whole
   upstream corpus as clean.

The inert milestone mirrors the already-shipped `dovetail` crate +
`dovetail/formal/rocq/` pattern exactly (gated `[features] engine = []`,
substrate-isolated, capped Rocq target).

## API findings (f1r3node-rust @ feature/cost-accounted-rho)

- **Trait:** `OslfResourceLogic<G: GsltPresentation>` (`resource_logic.rs:54`),
  two methods: `fn demand(&self, &G::CanonicalProgram, &G::Signature) -> DemandEntry`
  (`:55`); `fn is_funded(&self, &DemandEntry, effective_supply_s: i64, margin: i64) -> bool`
  (`:61`). `trait ResourceLogic: OslfResourceLogic<RhoGslt>` + blanket impl (`:65-67`).
- **Presentation:** `trait GsltPresentation { type Program; type CanonicalProgram;
  type Signature: ResourceSignature; fn canonicalize_for_funding(&self, &Program)
  -> CanonicalProgram }` (`:46-52`); `trait ResourceSignature { type Key: Clone+Ord+Eq;
  fn key(&self)->Key; fn split_join_decompositions(&self, &mut Vec<ResourceDecomposition<Key>>) }`
  (`:38-44`). `DemandEntry { known_lower_bound: i64, unknown: bool }` (delta_sigma.rs),
  `DemandEntry::ZERO`.
- **Rho instance:** `RhoGslt` with `Program = CanonicalProgram = Par`,
  `Signature = Sig`; `canonicalize_for_funding` → `delta_sigma::desugar_for_funding`
  (`:72-81`). `Par = models::rhoapi::Par`. `Sig` enum (`Sig::And/Ground/Threshold`,
  `lane_hash() -> [u8;32]`).
- **Template (copy-from):** `FakeGslt`/`FakeLogic`/`FakeSig` (`resource_logic.rs:221-270`).
- **Generic consumption (the real "DenyLogic pattern"):**
  `casper .../acceptance.rs::admit_by_funding_with_logic<L>(…, logic: &L) where
  L: OslfResourceLogic<RhoGslt>` (`:483-492`); test logics `DenyLogic`/`ZeroDemandLogic`
  injected via it. **Seam is fixed to `RhoGslt`** — an external `…<MettaGslt>` is not
  directly consumable here (blocker B1).
- **Runtime:** historical source evaluation uses
  `RhoRuntime::evaluate(&self, &str, Cost, HashMap<String,Par>,
  Blake2b512Random) -> Result<EvaluateResult, InterpreterError>`. The current
  generated-backend path builds normalized `models::rhoapi::Par` directly and
  injects it with `RhoRuntime::inj(Par, Env<Par>, Blake2b512Random)` after
  installing an explicit `Cost::unsafe_max()` budget. `RhoRuntimeImpl {
  reducer: Arc<DebruijnInterpreter>, .. }` (rho_runtime.rs);
  `EvaluateResult { cost: Cost, errors: Vec<InterpreterError>, .. }` remains the
  source-path result type.
- **Crates `publish = false`:** `rholang`, `rspace_plus_plus` (dir `rspace++`),
  `models`, `casper`. ⇒ one-way dep must be a **cross-repo `path` dep**, gated
  behind `engine` (blocker B2).
- **Reverse-dep guard:** `resource_logic.rs:293
  fn mettail_rust_is_not_a_cargo_dependency()` — scans f1r3node-rust manifests;
  green iff none names mettail-rust (verified: 0 references, 2026-06-09).
- **Rocq reuse (Qed-closed):** `GSLTOSLFCapstone.v`
  (`oslf_funding_logic_sound`, `cost_accounted_calculus_is_gslt_with_oslf_logic`),
  `LinearLogicResources.v` (`funds`, `funding_decidable`,
  `strict_reject_when_underfunded`, `ll_linear_no_contraction`),
  `CAUntypedLambda.v` (2nd minimal instance).

## MeTTaIL-side inputs

- Calculator `LanguageDef`: `languages/src/calculator.rs` (`calculator_source`,
  `CalculatorLanguage`). `LanguageDef` type: `ast/src/language.rs:38`.
- Existing backend: generated `run_ascent` (`macros/src/gen/runtime/language.rs:3428`),
  native eval generator `generate_eval_method` (`macros/src/gen/native/eval.rs:250`)
  — `generate_rho_vm` is a NEW sibling.
- Oracle hook: `languages/tests/gen_calculator_op.rs`;
  `Language::run_ascent` + `AscentResults::normal_forms()` (`runtime/src/language.rs:229`).
- Inert template: `dovetail/Cargo.toml` (`[features] engine=[]`),
  `dovetail/formal/rocq/{_CoqProject,Makefile}`, and the `rocq-dovetail`
  target in `formal/Makefile`.

## Blockers / user decisions

- **B1 (resolved for .0):** the host conformance laws are test-private and the
  gate seam is `RhoGslt`-fixed. **B1-a (chosen and shipped for .0):** re-host the
  4 generic laws as a `pub fn` kit in `rholang-adapter` and run them against
  `OslfResourceLogic<MettaGslt>`; this is the MeTTaIL bridge contract. **B1-b
  (host genericization option):** upstreaming a `pub` conformance kit plus a
  `G`-generic gate seam in f1r3node-rust would be host-maintenance work, not an
  active blocker for the CESK runtime-backend replacement path.
- **B2 (resolved for .0):** core crates `publish=false` ⇒ cross-repo `path` deps,
  declared `optional` + pulled only by `engine`; default build f1r3node-free.
- **B3 (not a .0 blocker):** the Reified-RSpace seam (Scala`→`Rust PRs) blocks
  M-RHO post-.0 only; .0 canonicalizes `Term→Par` for funding analysis + (optional)
  runs a string through `RhoRuntime::evaluate` — no reified spaces.
- **B4 (hygiene):** `CAUntypedLambda.v` cites a `cost-decoration/src/main.rs`
  absent in this tree; self-contained proof, so not a blocker — stale prose ref.
- **B5 (axiom-free scope):** guaranteed for new mettail theory + reused
  Qed-closed modules; NOT the whole upstream corpus.

## Substage decomposition (each independently completable + zero-admission)

| Substage | Goal | Key files | Rocq obligation | Gate |
|----------|------|-----------|-----------------|------|
| **.0.0** ✅ | Inert gated crates + one-way-dep proof + guard verified | `mettail-rho-{codegen,runtime,adapter}/{Cargo.toml,src/lib.rs}`, workspace `Cargo.toml`, `formal/rocq/rho_bridge/*`, `formal/Makefile` | `BridgeInertness.v` (one-way acyclic dep graph) | default build f1r3node-free; guard green; `rocq-rho-bridge` green |
| .0.1 | `MettaGslt` presentation + adapter trait surface (engine-gated, pure) | `rholang-adapter/src/{gslt,logic}.rs` | `MettaGsltPresentation.v` (canonicalize total; `split_join` sound) | `cargo check --features engine` |
| .0.2 | Delegate `demand`/`is_funded` to `delta_sigma`; 4-law conformance | `rholang-adapter/src/{logic,conformance}.rs` | `MettaOslfLawsConformance.v` (2nd instance of capstone; reuse `LinearLogicResources.v`) | 4 laws green for `MettaResourceLogic` |
| .0.3 | `generate_rho_vm`: calculator `LanguageDef` → normalized Rholang AST (`Par`) | `macros/.../rho_vm.rs`, `rholang-codegen/src/lib.rs` | `RhoLoweringTotalOrRejects.v` (total-or-explicit-reject; miss nothing) | generated `Par` has the expected contract/ABI shape |
| .0.4 | Differential oracle vs Ascent on `gen_calculator_op` | `languages/tests/rho_oracle_calculator.rs`, `rholang-runtime/src/oracle.rs` | `OracleQuotientEquivalence.v` (weight-erase ∘ eqrel-quotient is an exact equiv) | set-equality rho ≡ Ascent |
| .0.5 (opt) | Run lowered calculator on a real `RhoRuntime` | `rholang-runtime/src/run.rs`, `tests/run_calculator.rs` | `RhoRunPreservesFunding.v` (run-demand = charged-demand) | `evaluate` Ok + Welch |

Dependency: `.0.0 → .0.1 → {.0.2, .0.3} → .0.4 → .0.5(opt)`. Risk ascends with
number; `.0.5` isolates all Tokio/RSpace and is gated behind an explicit go/no-go.

## Deliverable map

| Plan deliverable | Substage | Evidence |
|---|---|---|
| #1 three bridge crates, one-way, gated OFF | .0.0 | `engine=[]`; `cargo tree` 0 f1r3node deps by default |
| #2 `OslfResourceLogic<MettaGslt>` conformance | .0.1+.0.2 | 4 laws green (re-hosted, B1-a) + `delta_sigma` delegation |
| #3 calculator→RhoRuntime, runnable | .0.3 (compile) + .0.5 (run) | generated `Par` injects directly; no source parse gate |
| #4 differential oracle vs Ascent | .0.4 | weight-erased/eqrel-quotiented set-equality |
| #5 f1r3node guard green | .0.0 (+each) | 0 mettail refs in f1r3node manifests |
| #6 axiom-free Rocq + Welch | every substage | `rocq-rho-bridge`; Welch in .0.5 |

## ★ Integration decision (user, 2026-06-09): NO feature gating — full integration

The user directed full, clean integration with NO feature gating (the end goal is
MeTTaIL fully integrated with Rholang/f1r3node). The `engine` feature was a
bring-up risk-isolation measure, not a design necessity, so it was REMOVED: the
bridge crates' f1r3node deps are mandatory cross-repo `path` deps, centralized in
the root `[workspace.dependencies]` (`models`, `rholang`; each bridge crate
references the ones it uses via `workspace = true`). f1r3node deps are added
per-substage as the code that uses them lands (adapter: `models`+`rholang` now;
codegen: `rholang` at .0.3; runtime: `rspace_plus_plus`+`casper`+tokio at .0.5).

**Toolchain finding (real, surfaced not hidden):** `gxhash 3.5.0` (pulled via
`pathmap` → f1r3node-rust `models`) `compile_error!`s unless `cfg(target_feature =
"aes")` is set, and the **cranelift** dev backend (mettail's fast-dev codegen) does
NOT set that cfg (cranelift only enables cfgs for features it supports), whereas
LLVM does. Clean fix (in the workspace, persistent):
1. `.cargo/config.toml` `[target.x86_64-unknown-linux-gnu].rustflags +=
   -C target-feature=+aes,+sse2` (mirrors f1r3node-rust/.cargo/config.toml).
2. `Cargo.toml` `[profile.dev.package.gxhash]` + `[profile.test.package.gxhash]`
   `codegen-backend = "llvm"` — forces ONLY gxhash onto LLVM (so the aes cfg is
   honored + the aes intrinsics codegen), keeping the rest of the workspace on the
   fast cranelift dev loop.
Verified: `cargo check`/`cargo test -p rholang-adapter` green config-only (no env
override); the cross-repo build compiles + runs under mettail's toolchain.

Note: targeted per-package test runs (e.g. `cargo test -p prattail`, the
formal Makefile gates) do NOT pull f1r3node (the bridge crates are not their deps);
only building the bridge crates (or `--workspace`) does.

## Status

- **M-RHO.0.0 — SHIPPED** (9c9300ec): three bridge crates; `BridgeInertness.v`
  (zero-admission); workspace + `formal/Makefile` (`rocq-rho-bridge`) wired; guard
  invariant verified (0 mettail refs). dovetail/Cargo.toml "cube-pruning" corrected.
  (Crates were `engine`-gated at .0.0; ungated at .0.1 per the user decision above.)
- **M-RHO.0.1 + M-RHO.0.2 — SHIPPED** (this session, ungated): `MettaGslt`
  (`GsltPresentation`, `CanonicalProgram = Par`), `MettaSig` (`ResourceSignature`
  delegating to the host lane algebra), `MettaProgram`; `MettaResourceLogic`
  (`OslfResourceLogic<MettaGslt>`) delegating `demand`/`is_funded` to the verified
  `delta_sigma`; the 4 OSLF conformance laws re-hosted (B1-a) + proven green for
  `MettaResourceLogic` (3/3 adapter tests pass). Zero-admission Rocq:
  `MettaGsltPresentation.v` (lane-decomposition sound+complete) +
  `MettaOslfLawsConformance.v` (the 4 laws over the modelled `is_funded`), both
  `Print Assumptions`-clean; `rocq-rho-bridge` green.
- **M-RHO.0.3 — SHIPPED** (`9478e791`): `rholang-codegen::lower_language_def`
  (operand-type-gated; supported scalar ops `→` normalized Rholang AST contracts;
  all else recorded rejected) + AST-shape tests for contract count, operand-first
  return-channel-last ABI, and de Bruijn binding order;
  `RhoLoweringTotalOrRejects.v` (total/sound/disjoint/count, zero-admission).
- **M-RHO.0.4 — SHIPPED** (`168859e3` + `7629c828`): `OracleQuotientEquivalence.v`
  (the oracle is a sound exact equivalence) + the literal two-backend differential
  `rho_vs_ascent.rs` — lowered calculator on a real RhoRuntime ≡ `run_ascent` (5/5).
- **M-RHO.0.5 — SHIPPED** (`bfe56c4b`, AST-first updated 2026-06-13):
  `run_normalized_par_for_oracle_and_read_ints` builds an in-memory RhoRuntime,
  injects raw oracle/debug `Par` directly with an explicit max budget, and reads
  correct results (6/6). Generated backend execution uses validated
  `rhoapi::Par` artifacts through `PlannedRhoBackend`, not generic source-text
  or raw-`Par` helper aliases. `RUST_MIN_STACK` proved unnecessary for these
  shallow reductions (the speculative global config edit was reverted).
- **★ M-RHO.0 COMPLETE end-to-end** (tip `7629c828`, AST-first updated
  2026-06-13): LanguageDef `→` lowered normalized Rholang AST `→` direct f1r3node
  injection `→` differentially equals Ascent. Full ungated integration; 7
  zero-admission `rocq-rho-bridge` proofs. **Next: M-RHO.1** (rhocalc native fast
  path, `Comm`→RSpace COMM) and later per-language CESK runtime-backend flip
  gates. Parser FV remains a separate active-parser track, not part of this
  runtime-backend replacement.
