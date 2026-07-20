# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### A-S6 — the DEMO FLIP + step-policy hygiene: the runtime mandate is registry-wide (2026-07-20)

#### Changed

- **BREAKING (registry membership + demo exec routing, A-S6 — USER decision
  2026-07-20)**: every rho_net demo language joins the production REPL registry on the
  two-stage LAZY Dovetail+Rholang wrapper — AcDemo, AcBagDemo, NlAcDemo, AmbDemo,
  AmbNewDemo, InOutDemo, CommDemo, CtxDemo, BiCongDemo, LambdaDemo, NativeDemo,
  NativeFoldDemo (SwapDemo was already flipped). The default exec path is the generated
  report-free `rho_net_match_invocation_to` (the in-Rho locate-all set-automaton match,
  single-shot locate-and-fire; demos are NOT drive-opted — `DRIVE_OPT_IN` stays exactly
  `{"Lambda", "Ambient"}`); the Dovetail D-stage runs only on typed deferrals. The
  runtime mandate — "Dovetail handles only semantic predicates at runtime", plus labeled
  step introspection and lazy deferral reports — now holds for EVERY registered
  language. Per-family exec pins: `repl/tests/a_s6_demo_registry_exec.rs`; zero-D-stage
  extension (AcDemo / CtxDemo / NativeFoldDemo): `repl/tests/zero_dstage_exec.rs`.
- **Per-demo fallback shapes (probed reality, 2026-07-20)**: LambdaDemo's
  report-carrying fallback is the Lambda/F16 shape (match-then-TYPED-ERROR — the
  sigma-replay driver has no Beta arm; a replayed beta would double-substitute); every
  other demo keeps the SwapDemo match-then-sigma-replay shape. CommDemo is the one
  BY-DESIGN deferring demo: its `PFor` binder carries a pre-scope Name field the
  match-path reflection does not support, so an exec lazily builds the report and the
  sigma-replay driver fires the Comm (per-firing replay channels `OUT0`, ...).
- **Step-policy hygiene**: `dovetail_step_graph` is KEPT everywhere as LABELED host
  introspection — the REPL `step` Layer-1 display now prints "rewrite-graph evidence
  (host introspection, display-only — exec results never flow from this graph)"; the
  Layer-2 `StepSession` COMM trace is the ONLY executable stepper. Typed-path demos
  (AmbDemo/AmbNewDemo/InOutDemo/CommDemo/LambdaDemo/NativeDemo/NativeFoldDemo) keep
  Layer-1 rewrite graphs; untyped demos (AcDemo/AcBagDemo/NlAcDemo/CtxDemo/BiCongDemo)
  fall through to the Layer-2 trace, whose legacy `sa:`/`loc:`/`ac:` COMMs are
  unclassified-VISIBLE by design (the tau classifier labels only the reserved `^...`
  families). Pins: `repl/tests/a_s6_demo_step_policy.rs`.
- **Dovetail-only build (decision (4), now universal)**: SwapDemo and the 12 demos
  register through the fail-closed wrapper in the no-f1r3node profile — parse and
  introspection work; `exec` returns the typed error naming the in-Rho set-automaton
  match and the rho build flag (`repl/tests/dovetail_only_fail_closed.rs`).
- Docs: 09/10 rewritten to the post-A-S6 universal runtime split; 24/29 status updates
  (A-S6 landed).

### A-S5 — the Lambda/Ambient production flip onto the in-Rho quiescence driver (2026-07-19..20)

#### Added

- **The generated in-Rho quiescence driver** (`rho_net_drive.rs` + the generated
  `rho_net_drive_invocation_to`): one `exec` of a drive-admitted language is one seed —
  the `^drive` receiver family drives the reflected subject to rest entirely on the Rho
  machine (fuel-gated redex arms firing through the sigma ABI with contractum re-drive;
  congruence descent with per-path `GInt` fuel, fixed 64, atomic join + inline post-join
  re-check; the binder arm; the A-S5.5 AC bag/nested-AC arms with the three-case
  Nil/soup/wrap splice at both reassembly seams). Four observation channels (OUT value,
  fired-label multiset, typed error, typed `^drive-fuel`) and an always-on
  fired-vs-NF-scan exec cross-check. (A-S5.2 Lambda core; A-S5.5 Ambient.)
- **Recorded drive admission** (`DriveAdmission`: `Admitted` / `NotRequested` /
  `Unsupported` with every failed conjunct named; the codegen-visible `DRIVE_OPT_IN`
  const = exactly `{"Lambda", "Ambient"}`); a non-opted-in language's generated module is
  byte-identical (pinned by `a_s5_6_byte_identity_pins.rs`).
- **Installer tolerance for congruence-exempt rules** (A-S5.1): a congruence-only rewrite
  is RECORDED-exempt (`RhoNetLowered::congruence_exempt_rules`) instead of blocking the
  install; Lambda installs with its three recorded exemptions.
- **`::=`-declared collection-kind resolution** (A-S5.3): collection kinds resolve from
  grammar items, admitting Ambient's real `OpenRule` as structural-AC.
- **FV**: `InRhoQuiescenceDriver.v` (driver LTS: `drive_steps_sound`, per-trace
  `quiescence_sound`, `fuel_exhaustion_never_wrong`, the ITERATED beta weak bisimulation
  `drive_weak_bisim`, and the A-S5.5 bag model — `driver_flatten_agrees_with_add_flattened_bag`,
  `bag_flatness_sound`, `bag_atoms_preserved`, `bag_quiescence_sound`);
  `BinderFloatCanonicalization.v` (float completeness over the Cardelli–Gordon subset —
  a theorem, demoted from premise); the re-proved `AmbientInOutFiring.v` over the
  (Red Out) redeclaration; the A-S5.7 capstone upgrade
  (`WholeGsltInRhoOpCorrespondence.v` §5: per-family premises over drive-mediated
  multi-step traces, drive schedules, per-trace quiescence; the
  `WholeGsltInRhoOpCorrespondenceIteratedViaDriver.v` companion consuming
  `drive_weak_bisim` and the bag model literally; the
  `DovetailRhoLanguageBackendWrapper.v` driver-admitted branch). All zero-admission,
  every `Print Assumptions` Closed.

#### Changed

- **BREAKING (production exec routing, A-S5.6)**: production Lambda and Ambient execute
  on the Rho machine via the in-Rho quiescence driver — the report-free invocation slot
  IS the drive seed; the Dovetail D-stage runs only on the deferral path (zero D-stage on
  admitted paths, pinned by `repl/tests/zero_dstage_exec.rs`); Lambda's report-carrying
  fallback carries NO sigma-replay Beta arm (F16 — a replayed beta would
  double-substitute); exec result display is de-reflected with alpha-equivalence goldens;
  REPL `step` splits Lambda (Layer-1 typed rewrite graph) from Ambient (Layer-2 live COMM
  trace) with tau-COMM classification and filtering. The Dovetail-only build fails closed
  pointing at the Rho build.
- **BREAKING (Ambient language semantics — Cardelli–Gordon alignment, A-S5.4b)**:
  - the four prefix-float equation premises corrected `x # P` -> `x # N` (`AmbNew`
    becomes C-G (Struct Res Amb) verbatim; `InNew`/`OutNew`/`OpenNew` documented as
    sound extensions, not C-G axioms);
  - **`OutRule` redeclared to C-G (Red Out)**: the parent's residual `...rest2` stays
    INSIDE the parent membrane (the old rule ejected it through the membrane for bodies
    of three or more elements and could never fire on singleton bodies); an empty rest is
    legal, so the singleton fires to `{n[{p}], m[{}]}` (`m[{}]` versus C-G `m[0]` is the
    documented empty-bag-for-zero fragment deviation). The rewrite fingerprint changed.
    Record: `docs/architecture/rho-native-integration/26-in-rho-ac-family-reference.md`
    §13.
- **The binder float is UNCONDITIONAL unbind-first with a bag-flat splice** (A-S5.4a):
  the `is_fresh` gates are retired (freshen-then-float is capture-safe by construction —
  moniker unbind is a process-global gensym); a bag-bodied new-binder body is SPLICED
  flat at the extrusion seam (the AM-2 flatness obligation).
- Docs: 09/10/20/24/25/26/29 updated to the post-flip state (driver architecture, the
  runtime boundary, the honest-premise inventory, the A-S5 mechanized-additions
  crosswalk, the Cardelli–Gordon alignment record);
  `docs/architecture/dovetail/ambient-binder/inc1-handler-spec.md` marked superseded in
  part by the unconditional float.
