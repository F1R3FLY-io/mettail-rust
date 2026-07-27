# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Task #22 — `RhoCalc` is renamed `Rholang`, workspace-wide (2026-07-27)

USER: *"rhocalc IS rholang."* The language the `language!` macro declared as `RhoCalc`
has always been MeTTaIL's Rholang 1.4 surface; it now carries that name everywhere.
4,088 lowercase, ~1,698 `RhoCalc`, 590 `Rhocalc` and 46 `RHOCALC` occurrences moved
across six commits. Every casing variant is 7 characters in and 7 out, so no
rustfmt output shifted.

#### Changed — BREAKING

- **The bag ABI tag changed value.** `RHOCALC_BAG_ABI_TAG = "mettail.rhocalc.bag.v1"`
  became `RHOLANG_BAG_ABI_TAG = "mettail.rholang.bag.v1"`
  (`rholang-codegen/src/lib.rs`). A `Bag` — a MeTTaIL-only category with no Rholang
  analog — lowers to an `EList` tagged with a `GPrivate` built from this string, so the
  tag's BYTES ride the encoding: a `Par` produced by the old constant does not decode as
  a bag under the new one. Producer (`rholang-codegen/src/ast.rs`) and consumers
  (`rholang-runtime/src/{run,observation}.rs`,
  `rholang-runtime/src/rholang_ast/recursive_oracle.rs`) are all in this repository, and
  the sibling f1r3node checkout names the tag nowhere, so nothing off-tree is keyed to
  it. Both halves — the constant AND its value — moved together, deliberately: leaving
  the value behind would have made the name a lie at the one place the bytes are read.
- **The interpreter binary `rhocalc` is now `rholang`** (`--bin rholang`,
  `target/debug/rholang`). No `rholang` binary existed to collide with: f1r3node's is
  `rholang-cli`, and it is a path dependency rather than a workspace member, so `--bin`
  could never have resolved to it.
- **The REPL registry key is now `rholang`.** `LanguageRegistry` keys on
  `language.name().to_lowercase()`, so `lang rhocalc` becomes `lang rholang` and the
  example environment auto-loaded at language load moved with it
  (`repl/src/examples/rholang.txt`).
- **The Cargo feature `rhocalc-runtime` is now `rholang-runtime`** (convention
  `{lang}-runtime`), and `oracle-rhocalc` is now `oracle-rholang`. A feature may share a
  name with its own package; only a DEPENDENCY name would collide, and f1r3node's
  `rholang` crate is a non-optional dependency, so it declares no implicit feature.
- **`languages`' feature `rhocalc` is now `rholang`**, and the module moved:
  `languages/src/rhocalc.rs` + `languages/src/rhocalc/` -> `rholang.rs` + `rholang/`.

#### Notes

- **The definition fingerprint of this language changed.** The name is the first field
  `ast/src/identity.rs` writes, so `Rholang`'s `definition_fingerprint()` differs from
  `RhoCalc`'s. Nothing required re-pinning: the only literal `mettail-langdef-v1:` pins
  in the tree are Lambda's and synthetic test constants, and the set-automaton size pin,
  the guard-tier goldens and the a_s5_6 byte-identity pins are structural or name-free.
  Verified by measurement — the full suite reports the same 10,725 passing tests before
  and after.
- **`macros/src/gen/compose_gen.rs` is excluded from the rename on purpose.** Its
  `assert_eq!(to_snake_case("RhoCalc"), "rho_calc")` uses `RhoCalc` as a CAMEL-SPLITTING
  INPUT, not as a reference to the language; substituting it would have produced the
  silently-wrong `to_snake_case("Rholang") == "rho_calc"`.
- **Historical measurements keep the old name**: `docs/benchmarks/**`,
  `prattail/docs/benchmarks/**` and the captured `baseline-cf03e571` files record what
  was run, and what was run was called rhocalc. `docs/archive/**` and the rootcause
  artifacts likewise. "rho calculus" prose is untouched throughout — Meredith's process
  calculus is not this language.

### A-S5.8 — the in-Rho `^float` receiver family: the boundary-float premise discharged constructively (2026-07-20)

#### Added

- **The `^float` receiver family (leg 1, `rholang-codegen/src/rho_net_float.rs`)**: the
  per-iteration binder-float canonicalizer for FLOAT-BEARING drive-admitted languages
  (gate: `language_has_float_handler` ∧ `equations_boundary_canonicalizable` ∧
  `DriveAdmission::Admitted` — bundled corpus: exactly the production Ambient). The
  8-arm `^float` dispatcher (`^lambda` rewrap / float-across-ctor hoist dispatch /
  other-ctor descend+rewrap / nullary / soup peel→merge / Nil / `^free`+`^bound`
  passthrough / the EXISTING `^drive-err` wildcard), the `^float-merge:{op}` satellite
  (ScopeExtrusion: u-first deterministic strip order, shift-the-other-side by 1 at
  cutoff 0 per stripped binder — capture avoidance by the SHIFT-IMAGE argument, no
  gensym — base = the three-case `bag_fragment_dispatch` splice), and the
  `^float-hoist:{C}` satellites (shift every other field per hoisted binder, rewrap) —
  ALL satellites DERIVED from the landed float-equation recognizer classification
  (`float_satellite_table`), never hardcoded to Ambient. Reserved labels `^float` /
  `^float-hoist` / `^float-merge` (registry 16 → 19); `^shift` gains soup + Nil arms
  GATED on `hashbag_collection_ops` non-empty (Lambda byte-identical); installed as the
  third `Option<Par>` beside `subst_trs`/`drive` — Ambient 7 → 15 receives.
- **Always-float firing + the S2 float-routed seed (USER decisions Q-AB = A,
  Q-SEED = S2)**: both firing emitters route every contractum through `⌜^float⌝` before
  the re-drive (float COMMs consume NO drive fuel; non-float languages BYTE-IDENTICAL —
  the Lambda pins hold unchanged); the generated drive fn assembles the float-routed
  seed `new rf { ⌜^float⌝!(⟦t⟧, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel, @out) } }` for
  float-bearing languages while the HOST boundary float is RETAINED (defense-in-depth +
  the NewComm display ordering the run-order-sensitive α goldens ride, F8-AM-5b).
  `RhoNetDriveInvocation` carries the raw `subject` and the backend seed readers are
  S2-aware (F8-AM-5a).
- **`AcReconstructTemplate::Binder` (F8-AM-1)**: RHS-introduced binder scopes at
  ELEMENT template positions (ctor tag erased, mirroring the `^lambda` reflection) with
  the F8-AM-1c depth-`k` PRE-SPLICE σ-slot shift rule — host side via the new
  `^shift` mirror on `GroundTerm`s, drive side via the carrier's asynchronous
  chained-`^shift(Z,·)` pre-stage; the MATCH path gives binder-templated rules the
  FAIL-CLOSED NO-MATCH-ENTRY disposition `NestedStructuralAcBinderTemplated` (recorded,
  never an install error), and `drive_admissible` discharges a static-gate defer exactly
  when the rewrite transcribes to a self-contained driver AC-carrier arm.
- **The runtime witness suite (leg 2, `rholang-runtime/tests/rho_net_ambient_float.rs`)**:
  THE CONSTRUCTIVE-DISCHARGE WITNESS (the F8-AM-1a `Seal` shape in a name-keyed test
  `Ambient` def, decision Q-W) — drive fires `Seal`, the contractum hides `Open` under
  the fresh ν, `^float` extrudes, `OpenRule` fires, ledger `{Seal, OpenRule}` — plus the
  NewComm double-binder subject under the NEW run-permutation-insensitive membership
  helper (F8-AM-4), raw F1/AM-2 subjects with NO host float and no `^bound` leakage,
  run length 8 (beyond the host's display-only ≤6 cap), multi-seam nests, the Nil family
  (ν over the empty bag, element `^lambda(Nil)` — F8-AM-5g, the LOAD-BEARING
  `^shift`-Nil case — F8-AM-5f), the in-float same-op-soup splice, and the AM-3 Nil
  cases through the float path.
- **`[τ float]` (F8-AM-2)**: `RuntimeTauClass::Float` + the classifier's float family
  (the exact `^float` tag + the `^float-hoist:`/`^float-merge:` prefixes; families
  disjoint — the `^shift`/`^cmp` satellites stay `[τ subst]`, nothing reclassifies),
  WITNESSED by a new drive-seeded `StepSession` trace test; the
  `a_s5_6_step_routing.rs:125` match-fallback trace pin is byte-identical (MUST-NOT-MOVE
  honored).
- **FV (leg 3, zero admissions)**: `InRhoFloatCanonicalization.v` — the de Bruijn
  float over run-length configurations: `float_step_sound` (=`fstep_side_condition` +
  `float_reachable`; the C-G freshness side condition held by
  `hoist_side_condition_by_shift_image`), the F8-AM-4 split
  `float_functional_up_to_NewComm` (any peel order lands in the same NewComm class,
  explicit two-sided-inverse renamings) / `float_identity_on_canonical`, the F8-AM-3
  lemma `redex_invariant_under_run_permutation` (BFC.v:381-397 cover bag permutation
  only), `float_preserves_bag_flatness`, `float_exposes_redexes_{in,open,out}`; and
  `InRhoDriveWithFloat.v` — the driver float phase (`fval` = `bval` + `FNu`): THE
  PREMISE DISCHARGE `drive_with_float_on_raw_eq_drive_on_canonical`, the ν-hidden
  contractum witness + its load-bearing contrast, and `float_phase_conservative`
  (landed bag-driver theorems become corollaries; conservative extension). DOC29
  §2.1/§3/§4 rewritten (per-iteration in-Rho canonicalization; host float →
  defense-in-depth + display ordering; the moniker u32 premise narrowed to host paths;
  the corrected Q-NC rationale).

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
