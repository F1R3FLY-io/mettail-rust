# OSLF resource-logic conformance

This document maps the demand-verification proofs to the native Rholang
checker and the MeTTaIL adapter. OSLF means *Operational Semantics in Logical
Form*. A GSLT is a graph-structured lambda theory. Here, `RhoGslt` presents a
Rholang `Par`; `MettaGslt` presents an already-lowered `Par` inside
`MettaProgram`. Neither presentation proves that an arbitrary guest grade has
a valid host interpretation.

The adapter delegates to the native checker. The tests below check that
delegation. They do not extract Rust from Rocq, prove the full native demand
analyzer, authenticate a supply, or activate the live funding path. The
[approved V2 boundary](cost-g-funding-projection-v2.md) retains those separate
installation, projection, admission, and settlement obligations.

## Data and trust boundaries

A **surface**, also called a **lane**, is a host cost-signature key. A resource
map assigns a nonnegative amount to each surface; a missing entry means zero.
`ResourceMultiset<SigKey>` implements this finite map. Let $`S`$ be an
independently authenticated supply map, $`R`$ a verified reservation, and
$`\ell`$ a surface. Supply covers a reservation exactly when:

```math
S \succeq R \quad\Longleftrightarrow\quad
\forall \ell,\;R(\ell)\leq S(\ell).
```

The method parameter `authenticated_supply` states a caller obligation. The
pure checker does not obtain or authenticate a ledger snapshot. In particular,
a candidate's cost stack is not pre-state supply.

`DemandBound` distinguishes three evidence kinds:

| Evidence | Meaning at this boundary | Native structural producer |
|---|---|---|
| `Exact(map)` | A claim of exact demand, accepted only against independently recomputed exact evidence | Not produced by `delta_sigma::demand_bound` |
| `FiniteUpperBound { bound, proof }` | A conservative finite reservation with native verifier evidence | Produced for supported finite programs, including the empty program |
| `Unprovable(reason)` | No accepted finite structural certificate | Produced for unsupported syntax, dynamic authority, recursive dequotation, or unbounded control flow |

The [generic trait default][native-resource-logic] accepts only an `Exact`
claim equal to a fresh `Exact` analysis of the supplied canonical program and
signature. Its default `demand_bound` is `Unprovable`. A scalar `DemandEntry`
estimate alone cannot create a certificate. An implementation that supports
finite-upper evidence must provide its verifier explicitly.

The native override recomputes [structural demand][native-delta-sigma]. It
accepts only the same evidence kind, resource map, and proof bytes. Current
finite proof bytes are the constant `rho-native-wrapping-upper-bound-v2`.
They identify this verifier's evidence format; they are not a program hash,
signature hash, cryptographic signature, or independent execution trace.

Thus two different canonical programs may legitimately reuse the same claim
when native recomputation produces the same map and evidence. The checker
still recomputes from the supplied program and signature. A changed program
or signature is rejected if that recomputation changes the evidence; identity
change alone is not a rejection rule. T6 below tests both cases.

## One native implementation, two presentations

The following table traces the whole pure-checker path. There is no second
analyzer, verifier, or formula evaluator in the adapter.

| Operation | Native implementation | MeTTaIL path |
|---|---|---|
| Canonical program | `RhoGslt::canonicalize_for_funding` calls `desugar_for_funding` | [`MettaGslt`](../../rholang-adapter/src/gslt.rs) unwraps `MettaProgram` and calls the same function |
| Signature key and split/join decomposition | `ResourceSignature for Sig` | `MettaSig` delegates to its wrapped `Sig` |
| Scalar demand and scalar funding | `delta_sigma::demand` and `delta_sigma::is_funded` | [`MettaResourceLogic`](../../rholang-adapter/src/logic.rs) calls those functions |
| Certified demand | `DefaultResourceLogic::demand_bound` | Explicit delegation to `OslfResourceLogic<RhoGslt>` |
| Claim verification | `DefaultResourceLogic::verify_demand_bound` | Explicit delegation to `OslfResourceLogic<RhoGslt>` |
| Bound funding | Verify claim, then call `supply.dominates(reservation)` | Same generic trait method with delegated verification |
| Observation | `DefaultResourceLogic::resource_observation` calls `oslf::rho_observation` | Explicit delegation to that native method |
| Formula | Generic `check_formula` calls `oslf::check` on the observation | Same generic method with delegated native observation |

Canonicalization currently clones the host `Par`; it is not a source parser
or a guest-to-host projection. Signature keys and decompositions retain the
host's lane algebra. These calls alone neither move funds nor accept a live
deploy.

### Gross demand and observed reservation are different

`demand_bound` returns gross structural demand. The native observation instead
uses `static_authority_plan().external_reservation`. That plan accounts for
backed transfers, while preserving transfer demand on the funding source.
The distinction is why the adapter must delegate `resource_observation`
explicitly, not inherit the generic observation made from the gross bound.

For example, consider one stack cell that transfers from the deploy lane to
lane A, together with an empty signed process on A. The gross demand has one
unit on each lane. The external reservation has one unit on the deploy lane:
its backed transfer covers the signed process on A. If supplied pre-state
authority contains only that deploy unit, `observation.available` still has
zero on A. The candidate did not create authenticated available authority.
T8 checks each part of this example against the native implementation.

This distinction also prevents an invalid equivalence claim: funding a gross
`DemandBound` and satisfying a formula about the external reservation need not
give the same result. The adapter preserves both native meanings.

## Formal correspondence

The node's [`GenericDemandVerification.v`][generic-proof] contains twelve
theorems and four examples. Its resource type and equality decision are
parameters. Its execution-safety theorems also require `exact_analyzer_sound`:
whenever analysis returns exact evidence, an independently defined execution
has that exact per-surface cost. The finite example proves this assumption
for a small two-surface sequence language. It does not discharge it for Rust
`Par` execution.

The theorem table separates the generic exact contract from the native
finite-upper extension. T identifiers name the adapter tests below. G
identifiers name existing native generic-contract tests.

| Rocq theorem | Evidence and assumptions | Rust correspondence and executable obligation |
|---|---|---|
| `verified_exact_authenticates_claim_and_analysis` | Accepted generic evidence must be exact; declared and recomputed maps are equal | Generic `verify_demand_bound`; G1 checks equality against independently enumerated finite events. T5 checks the corresponding kind/map integrity in the native finite override, not an exact native success path. |
| `checked_exact_is_accepted` | Identical exact claim and exact analysis; decidable map equality | Generic default; G1 and `oslf_resource_logic_is_generic_over_gslt_presentations`. Native structural analysis never produces this kind. |
| `changed_exact_is_rejected` | Exact declared and expected maps differ | Generic default; G1 and G3. T5 and T6 cover changed native finite maps and recomputation. |
| `unprovable_analysis_rejects_every_claim` | Recomputed evidence is unprovable | Generic default and native override reject. G4 and T4 cover the two boundaries. |
| `upper_analysis_cannot_be_promoted` | Recomputed evidence is upper-bound, not exact | Generic default cannot promote it. G5 and T5 reject an exact label even when its map equals the finite bound. The native override may separately verify a finite claim. |
| `finite_claim_requires_explicit_verifier` | Generic exact verifier, any recomputed evidence | Generic default rejects all finite claims. `generic_formula_check_rejects_unverified_finite_claim` tests this. Native and adapter deliberately use the explicit finite verifier; T3 and T5 check it. |
| `verified_reservation_bounds_execution` | Exact acceptance plus `exact_analyzer_sound` and an independent execution | G1 exercises the finite-sequence instance. No Rust-native analyzer-soundness proof or adapter theorem is claimed. T3 tests parity only. |
| `verified_funding_covers_execution` | Previous assumptions plus pointwise supply dominance | G2 compares funding with independently counted finite events. T7 checks native verified-reservation dominance, not full execution coverage. |
| `verified_funding_is_supply_monotone` | A verified exact reservation and pointwise increased supply | Generic `is_funded_bound` retains verification and applies `dominates`. G2 covers exact evidence; T1 and T7 cover native scalar and verified finite evidence. |
| `deficient_surface_rejects_funding` | A verified exact reservation and one deficient surface | Generic `is_funded_bound`; G2 checks each deficit. T7 checks the same reservation law for native finite evidence across two independent lanes. |
| `finite_analysis_matches_independent_execution` | Small finite syntax; analysis is exact; independently defined `finite_execution` | A proof about `SpendFirst`, `SpendSecond`, `Sequence`, and `Branch`, not `Par`. G1 is a separate Rust finite-sequence regression with independent event counting; it is not extraction of this Rocq syntax. |
| `finite_analyzer_discharge` | Same finite model; signature parameter is `unit` | Discharges `exact_analyzer_sound` only for that model. It does not prove soundness of `delta_sigma` or certify guest projections. G1 and G2 are related executable checks. |

The four examples make the attack and repair concrete:

| Rocq example | Meaning | Executable check |
|---|---|---|
| `exact_extension_remains_accepted` | Verified exact extensions remain usable | G1 and the native generic-presentation test; no fabricated native exact provider is added to the adapter suite |
| `caller_trust_accepts_underfunded_execution` | Trusting a caller's zero exact claim can admit an execution that spends one unit | G4 and G6 reject that class of claim with the repaired default |
| `repaired_verifier_rejects_unproved_zero` | Recomputed unprovable evidence rejects a zero exact claim | G6 and the exact-zero cases in T4 |
| `caller_trust_promotes_upper_evidence` | A caller label cannot turn an upper bound into exact evidence | G5, `finite_bound_cannot_be_relabelled_as_exact_evidence`, and T5 |

The formal file's `Print Assumptions` commands expose its proof dependencies.
The execution-safety hypotheses are explicit theorem inputs, not a hidden
proof of the native analyzer. Kernel checking these theorems and testing Rust
are distinct evidence steps.

## Formula and observation semantics

The native [finite formula checker][native-oslf] uses three results:
`Satisfied`, `Unsatisfied`, and `Indeterminate`. `check` maps them to `Ok(())`,
`CheckError::Unsatisfied`, and `CheckError::Indeterminate`. Failure to construct
an observation instead returns `CheckError::Unprovable(reason)`; even `True`
cannot bypass that failure at the program-checking API.

| Formula | Native rule preserved by the adapter |
|---|---|
| `True`, `All`, `Not` | Truth and three-valued conjunction/negation; negation retains uncertainty |
| `Available` | Compare only the authenticated supplied map with the requested amount |
| `Required` | Zero is true. Exact evidence decides the comparison. An upper bound disproves requests above the bound; otherwise a positive request is indeterminate. |
| `Sufficient` | Supply at least the bound proves sufficiency. Supply below an upper bound is indeterminate, not proof that realized execution is underfunded. Exact demand decides both cases. |
| `Located` | Reject a body that refers to another surface, then restrict the observation to the named surface |
| `Spatial` | Require disjoint surface footprints and check each side on its own restricted observation |
| `Spend` | Reject a zero grade, deficient supply, or demand evidence below the grade. An adequate upper bound remains indeterminate. Exact evidence permits subtraction from both supply and demand before checking the continuation. |

The checker validates formula scopes before evaluation. Negation cannot turn
an invalid scope into a satisfied formula. `linear`, `copyable`, and `relevant`
construct formulas in this same language; they are not separate evaluators.
Native program observations currently carry `UpperBound`, so they cannot
prove that a specific graded interaction occurred. T3, T4, T8, and T9 preserve
these boundaries. T10 compares sufficiency and its negation for a bounded
grid of native upper bounds and supplied amounts. It also checks the native
formula evaluator with explicit exact observations. These are formula-level
fixtures, not exact evidence from the native program analyzer. Native tests
in `oslf.rs` additionally cover exact post-spend observations; the adapter
suite does not invent replay evidence.

The existing [native property suite][native-oslf-properties] checks positive
grades, zero padding, located residual composition, modal uncertainty, and
usage disciplines. These properties remain at their implementation boundary.
The adapter tests reuse that implementation instead of duplicating its logic.
The focused native `oslf` run passed all 27 tests on 2026-10-10. Its log is
`target/verification/native-oslf-properties-20261010.log`.

The neighboring [`CAOSLFSpatialModal.v`][spatial-proof] distinguishes exact
shortage from upper-bound shortage in `sufficient_check`, matching native
Rust. It preserves uncertainty instead of inferring an actual shortage
from a conservative bound. Rocq compilation and kernel checking passed on
2026-10-10 for this model, `GenericDemandVerification`, and the strengthened
`GSLTOSLFCapstone`. The check used a 512 MiB memory limit.

| Sufficiency theorem | Native behavior and test |
|---|---|
| `sufficient_check_satisfied_iff` | Available supply covers the demand map; T10 |
| `sufficient_check_unsatisfied_iff` | A disproved sufficiency claim needs exact demand and a shortage; T10's exact observations |
| `upper_bound_shortage_is_indeterminate` | A conservative bound above supply does not decide sufficiency; T9 and T10 |
| `upper_bound_shortage_negation_is_indeterminate` | Negation cannot turn that uncertainty into evidence of shortage; T10 |
| `upper_bound_shortage_has_both_concretizations` | Actual demand could be zero or the upper bound, producing different exact verdicts; T10 |

This is a correspondence for these finite formula operations, not a proof of
the full OSLF calculus or native runtime execution.

## Executable coverage

The ten tests in
[`resource_logic_conformance.rs`](../../rholang-adapter/tests/resource_logic_conformance.rs)
compare the actual native and adapter implementations. They reuse native
signature conversion, canonicalization, demand computation, verification,
resource maps, observations, and formula evaluation.

All ten tests passed on 2026-10-10. The serial test run used one Cargo job,
a 32 GiB hard memory limit, and no swap. Its log is
`target/verification/oslf-resource-logic-conformance-20261010.log`.

| ID | Test name after `native_resource_logic_parity_` | Scope |
|---|---|---|
| T1 | `reuses_the_existing_funding_laws` | Existing generic funding-law harness for both presentations; scalar bounds 0–16, known/unknown demand, supplies −2–18 |
| T2 | `preserves_signature_keys_and_decompositions` | Unit, ground, quote, binary compound, and nested compound signatures |
| T3 | `covers_finite_cost_carrier_grid` | Sends 0–3; signed nesting 1–3; ground, unit, quote, name, and compound carriers; fixed/dynamic stack targets and lengths 1–3; five deploy signatures; zero, exact-bound, surplus, and per-lane-deficient supplies; all formula constructors |
| T4 | `rejects_every_unprovable_reason` | Persistent send/receive, dequotation, dynamic signed authority, missing signature, empty stack, unit stack; each reason; exact/finite/unprovable claims; maximal supplied amount cannot rescue the claim |
| T5 | `authenticates_evidence_kind_amount_lane_and_proof` | Exact promotion, unprovable label, omitted/changed map, changed lane, empty proof, every one-byte proof mutation, and appended proof byte |
| T6 | `recomputes_canonical_program_and_deploy_signature` | Changed demand count or deploy lane rejects; changed ground channel with unchanged demand legitimately reuses evidence |
| T7 | `requires_each_lane_and_preserves_supply_monotonicity` | Two independently signed lanes, send counts 1–3, supply pairs 0–4, and monotone supply increases |
| T8 | `keeps_observation_distinct_from_gross_demand` | Backed transfer changes external reservation, not pre-state available authority |
| T9 | `preserves_modal_uncertainty_and_surface_scopes` | Upper-bound modal uncertainty, wrong location, overlapping spatial scopes, zero spend, and sufficient/deficient upper-bound supply |
| T10 | `preserves_sufficient_evidence_strength` | Bounds 0–16 and supplies 0–18: upper-bound shortage and its negation stay indeterminate; exact shortage is false; sufficient supply is true. A zero-demand exact realization shows why upper-bound shortage cannot prove actual shortage. |

The G tests live in the node's
[`generic_demand_verification_properties` module][native-resource-logic]:

| ID | Existing native test |
|---|---|
| G1 | `generic_exact_claim_authentication_matches_finite_execution` |
| G2 | `generic_funding_tracks_finite_execution_per_surface` |
| G3 | `generic_exact_claim_rechecks_program_and_signature` |
| G4 | `generic_uncertified_provider_rejects_every_exact_claim` |
| G5 | `generic_finite_analysis_cannot_be_relabelled_exact` |
| G6 | `generic_unproved_zero_reservation_is_rejected` |
| G7 | `native_finite_verifier_authenticates_proof_bytes` |

G7 complements T5's complete byte-position mutation grid. The
[scalar MeTTaIL laws](../../formal/rocq/rho_bridge/theories/MettaFundingLawsConformance.v)
separately characterize known finite demand, unknown-demand rejection,
underfunding rejection, monotonicity, and decidability. Those abstract laws
and the existing [conformance harness](../../rholang-adapter/src/conformance.rs)
do not by themselves authenticate an evidence map.

Run the adapter obligations from the MeTTaIL workspace:

```sh
cargo test -p rholang-adapter --test resource_logic_conformance -- --test-threads=1
```

This is a bounded differential grid, not an exhaustive syntax proof or a new
property-testing dependency. It does not cover arbitrary recursive `Par`,
arithmetic overflow at arbitrary nesting depth, live supply provenance,
offered-funded admission, state-bound replay, settlement, or the complete
guest-installation/projection path. Positive exact verification belongs to
the existing generic-provider tests; it is unavailable through the current
native structural producer. A passing parity suite cannot show that a bug
shared by both presentations is absent.

The cross-workspace references below target the campaign's sibling node
worktree, which provides the adapter's host implementation.

[native-resource-logic]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/resource_logic.rs
[native-delta-sigma]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/delta_sigma.rs
[native-oslf]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/oslf.rs
[native-oslf-properties]: ../../../../f1r3node-rust-f1r3lang/rholang/src/rust/interpreter/accounting/oslf/property_tests.rs
[generic-proof]: ../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/GenericDemandVerification.v
[spatial-proof]: ../../../../f1r3node-rust-f1r3lang/formal/rocq/cost_accounted_rho/theories/CAOSLFSpatialModal.v
