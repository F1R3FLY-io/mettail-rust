//! Stage 4 (Ambient In/Out) end-to-end: a GENERATED language's DEPTH-2 NESTED structural non-linear
//! AC rewrites — the Ambient-calculus `InRule` + `OutRule` — fire end-to-end as ONE atomic COMM on
//! the live f1r3node Rholang interpreter, VIA THE SPREAD PATH, GENERALIZING the flat `OpenRule`
//! (`rho_net_ambient_firing`) to depth-2.
//!
//!     InRule  . { n[{in(m,P), ...q}], m[R], ...s } ~> { m[{ n[{P, ...q}], R }], ...s }
//!     OutRule . m[{ n[{out(m,P), ...q}], R, ...s }] ~> { n[{P, ...q}], m[R], ...s }
//!
//! ## The SPREAD path (this file's subject — the dual-path elimination)
//!
//! Every test here drives the DEFAULT `rho_net_match_invocation_from_dovetail_to` (the match-or-replay
//! gate's MATCH branch), NOT the report-path `rho_net_invocation_from_dovetail_to`. So In/Out now ride
//! the SAME in-Rho spread mechanism as OpenRule / AC / native / contextual — one runtime path, not the
//! former dual (report for In/Out; spread for everything else). It composes, in ONE COMM on the
//! reducer:
//!
//!   * an IN-RHO LOCATE: the whole subject is STRUCTURALLY reflected (M-reflect, NOT the report σ) and
//!     the nested-structural-AC match driver walks it, co-installing a per-site MATCH receiver at every
//!     node whose head is a nested rule's LHS root constructor — the bag op `PPar` (bag-rooted
//!     `InRule`) or the wrapper `PAmb` (wrapper-rooted `OutRule`) — over a SITE-KEYED `ac:` carrier the
//!     walk publishes the SUBJECT operand's reflection on (`carrier!(⟦operand⟧, @out)`);
//!   * a DEPTH-2 nested HashBag AC match: the co-installed receiver's operand pattern matches the outer
//!     operand + the NESTED inner ambient `n[{in(m,P), ...q}]` (a `PAmb` whose second argument is a
//!     HashBag) + the plain ambient `m[R]` + the outer soup remainder `...s`; the reducer's
//!     `SpatialMatcher<Par,Par>` recurses into the inner bag in the SAME atomic `consume`;
//!   * a CROSS-LEVEL NON-LINEAR guard: the ambient name `M` occurs one level down (in `in(m,P)`) AND at
//!     the outer level (in `m[R]`), each binding a DISTINCT σ slot; the receiver's `Receive.condition`
//!     `EEq(M_outer, M_inner)` enforces `M ≡ M`, reject-safe (depth-agnostic);
//!   * an IN-RHO NESTED REDUCT: the restructured `m[{ n[{P, ...q}], R }]` is BUILT IN THE RECEIVER BODY
//!     from the in-Rho-bound σ slots (`m`, `n`, `P`, the inner `...q`, `R`), NESTED AC bags included
//!     (rebuilt via the `ac:` carrier + the bound `rest` slot) — NOT the host-computed `RHS[σ]` the
//!     report path delivered as a message value. The operand AND the reduct come from the SPREAD.
//!
//! The concrete `InRule` redex `{ na[{ in(nb, A) }] | nb[B] }` (both cross-level names `nb`) reduces
//! to `{ nb[{ na[{ A }] | B }] }` — the `na` ambient MOVED INTO the `nb` ambient. The mismatched soup
//! `{ na[{ in(nb, A) }] | nc[B] }` (`nb` ≠ `nc`) does NOT fire — the cross-level guard vetoes ON THE
//! REDUCER. The corrupted-σ probes prove the operand AND the nested reduct come from the SPREAD (the
//! subject), not the report σ: a decoy report σ leaves OUT correct.
//!
//! The report path (`structural_ac_contract_call` → the installed `NestedStructuralAcRewrite`
//! σ-receiver) survives only as the fail-closed fallback (reached when the gate defers), like every
//! other family.
#![cfg(feature = "in-out-demo-runtime")]

// Task #11 (extended 2026-07-26): `InOutDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/inoutdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `inoutdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/inout_dovetail_report.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/inoutdemo.rs"]
mod inoutdemo;

use inoutdemo::InOutDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_nested_structural_ac_injection_sites, suggest_rejected_rule_dispositions,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue, RuntimeReflectedSubterm};

/// Reconstruct `InOutDemo`'s augmented `LanguageDef`, plan its Rho-default backend (the nested
/// `InRule`/`OutRule` σ-receivers install alongside the structural constructors), and return the
/// planned backend + its definition fingerprint.
fn inout_demo_backend() -> (PlannedRhoBackend, String) {
    let source = InOutDemoLanguage
        .metadata()
        .definition_source()
        .expect("generated InOutDemoLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("InOutDemoLanguage definition_source must reconstruct as a LanguageDef");

    // Exactly two nested structural-AC firing sites: InRule + OutRule.
    let sites = rho_net_nested_structural_ac_injection_sites(&def);
    assert_eq!(sites.len(), 2, "InOutDemo has two nested structural AC rewrites, got {sites:?}");
    let labels: Vec<&str> = sites.iter().map(|s| s.rule_label.as_str()).collect();
    assert!(labels.contains(&"InRule") && labels.contains(&"OutRule"));
    for site in &sites {
        assert_eq!(site.op, "PPar");
        assert_eq!(site.nonlinear_var, "M");
    }

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("InOutDemo (nested structural non-linear AC In/Out) must flip to the Rho backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// A nullary observation value (e.g. the process leaf `PA` = `A` or the ambient name `Nb` = `nb`).
fn leaf(constructor: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children: Vec::new() }
}

/// An ambient observation value `PAmb(name, body)`.
fn amb(name: &str, body: RuntimeObservationValue) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: "PAmb".to_string(),
        children: vec![leaf(name), body],
    }
}

/// A `PPar` bag observation value (each element multiplicity 1).
fn par_bag(elements: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Bag(elements.into_iter().map(|e| (e, 1)).collect())
}

/// Multiset-structural equality that is ORDER-INDEPENDENT at EVERY `Bag` level (the reducer's HashBag
/// carrier is order-independent, so a nested bag may decode in any element order). Mirrors the intent
/// of `assert_bag_is` but recurses through nested `Bag`s.
fn obs_multiset_eq(a: &RuntimeObservationValue, b: &RuntimeObservationValue) -> bool {
    match (a, b) {
        (RuntimeObservationValue::Bag(xs), RuntimeObservationValue::Bag(ys)) => {
            let xn: usize = xs.iter().map(|(_, c)| *c).sum();
            let yn: usize = ys.iter().map(|(_, c)| *c).sum();
            if xn != yn {
                return false;
            }
            // Greedy multiset match (small bags): every x element pairs with a distinct y element.
            let mut used = vec![false; ys.len()];
            xs.iter().all(|(xv, xc)| {
                (0..*xc).all(|_| {
                    if let Some(idx) = ys
                        .iter()
                        .enumerate()
                        .find(|(i, (yv, yc))| !used[*i] && *yc >= 1 && obs_multiset_eq(xv, yv))
                        .map(|(i, _)| i)
                    {
                        used[idx] = true;
                        true
                    } else {
                        false
                    }
                })
            })
        },
        (
            RuntimeObservationValue::Term { constructor: ca, children: cha },
            RuntimeObservationValue::Term { constructor: cb, children: chb },
        ) => {
            ca == cb
                && cha.len() == chb.len()
                && cha.iter().zip(chb).all(|(x, y)| obs_multiset_eq(x, y))
        },
        _ => a == b,
    }
}

/// Assert `value` is (order-independently, at every nesting depth) the restructured `expected`.
fn assert_obs_eq(value: &RuntimeObservationValue, expected: &RuntimeObservationValue) {
    assert!(
        obs_multiset_eq(value, expected),
        "restructured observation mismatch\n   got: {value:?}\n  want: {expected:?}"
    );
}

/// The restructured `InRule` bag `{ nb[{ na[{ A }] | B }] }` — the `na` ambient moved INTO `nb`.
fn in_reduct() -> RuntimeObservationValue {
    par_bag(vec![amb(
        "Nb",
        par_bag(vec![amb("Na", par_bag(vec![leaf("PA")])), leaf("PB")]),
    )])
}

/// The restructured `OutRule` bag `{ na[{ A }] | nb[B] }` — the `na` ambient moved OUT of `nb`.
fn out_reduct() -> RuntimeObservationValue {
    par_bag(vec![
        amb("Na", par_bag(vec![leaf("PA")])),
        amb("Nb", leaf("PB")),
    ])
}

/// POSITIVE In (empty rest) VIA THE SPREAD: `{ na[{ in(nb, A) }] | nb[B] }` (both cross-level names
/// `nb`) MATCHES + FIRES IN RHO as ONE COMM through the DEFAULT match path, landing the restructured
/// `{ nb[{ na[{ A }] | B }] }` on OUT. Unlike the report path (which reconstructs the operand + the
/// nested reduct from σ), this STRUCTURALLY reflects the WHOLE subject, LOCATES the outer bag by the
/// nested descent, and the co-installed MATCH receiver binds the σ slots from the operand + REBUILDS
/// the nested reduct `nb[{ na[{A}] | B }]` in its body — the operand AND the reduct from the spread.
#[tokio::test]
async fn inoutdemo_in_matches_in_rho_via_the_spread() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = inout_demo_backend();
    assert_eq!(
        InOutDemoLanguage.metadata().definition_fingerprint(),
        Some(fingerprint.as_str()),
        "planned backend fingerprint must equal the generated metadata fingerprint"
    );

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nb[B] }")
        .expect("InOutDemo must parse the InRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    // The DEFAULT match path (NOT the replay branch — the retirement proof for In/Out): it admits the
    // InRule and assembles the in-Rho DEPTH-2 spread-match call.
    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC MATCH path admits InRule and assembles the spread call");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho nested structural-AC match + firing executes on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested InRule MATCH receiver must fire exactly once (got {:?})",
        observation.values
    );
    assert_obs_eq(&observation.values[0], &in_reduct());
}

/// POSITIVE In (with rest) VIA THE SPREAD: `{ na[{ in(nb, A) }] | nb[B] | 0 }` — the residual `0` (a
/// `PZero`, distinct tag) rides the outer remainder `...s` and is spliced back IN THE RECEIVER BODY,
/// so OUT is `{ nb[{ na[{ A }] | B }] | 0 }`. The outer remainder is bound from the operand and
/// re-composed by the in-Rho body — not host-delivered.
#[tokio::test]
async fn inoutdemo_in_splices_the_outer_remainder_via_the_spread() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nb[B] | 0 }")
        .expect("InOutDemo must parse the with-rest InRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC MATCH path admits the with-rest InRule");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho nested structural-AC match + firing executes on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested InRule MATCH receiver must fire exactly once (got {:?})",
        observation.values
    );
    // `{ nb[{ na[{ A }] | B }], 0 }` — the restructured ambient PLUS the spliced outer residual `0`.
    let expected = par_bag(vec![
        amb(
            "Nb",
            par_bag(vec![amb("Na", par_bag(vec![leaf("PA")])), leaf("PB")]),
        ),
        leaf("PZero"),
    ]);
    assert_obs_eq(&observation.values[0], &expected);
}

/// POSITIVE Out VIA THE SPREAD: `nb[{ na[{ out(nb, A) }] | B }]` (the `out` target `nb` = the ROOT
/// ambient `nb`) MATCHES + FIRES IN RHO through the DEFAULT match path, landing the restructured
/// `{ na[{ A }] | nb[B] }` on OUT — the `na` ambient MOVED OUT of `nb`, alongside the residual `nb[B]`.
/// This exercises the WRAPPER-rooted LOCATE: the located node is a `PAmb(M, {…})` (a constructor
/// wrapping the bag), reflected WHOLE to a tagged `EList` the OutRule MATCH receiver's top pattern
/// matches; its body REBUILDS the two nested reducts `na[{A}]` and `nb[B]` from the bound σ slots.
#[tokio::test]
async fn inoutdemo_out_matches_in_rho_via_the_spread() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("nb[{ na[{ out(nb, A) }] | B }]")
        .expect("InOutDemo must parse the OutRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC MATCH path admits OutRule and assembles the spread call");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho nested structural-AC match + firing executes on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested OutRule MATCH receiver must fire exactly once (got {:?})",
        observation.values
    );
    assert_obs_eq(&observation.values[0], &out_reduct());
}

/// NEGATIVE In (mismatched cross-level names) VIA THE SPREAD, reject-safe: `{ na[{ in(nb, A) }] | nc[B] }`
/// — the `in` target `nb` ≠ the sibling ambient `nc`. The match path ASSEMBLES a call (the reflection +
/// LOCATE + co-install succeed exactly as the positive case — the mismatched names change only the
/// ground bound-var subterms, not the shape), so it returns `Ok`; the veto happens ON THE REDUCER,
/// where the co-installed MATCH receiver's cross-level `Receive.condition` `EEq(M_outer, M_inner)`
/// binds `M_inner = nb`, `M_outer = nc`, evaluates to `false`, and the reducer NEVER commits the COMM:
/// nothing lands on OUT. `in` cannot enter a NON-matching ambient — the guard makes it decidable in Rho.
#[tokio::test]
async fn inoutdemo_in_mismatched_name_vetoes_on_the_spread() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nc[B] }")
        .expect("InOutDemo must parse the mismatched-name InRule soup");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");

    // No InRule fired (the Dovetail matcher's cross-level guard already vetoed upstream), so `fired` is
    // empty and the match gate admits the (no-op-firing) path; the co-installed spread receiver then
    // decides on the reducer.
    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the match path assembles a call; the guard vetoes on the reducer, not at build");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho match call executes (the guard decides whether it commits)");
    assert_eq!(
        observation.observed_count(),
        0,
        "the cross-level `Receive.condition` vetoes a mismatched-M operand on the reducer (got {:?})",
        observation.values
    );
}

/// DECISIVE PROBE (In) — the operand BAG AND the NESTED reduct are re-sourced from the SPREAD of the
/// reflected subject, NOT the host report σ. The nested analogue of AmbDemo's
/// `s_ac_structural_bag_is_produced_by_the_spread_not_the_report`.
///
/// We take a real, complete report for `{ na[{ in(nb, A) }] | nb[B] }` and CORRUPT its σ (the ambient
/// names `N`/`M`, the processes `P`/`R`, and the residual bags `rest1`/`rest2` — the SAME σ the
/// report-path `structural_ac_contract_call` reconstructs the operand + the nested reduct from) to a
/// decoy `PZero`, leaving the rule label (`InRule`) valid so the in-Rho match GATE still admits. The
/// DEFAULT `rho_net_match_invocation_from_dovetail_to` STRUCTURALLY reflects the WHOLE subject
/// (M-reflect, NOT the report σ); the match driver LOCATES the outer bag, publishes its reflection on
/// the SITE-KEYED `ac:` carrier from the SUBJECT's ground term, and the co-installed MATCH receiver
/// binds the σ slots ON the reducer and REBUILDS `nb[{ na[{A}] | B }]` in its body.
///
/// Because the operand AND the nested reduct are built from `term`, not the corrupted σ, OUT is
/// `{ nb[{ na[{ A }] | B }] }` (with the REAL `A`/`B`). A report-σ arm would have rebuilt a
/// `PZero`-laden garbage term. So a positive, correct OUT is non-vacuous evidence the operand + reduct
/// came from the spread, not the report — In/Out matching is a genuine in-Rho replacement, not a
/// σ-replay duplicate.
#[tokio::test]
async fn s_ac_nested_in_bag_is_produced_by_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nb[B] }")
        .expect("InOutDemo must parse the InRule redex");
    let mut report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the InRule must surface at least one firing justification"
    );

    // Deliberately WRONG σ: a report-σ nested-AC arm would rebuild the operand + reduct from these and
    // fire a `PZero`-laden term. The rule label (`InRule`) stays valid so the in-Rho match gate admits
    // the path; ONLY the σ (the operand + reduct source) is corrupted.
    let decoy = RuntimeReflectedSubterm { constructor: "PZero".to_string(), children: Vec::new() };
    let decoy_bag =
        RuntimeReflectedSubterm { constructor: "PPar".to_string(), children: Vec::new() };
    for justification in &mut report.rewrite_justifications {
        assert_eq!(justification.rule_label, "InRule", "the fired rule label stays valid");
        justification.sigma = vec![
            ("N".to_string(), decoy.clone()),
            ("M".to_string(), decoy.clone()),
            ("P".to_string(), decoy.clone()),
            ("R".to_string(), decoy.clone()),
            ("rest1".to_string(), decoy_bag.clone()),
            ("rest2".to_string(), decoy_bag.clone()),
        ];
    }

    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the MATCH path admits InRule despite the corrupted report σ");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho nested structural-AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "the located InRule redex fires exactly once (got {:?})",
        observation.values
    );
    // OUT is `{ nb[{ na[{ A }] | B }] }` from the SPREAD subject — never the corrupted σ's PZero garbage.
    assert_obs_eq(&observation.values[0], &in_reduct());
    assert_ne!(
        &observation.values[0],
        &par_bag(vec![leaf("PZero")]),
        "the operand + nested reduct were re-sourced from the spread, not the corrupted report σ"
    );
}

/// DECISIVE PROBE (Out) — the WRAPPER-rooted operand AND the two nested reducts are re-sourced from the
/// SPREAD, NOT the host report σ. The `OutRule` twin of the In probe: we CORRUPT the report σ of
/// `nb[{ na[{ out(nb, A) }] | B }]` to a decoy, leaving the `OutRule` label valid so the gate admits.
/// The match driver STRUCTURALLY reflects the WHOLE subject, LOCATES the `PAmb` wrapper, reflects it
/// WHOLE onto the site-keyed `ac:` carrier, and the co-installed MATCH receiver binds the σ slots ON
/// the reducer and REBUILDS `na[{A}]` + `nb[B]` in its body — so OUT is STILL `{ na[{ A }] | nb[B] }`,
/// never the decoy.
#[tokio::test]
async fn s_ac_nested_out_bag_is_produced_by_the_spread_not_the_report() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("nb[{ na[{ out(nb, A) }] | B }]")
        .expect("InOutDemo must parse the OutRule redex");
    let mut report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the OutRule must surface at least one firing justification"
    );

    let decoy = RuntimeReflectedSubterm { constructor: "PZero".to_string(), children: Vec::new() };
    let decoy_bag =
        RuntimeReflectedSubterm { constructor: "PPar".to_string(), children: Vec::new() };
    for justification in &mut report.rewrite_justifications {
        assert_eq!(justification.rule_label, "OutRule", "the fired rule label stays valid");
        justification.sigma = vec![
            ("N".to_string(), decoy.clone()),
            ("M".to_string(), decoy.clone()),
            ("P".to_string(), decoy.clone()),
            ("R".to_string(), decoy.clone()),
            ("rest1".to_string(), decoy_bag.clone()),
            ("rest2".to_string(), decoy_bag.clone()),
        ];
    }

    let invocation =
        InOutDemoLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the MATCH path admits OutRule despite the corrupted report σ");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the in-Rho nested structural-AC match + firing executes on the reducer");

    assert_eq!(
        observation.observed_count(),
        1,
        "the located OutRule redex fires exactly once (got {:?})",
        observation.values
    );
    // OUT is `{ na[{ A }] | nb[B] }` from the SPREAD subject — never the corrupted σ's PZero garbage.
    assert_obs_eq(&observation.values[0], &out_reduct());
    assert_ne!(
        &observation.values[0],
        &par_bag(vec![leaf("PZero")]),
        "the wrapper operand + nested reducts were re-sourced from the spread, not the corrupted report σ"
    );
}
