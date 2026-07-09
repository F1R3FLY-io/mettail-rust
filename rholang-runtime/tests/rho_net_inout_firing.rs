//! Stage 4 (Ambient In/Out) end-to-end: a GENERATED language's DEPTH-2 NESTED structural non-linear
//! AC rewrites — the Ambient-calculus `InRule` + `OutRule` — fire end-to-end as ONE atomic COMM on
//! the live f1r3node Rholang interpreter, GENERALIZING the flat `OpenRule` (`rho_net_ambient_firing`).
//!
//!     InRule  . { n[{in(m,P), ...q}], m[R], ...s } ~> { m[{ n[{P, ...q}], R }], ...s }
//!     OutRule . m[{ n[{out(m,P), ...q}], R, ...s }] ~> { n[{P, ...q}], m[R], ...s }
//!
//! It composes, in ONE COMM on the reducer:
//!
//!   * a DEPTH-2 nested HashBag AC match: the outer operand bag matches the NESTED ambient
//!     `n[{in(m,P), ...q}]` (a `PAmb` whose second argument is itself a HashBag) + the plain ambient
//!     `m[R]` + the outer soup remainder `...s`; the reducer's `SpatialMatcher<Par,Par>` recurses into
//!     the inner bag in the SAME atomic `consume` (a HashBag ARGUMENT reflects to the same soup
//!     carrier as the top bag);
//!   * a CROSS-LEVEL NON-LINEAR guard: the ambient name `M` occurs one level down (in `in(m,P)`) AND
//!     at the outer level (in `m[R]`), so each binds a DISTINCT σ slot and the installed receiver's
//!     `Receive.condition` `EEq(M_outer, M_inner)` enforces `M ≡ M`, reject-safe (depth-agnostic — the
//!     reducer flattens every free var at every depth into ONE De Bruijn frame);
//!   * a NESTED reduct: the restructured `m[{ n[{P, ...q}], R }]` is the host-computed contractum
//!     `RHS[σ]`, reconstructed from σ by walking the reduct template and delivered as the single
//!     host-σ-sourced value; the receiver body splices `@"ac:PPar"!(reduct) | ...s`.
//!
//! The concrete `InRule` redex `{ na[{ in(nb, A) }] | nb[B] }` (both cross-level names `nb`) reduces
//! to `{ nb[{ na[{ A }] | B }] }` — the `na` ambient MOVED INTO the `nb` ambient — non-vacuous
//! evidence the `InRule` fired as ONE COMM with the σ Dovetail computed. The mismatched soup
//! `{ na[{ in(nb, A) }] | nc[B] }` (`nb` ≠ `nc`) does NOT fire — the cross-level guard vetoes.
#![cfg(feature = "in-out-demo-runtime")]

use mettail_languages::inoutdemo::InOutDemoLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    rho_net_nested_structural_ac_injection_sites, structural_ac_contract_call,
    suggest_rejected_rule_dispositions, CollectionType, GroundTerm, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::{Language, RuntimeObservationValue};

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

/// POSITIVE In (empty rest): `{ na[{ in(nb, A) }] | nb[B] }` (both cross-level names `nb`) fires as
/// ONE COMM, landing the restructured `{ nb[{ na[{ A }] | B }] }` on OUT.
#[tokio::test]
async fn inoutdemo_in_fires_as_a_comm_on_the_reducer() {
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
    let invocation =
        InOutDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC σ-injection must assemble from a complete report");
    assert_eq!(invocation.out_channel, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the nested structural-AC injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested InRule receiver must fire exactly once (got {:?})",
        observation.values
    );
    // The restructured bag `{ nb[{ na[{ A }] | B }] }` — the `na` ambient moved INTO the `nb` ambient.
    let expected = par_bag(vec![amb(
        "Nb",
        par_bag(vec![amb("Na", par_bag(vec![leaf("PA")])), leaf("PB")]),
    )]);
    assert_obs_eq(&observation.values[0], &expected);
}

/// POSITIVE In (with rest): `{ na[{ in(nb, A) }] | nb[B] | 0 }` — the residual `0` (a `PZero`, distinct
/// tag) rides the outer remainder `...s` and is spliced back, so OUT is `{ nb[{ na[{ A }] | B }] | 0 }`.
#[tokio::test]
async fn inoutdemo_in_splices_the_outer_remainder() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nb[B] | 0 }")
        .expect("InOutDemo must parse the with-rest InRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    let invocation =
        InOutDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC σ-injection must assemble from a complete report");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the nested structural-AC injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested InRule receiver must fire exactly once (got {:?})",
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

/// NEGATIVE In (mismatched cross-level names): `{ na[{ in(nb, A) }] | nc[B] }` — the `in` target `nb`
/// ≠ the sibling ambient `nc`. The NON-LINEAR AC guard VETOES at the Dovetail matcher: the nested
/// native rule finds NO pairing (`M ≡ M` is unsatisfiable — `nb` and `nc` are distinct e-classes), so
/// the report carries NO InRule firing and the σ-injection has nothing to inject.
#[test]
fn inoutdemo_in_mismatched_name_does_not_fire() {
    mettail_runtime::clear_var_cache();

    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nc[B] }")
        .expect("InOutDemo must parse the mismatched-name InRule soup");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");

    assert!(
        report.is_complete(),
        "the mismatched-name soup is a normal form (Complete), got {:?}",
        report.completeness
    );
    assert!(
        report
            .rewrite_justifications
            .iter()
            .all(|j| j.rule_label != "InRule"),
        "the cross-level guard must VETO the mismatched-name soup — no InRule firing (got {:?})",
        report.rewrite_justifications
    );
    assert!(
        InOutDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .is_err(),
        "no InRule firing ⇒ the σ-injection has nothing to inject (nothing lands on OUT)"
    );
}

/// REDUCER-LEVEL guard veto (the `check_commit` belt-and-suspenders) — the DECISIVE probe that the
/// cross-level non-linear `Receive.condition` `EEq(M_outer, M_inner)` is REAL on the reducer, not just
/// at the Dovetail matcher. We hand-deliver a MISMATCHED operand `{ na[{ in(nb, A) }] | nc[B] }` (the
/// inner `in`-target `nb` ≠ the sibling ambient `nc`) DIRECTLY to the installed InRule receiver via
/// `structural_ac_contract_call` (bypassing the Dovetail matcher's upstream veto entirely), with an
/// arbitrary reduct. The reducer's spatial matcher binds `M_inner = nb` and `M_outer = nc`, the
/// `where`-clause `EEq(nb, nc)` evaluates to `false`, and the reducer NEVER commits the COMM: nothing
/// lands on OUT. `in` cannot enter a NON-matching ambient — the guard makes it decidable in Rho.
#[tokio::test]
async fn inoutdemo_in_reducer_guard_vetoes_mismatched_m() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();
    let fingerprint = InOutDemoLanguage
        .metadata()
        .definition_fingerprint()
        .expect("InOutDemo has a definition fingerprint");
    let source = InOutDemoLanguage
        .metadata()
        .definition_source()
        .expect("InOutDemo exposes its definition_source");
    let def = reconstruct_language_def(source).expect("InOutDemo reconstructs");
    let sites = rho_net_nested_structural_ac_injection_sites(&def);
    let in_channel = &sites
        .iter()
        .find(|s| s.rule_label == "InRule")
        .expect("the InRule firing site is installed")
        .channel;

    let nullary = GroundTerm::nullary;
    let bag = |elements| GroundTerm::collection(CollectionType::HashBag, "PPar", elements);
    // A MISMATCHED operand: `{ na[{ in(nb, A) }] | nc[B] }` — the inner `in`-target `nb` ≠ the sibling
    // ambient `nc`, so `M_inner = nb`, `M_outer = nc` — the guard `EEq(M_outer, M_inner)` is FALSE.
    let operand = bag(vec![
        GroundTerm::new(
            "PAmb",
            vec![
                nullary("Na"),
                bag(vec![GroundTerm::new("PIn", vec![nullary("Nb"), nullary("PA")])]),
            ],
        ),
        GroundTerm::new("PAmb", vec![nullary("Nc"), nullary("PB")]),
    ]);
    // Any reduct — the guard vetoes BEFORE the body runs, so its value never lands.
    let reduct = GroundTerm::new("PAmb", vec![nullary("Nb"), bag(vec![nullary("PZero")])]);
    let call = structural_ac_contract_call(in_channel, &operand, &[reduct], fingerprint, "OUT");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&call, "OUT")
        .await
        .expect("the in-Rho call executes (the guard decides whether it commits)");
    assert_eq!(
        observation.observed_count(),
        0,
        "the cross-level `Receive.condition` vetoes a mismatched-M operand on the reducer (got {:?})",
        observation.values
    );
}

/// POSITIVE Out: `nb[{ na[{ out(nb, A) }] | B }]` (the `out` target `nb` = the ROOT ambient `nb`)
/// fires as ONE COMM, landing the restructured `{ na[{ A }] | nb[B] }` on OUT — the `na` ambient
/// (carrying `A`) MOVED OUT of the `nb` ambient, alongside the residual `nb[B]`. This exercises the
/// WRAPPER-rooted entry shape: the operand is a `PAmb(M, {…})` (a constructor wrapping the bag, not a
/// bare bag), reflected to a tagged `EList` the OutRule receiver's top pattern matches.
#[tokio::test]
async fn inoutdemo_out_fires_as_a_comm_on_the_reducer() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = inout_demo_backend();

    let term = InOutDemoLanguage
        .parse_term("nb[{ na[{ out(nb, A) }] | B }]")
        .expect("InOutDemo must parse the OutRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile");
    let invocation =
        InOutDemoLanguage::rho_net_invocation_from_dovetail_to(term.as_ref(), &report, "OUT")
            .expect("the nested structural-AC σ-injection must assemble the OutRule firing");

    let observation = backend
        .run_rho_net_with_call_and_observe_runtime_values(&invocation.call, &invocation.out_channel)
        .await
        .expect("the nested structural-AC injection must execute on the Rho runtime");

    assert_eq!(
        observation.observed_count(),
        1,
        "the nested OutRule receiver must fire exactly once (got {:?})",
        observation.values
    );
    // The restructured bag `{ na[{ A }] | nb[B] }` — the `na` ambient moved OUT of `nb`.
    let expected = par_bag(vec![
        amb("Na", par_bag(vec![leaf("PA")])),
        amb("Nb", leaf("PB")),
    ]);
    assert_obs_eq(&observation.values[0], &expected);
}
