//! A-S5.2 (leg 3) end-to-end: the PRODUCTION `Lambda` language driven to quiescence FULLY
//! IN-RHO by the generated `^drive` receiver family — matching, β firing (through the
//! existing σ ABI + the installed subst TRS), contractum re-drive, congruence descent with
//! the post-join re-check, and the binder arm all execute as COMMs on the live f1r3node
//! reducer; the host seeds once (`rho_net_drive_invocation_to`) and reads the four
//! observation channels back ([`DriveObservationChannels`]).
//!
//! THE LIFTED BOUNDARY: pre-A-S5.2, a REAL-Lambda subject with n ≥ 2 head-`App` candidate
//! sites failed closed at `NestedEntryMultiSite`
//! (`a_s5c_production_language_gates.rs::lambda_multi_app_subjects_fail_closed_nested_entry_multi_site`);
//! the single-root drive admission (`lambda_single_root_drive_admits_every_chain_length`,
//! the A-S5.2 baseline) said every chain length SERIALIZES. This suite drives those chains
//! (n ∈ 2..=8) TO NORMAL FORM in-Rho — the driver's per-node outermost-first Match arms
//! replace the locate-all co-install entirely, so the multi-site gate has nothing to trip.
//!
//! Every driven test runs the ALWAYS-ON cross-check ([`drive_cross_check`], plan v2 §4.7):
//! host NF-scan over the decoded resting term (the static mirror of the Beta redex arm —
//! no `App(^lambda(_), _)` present; Lambda needs no flattening), ledger consistency
//! (`fired ≥ 1 ⟺ the subject had a redex`), and empty typed error/fuel channels — plus the
//! AM-5 test-tier replay: the fired multiset is replayed host-side (greedy valid order;
//! Lambda is confluent, so any valid order reaches the unique NF) and must reproduce the
//! observed resting term.
#![cfg(feature = "lambda-runtime")]

use mettail_languages::lambda::LambdaLanguage;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    reflect_ground_term_par, rho_net_drive_call_par_with_fuel, suggest_rejected_rule_dispositions,
    GroundTerm, RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    binder_apply_redex_present, drive_cross_check, DriveCrossCheckError, DriveObservationChannels,
    PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};

/// Reconstruct the PRODUCTION Lambda's augmented `LanguageDef` from the generated
/// metadata's `definition_source()` and plan its Rho-default backend — the SAME
/// derivation `rho_net_drive_invocation_to`'s memoized artifacts use, so the installed
/// program (β seed + subst TRS + the A-S5.2 `^drive` receiver family) and the seed's
/// reflected tags share one fingerprint.
fn lambda_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("LambdaLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("production Lambda must plan its Rho-default backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

// ── decoded-observation builders ───────────────────────────────────────────────────────
fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}
fn onullary(constructor: &str) -> RuntimeObservationValue {
    oterm(constructor, Vec::new())
}
/// The decoded Peano numeral `S^n(Z)`.
fn opeano(n: usize) -> RuntimeObservationValue {
    let mut peano = onullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..n {
        peano = oterm(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    peano
}
/// The decoded de-Bruijn bound-variable leaf `^bound(S^n(Z))`.
fn obound(n: usize) -> RuntimeObservationValue {
    oterm(BOUND_VAR_REFLECT_LABEL, vec![opeano(n)])
}
fn olambda(body: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm(LAMBDA_REFLECT_LABEL, vec![body])
}
fn oapp(fun: RuntimeObservationValue, arg: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm("App", vec![fun, arg])
}
/// The decoded identity `λ.0`.
fn oid() -> RuntimeObservationValue {
    olambda(obound(0))
}
/// The decoded `K = λ.λ.1` — the α-erased image of `lam a. lam b. a`.
fn okonst() -> RuntimeObservationValue {
    olambda(olambda(obound(1)))
}

// ── reflected-term (GroundTerm) builders, for the direct-seed subjects ─────────────────
fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = g_node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    g_node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}
fn g_lambda(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}

// ── the AM-5 host replay: a de-Bruijn β reducer over decoded observations ──────────────
//
// The host mirror of `DeBruijnSubstTRS.v`'s `oshift`/`osubst`/`odbeta` over the DECODED
// observation shape, used to REPLAY the fired multiset: `get_data` returns an unordered
// multiset (no ordinal is added to the driver — AM-5), so replay is
// search-for-a-valid-order; Lambda is CONFLUENT, so the greedy leftmost-outermost order is
// a valid order and must reach the unique NF.

fn peano_value(value: &RuntimeObservationValue) -> usize {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_ZERO_REFLECT_LABEL && children.is_empty() =>
        {
            0
        },
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_SUCC_REFLECT_LABEL && children.len() == 1 =>
        {
            1 + peano_value(&children[0])
        },
        other => panic!("not a decoded Peano numeral: {other:?}"),
    }
}

/// `oshift c t`: lift every free index ≥ `c` by one (cutoff increments under a binder).
fn host_shift(c: usize, term: &RuntimeObservationValue) -> RuntimeObservationValue {
    match term {
        RuntimeObservationValue::Term { constructor, children } => match constructor.as_str() {
            BOUND_VAR_REFLECT_LABEL => {
                let n = peano_value(&children[0]);
                obound(if n < c { n } else { n + 1 })
            },
            LAMBDA_REFLECT_LABEL => olambda(host_shift(c + 1, &children[0])),
            FREE_VAR_REFLECT_LABEL => term.clone(),
            _ => oterm(constructor, children.iter().map(|child| host_shift(c, child)).collect()),
        },
        other => other.clone(),
    }
}

/// `osubst j a t` — capture-avoiding de-Bruijn substitution `t[a/j]`.
fn host_subst(
    j: usize,
    a: &RuntimeObservationValue,
    term: &RuntimeObservationValue,
) -> RuntimeObservationValue {
    match term {
        RuntimeObservationValue::Term { constructor, children } => match constructor.as_str() {
            BOUND_VAR_REFLECT_LABEL => {
                let n = peano_value(&children[0]);
                match n.cmp(&j) {
                    std::cmp::Ordering::Equal => {
                        // `oshiftk j a`.
                        let mut shifted = a.clone();
                        for _ in 0..j {
                            shifted = host_shift(0, &shifted);
                        }
                        shifted
                    },
                    std::cmp::Ordering::Greater => obound(n - 1),
                    std::cmp::Ordering::Less => term.clone(),
                }
            },
            LAMBDA_REFLECT_LABEL => olambda(host_subst(j + 1, a, &children[0])),
            FREE_VAR_REFLECT_LABEL => term.clone(),
            _ => oterm(
                constructor,
                children
                    .iter()
                    .map(|child| host_subst(j, a, child))
                    .collect(),
            ),
        },
        other => other.clone(),
    }
}

/// One leftmost-outermost β step, or `None` on a normal form.
fn host_beta_step(term: &RuntimeObservationValue) -> Option<RuntimeObservationValue> {
    if let RuntimeObservationValue::Term { constructor, children } = term {
        if constructor == "App" {
            if let RuntimeObservationValue::Term {
                constructor: head,
                children: head_children,
            } = &children[0]
            {
                if head == LAMBDA_REFLECT_LABEL {
                    return Some(host_subst(0, &children[1], &head_children[0]));
                }
            }
        }
        for (index, child) in children.iter().enumerate() {
            if let Some(reduced) = host_beta_step(child) {
                let mut next = children.clone();
                next[index] = reduced;
                return Some(oterm(constructor, next));
            }
        }
    }
    None
}

/// AM-5 replay: the fired multiset (all `"Beta"` for Lambda) replayed greedily from the
/// decoded initial subject — exactly `firings` β steps must exist, and the result must be
/// the observed resting term (assert at the call sites).
fn host_greedy_replay(
    subject: &RuntimeObservationValue,
    firings: usize,
) -> RuntimeObservationValue {
    let mut term = subject.clone();
    for step in 0..firings {
        term = host_beta_step(&term).unwrap_or_else(|| {
            panic!("replay step {step}: the term is already normal but the ledger fired more")
        });
    }
    assert!(
        host_beta_step(&term).is_none(),
        "replay consumed the fired multiset but the result still has a redex"
    );
    term
}

// ── shared drive runner ────────────────────────────────────────────────────────────────

/// Drive one PARSED production-Lambda subject through the generated seed invocation,
/// returning the observation set and the channel names.
async fn drive_parsed(
    backend: &PlannedRhoBackend,
    source: &str,
) -> (mettail_rholang_runtime::DriveObservationSet, DriveObservationChannels) {
    let term = LambdaLanguage
        .parse_term(source)
        .unwrap_or_else(|err| panic!("production Lambda must parse {source:?}: {err:?}"));
    let invocation = LambdaLanguage::rho_net_drive_invocation_to(term.as_ref(), "OUT")
        .expect("production Lambda is drive-admitted (A-S5.2)");
    let channels = DriveObservationChannels::from_invocation(&invocation);
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&invocation.call, &channels)
        .await
        .expect("the drive seed runs to quiescence on the reducer");
    (set, channels)
}

/// The Lambda NF-scan: `true` iff a `App(^lambda(_), _)` node is present.
fn lambda_redex_scan(value: &RuntimeObservationValue) -> bool {
    binder_apply_redex_present("App", value)
}

/// Assert the always-on cross-check is green plus the AM-5 replay reproduces the observed
/// resting term.
fn assert_green_drive(
    set: &mettail_rholang_runtime::DriveObservationSet,
    channels: &DriveObservationChannels,
    subject: &RuntimeObservationValue,
    expected_firings: usize,
) {
    drive_cross_check(
        set,
        channels,
        expected_firings > 0,
        mettail_rholang_codegen::DRIVE_DEFAULT_FUEL,
        &lambda_redex_scan,
    )
    .expect("the always-on drive cross-check is green");
    let fired = set
        .fired_labels()
        .expect("every ledger datum is a GString rule label");
    assert_eq!(fired.len(), expected_firings, "the ledger records every firing exactly once");
    assert!(
        fired.iter().all(|label| label == "Beta"),
        "production Lambda's only firing rule is Beta: {fired:?}"
    );
    // AM-5 replay: greedy valid order over the fired multiset reproduces the observed NF.
    assert_eq!(
        &host_greedy_replay(subject, expected_firings),
        &set.out_values[0],
        "the fired-multiset replay reproduces the observed resting term"
    );
}

// ── (1) single β to NF ─────────────────────────────────────────────────────────────────

/// One β redex `(λx.x) K` drives to `K` fully in-Rho: the driver's Beta arm matches at the
/// root, fires through the σ ABI (the installed β SEED + subst TRS compute the reduct),
/// and the re-driven contractum quiesces through the binder arm.
#[tokio::test]
async fn single_beta_drives_to_nf_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = lambda_backend();
    let (set, channels) = drive_parsed(&backend, "(lam x. x, lam a. lam b. a)").await;

    assert_eq!(
        set.out_values,
        vec![okonst()],
        "(λx.x) K must rest at K = λ.λ.1 — the β fired and the contractum re-drove to NF"
    );
    let subject = oapp(oid(), okonst());
    assert_green_drive(&set, &channels, &subject, 1);
}

// ── (2) THE chain ladder n ∈ 2..=8 (the lifted NestedEntryMultiSite boundary) ──────────

/// Arg-position identity chains `(λx.x, (λx.x, … (λx.x, K)…))` — EVERY level is a
/// head-`App` candidate site, exactly the multi-candidate shape the pre-A-S5.2 locate-all
/// failed closed on at n ≥ 2 (`NestedEntryMultiSite`). The driver reduces each chain to
/// its unique NF `K` with exactly n firings — the boundary is LIFTED.
#[tokio::test]
async fn identity_chains_2_to_8_drive_to_nf_in_rho() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = lambda_backend();
    for n in 2..=8usize {
        let mut source = "lam a. lam b. a".to_string();
        let mut subject = okonst();
        for _ in 0..n {
            source = format!("(lam x. x, {source})");
            subject = oapp(oid(), subject);
        }
        let (set, channels) = drive_parsed(&backend, &source).await;
        assert_eq!(
            set.out_values,
            vec![okonst()],
            "the n = {n} identity chain rests at K (fully in-Rho)"
        );
        assert_green_drive(&set, &channels, &subject, n);
    }
}

/// Fun-position spines `((…((λx.x, λz.z), λz.z)…), λz.z)` — only the INNERMOST node is an
/// immediate redex; every outer `App` must DESCEND, join its children's NFs, and detect
/// the redex its child normalization ENABLED via the inline post-join re-check (n − 1
/// re-checks along the spine). Rests at `λ.0` with exactly n firings.
#[tokio::test]
async fn fun_position_spines_2_to_8_exercise_the_post_join_recheck() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = lambda_backend();
    for n in 2..=8usize {
        let mut source = "(lam x. x, lam z. z)".to_string();
        let mut subject = oapp(oid(), oid());
        for _ in 1..n {
            source = format!("({source}, lam z. z)");
            subject = oapp(subject, oid());
        }
        let (set, channels) = drive_parsed(&backend, &source).await;
        assert_eq!(
            set.out_values,
            vec![oid()],
            "the n = {n} fun-position spine rests at λ.0 (descent + post-join re-checks)"
        );
        assert_green_drive(&set, &channels, &subject, n);
    }
}

// ── (3) an under-binder redex (the LamCong subsumption via the binder arm) ─────────────

/// `λy.((λx.x) y)` — the redex sits UNDER the binder: the driver's binder arm descends the
/// body (the recorded `LamCong` congruence exemption's closure, carried by the driver per
/// A-S5.1 §1.3/F14), fires it, and rewraps. Rests at `λ.0`.
#[tokio::test]
async fn under_binder_redex_reduces_via_the_binder_arm() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = lambda_backend();
    let (set, channels) = drive_parsed(&backend, "lam y. (lam x. x, y)").await;

    assert_eq!(
        set.out_values,
        vec![oid()],
        "λy.((λx.x) y) must rest at λ.0 — the binder arm reduced INSIDE the lambda body"
    );
    let subject = olambda(oapp(oid(), obound(0)));
    assert_green_drive(&set, &channels, &subject, 1);
}

// ── (4) a normal form: zero firings, empty ledger, NF-scan Ok ──────────────────────────

/// `λx.x` is already normal: the drive descends (binder arm), fires NOTHING (empty
/// ledger), and rests the subject itself — `fired ≥ 1 ⟺ subject had a redex` holds in the
/// zero direction.
#[tokio::test]
async fn normal_form_drives_with_zero_firings() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = lambda_backend();
    let (set, channels) = drive_parsed(&backend, "lam x. x").await;

    assert_eq!(set.out_values, vec![oid()], "a normal form rests unchanged");
    assert!(set.fired_data.is_empty(), "no firing occurred — the ledger is EMPTY");
    assert_green_drive(&set, &channels, &oid(), 0);
}

// ── (5) fuel exhaustion: Ω under a small per-path bound ────────────────────────────────

/// `Ω = (λx.(x x))(λx.(x x))` diverges; a small seed fuel (3) exhausts: exactly `fuel`
/// firings are ledgered, the typed `^drive-fuel` datum carries the stuck redex node (Ω
/// itself), OUT stays EMPTY (exhaustion never claims an NF —
/// `fuel_exhaustion_never_wrong`), and the host cross-check error names BOTH the per-path
/// bound AND the global fired count (F10/AM-5 wording).
#[tokio::test]
async fn omega_exhausts_the_per_path_fuel_with_the_typed_datum() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_backend();

    // Ω, built as a direct reflected seed (the generated invocation pins fuel at the
    // production default; the explicit-fuel seed surface exists exactly for this probe).
    let omega_half = g_lambda(g_node("App", vec![g_bound(0), g_bound(0)]));
    let omega = g_node("App", vec![omega_half.clone(), omega_half]);
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&omega, &fingerprint),
        3,
        "OUT",
    );
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the Ω drive terminates BY FUEL on the reducer");

    // Exactly `fuel` firings along the single causal chain, then the typed datum.
    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["Beta".to_string(); 3],
        "Ω fires exactly per-path-fuel = 3 times before exhaustion"
    );
    assert_eq!(set.fuel_data.len(), 1, "exactly one typed exhaustion datum rests");
    let omega_decoded =
        oapp(olambda(oapp(obound(0), obound(0))), olambda(oapp(obound(0), obound(0))));
    assert_eq!(
        mettail_rholang_runtime::par_as_runtime_observation_value(&set.fuel_data[0]),
        Some(omega_decoded),
        "the exhaustion datum is the stuck redex node (Ω) — typed, never an NF claim"
    );
    assert!(
        set.out_values.is_empty(),
        "exhaustion NEVER claims a visible NF (fuel_exhaustion_never_wrong)"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head — the err channel stays empty");

    // The host error names BOTH bounds: the per-path fuel AND the global fired count.
    let violation = drive_cross_check(&set, &channels, true, 3, &lambda_redex_scan)
        .expect_err("fuel exhaustion must surface as the typed cross-check error");
    match &violation {
        DriveCrossCheckError::FuelChannel {
            channel,
            count,
            per_path_fuel,
            global_fired,
        } => {
            assert_eq!(channel, &channels.fuel, "the error names the fuel channel");
            assert_eq!(*count, 1);
            assert_eq!(*per_path_fuel, 3, "the error carries the per-path bound");
            assert_eq!(*global_fired, 3, "the error carries the ledger's global fired count");
        },
        other => panic!("expected the FuelChannel violation, got {other:?}"),
    }
    let rendered = violation.to_string();
    assert!(
        rendered.contains("per-path bound of 3") && rendered.contains("3 firing(s) globally"),
        "the rendered error names the per-path bound AND the global fired count: {rendered}"
    );
}

// ── (6) the corrupted-σ probe (family discipline) ──────────────────────────────────────

/// The PS value carrier's σ IS the seeded subject payload (per-candidate private datum —
/// plan v2 §5.1), so the family-discipline probe corrupts a σ slot by SWAPPING the App
/// children of the reflected subject: the true subject `(λx.x) K` rests at `K = λ.λ.1`;
/// the corrupted payload `K (λx.x)` must NOT produce the true NF — the observed resting
/// term is exactly the corrupted subject's NF `λ.λ.0`, loudly distinct. The firing output
/// is a function of the DELIVERED σ payload and nothing else (no host residue can sneak
/// the true answer back in).
#[tokio::test]
async fn corrupted_sigma_payload_does_not_produce_the_true_nf() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = lambda_backend();

    let g_id = g_lambda(g_bound(0));
    let g_k = g_lambda(g_lambda(g_bound(1)));
    // The CORRUPTED payload: the App children swapped — `K (λx.x)` instead of `(λx.x) K`.
    let corrupted = g_node("App", vec![g_k, g_id]);
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&corrupted, &fingerprint),
        mettail_rholang_codegen::DRIVE_DEFAULT_FUEL,
        "OUT",
    );
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the corrupted-payload drive runs to quiescence");

    // K (λx.x) →β λ.(λx.x) = λ.λ.0 — NOT the true subject's NF K = λ.λ.1.
    let corrupted_nf = olambda(oid());
    assert_eq!(
        set.out_values,
        vec![corrupted_nf.clone()],
        "the firing computed the CORRUPTED payload's NF — the output is a function of the \
         delivered σ payload"
    );
    assert_ne!(
        set.out_values[0],
        okonst(),
        "the corrupted σ payload must NOT produce the true subject's NF (family discipline)"
    );
    assert_eq!(set.fired_labels().expect("ledger decodes").len(), 1);
}
