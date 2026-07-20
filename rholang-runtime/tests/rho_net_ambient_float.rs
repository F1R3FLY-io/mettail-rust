//! A-S5.8 (leg 2) end-to-end: the in-Rho `^float` receiver family — the per-iteration
//! binder-float canonicalizer — exercised on the live f1r3node reducer through the
//! FLOAT-ROUTED seed (`rho_net_drive_float_call_par_with_fuel`, decision Q-SEED = S2's
//! sibling assembler): RAW float-boundary subjects fire WITHOUT the host boundary float,
//! and THE CONSTRUCTIVE-DISCHARGE WITNESS (the F8-AM-1a `Seal` shape in a name-keyed
//! test `Ambient` def, decision Q-W) proves the premise the host float carried is now
//! discharged IN-RHO: a contractum-INTRODUCED `ν` hides an `Open` redex, `^float`
//! extrudes it, and the redex fires — ledger `{Seal, OpenRule}`.
//!
//! The subjects (design §7 + amendments F8-AM-4/5):
//!
//! * the F1 subject and the AM-2 bag-bodied-ν subject as RAW GroundTerms (no host
//!   float, no `^bound` leakage — the capture-avoidance pin rides the shift-image
//!   argument, not gensym freshness);
//! * THE WITNESS (drive fires `Seal`; the contractum hides `Open` under the fresh ν;
//!   `^float` extrudes; `OpenRule` fires) + its NewComm DOUBLE-BINDER subject, asserted
//!   with the RUN-PERMUTATION-INSENSITIVE membership helper (F8-AM-4 — `flatten` is
//!   bag-order-insensitive only, NOT lambda-run-insensitive);
//! * run length 8 (beyond the host's ≤6 canonical-ordering cap — the cap is
//!   display-ordering-only; the in-Rho float has no cap);
//! * multi-seam nests (a binder inside an ambient BODY hoists through the wall, then
//!   merges at the top seam);
//! * ν over the EMPTY bag (top-level) and the element `^lambda(Nil)` merge shape
//!   (F8-AM-5g — the vacuous binder wraps the rest);
//! * ν over a same-op soup (the AM-2 splice INSIDE the float — the merge base's
//!   three-case dispatch);
//! * the `^shift`-Nil LOAD-BEARING case (F8-AM-5f — a merge strip shifts a Nil side;
//!   `@"ac:PPar"!(Nil)` is FIRST-CLASS input, the reflection image of a nested empty
//!   bag);
//! * the AM-3 Nil cases INSIDE the float path (empty-bag Open continuation through the
//!   float-routed seed).
//!
//! Every driven test asserts the fired multiset, err/fuel channel emptiness, and the
//! resting NF (structurally, or via the run-permutation-insensitive membership form for
//! double-binder subjects). The FULL A-S5.5 cross-check mirror stays with the existing
//! `rho_net_ambient_full.rs` suite (which now runs through the S2 seed — F8-AM-5a).
#![cfg(feature = "ambient-runtime")]

use mettail_languages::ambient::AmbientLanguage;
use mettail_rholang_codegen::{
    reflect_ground_term_par, rho_net_drive_float_call_par_with_fuel, CollectionType, GroundTerm,
    DRIVE_DEFAULT_FUEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
};
use mettail_rholang_runtime::{DriveObservationChannels, PlannedRhoBackend};
use mettail_runtime::{Language, RuntimeObservationValue};

// ── backends ───────────────────────────────────────────────────────────────────────────

/// The PRODUCTION Ambient backend (the `rho_net_ambient_full.rs` derivation).
fn ambient_backend() -> (PlannedRhoBackend, String) {
    let source = AmbientLanguage
        .metadata()
        .definition_source()
        .expect("generated AmbientLanguage must expose its definition_source");
    backend_for_source(source)
}

/// Plan a backend for a `language!` body source (production or the name-keyed witness).
fn backend_for_source(source: &str) -> (PlannedRhoBackend, String) {
    let def = mettail_rholang_codegen::reconstruct_language_def(source)
        .expect("the language body must reconstruct as a LanguageDef");
    let lowering = mettail_rholang_codegen::lower_language_def(&def);
    let requirements = mettail_rholang_codegen::RhoDefaultBackendRequirements {
        coverage: mettail_rholang_codegen::RhoCoverageEvidence::CoveredRejectedRules(
            mettail_rholang_codegen::suggest_rejected_rule_dispositions(&def, &lowering),
        ),
        guard_coverage: mettail_rholang_codegen::RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = mettail_rholang_codegen::plan_rho_default_backend(&def, requirements)
        .expect("the language must plan its Rho-default backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// THE WITNESS DEF (F8-AM-1a pinned `Seal` shape, corrected to the step-2 depth-2-nested
/// LHS the recognizer demands — the `PAmb N (PPar {Q, ...rest1})` element carries the
/// literal bag argument; decision Q-W: a name-keyed test def named `Ambient`,
/// `DRIVE_OPT_IN` unchanged). Every equation is a recognized float congruence, so the
/// def is float-bearing and its `Seal` rule takes the F8-AM-1b NO-MATCH-ENTRY
/// disposition while the DRIVE carries it.
const WITNESS_SEAL_SOURCE: &str = r#"
    name: Ambient,
    types { Proc Name },
    terms {
        PZero . Proc ::= "0" ;
        PSeal . Proc ::= "seal(" Name "," Proc ")" ;
        POpen . Proc ::= "open(" Name "," Proc ")" ;
        PAmb . Proc ::= Name "[" Proc "]" ;
        PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
        PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
    },
    equations {
        NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
        ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
        OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
        SealNew . | x # N |- (PSeal N (PNew ^x.P)) = (PNew ^x.(PSeal N P));
        AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
    },
    rewrites {
        Seal . |- (PPar {(PSeal N P), (PAmb N (PPar {Q, ...rest1})), ...rest})
            ~> (PPar {(PNew ^x.(PPar {(POpen N P)})), (PAmb N (PPar {Q, ...rest1})), ...rest});
        OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest})
            ~> (PPar {P, Q, ...rest});
    }
"#;

// ── decoded-observation vocabulary + GroundTerm builders ───────────────────────────────

type Value = RuntimeObservationValue;

fn oterm(constructor: &str, children: Vec<Value>) -> Value {
    Value::Term { constructor: constructor.to_string(), children }
}
fn ozero() -> Value {
    oterm("PZero", Vec::new())
}
fn oname(atom: &str) -> Value {
    oterm(FREE_VAR_REFLECT_LABEL, vec![oterm(atom, Vec::new())])
}
fn olam(body: Value) -> Value {
    oterm(LAMBDA_REFLECT_LABEL, vec![body])
}
fn obound(index: usize) -> Value {
    let mut peano = oterm("Z", Vec::new());
    for _ in 0..index {
        peano = oterm("S", vec![peano]);
    }
    oterm("^bound", vec![peano])
}
fn oamb(name: Value, body: Value) -> Value {
    oterm("PAmb", vec![name, body])
}
fn obag(values: Vec<Value>) -> Value {
    let mut counts = std::collections::BTreeMap::<Value, usize>::new();
    for value in values {
        *counts.entry(value).or_insert(0) += 1;
    }
    Value::Bag(counts.into_iter().collect())
}
fn bag_elems(value: &Value) -> Option<Vec<Value>> {
    match value {
        Value::Bag(entries) => Some(
            entries
                .iter()
                .flat_map(|(element, count)| std::iter::repeat_n(element.clone(), *count))
                .collect(),
        ),
        _ => None,
    }
}

fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
fn g_zero() -> GroundTerm {
    GroundTerm::nullary("PZero")
}
fn g_name(atom: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(atom)])
}
fn g_bound(index: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary("Z");
    for _ in 0..index {
        peano = g_node("S", vec![peano]);
    }
    g_node("^bound", vec![peano])
}
fn g_lam(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}
fn g_bag(elements: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::collection(CollectionType::HashBag, "PPar", elements)
}
fn g_amb(name: GroundTerm, body: GroundTerm) -> GroundTerm {
    g_node("PAmb", vec![name, body])
}
fn g_in(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
    g_node("PIn", vec![name, cont])
}
fn g_open(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
    g_node("POpen", vec![name, cont])
}
fn g_seal(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
    g_node("PSeal", vec![name, cont])
}
fn g_leaf_amb(atom: &str) -> GroundTerm {
    g_amb(g_name(atom), g_bag(vec![g_zero()]))
}
fn o_leaf_amb(atom: &str) -> Value {
    oamb(oname(atom), obag(vec![ozero()]))
}

// ── the flatten mirror (bag canonicalization for comparisons) ──────────────────────────

fn flatten(value: &Value) -> Value {
    match value {
        Value::Bag(entries) => {
            let mut flat: Vec<Value> = Vec::with_capacity(entries.len());
            for (element, count) in entries {
                let element = flatten(element);
                for _ in 0..*count {
                    match &element {
                        Value::Bag(inner) => {
                            for (inner_element, inner_count) in inner {
                                for _ in 0..*inner_count {
                                    flat.push(inner_element.clone());
                                }
                            }
                        },
                        other => flat.push(other.clone()),
                    }
                }
            }
            obag(flat)
        },
        Value::Term { constructor, children } => {
            oterm(constructor, children.iter().map(flatten).collect())
        },
        other => other.clone(),
    }
}

// ── the RUN-PERMUTATION-INSENSITIVE membership helper (F8-AM-4) ────────────────────────

/// Decode a `^bound(peano)` leaf's index.
fn bound_index(value: &Value) -> Option<usize> {
    let Value::Term { constructor, children } = value else { return None };
    if constructor != "^bound" || children.len() != 1 {
        return None;
    }
    let mut index = 0usize;
    let mut cursor = &children[0];
    loop {
        let Value::Term { constructor, children } = cursor else { return None };
        match constructor.as_str() {
            "Z" if children.is_empty() => return Some(index),
            "S" if children.len() == 1 => {
                index += 1;
                cursor = &children[0];
            },
            _ => return None,
        }
    }
}

/// Strip the LEADING `^lambda` run: `(run length, body)`.
fn strip_run(value: &Value) -> (usize, &Value) {
    let mut run = 0usize;
    let mut cursor = value;
    loop {
        match cursor {
            Value::Term { constructor, children }
                if constructor == LAMBDA_REFLECT_LABEL && children.len() == 1 =>
            {
                run += 1;
                cursor = &children[0];
            },
            _ => return (run, cursor),
        }
    }
}

/// Apply the injective index renaming a RUN PERMUTATION `rho` (over run positions
/// `[0, rho.len())`) induces on a body sitting under that run: a `^bound(n)` at nesting
/// depth `d` (inner binders crossed) with `d ≤ n < d + rho.len()` references run position
/// `n - d` and renames to `rho[n - d] + d`; every other name is untouched. The de Bruijn
/// form of BFC.v's (Struct Res Res) — the amendment F8-AM-3 index-renaming content.
fn rename_run(value: &Value, rho: &[usize], depth: usize) -> Value {
    if let Some(n) = bound_index(value) {
        if n >= depth && n < depth + rho.len() {
            return obound(rho[n - depth] + depth);
        }
        return value.clone();
    }
    match value {
        Value::Term { constructor, children } if constructor == LAMBDA_REFLECT_LABEL => oterm(
            constructor,
            children
                .iter()
                .map(|child| rename_run(child, rho, depth + 1))
                .collect(),
        ),
        Value::Term { constructor, children } => oterm(
            constructor,
            children.iter().map(|child| rename_run(child, rho, depth)).collect(),
        ),
        Value::Bag(entries) => obag(
            entries
                .iter()
                .flat_map(|(element, count)| {
                    std::iter::repeat_n(rename_run(element, rho, depth), *count)
                })
                .collect(),
        ),
        other => other.clone(),
    }
}

/// F8-AM-4: equality UP TO the NewComm run permutation — equal run lengths, and SOME
/// permutation of `[0, run)` renames `a`'s body (flattened, bag-multiset-insensitive)
/// onto `b`'s. `flatten` alone is bag-order-insensitive but NOT lambda-run-insensitive;
/// this helper is both.
fn run_permutation_equal(a: &Value, b: &Value) -> bool {
    let a = flatten(a);
    let b = flatten(b);
    let (run_a, body_a) = strip_run(&a);
    let (run_b, body_b) = strip_run(&b);
    if run_a != run_b {
        return false;
    }
    if run_a == 0 {
        return body_a == body_b;
    }
    // Heap-permutation enumeration over the (small) run.
    let mut indices: Vec<usize> = (0..run_a).collect();
    let mut c = vec![0usize; run_a];
    let matches = |perm: &[usize]| flatten(&rename_run(body_a, perm, 0)) == *body_b;
    if matches(&indices) {
        return true;
    }
    let mut i = 0usize;
    while i < run_a {
        if c[i] < i {
            if i % 2 == 0 {
                indices.swap(0, i);
            } else {
                indices.swap(c[i], i);
            }
            if matches(&indices) {
                return true;
            }
            c[i] += 1;
            i = 0;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    false
}

/// No `^bound` occurs anywhere — the capture-avoidance / no-leakage scan.
fn contains_bound(value: &Value) -> bool {
    match value {
        Value::Term { constructor, children } => {
            constructor == "^bound" || children.iter().any(contains_bound)
        },
        Value::Bag(entries) => entries.iter().any(|(element, _)| contains_bound(element)),
        _ => false,
    }
}

// ── the float-routed raw driver ────────────────────────────────────────────────────────

/// Drive one RAW reflected subject through the A-S5.8 FLOAT-ROUTED seed
/// (`new rf { ⌜^float⌝!(⟦subject⟧, rf) | for(@cf <- rf){ ⌜^drive⌝!(cf, fuel, @out) } }`)
/// — NO host boundary float anywhere on this path.
async fn drive_float_raw(
    backend: &PlannedRhoBackend,
    fingerprint: &str,
    subject: &GroundTerm,
    fuel: i64,
) -> (mettail_rholang_runtime::DriveObservationSet, DriveObservationChannels) {
    let seed = rho_net_drive_float_call_par_with_fuel(
        fingerprint,
        reflect_ground_term_par(subject, fingerprint),
        fuel,
        "OUT",
    );
    let channels = DriveObservationChannels::for_fingerprint(fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the float-routed drive seed runs on the reducer");
    (set, channels)
}

/// The shared green assertions: exactly the expected fired multiset, err/fuel empty,
/// exactly one resting OUT value (returned flattened).
fn assert_float_drive_green(
    set: &mettail_rholang_runtime::DriveObservationSet,
    expected_fired: &[&str],
) -> Value {
    assert!(set.err_data.is_empty(), "no ^drive-err datum: {:?}", set.err_data);
    assert!(set.fuel_data.is_empty(), "no fuel exhaustion: {:?}", set.fuel_data);
    let mut fired = set.fired_labels().expect("every ledger datum is a GString rule label");
    fired.sort();
    let mut expected: Vec<String> = expected_fired.iter().map(|s| s.to_string()).collect();
    expected.sort();
    assert_eq!(fired, expected, "the ledger records exactly the expected fired multiset");
    assert_eq!(set.out_values.len(), 1, "exactly one quiescent resting term");
    flatten(&set.out_values[0])
}

// ── (1) the RAW float-boundary subjects (no host float) ────────────────────────────────

/// The F1 subject as a RAW GroundTerm — the binder NOT pre-floated:
/// `{ ^lambda(n[{in(m,0)}]) | m[{x[{0}]}] }` with `x` a FREE name distinct from the
/// bound one. The in-Rho `^float` extrudes the ν (merge seam), `InRule` fires under the
/// binder arm, and the NF keeps the (vacuous) binder with NO `^bound` anywhere — the
/// free `x` was never captured (capture avoidance by the SHIFT-IMAGE argument, no
/// gensym).
#[tokio::test]
async fn raw_f1_subject_fires_through_the_in_rho_float_without_the_host_float() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_lam(g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())]))),
        g_amb(g_name("m"), g_bag(vec![g_amb(g_name("x"), g_bag(vec![g_zero()]))])),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["InRule"]);
    let expected = olam(obag(vec![oamb(
        oname("m"),
        obag(vec![
            oamb(oname("n"), obag(vec![ozero()])),
            oamb(oname("x"), obag(vec![ozero()])),
        ]),
    )]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the raw F1 subject rests ν-outermost with In fired underneath\n  observed: \
         {observed:?}\n  expected: {expected:?}"
    );
    assert!(
        !contains_bound(&observed),
        "no ^bound leaks — the extruded binder is vacuous and the free x survives: \
         {observed:?}"
    );
}

/// The AM-2 bag-bodied-ν subject as a RAW GroundTerm:
/// `{ ^lambda({ n[{in(m,0)}] | q }) | m[{0}] }` — the ν body is ITSELF a bag; the merge
/// base's three-case dispatch SPLICES its members into the outer bag (never a nested
/// element), exposing the In-redex, which fires.
#[tokio::test]
async fn raw_am2_bag_bodied_nu_subject_splices_and_fires() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_lam(g_bag(vec![
            g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())])),
            g_leaf_amb("q"),
        ])),
        g_amb(g_name("m"), g_bag(vec![g_zero()])),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["InRule"]);
    let expected = olam(obag(vec![
        oamb(
            oname("m"),
            obag(vec![oamb(oname("n"), obag(vec![ozero()])), ozero()]),
        ),
        o_leaf_amb("q"),
    ]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the bag-bodied ν splices FLAT and In fires\n  observed: {observed:?}\n  \
         expected: {expected:?}"
    );
    assert!(!contains_bound(&observed), "no ^bound leaks: {observed:?}");
}

// ── (2) THE CONSTRUCTIVE-DISCHARGE WITNESS ─────────────────────────────────────────────

/// ★ THE WITNESS (F8-AM-1a, decision Q-W): on the name-keyed `Ambient` witness def, the
/// drive fires `Seal` on `{seal(n, p) | n[{q}]}`; the contractum hides `open(n, p)`
/// under a FRESH RHS-introduced ν (`AcReconstructTemplate::Binder` → the carrier's
/// ctor-erased `⌜^lambda⌝` rebuild with the F8-AM-1c σ-slot shifts); the per-firing
/// `^float` (decision Q-AB = A) extrudes the ν; `OpenRule` fires under the binder arm —
/// ledger `{Seal, OpenRule}`, NF `^lambda({p, q})`. This is the boundary-float premise
/// discharged CONSTRUCTIVELY: no host float ran anywhere, yet the ν-hidden redex fired.
#[tokio::test]
async fn witness_seal_contractum_nu_is_floated_and_open_fires() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = backend_for_source(WITNESS_SEAL_SOURCE);
    let subject = g_bag(vec![
        g_seal(g_name("n"), g_leaf_amb("p")),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("q")])),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["OpenRule", "Seal"]);
    let expected = olam(obag(vec![o_leaf_amb("p"), o_leaf_amb("q")]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the witness rests ^lambda({{p, q}}) — Seal introduced the ν, ^float extruded \
         it, Open fired\n  observed: {observed:?}\n  expected: {expected:?}"
    );
    assert!(!contains_bound(&observed), "the witness ν is vacuous in the NF: {observed:?}");
}

/// ★ The WITNESS's NewComm double-binder subject (F8-AM-4): the whole `Seal` cascade
/// UNDER an outer ν that binds the ambient name — `^lambda({seal(^bound 0, p),
/// ^bound 0[{q}]})`. The carrier's F8-AM-1c σ-slot shift maps the under-template-binder
/// `N` slot `^bound 0 ↦ ^bound 1`, the merge's stayed-outside shift keeps the sibling
/// consistent, the guard `^bound 1 ≡ ^bound 1` passes, and Open fires — the NF has run
/// length 2, asserted with the run-permutation-insensitive helper.
#[tokio::test]
async fn witness_double_binder_subject_shifts_consistently_and_fires() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = backend_for_source(WITNESS_SEAL_SOURCE);
    let subject = g_lam(g_bag(vec![
        g_seal(g_bound(0), g_leaf_amb("p")),
        g_amb(g_bound(0), g_bag(vec![g_leaf_amb("q")])),
    ]));
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["OpenRule", "Seal"]);
    let expected = olam(olam(obag(vec![o_leaf_amb("p"), o_leaf_amb("q")])));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the double-binder witness rests ^lambda^2({{p, q}})\n  observed: {observed:?}\n  \
         expected: {expected:?}"
    );
}

// ── (3) run length 8 — beyond the host's ≤6 canonical-ordering cap ─────────────────────

/// Two elements each under FOUR nested νs: the merge extrudes all 8 binders into one
/// top run (the host's ≤6 cap is a DISPLAY-ordering cap only — the in-Rho float has no
/// cap), the In-redex exposed underneath fires, and the NF's run length is exactly 8.
#[tokio::test]
async fn eight_binder_run_extrudes_fully_and_fires() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let nu4 = |core: GroundTerm| g_lam(g_lam(g_lam(g_lam(core))));
    let subject = g_bag(vec![
        nu4(g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())]))),
        nu4(g_amb(g_name("m"), g_bag(vec![g_zero()]))),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["InRule"]);
    let (run, _body) = strip_run(&observed);
    assert_eq!(run, 8, "all 8 binders extrude into ONE top run: {observed:?}");
    let expected = {
        let mut nf = obag(vec![oamb(
            oname("m"),
            obag(vec![oamb(oname("n"), obag(vec![ozero()])), ozero()]),
        )]);
        for _ in 0..8 {
            nf = olam(nf);
        }
        nf
    };
    assert!(
        run_permutation_equal(&observed, &expected),
        "the 8-run NF is the In-fired core under the full run\n  observed: {observed:?}"
    );
}

// ── (4) multi-seam nests ───────────────────────────────────────────────────────────────

/// A binder at BOTH seams: `{ ^lambda(n[{ ^lambda(in(m,0)) }]) | m[{0}] }` — the inner ν
/// merges out of the ambient BODY bag, hoists through the `PAmb` wall
/// (`^float-hoist:PAmb`), and both binders merge into the top run; In fires underneath.
#[tokio::test]
async fn multi_seam_nested_binders_hoist_merge_and_fire() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_lam(g_amb(
            g_name("n"),
            g_bag(vec![g_lam(g_in(g_name("m"), g_zero()))]),
        )),
        g_amb(g_name("m"), g_bag(vec![g_zero()])),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["InRule"]);
    let (run, _body) = strip_run(&observed);
    assert_eq!(run, 2, "both seams' binders reach the top run: {observed:?}");
    let expected = olam(olam(obag(vec![oamb(
        oname("m"),
        obag(vec![oamb(oname("n"), obag(vec![ozero()])), ozero()]),
    )])));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the multi-seam NF is the In-fired core under the 2-run\n  observed: {observed:?}"
    );
}

// ── (5) the Nil family: ν over the empty bag / element ^lambda(Nil) / ^shift-Nil ───────

/// ν over the EMPTY bag as the WHOLE subject: `^lambda({})` floats (and drives) to
/// itself — the dispatcher's binder arm over the Nil leaf.
#[tokio::test]
async fn nu_over_the_empty_bag_rests_as_itself() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_lam(g_bag(Vec::new()));
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &[]);
    assert_eq!(observed, olam(obag(Vec::new())), "^lambda(Nil) is its own float/drive NF");
}

/// F8-AM-5g: the element `^lambda(Nil)` (`new(x, {})`) inside a bag — the merge strips
/// the vacuous binder (shifting the sibling side), hits the Nil base, and the binder
/// wraps the REST: `{ ^lambda({}) | c[{0}] }` rests `^lambda({c[{0}]})`.
#[tokio::test]
async fn element_lambda_nil_wraps_the_rest() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![g_lam(g_bag(Vec::new())), g_leaf_amb("c")]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &[]);
    let expected = olam(obag(vec![o_leaf_amb("c")]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the vacuous ν wraps the rest\n  observed: {observed:?}\n  expected: {expected:?}"
    );
}

/// F8-AM-5f — the `^shift`-Nil LOAD-BEARING case: a bag with an EMPTY-BAG element
/// (`@"ac:PPar"!(Nil)` — the FIRST-CLASS reflection image of a nested empty bag) beside
/// a ν'd element. Whichever side the merge strips first, the OTHER side is (or becomes)
/// Nil and MUST shift through the A-S5.8 `^shift` Nil arm — without it the float stalls
/// and OUT never lands.
#[tokio::test]
async fn shift_nil_arm_is_load_bearing_for_the_empty_bag_element_merge() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_bag(Vec::new()),
        g_lam(g_amb(g_bound(0), g_bag(vec![g_zero()]))),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &[]);
    let expected = olam(obag(vec![oamb(obound(0), obag(vec![ozero()]))]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the empty-bag element splices as nothing; the ν'd ambient keeps its bound \
         name\n  observed: {observed:?}\n  expected: {expected:?}"
    );
}

// ── (6) ν over a same-op soup (the AM-2 splice inside the float) ───────────────────────

/// `{ ^lambda({a[{0}] | b[{0}]}) | c[{0}] }` — stripping the ν leaves a SAME-OP soup;
/// the merge base's three-case dispatch SPLICES its sends into the outer bag: the NF is
/// the FLAT `^lambda({a, b, c})`, never `^lambda({{a|b}, c})`.
#[tokio::test]
async fn nu_over_a_same_op_soup_splices_flat() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_lam(g_bag(vec![g_leaf_amb("a"), g_leaf_amb("b")])),
        g_leaf_amb("c"),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &[]);
    let expected = olam(obag(vec![o_leaf_amb("a"), o_leaf_amb("b"), o_leaf_amb("c")]));
    assert!(
        run_permutation_equal(&observed, &expected),
        "the ν'd soup splices FLAT under the extruded binder\n  observed: {observed:?}\n  \
         expected: {expected:?}"
    );
    // The raw resting body is ALREADY flat (the splice happened in-Rho).
    let (_, body) = strip_run(&observed);
    let elems = bag_elems(body).expect("the body is a bag");
    assert_eq!(elems.len(), 3, "three FLAT members: {observed:?}");
    assert!(
        elems.iter().all(|element| !matches!(element, Value::Bag(_))),
        "no nested-bag member survives the in-float splice: {observed:?}"
    );
}

// ── (7) the AM-3 Nil cases INSIDE the float path ───────────────────────────────────────

/// `{open(n, {}) | n[{c[{0}]}]}` through the FLOAT-ROUTED seed: the float is the
/// identity on this binder-free subject (Nil arms included), Open fires, the empty-bag
/// continuation splices as NOTHING — rests `{c[{0}]}`.
#[tokio::test]
async fn am3_empty_bag_open_through_the_float_path() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_open(g_name("n"), g_bag(Vec::new())),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
    ]);
    let (set, _channels) =
        drive_float_raw(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;
    let observed = assert_float_drive_green(&set, &["OpenRule"]);
    assert_eq!(
        observed,
        obag(vec![o_leaf_amb("c")]),
        "the empty-bag P contributes NOTHING through the float path"
    );
}

// ── (8) F8-AM-2: [τ float] WITNESSED by a drive-seeded live trace ──────────────────────

/// ★ F8-AM-2: the `[τ float]` classifier WITNESS — a live `StepSession` over the
/// installed Ambient program composed with the FLOAT-ROUTED seed (the raw F1 subject)
/// observes COMMs whose rendezvous rides the `^float` family, classified
/// `RuntimeTauClass::Float`; the trace also carries `[τ drive]` machinery COMMs and
/// NEVER reclassifies them. (The `a_s5_6_step_routing.rs:125` pin is MUST-NOT-MOVE: the
/// REPL's Ambient Layer-2 trace rides the report-carrying MATCH fallback whose channels
/// are the legacy `ac:loc:` names — this test drive-seeds its own session instead.)
#[cfg(feature = "runtime-report")]
#[test]
fn tau_float_is_witnessed_by_a_drive_seeded_trace() {
    use mettail_rholang_runtime::{StepSession, TauChannelClassifier};
    use mettail_runtime::{ReductionStepper, RuntimeTauClass};

    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_lam(g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())]))),
        g_amb(g_name("m"), g_bag(vec![g_amb(g_name("x"), g_bag(vec![g_zero()]))])),
    ]);
    let seed = rho_net_drive_float_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&subject, &fingerprint),
        DRIVE_DEFAULT_FUEL,
        "OUT",
    );
    let program = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("production Ambient installs")
        .append(seed);
    let mut session = StepSession::start(
        program,
        Vec::new(),
        Some("OUT".to_string()),
        Some(TauChannelClassifier::for_language_fingerprint(&fingerprint)),
    )
    .expect("the drive-seeded step session starts");

    let mut float_steps = 0usize;
    let mut drive_steps = 0usize;
    let mut steps = 0usize;
    while let Some(step) = session.next_step().expect("the trace advances") {
        match step.tau {
            Some(RuntimeTauClass::Float) => float_steps += 1,
            Some(RuntimeTauClass::Drive) => drive_steps += 1,
            _ => {},
        }
        steps += 1;
        assert!(steps < 20_000, "the drive-seeded trace terminates");
    }
    assert!(
        float_steps >= 1,
        "the float-routed seed's trace WITNESSES [τ float] COMMs (dispatcher/satellites): \
         {steps} steps, {drive_steps} [τ drive]"
    );
    assert!(
        drive_steps >= 1,
        "the drive machinery still classifies [τ drive] — families disjoint, no \
         reclassification"
    );
}
