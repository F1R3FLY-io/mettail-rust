//! A-S5.5 (leg 2) end-to-end: the PRODUCTION `Ambient` language driven to quiescence
//! FULLY IN-RHO by the generated `^drive` receiver family + the three per-rule
//! AC-CARRIER receivers — matching (the guarded AC redex arms: `MatchCase.guard`
//! cross-level `EEq`), firing (through the carrier ABI `⌜^drive-ac:R⌝!(t, r)`),
//! contractum re-drive, the bag arm's peel/join/three-case-splice reassembly (AM-3), and
//! congruence/binder descent all execute as COMMs on the live f1r3node reducer; the host
//! seeds once (`rho_net_drive_invocation_to` or a direct reflected seed) and reads the
//! four observation channels back.
//!
//! The MANDATORY subjects (plan v2 §4.3.3 / §6.6, amendments AM-1/AM-2/AM-3/AM-5,
//! decision (3)):
//!
//! * (a)/(b) `OpenRule` and `InRule` fire in-Rho (wrap + splice dispatch legs);
//! * (c) the A-S5.4b C-G (Red Out) REDECLARED `OutRule`: the residual stays INSIDE `m`
//!   (3-element parent body), and the singleton `m[{n[{out(m,0)}]}]` fires to
//!   `{n[{0}], m[{}]}` — `m[{}]`'s empty body decodes as the empty bag (AM-3 Nil);
//! * (d) the in-THEN-open cascade — `InRule`'s contractum CREATES the `OpenRule` redex;
//! * (e) the F1 extrusion/float-boundary subject — the redex split across a `new`
//!   boundary, exposed by the A-S5.4a unconditional unbind-first float at the invocation
//!   boundary, driven under the binder arm, capture-avoidance asserted;
//! * (f) the guard VETO — mismatched cross-level names never fire (ledger empty);
//! * (g) the three MANDATORY flattening subjects: bag-bodied open rests FLAT
//!   `{P, Q, R}`-style (never `{{P|Q}, R}`); the empty-bag Nil case; the double-nested
//!   NEVER-DRIVEN subject rests flat through the AM-3(b) re-drive induction;
//! * (h) fuel exhaustion (per-path GInt) with the typed `^drive-fuel` datum;
//! * (i) the corrupted-σ probe (PS family discipline: the output is a function of the
//!   DELIVERED subject payload);
//! * (j) the decision-(3) NON-CONFLUENT subject — membership in the enumerated valid-NF
//!   set, never a unique-NF claim;
//! * (k) the AM-5 replay — a SEARCH-FOR-A-VALID-ORDER over the unordered fired multiset
//!   must reproduce the observed resting term (run on every green subject).
//!
//! Every driven test runs the ALWAYS-ON cross-check (plan v2 §4.7) over FLATTENED
//! semantics: decode OUT → flatten (the host mirror of `add_flattened_bag`,
//! `dovetail/src/rules.rs:707` — multiplicity-preserving, no cycle case on tree values)
//! → NF-scan (the host mirror of ALL the driver's redex arms — In/Out/Open with their
//! name-equality guards — over the canonicalized flattened term) → ledger consistency
//! (`fired ≥ 1 ⟺ redex`; err/fuel channels empty).
//!
//! Free Ambient names decode as `^free(<moniker FreeVar debug>)` leaves whose strings
//! are process-global-gensym-dependent, so PARSE-based expectations are computed by
//! TRANSFORMING the decoded seed subject through the same host rule mirrors the replay
//! uses (never hard-coded name strings); DIRECT-seed subjects control their name atoms
//! exactly.
#![cfg(feature = "ambient-runtime")]

use mettail_languages::ambient::AmbientLanguage;
use mettail_rholang_codegen::{
    reflect_ground_term_par, rho_net_drive_call_par_with_fuel, CollectionType, GroundTerm,
    DRIVE_DEFAULT_FUEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    drive_cross_check, par_as_runtime_observation_value, DriveCrossCheckError,
    DriveObservationChannels, PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};

// ── backend ────────────────────────────────────────────────────────────────────────────

/// Reconstruct the PRODUCTION Ambient's augmented `LanguageDef` from the generated
/// metadata's `definition_source()` and plan its Rho-default backend — the SAME
/// derivation `rho_net_drive_invocation_to`'s memoized artifacts use, so the installed
/// program (the 3 AC σ-receivers + `^drive` + the 3 carrier receivers) and the seed's
/// reflected tags share one fingerprint.
fn ambient_backend() -> (PlannedRhoBackend, String) {
    let source = AmbientLanguage
        .metadata()
        .definition_source()
        .expect("generated AmbientLanguage must expose its definition_source");
    let def = mettail_rholang_codegen::reconstruct_language_def(source)
        .expect("AmbientLanguage definition_source must reconstruct as a LanguageDef");

    let lowering = mettail_rholang_codegen::lower_language_def(&def);
    let requirements = mettail_rholang_codegen::RhoDefaultBackendRequirements {
        coverage: mettail_rholang_codegen::RhoCoverageEvidence::CoveredRejectedRules(
            mettail_rholang_codegen::suggest_rejected_rule_dispositions(&def, &lowering),
        ),
        guard_coverage: mettail_rholang_codegen::RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = mettail_rholang_codegen::plan_rho_default_backend(&def, requirements)
        .expect("production Ambient must plan its Rho-default backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

// ── decoded-observation vocabulary ─────────────────────────────────────────────────────

type Value = RuntimeObservationValue;

fn oterm(constructor: &str, children: Vec<Value>) -> Value {
    Value::Term { constructor: constructor.to_string(), children }
}
fn ozero() -> Value {
    oterm("PZero", Vec::new())
}
/// A decoded free NAME leaf with an exact atom (direct-seed subjects only — parse-based
/// names carry moniker-gensym debug strings).
fn oname(atom: &str) -> Value {
    oterm(FREE_VAR_REFLECT_LABEL, vec![oterm(atom, Vec::new())])
}
fn oamb(name: Value, body: Value) -> Value {
    oterm("PAmb", vec![name, body])
}
fn oin(name: Value, cont: Value) -> Value {
    oterm("PIn", vec![name, cont])
}
fn oout(name: Value, cont: Value) -> Value {
    oterm("POut", vec![name, cont])
}
fn oopen(name: Value, cont: Value) -> Value {
    oterm("POpen", vec![name, cont])
}

/// A canonical decoded bag from a value LIST (multiplicities counted; entries sorted the
/// way `decode_ac_bag_soup` sorts them — `BTreeMap` order).
fn obag(values: Vec<Value>) -> Value {
    let mut counts = std::collections::BTreeMap::<Value, usize>::new();
    for value in values {
        *counts.entry(value).or_insert(0) += 1;
    }
    Value::Bag(counts.into_iter().collect())
}

/// The expanded element list of a decoded bag (each entry repeated by multiplicity).
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

// ── the host FLATTEN mirror (add_flattened_bag, dovetail/src/rules.rs:707) ─────────────

/// Recursively canonicalize every bag in `value` to its FLAT form: a bag element that is
/// itself a bag SPLICES its (already-flattened) elements, multiplicity-preserving —
/// exactly the host's value-level `add_flattened_bag` on tree-shaped values (no cycle
/// case). The single-bag-op caveat: decoded `Bag`s erase the `op`, so all bags splice —
/// exact for Ambient (one collection constructor, `PPar`).
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
        Value::Term { constructor, children } => oterm(
            constructor,
            children.iter().map(flatten).collect(),
        ),
        other => other.clone(),
    }
}

/// A FLAT bag built from a value list: elements flattened, one splice level dissolved —
/// the construction-time mirror the rule mirrors use for every rebuilt bag.
fn flat_bag(values: Vec<Value>) -> Value {
    flatten(&obag(values))
}

// ── the host redex-arm mirrors (In / Out / Open, name-equality guards included) ────────

/// All results of ONE `OpenRule` application at THIS bag's top level:
/// `{open(n,P), n'[Q], ...rest}` with `n == n'` ⟹ `flat{P, Q, ...rest}`.
fn open_apply_here(elems: &[Value]) -> Vec<Value> {
    let mut results = Vec::new();
    for (i, open_element) in elems.iter().enumerate() {
        let Value::Term { constructor, children } = open_element else { continue };
        if constructor != "POpen" {
            continue;
        }
        let (open_name, open_cont) = (&children[0], &children[1]);
        for (j, amb_element) in elems.iter().enumerate() {
            if i == j {
                continue;
            }
            let Value::Term { constructor, children } = amb_element else { continue };
            if constructor != "PAmb" || &children[0] != open_name {
                continue;
            }
            let mut rest: Vec<Value> = Vec::with_capacity(elems.len());
            for (k, element) in elems.iter().enumerate() {
                if k != i && k != j {
                    rest.push(element.clone());
                }
            }
            rest.push(open_cont.clone());
            rest.push(children[1].clone());
            results.push(flat_bag(rest));
        }
    }
    results
}

/// All results of ONE `InRule` application at THIS bag's top level:
/// `{n[{in(m,P), ...rest1}], m'[R], ...rest2}` with `m == m'` ⟹
/// `flat{ m[flat{ n[flat{P, ...rest1}], R }], ...rest2 }` (the `R` splice is the AM-3
/// three-case at the inner bag-element seam; `flat_bag` mirrors it).
fn in_apply_here(elems: &[Value]) -> Vec<Value> {
    let mut results = Vec::new();
    for (i, nested_element) in elems.iter().enumerate() {
        let Value::Term { constructor, children } = nested_element else { continue };
        if constructor != "PAmb" {
            continue;
        }
        let n_name = &children[0];
        let Some(body) = bag_elems(&children[1]) else { continue };
        for (in_index, in_element) in body.iter().enumerate() {
            let Value::Term { constructor, children: in_children } = in_element else {
                continue;
            };
            if constructor != "PIn" {
                continue;
            }
            let (m_name, in_cont) = (&in_children[0], &in_children[1]);
            for (j, amb_element) in elems.iter().enumerate() {
                if i == j {
                    continue;
                }
                let Value::Term { constructor, children: amb_children } = amb_element else {
                    continue;
                };
                if constructor != "PAmb" || &amb_children[0] != m_name {
                    continue;
                }
                let mut inner_n: Vec<Value> = vec![in_cont.clone()];
                for (k, element) in body.iter().enumerate() {
                    if k != in_index {
                        inner_n.push(element.clone());
                    }
                }
                let rebuilt_m = oamb(
                    m_name.clone(),
                    flat_bag(vec![oamb(n_name.clone(), flat_bag(inner_n)), amb_children[1].clone()]),
                );
                let mut top: Vec<Value> = vec![rebuilt_m];
                for (k, element) in elems.iter().enumerate() {
                    if k != i && k != j {
                        top.push(element.clone());
                    }
                }
                results.push(flat_bag(top));
            }
        }
    }
    results
}

/// All results of ONE C-G (Red Out) REDECLARED `OutRule` application at THIS node:
/// `m[{n[{out(m',P), ...rest1}], ...rest2}]` with `m == m'` ⟹
/// `flat{ n[flat{P, ...rest1}], m[flat{...rest2}] }` — the residual `...rest2` KEPT
/// INSIDE `m` (empty rest legal, so the singleton fires to `{n[{P}], m[{}]}`).
fn out_apply_here(value: &Value) -> Vec<Value> {
    let mut results = Vec::new();
    let Value::Term { constructor, children } = value else { return results };
    if constructor != "PAmb" {
        return results;
    }
    let m_name = &children[0];
    let Some(body) = bag_elems(&children[1]) else { return results };
    for (i, nested_element) in body.iter().enumerate() {
        let Value::Term { constructor, children: n_children } = nested_element else {
            continue;
        };
        if constructor != "PAmb" {
            continue;
        }
        let n_name = &n_children[0];
        let Some(inner) = bag_elems(&n_children[1]) else { continue };
        for (out_index, out_element) in inner.iter().enumerate() {
            let Value::Term { constructor, children: out_children } = out_element else {
                continue;
            };
            if constructor != "POut" || &out_children[0] != m_name {
                continue;
            }
            let mut inner_n: Vec<Value> = vec![out_children[1].clone()];
            for (k, element) in inner.iter().enumerate() {
                if k != out_index {
                    inner_n.push(element.clone());
                }
            }
            let mut rest2: Vec<Value> = Vec::with_capacity(body.len());
            for (k, element) in body.iter().enumerate() {
                if k != i {
                    rest2.push(element.clone());
                }
            }
            results.push(flat_bag(vec![
                oamb(n_name.clone(), flat_bag(inner_n)),
                oamb(m_name.clone(), flat_bag(rest2)),
            ]));
        }
    }
    results
}

/// All results of ONE application of `rule` ANYWHERE in `value` (the driver's descent
/// closure: bags, ambient bodies, capability continuations, and under the binder —
/// matching the driver's congruence/binder/bag arms and the host e-graph's
/// everywhere-application). Every rebuilt bag is flattened at construction.
fn apply_rule_anywhere(rule: &str, value: &Value) -> Vec<Value> {
    let mut results = Vec::new();
    match value {
        Value::Bag(_) => {
            let elems = bag_elems(value).expect("a Bag expands");
            match rule {
                "OpenRule" => results.extend(open_apply_here(&elems)),
                "InRule" => results.extend(in_apply_here(&elems)),
                _ => {},
            }
            // Recurse into each element position.
            for (i, element) in elems.iter().enumerate() {
                for reduced in apply_rule_anywhere(rule, element) {
                    let mut next = elems.clone();
                    next[i] = reduced;
                    results.push(flat_bag(next));
                }
            }
        },
        Value::Term { constructor, children } => {
            if rule == "OutRule" {
                results.extend(out_apply_here(value));
            }
            for (i, child) in children.iter().enumerate() {
                for reduced in apply_rule_anywhere(rule, child) {
                    let mut next = children.clone();
                    next[i] = reduced;
                    results.push(oterm(constructor, next));
                }
            }
        },
        _ => {},
    }
    results
}

/// The host NF-scan (plan v2 §4.7): the mirror of ALL the driver's redex arms — a redex
/// is present iff SOME rule applies somewhere in the (flattened) term.
fn ambient_redex_present(value: &Value) -> bool {
    ["InRule", "OutRule", "OpenRule"]
        .iter()
        .any(|rule| !apply_rule_anywhere(rule, value).is_empty())
}

// ── the AM-5 replay: search-for-a-valid-order over the fired multiset ──────────────────

/// Whether SOME order + position/pairing choice of the remaining fired multiset rewrites
/// `current` into `target` (`get_data` returns an UNORDERED multiset and the driver adds
/// no ordinal — AM-5 — so replay is DEFINED as this search; on confluent subjects every
/// valid order lands on the unique NF, on non-confluent ones success ⟺ the observed NF
/// is reachable with exactly the ledgered firings).
fn replay_search(current: &Value, remaining: &[String], target: &Value) -> bool {
    if remaining.is_empty() {
        return current == target;
    }
    let mut tried: Vec<&String> = Vec::with_capacity(remaining.len());
    for (index, label) in remaining.iter().enumerate() {
        if tried.contains(&label) {
            continue;
        }
        tried.push(label);
        let mut rest: Vec<String> = remaining.to_vec();
        rest.remove(index);
        for next in apply_rule_anywhere(label, current) {
            if replay_search(&next, &rest, target) {
                return true;
            }
        }
    }
    false
}

// ── shared runners + the always-on cross-check ─────────────────────────────────────────

/// Decode the SEED's reflected subject (the first datum of the `^drive` seed send) —
/// verbatim for a direct seed. (The GENERATED invocation's subject is read off
/// `RhoNetDriveInvocation::subject` instead — A-S5.8 F8-AM-5a: under the S2 float-routed
/// seed the subject is no longer the call's first top-level send datum.)
fn decode_seed_subject(call: &models::rhoapi::Par) -> Value {
    let datum = &call.sends[0].data[0];
    par_as_runtime_observation_value(datum)
        .expect("the drive seed's reflected subject must decode")
}

/// Drive one PARSED production-Ambient subject through the generated seed invocation
/// (boundary canonicalization + admission re-check + default fuel; A-S5.8: the S2
/// FLOAT-ROUTED seed — the installed `^float` dispatcher re-canonicalizes in-Rho, an
/// identity pass on the host-floated subject), returning the observation set, the
/// channels, and the DECODED (canonicalized) seed subject.
async fn drive_parsed(
    backend: &PlannedRhoBackend,
    source: &str,
) -> (mettail_rholang_runtime::DriveObservationSet, DriveObservationChannels, Value) {
    let term = AmbientLanguage
        .parse_term(source)
        .unwrap_or_else(|err| panic!("production Ambient must parse {source:?}: {err:?}"));
    let invocation = AmbientLanguage::rho_net_drive_invocation_to(term.as_ref(), "OUT")
        .expect("production Ambient is drive-admitted (A-S5.5)");
    // F8-AM-5a: the raw reflected subject rides the invocation itself (S2-shape-agnostic).
    let subject = par_as_runtime_observation_value(&invocation.subject)
        .expect("the drive invocation's reflected subject must decode");
    let channels = DriveObservationChannels::from_invocation(&invocation);
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&invocation.call, &channels)
        .await
        .expect("the drive seed runs to quiescence on the reducer");
    (set, channels, subject)
}

/// Drive one DIRECT reflected subject (exact name atoms, no boundary canonicalization)
/// with an explicit per-path fuel.
async fn drive_direct(
    backend: &PlannedRhoBackend,
    fingerprint: &str,
    subject: &GroundTerm,
    fuel: i64,
) -> (mettail_rholang_runtime::DriveObservationSet, DriveObservationChannels, Value) {
    let seed = rho_net_drive_call_par_with_fuel(
        fingerprint,
        reflect_ground_term_par(subject, fingerprint),
        fuel,
        "OUT",
    );
    let subject_value = decode_seed_subject(&seed);
    let channels = DriveObservationChannels::for_fingerprint(fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the direct drive seed runs on the reducer");
    (set, channels, subject_value)
}

/// The always-on cross-check over FLATTENED semantics (plan v2 §4.7) + the ledger
/// multiset + the AM-5 replay: `expected_fired` is the expected fired MULTISET
/// (order-insensitive).
fn assert_green_drive(
    set: &mettail_rholang_runtime::DriveObservationSet,
    channels: &DriveObservationChannels,
    subject: &Value,
    expected_fired: &[&str],
) {
    drive_cross_check(
        set,
        channels,
        !expected_fired.is_empty(),
        DRIVE_DEFAULT_FUEL,
        &|value| ambient_redex_present(&flatten(value)),
    )
    .expect("the always-on flattened drive cross-check is green");
    let mut fired = set.fired_labels().expect("every ledger datum is a GString rule label");
    fired.sort();
    let mut expected: Vec<String> = expected_fired.iter().map(|s| s.to_string()).collect();
    expected.sort();
    assert_eq!(fired, expected, "the ledger records exactly the expected fired multiset");
    // AM-5: some valid order over the fired multiset reproduces the observed NF.
    let observed = flatten(&set.out_values[0]);
    assert!(
        replay_search(&flatten(subject), &fired, &observed),
        "the AM-5 search-for-a-valid-order replay must reproduce the observed resting \
         term\n  subject: {subject:?}\n  fired: {fired:?}\n  observed: {observed:?}"
    );
}

// ── direct-seed (GroundTerm) builders ──────────────────────────────────────────────────

fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
fn g_zero() -> GroundTerm {
    GroundTerm::nullary("PZero")
}
/// A free NAME leaf with an exact atom (`^free(atom)` — the reflection shape of
/// `Var::Free`, with a test-controlled tag instead of the moniker debug string).
fn g_name(atom: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(atom)])
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
/// A distinct inert element: an ambient `atom[{0}]`.
fn g_leaf_amb(atom: &str) -> GroundTerm {
    g_amb(g_name(atom), g_bag(vec![g_zero()]))
}
fn o_leaf_amb(atom: &str) -> Value {
    oamb(oname(atom), obag(vec![ozero()]))
}

// ── (a) OPEN fires (the WRAP dispatch leg: a non-bag continuation) ─────────────────────

/// `{open(n, a[{0}]) | n[{b[{0}]}]}` — `P` is an AMBIENT (non-bag ⟹ the carrier's
/// three-case WRAP leg), `Q` is a bag (⟹ the SPLICE leg): rests FLAT
/// `{a[{0}], b[{0}]}` with exactly one `OpenRule` firing.
#[tokio::test]
async fn open_fires_in_rho_with_wrap_and_splice_dispatch() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = ambient_backend();
    let (set, channels, subject) =
        drive_parsed(&backend, "{open(n, a[{0}]) | n[{b[{0}]}]}").await;

    let observed = flatten(&set.out_values[0]);
    let elems = bag_elems(&observed).expect("the resting term is a bag");
    assert_eq!(elems.len(), 2, "open splices P (wrapped) and Q (spliced): {observed:?}");
    assert_green_drive(&set, &channels, &subject, &["OpenRule"]);
}

// ── (b) IN fires (the R-splice at the contractum entry) ────────────────────────────────

/// `{n[{in(m, 0)}] | m[{r[{0}]}]}` — the `n` ambient moves INTO `m`; the delivered `R`
/// (m's bag body) SPLICES at the inner bag-element seam (the F4 contractum-entry
/// three-case), so the resting inner bag is FLAT `{n[{0}], r[{0}]}` — never
/// `{n[{0}], {r[{0}]}}`.
#[tokio::test]
async fn in_fires_in_rho_with_the_contractum_entry_splice() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = ambient_backend();
    let (set, channels, subject) =
        drive_parsed(&backend, "{n[{in(m, 0)}] | m[{r[{0}]}]}").await;

    let observed = flatten(&set.out_values[0]);
    // The resting term is `{m[{n[{0}], r[{0}]}]}` — ONE top element, whose body has TWO
    // flat elements.
    let top = bag_elems(&observed).expect("the resting term is a bag");
    assert_eq!(top.len(), 1, "in nests everything under m: {observed:?}");
    let Value::Term { constructor, children } = &top[0] else {
        panic!("the top element is the m ambient: {observed:?}");
    };
    assert_eq!(constructor, "PAmb");
    let m_body = bag_elems(&children[1]).expect("m's body is a bag");
    assert_eq!(
        m_body.len(),
        2,
        "m's body is the FLAT {{n[{{0}}], r[{{0}}]}} (the R splice): {observed:?}"
    );
    assert!(
        m_body.iter().all(|element| !matches!(element, Value::Bag(_))),
        "no nested-bag element survives the contractum-entry splice: {observed:?}"
    );
    assert_green_drive(&set, &channels, &subject, &["InRule"]);
}

// ── (c) the REDECLARED OutRule — C-G (Red Out) in-Rho ──────────────────────────────────

/// The 3-element parent body `m[{n[{out(m, a[{0}])}] | b[{0}] | c[{0}]}]`: the residual
/// `{b[{0}], c[{0}]}` stays INSIDE `m` (the A-S5.4b AM-1 redeclaration — boundary
/// ejection is GONE); rests `{n[{a[{0}]}], m[{b[{0}], c[{0}]}]}` (single redex ⟹ strict
/// structural equality).
#[tokio::test]
async fn out_fires_with_the_residual_kept_inside_m() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_amb(
        g_name("m"),
        g_bag(vec![
            g_amb(g_name("n"), g_bag(vec![g_node("POut", vec![g_name("m"), g_leaf_amb("a")])])),
            g_leaf_amb("b"),
            g_leaf_amb("c"),
        ]),
    );
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    let expected = obag(vec![
        oamb(oname("n"), obag(vec![o_leaf_amb("a")])),
        oamb(oname("m"), obag(vec![o_leaf_amb("b"), o_leaf_amb("c")])),
    ]);
    assert_eq!(
        flatten(&set.out_values[0]),
        expected,
        "the redeclared (Red Out): n exits with its continuation; the residual \
         {{b[{{0}}], c[{{0}}]}} is KEPT INSIDE m"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OutRule"]);
}

/// The SINGLETON body `m[{n[{out(m, 0)}]}]` fires to `{n[{0}], m[{}]}` — legal exactly
/// because the redeclared rest is the WHOLE residual (empty allowed); `m[{}]`'s empty
/// body decodes as the empty bag (the AM-3 Nil reflection).
#[tokio::test]
async fn out_singleton_fires_to_the_empty_bodied_m() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_amb(
        g_name("m"),
        g_bag(vec![g_amb(
            g_name("n"),
            g_bag(vec![g_node("POut", vec![g_name("m"), g_zero()])]),
        )]),
    );
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    let expected = obag(vec![
        oamb(oname("n"), obag(vec![ozero()])),
        oamb(oname("m"), obag(Vec::new())),
    ]);
    assert_eq!(
        flatten(&set.out_values[0]),
        expected,
        "the singleton fires: {{n[{{0}}], m[{{}}]}} — m keeps its (empty) residual body"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OutRule"]);
}

// ── (d) the in-THEN-open cascade ───────────────────────────────────────────────────────

/// `{n[{in(m, 0)}] | m[{open(n, {c[{0}]})}]}` — `open(n, ·)` has NO `n` sibling until
/// `InRule` moves `n[{0}]` INSIDE `m`; the contractum CREATES the `OpenRule` redex, the
/// re-drive fires it, and the subject rests `{m[{c[{0}], 0}]}` after exactly the ordered
/// two-firing cascade.
#[tokio::test]
async fn in_then_open_cascades_to_quiescence()  {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())])),
        g_amb(
            g_name("m"),
            g_bag(vec![g_open(g_name("n"), g_bag(vec![g_leaf_amb("c")]))]),
        ),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    let expected = obag(vec![oamb(oname("m"), obag(vec![o_leaf_amb("c"), ozero()]))]);
    assert_eq!(
        flatten(&set.out_values[0]),
        expected,
        "the cascade rests {{m[{{c[{{0}}], 0}}]}} — In created the Open redex, the \
         re-drive fired it"
    );
    assert_green_drive(&set, &channels, &subject_value, &["InRule", "OpenRule"]);
}

// ── (e) the F1 extrusion/float-boundary subject ────────────────────────────────────────

/// The F1 subject `{new(x, n[{in(m, 0)}]) | m[{x[{0}]}]}`: the In-redex is split across
/// the `new` boundary AND the residual references a FREE `x` distinct from the bound one
/// (the capture hazard the conditional float stalled on). The generated invocation's
/// boundary canonicalization (the A-S5.4a unconditional unbind-first float) extrudes the
/// binder — the seed subject is `^lambda({…})` — the driver descends the binder arm,
/// fires In UNDER it, and rests `new(x', {m[{n[{0}], x[{0}]}]})` with the free `x`
/// SURVIVING as `^free` (never captured: no `^bound` occurs anywhere in the NF).
#[tokio::test]
async fn f1_subject_drives_through_the_float_boundary_capture_free() {
    mettail_runtime::clear_var_cache();
    let (backend, _fp) = ambient_backend();
    let (set, channels, subject) =
        drive_parsed(&backend, "{new(x, n[{in(m, 0)}]) | m[{x[{0}]}]}").await;

    // The boundary float ran: the SEED subject is binder-outermost.
    let Value::Term { constructor, children } = &subject else {
        panic!("the canonicalized seed subject is a term: {subject:?}");
    };
    assert_eq!(
        constructor, LAMBDA_REFLECT_LABEL,
        "the unconditional unbind-first float extruded the binder to the top: {subject:?}"
    );
    assert!(
        matches!(&children[0], Value::Bag(_)),
        "the floated body is the (flat) subject bag: {subject:?}"
    );

    // The resting term: still binder-outermost, In fired underneath, and NO ^bound
    // occurs — the freshened binder is vacuous and the free residual `x` was NOT
    // captured (the α/capture-avoidance pin).
    let observed = flatten(&set.out_values[0]);
    let Value::Term { constructor, children } = &observed else {
        panic!("the resting term is the floated binder: {observed:?}");
    };
    assert_eq!(constructor, LAMBDA_REFLECT_LABEL, "the NF keeps the floated binder");
    fn contains_constructor(value: &Value, label: &str) -> bool {
        match value {
            Value::Term { constructor, children } => {
                constructor == label
                    || children.iter().any(|child| contains_constructor(child, label))
            },
            Value::Bag(entries) => entries
                .iter()
                .any(|(element, _)| contains_constructor(element, label)),
            _ => false,
        }
    }
    assert!(
        !contains_constructor(&observed, "^bound"),
        "no ^bound occurs in the NF — the float freshened the binder, so the free `x` \
         in the residual was never captured: {observed:?}"
    );
    let top = bag_elems(&children[0]).expect("the floated body rests as a bag");
    assert_eq!(top.len(), 1, "In moved n inside m: {observed:?}");
    assert_green_drive(&set, &channels, &subject, &["InRule"]);
}

// ── (f) the guard VETO ─────────────────────────────────────────────────────────────────

/// `{na[{in(nb, 0)}] | nc[{0}]}` — `nb ≠ nc`, so the In arm's cross-level
/// `MatchCase.guard` evaluates false ON THE REDUCER and the case falls through to the
/// descent arms: NOTHING fires (ledger EMPTY), the subject rests canonically, and the
/// host mirror agrees it has no redex.
#[tokio::test]
async fn guard_veto_name_mismatch_does_not_fire() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_amb(g_name("na"), g_bag(vec![g_in(g_name("nb"), g_zero())])),
        g_leaf_amb("nc"),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    assert!(set.fired_data.is_empty(), "the guard veto: the ledger is EMPTY");
    assert_eq!(
        flatten(&set.out_values[0]),
        flatten(&subject_value),
        "the vetoed subject rests unchanged (canonically)"
    );
    assert_green_drive(&set, &channels, &subject_value, &[]);
}

// ── (g) the three MANDATORY flattening subjects (F4 / AM-2 / AM-3) ─────────────────────

/// (g1) the bag-bodied open `{open(n, {a[{0}] | b[{0}]}) | n[{c[{0}]}]}` rests FLAT
/// `{a[{0}], b[{0}], c[{0}]}` — NEVER `{{a|b}, c}` (the carrier's three-case SPLICE leg
/// on the delivered `P` slot).
#[tokio::test]
async fn flattening_bag_bodied_open_rests_flat() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("a"), g_leaf_amb("b")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    let observed = &set.out_values[0];
    assert_eq!(
        observed,
        &flatten(observed),
        "the RAW resting term is ALREADY flat (the splice happened in-Rho, not in the \
         host mirror): {observed:?}"
    );
    assert_eq!(
        observed,
        &obag(vec![o_leaf_amb("a"), o_leaf_amb("b"), o_leaf_amb("c")]),
        "the bag-bodied open rests FLAT {{a[{{0}}], b[{{0}}], c[{{0}}]}}"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OpenRule"]);
}

/// (g2) the EMPTY-bag case `{open(n, {}) | n[{c[{0}]}]}`: the delivered `P` is Nil — the
/// three-case Nil leg splices it as NOTHING (no spurious `@"ac:PPar"!(Nil)` element) —
/// rests `{c[{0}]}`.
#[tokio::test]
async fn flattening_empty_bag_open_splices_as_nothing() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_open(g_name("n"), g_bag(Vec::new())),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    assert_eq!(
        &set.out_values[0],
        &obag(vec![o_leaf_amb("c")]),
        "the empty-bag P contributes NOTHING — no spurious Nil element"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OpenRule"]);
}

/// (g3, AM-3(b) strengthened) the DOUBLE-NESTED never-driven subject
/// `{open(n, {A | {B | {C | D}}}) | n[{R}]}` (a DIRECT seed — the nesting sits under
/// the capability, so no pre-drive ever touched it): ONE carrier splice dissolves one
/// level, and the contractum's own RE-DRIVE (the bag arm's peel + three-case
/// reassembly) dissolves the rest — the resting term is FLAT `{A, B, C, D, R}`. This is
/// the executable witness of the drive-based flattening induction
/// (`driver_flatten_agrees_with_add_flattened_bag`).
#[tokio::test]
async fn flattening_double_nested_never_driven_rests_flat() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let nested = g_bag(vec![
        g_leaf_amb("a"),
        g_bag(vec![g_leaf_amb("b"), g_bag(vec![g_leaf_amb("c"), g_leaf_amb("d")])]),
    ]);
    let subject = g_bag(vec![
        g_open(g_name("n"), nested),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("r")])),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    let observed = &set.out_values[0];
    assert_eq!(
        observed,
        &flatten(observed),
        "the RAW resting term is ALREADY flat: {observed:?}"
    );
    assert_eq!(
        observed,
        &obag(vec![
            o_leaf_amb("a"),
            o_leaf_amb("b"),
            o_leaf_amb("c"),
            o_leaf_amb("d"),
            o_leaf_amb("r"),
        ]),
        "the double-nested never-driven bag rests FLAT {{A, B, C, D, R}} — one splice \
         per reassembly, deeper levels via the contractum re-drive"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OpenRule"]);
}

// ── (h) fuel exhaustion (per-path GInt) ────────────────────────────────────────────────

/// The (d)-cascade subject with per-path fuel 1: `InRule` fires (1 → 0), the re-driven
/// contractum's `OpenRule` redex meets fuel 0 — the arm rests the TYPED `^drive-fuel`
/// datum (the stuck redex soup) instead of firing, OUT never lands
/// (`fuel_exhaustion_never_wrong`), and the cross-check error names BOTH the per-path
/// bound and the global fired count.
#[tokio::test]
async fn cascade_exhausts_the_per_path_fuel_with_the_typed_datum() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())])),
        g_amb(
            g_name("m"),
            g_bag(vec![g_open(g_name("n"), g_bag(vec![g_leaf_amb("c")]))]),
        ),
    ]);
    let (set, channels, _subject_value) = drive_direct(&backend, &fingerprint, &subject, 1).await;

    assert_eq!(
        set.fired_labels().expect("ledger decodes"),
        vec!["InRule".to_string()],
        "exactly the In firing fits the per-path fuel of 1"
    );
    assert_eq!(set.fuel_data.len(), 1, "exactly one typed exhaustion datum rests");
    let datum = par_as_runtime_observation_value(&set.fuel_data[0])
        .expect("the exhaustion datum decodes");
    // The stuck redex is the re-assembled m-body soup `{n[{0}], open(n, {c[{0}]})}`.
    let expected_stuck = obag(vec![
        oamb(oname("n"), obag(vec![ozero()])),
        oopen(oname("n"), obag(vec![o_leaf_amb("c")])),
    ]);
    assert_eq!(
        flatten(&datum),
        expected_stuck,
        "the typed datum is the STUCK Open-redex soup — never an NF claim"
    );
    assert!(
        set.out_values.is_empty(),
        "exhaustion NEVER claims a visible NF (fuel_exhaustion_never_wrong)"
    );
    assert!(set.err_data.is_empty(), "no unrecognized head");

    let violation = drive_cross_check(&set, &channels, true, 1, &|value| {
        ambient_redex_present(&flatten(value))
    })
    .expect_err("fuel exhaustion must surface as the typed cross-check error");
    match &violation {
        DriveCrossCheckError::FuelChannel { channel, count, per_path_fuel, global_fired } => {
            assert_eq!(channel, &channels.fuel);
            assert_eq!(*count, 1);
            assert_eq!(*per_path_fuel, 1, "the error carries the per-path bound");
            assert_eq!(*global_fired, 1, "the error carries the ledger's global count");
        },
        other => panic!("expected the FuelChannel violation, got {other:?}"),
    }
}

// ── (i) the corrupted-σ probe (PS family discipline) ───────────────────────────────────

/// The PS value carrier's σ IS the seeded subject payload, so the family-discipline
/// probe corrupts the payload: the TRUE subject `{n[{in(m,0)}] | m[{r[{0}]}]}` fires In;
/// the CORRUPTED payload swaps the inner capability name (`in(q,0)`, `q ≠ m`) — the
/// cross-level guard vetoes, NOTHING fires, and the resting term is the corrupted
/// subject itself: loudly distinct from the true NF (no host residue can sneak the true
/// answer back in).
#[tokio::test]
async fn corrupted_sigma_payload_does_not_produce_the_true_nf() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();

    let true_subject = g_bag(vec![
        g_amb(g_name("n"), g_bag(vec![g_in(g_name("m"), g_zero())])),
        g_amb(g_name("m"), g_bag(vec![g_leaf_amb("r")])),
    ]);
    let (true_set, true_channels, true_value) =
        drive_direct(&backend, &fingerprint, &true_subject, DRIVE_DEFAULT_FUEL).await;
    let true_nf = flatten(&true_set.out_values[0]);
    assert_green_drive(&true_set, &true_channels, &true_value, &["InRule"]);

    let corrupted = g_bag(vec![
        g_amb(g_name("n"), g_bag(vec![g_in(g_name("q"), g_zero())])),
        g_amb(g_name("m"), g_bag(vec![g_leaf_amb("r")])),
    ]);
    let (set, _channels, corrupted_value) =
        drive_direct(&backend, &fingerprint, &corrupted, DRIVE_DEFAULT_FUEL).await;

    assert!(set.fired_data.is_empty(), "the corrupted payload never fires (guard veto)");
    assert_eq!(
        flatten(&set.out_values[0]),
        flatten(&corrupted_value),
        "the resting term is exactly the corrupted payload's NF (itself)"
    );
    assert_ne!(
        flatten(&set.out_values[0]),
        true_nf,
        "the corrupted σ payload must NOT produce the true subject's NF — the firing \
         output is a function of the DELIVERED payload (family discipline)"
    );
}

// ── (j) the decision-(3) NON-CONFLUENT subject: valid-NF-set MEMBERSHIP ────────────────

/// `{open(n, {p[{0}]}) | n[{q[{0}]}] | n[{r[{0}]}]}` — TWO `n`-ambients compete for one
/// `open(n, ·)`: the spatial matcher's multiset element choice legitimately picks
/// either. The test asserts MEMBERSHIP in the ENUMERATED valid-NF set (decision (3) —
/// any-valid-reduction, never a unique-NF claim), exactly one `OpenRule` firing, and the
/// AM-5 replay (which searches the same choice space) reproduces the observed member.
#[tokio::test]
async fn non_confluent_open_rests_in_the_valid_nf_set() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let subject = g_bag(vec![
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("p")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("q")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("r")])),
    ]);
    let (set, channels, subject_value) =
        drive_direct(&backend, &fingerprint, &subject, DRIVE_DEFAULT_FUEL).await;

    // The valid-NF set, enumerated by the host mirror: one application of OpenRule at
    // the top level, either pairing.
    let valid_nfs = open_apply_here(
        &bag_elems(&flatten(&subject_value)).expect("the subject is a bag"),
    );
    assert_eq!(valid_nfs.len(), 2, "two legal pairings ⟹ two valid NFs");
    let expected_a = obag(vec![
        o_leaf_amb("p"),
        o_leaf_amb("q"),
        oamb(oname("n"), obag(vec![o_leaf_amb("r")])),
    ]);
    let expected_b = obag(vec![
        o_leaf_amb("p"),
        o_leaf_amb("r"),
        oamb(oname("n"), obag(vec![o_leaf_amb("q")])),
    ]);
    assert!(
        valid_nfs.contains(&expected_a) && valid_nfs.contains(&expected_b),
        "the enumerated set is exactly the two pairings: {valid_nfs:?}"
    );

    let observed = flatten(&set.out_values[0]);
    assert!(
        valid_nfs.contains(&observed),
        "decision (3): the resting term is a MEMBER of the valid-NF set\n  observed: \
         {observed:?}\n  set: {valid_nfs:?}"
    );
    assert_green_drive(&set, &channels, &subject_value, &["OpenRule"]);
}
