//! # X7 — ★★ `[*]` END TO END: the acceptance program
//!
//! The two halves of the lookahead feature were built and measured separately — the SURFACE
//! (`x5_lookahead_lowering.rs`: `x!(P)[*] ⟿ @"^spec-all"!(⟦P⟧, x)`, and the fail-closed
//! resting request when nothing serves it) and the ENGINE (`s2_lookahead_service.rs`:
//! `LookaheadService::serve` over a genuine tuplespace conflict). Neither of them makes a
//! `[*]` in a running program *do* anything. This file is the bolt, and its central cell is
//! the acceptance program:
//!
//! ```text
//! @"results"!(lambda`plus two three`)[*] |
//! @"results"!(lambda`mult two three`)[*] |
//! for(@lambda`lam f. lam x. ${body}` <- @"results") { @"OUT"!(lambda`${body}`) }
//! ```
//!
//! ★ **The payloads on `@"results"` are normal forms the MACHINE computed.** Nothing in the
//! source spells out a Church numeral; `plus 2 3` and `mult 2 3` are β-reduced inside a
//! speculative sandbox, one enumerated COMM at a time, and the results arrive on `@"results"`
//! *because `[*]` drove them*. A demo whose inputs are transcribed constants proves nothing
//! about the machine, which is exactly why `demos/flt-lambda-lab/04-desk.rho` — whose three
//! numerals ARE transcribed — is not this.
//!
//! ## What each cell holds down
//!
//! | cell | the thing that would otherwise be silently wrong |
//! |---|---|
//! | [`the_acceptance_program_runs`] | the whole bolt: request → server → engine → reply → an ordinary FLT receive, in ONE round |
//! | [`both_delivery_forms_are_published`] | the bare term AND the trace-keyed provenance AND the FIPS collections — "both forms are wanted, this is not either/or" |
//! | [`two_independent_lookaheads_do_not_collide`] | one installed continuation serves `n` requests; two `[*]`s in one program deliver two different answers |
//! | [`a_bounded_lookahead_truncates_and_says_so`] | `[n]` publishes a resumable handle rather than an empty answer |
//! | [`an_unregistered_guest_is_refused_loudly`] | ★ a foreign subject with no evaluator is a typed refusal, NOT an inert exploration that hands the subject back as a "normal form" |
//! | [`omega_reports_the_guest_evaluator_giving_up`] | a branch that reached quiescence WITHOUT computing is a trace-keyed FAILURE, not silence |
//! | [`installing_the_server_changes_nothing_a_lookahead_free_program_observes`] | ★ the server is INERT for a program that contains no `[*]` — two installed continuations on channels nothing sends to |
#![cfg(all(feature = "rhocalc-runtime", feature = "lambda-runtime"))]

use std::collections::HashMap;
use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rhocalc::Proc;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def,
    suggest_rejected_rule_dispositions, FltRegistry, FltResolve, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use mettail_rholang_runtime::lookahead::{
    SPEC_ALL_CHANNEL, SPEC_DELIVERY_CHANNEL, SPEC_ERR_CHANNEL, SPEC_FAILURE_CHANNEL,
    SPEC_N_CHANNEL, SPEC_SUCCESS_CHANNEL, SPEC_TRUNCATED_CHANNEL,
};
use mettail_rholang_runtime::speculation::server::{LookaheadEngine, SpeculationGuest};
use mettail_rholang_runtime::{
    lower_rhocalc_proc_with_resolver, par_as_runtime_observation_value,
    run_normalized_par_with_lookahead_engine, PlannedRhoBackend,
};
use mettail_runtime::{clear_var_cache, Language};
use models::rhoapi::Par;

// ══════════════════════════════════════════════════════════════════════════
// The λ terms, spelled out ONCE — as SOURCE, never as an expected answer
// ══════════════════════════════════════════════════════════════════════════

/// `plus ≡ λm.λn.λf.λx. m f (n f x)` applied to the Church numerals 2 and 3.
const PLUS_TWO_THREE: &str = "lambda`((lam m. lam n. lam f. lam x. ((m, f), ((n, f), x)), \
                              lam f. lam x. (f, (f, x))), lam f. lam x. (f, (f, (f, x))))`";

/// `mult ≡ λm.λn.λf. m (n f)` applied to the Church numerals 2 and 3.
const MULT_TWO_THREE: &str = "lambda`((lam m. lam n. lam f. (m, (n, f)), lam f. lam x. (f, (f, x))), \
                              lam f. lam x. (f, (f, (f, x))))`";

/// `Ω ≡ (λx. x x) (λx. x x)` — one β step takes it to itself, forever.
const OMEGA: &str = "lambda`(lam x. (x, x), lam x. (x, x))`";

// ══════════════════════════════════════════════════════════════════════════
// Harness
// ══════════════════════════════════════════════════════════════════════════

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

/// The engine the `rhocalc` interpreter installs: the Lambda guest, driven by its own in-Rho
/// quiescence driver inside every speculative sandbox.
fn lambda_engine() -> LookaheadEngine {
    let (backend, fingerprint) = lambda_backend();
    let prelude = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("the installed Lambda Rho-net program must lower");
    LookaheadEngine::new().with_guest(SpeculationGuest::driven(fingerprint, prelude))
}

fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lambda", Box::new(LambdaLanguage)))
}

fn lower(source: &str) -> Par {
    clear_var_cache();
    let proc = Proc::parse_via_wpda(source)
        .unwrap_or_else(|err| panic!("X7 source must parse: {source}\n{err}"));
    lower_rhocalc_proc_with_resolver(&proc, guest_resolver())
        .unwrap_or_else(|err| panic!("X7 source must lower: {source}\n{err:?}"))
}

/// Every channel a lookahead-bearing run has anything to say on.
fn observed() -> Vec<&'static str> {
    vec![
        "OUT",
        "results",
        SPEC_SUCCESS_CHANNEL,
        SPEC_FAILURE_CHANNEL,
        SPEC_TRUNCATED_CHANNEL,
        SPEC_ERR_CHANNEL,
        SPEC_DELIVERY_CHANNEL,
        SPEC_ALL_CHANNEL,
        SPEC_N_CHANNEL,
    ]
}

async fn run(source: &str) -> HashMap<String, Vec<Par>> {
    let program = lower(source);
    let engine = lambda_engine();
    let rest = run_normalized_par_with_lookahead_engine(&program, &engine, &observed())
        .await
        .expect("the lookahead-bearing program must run to rest");
    for channel in observed() {
        let count = rest.get(channel).map(Vec::len).unwrap_or_default();
        if count > 0 {
            eprintln!("[X7] {channel} ← {count} datum(a)");
        }
    }
    rest
}

fn on<'rest>(rest: &'rest HashMap<String, Vec<Par>>, channel: &str) -> &'rest [Par] {
    rest.get(channel).map(Vec::as_slice).unwrap_or_default()
}

/// The DECODED observation values on a channel, sorted so a comparison is over the multiset.
fn decoded(rest: &HashMap<String, Vec<Par>>, channel: &str) -> Vec<String> {
    let mut rendered: Vec<String> = on(rest, channel)
        .iter()
        .map(|par| match par_as_runtime_observation_value(par) {
            Some(value) => format!("{value:?}"),
            None => "<undecodable>".to_string(),
        })
        .collect();
    rendered.sort();
    rendered
}

/// How deeply a decoded Church-numeral BODY nests `App` — i.e. which numeral it is.
///
/// The acceptance program republishes the λ-term's *body* (`lam f. lam x. ${body}`), so `n`
/// applications of `f` to `x` is the numeral `n`.
fn application_depth(rendered: &str) -> usize {
    rendered.matches("constructor: \"App\"").count()
}

/// The request channels must be EMPTY: a request still resting means nothing served it, and
/// `crate::lookahead::unserved_requests` exists to make exactly that loud.
fn assert_every_request_was_served(rest: &HashMap<String, Vec<Par>>) {
    for channel in [SPEC_ALL_CHANNEL, SPEC_N_CHANNEL] {
        assert!(
            on(rest, channel).is_empty(),
            "★ a lookahead request RESTED on {channel}: nothing served it. {:?}",
            on(rest, channel)
        );
    }
    assert!(
        on(rest, SPEC_ERR_CHANNEL).is_empty(),
        "the engine reported a request-level refusal: {:?}",
        on(rest, SPEC_ERR_CHANNEL)
    );
}

// ══════════════════════════════════════════════════════════════════════════
// ★★ THE ACCEPTANCE PROGRAM
// ══════════════════════════════════════════════════════════════════════════

/// ★★ Two `[*]` sends and one collecting FLT receive, in one program, in one round.
///
/// The receive's pattern `lambda\`lam f. lam x. ${body}\`` is an ORDINARY Foreign Language
/// Term pattern — nothing about it knows a speculation produced the datum it matched. That is
/// the point of putting the bare terminal term on the reply channel rather than a tuple: a
/// program filters over values the machine computed with the same syntax it filters over
/// values someone sent.
#[tokio::test]
async fn the_acceptance_program_runs() {
    let rest = run(&format!(
        r#"@"results"!({PLUS_TWO_THREE})[*] |
           @"results"!({MULT_TWO_THREE})[*] |
           for(@lambda`lam f. lam x. ${{body}}` <- @"results") {{ @"OUT"!(lambda`${{body}}`) }}"#
    ))
    .await;

    assert_every_request_was_served(&rest);

    let out = decoded(&rest, "OUT");
    for (index, value) in out.iter().enumerate() {
        eprintln!("[X7] OUT[{index}] depth={} {value}", application_depth(value));
    }
    let leftover = decoded(&rest, "results");
    for (index, value) in leftover.iter().enumerate() {
        eprintln!("[X7] results[{index}] depth={} (unconsumed)", application_depth(value));
    }

    // ONE receive consumes ONE datum; the other speculative result is left resting, exactly
    // as it would be for two ordinary sends.
    assert_eq!(out.len(), 1, "the single `for` consumes one delivered normal form: {out:?}");
    assert_eq!(
        leftover.len(),
        1,
        "…and the other speculative result rests, unconsumed: {leftover:?}"
    );

    // ★ THE MEASUREMENT: the two delivered values are the Church numerals 5 (`plus 2 3`) and
    // 6 (`mult 2 3`), each read as the nesting depth of the republished BODY. Nothing in the
    // source spells either of them out.
    let mut depths: Vec<usize> = out
        .iter()
        .chain(leftover.iter())
        .map(|value| application_depth(value))
        .collect();
    depths.sort();
    assert_eq!(
        depths,
        vec![5, 6],
        "★ the machine must have COMPUTED `plus 2 3` = 5 and `mult 2 3` = 6 — the two \
         payloads on @\"results\" are normal forms `[*]` drove, not literals. Got {out:?} / \
         {leftover:?}"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Both delivery forms
// ══════════════════════════════════════════════════════════════════════════

/// ★ The bare term on `x`, the trace-keyed provenance on the companion channels, AND the
/// FIPS's own three collections — from one exploration. Both forms are wanted.
#[tokio::test]
async fn both_delivery_forms_are_published() {
    let rest = run(&format!(r#"@"results"!({PLUS_TWO_THREE})[*]"#)).await;
    assert_every_request_was_served(&rest);

    // 1. The bare terminal term, on the send's own channel.
    let reply = on(&rest, "results");
    assert_eq!(reply.len(), 1, "λ is confluent: one branch, one bare term");
    assert_eq!(
        application_depth(&decoded(&rest, "results")[0]),
        5,
        "and it is the computed Church numeral 5"
    );

    // 2. The trace-keyed provenance: `[trace, term]` per success branch.
    use models::rhoapi::expr::ExprInstance;
    let success = on(&rest, SPEC_SUCCESS_CHANNEL);
    assert_eq!(success.len(), 1, "one provenance datum per success branch");
    let Some(ExprInstance::EListBody(entry)) = success[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("a provenance datum must be an EList, got {:?}", success[0]);
    };
    assert_eq!(entry.ps.len(), 2, "[trace, term]");
    let Some(ExprInstance::EListBody(trace)) = entry.ps[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the trace must be an EList of step digests");
    };
    assert!(
        !trace.ps.is_empty(),
        "★ the branch fired real COMMs — a trace of length 0 would mean the subject was \
         explored INERT, which is what omitting the guest prelude looks like"
    );
    eprintln!("[X7] the success branch's trace is {} step(s) long", trace.ps.len());
    assert!(
        matches!(
            trace.ps[0].exprs.first().and_then(|e| e.expr_instance.as_ref()),
            Some(ExprInstance::GByteArray(bytes)) if bytes.len() == 32
        ),
        "a step is a 32-byte content digest"
    );

    // 3. The FIPS's own three collections, as one datum: `[success, truncated, failure]`.
    let delivery = on(&rest, SPEC_DELIVERY_CHANNEL);
    assert_eq!(delivery.len(), 1, "one collection triple per served request");
    let Some(ExprInstance::EListBody(collections)) = delivery[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the delivery datum must be an EList, got {:?}", delivery[0]);
    };
    assert_eq!(collections.ps.len(), 3, "[success, truncated, failure]");
    let Some(ExprInstance::ESetBody(fips_success)) = collections.ps[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the FIPS `success` collection must be an ESet");
    };
    assert_eq!(
        fips_success.ps.len(),
        1,
        "the FIPS success set carries one entry per quiescent branch"
    );

    // Nothing died and nothing was cut short.
    assert!(on(&rest, SPEC_FAILURE_CHANNEL).is_empty(), "nothing aborted");
    assert!(on(&rest, SPEC_TRUNCATED_CHANNEL).is_empty(), "`[*]` runs to quiescence");
}

// ══════════════════════════════════════════════════════════════════════════
// Independence, bounds, and the two loud failure modes
// ══════════════════════════════════════════════════════════════════════════

/// Two independent `[*]` sends in one program are both served — the installed continuation is
/// persistent, so `n` requests need no arrangement by the caller — and they deliver two
/// DIFFERENT answers, so one delivery cannot masquerade as two.
#[tokio::test]
async fn two_independent_lookaheads_do_not_collide() {
    let rest = run(&format!(
        r#"@"results"!({PLUS_TWO_THREE})[*] | @"results"!({MULT_TWO_THREE})[*]"#
    ))
    .await;
    assert_every_request_was_served(&rest);

    let mut depths: Vec<usize> = decoded(&rest, "results")
        .iter()
        .map(|value| application_depth(value))
        .collect();
    depths.sort();
    assert_eq!(depths, vec![5, 6], "two requests, two distinct computed answers");
    assert_eq!(
        on(&rest, SPEC_SUCCESS_CHANNEL).len(),
        2,
        "…and two provenance data, one per request's single branch"
    );
    assert_eq!(
        on(&rest, SPEC_DELIVERY_CHANNEL).len(),
        2,
        "…and two FIPS collection triples, one per served request"
    );
}

/// `[n]` cuts the exploration short and publishes a RESUMABLE handle rather than an empty
/// answer: `[trace, handle, |E(S)|]` on the truncated channel, and nothing on the reply
/// channel, because no branch reached a normal form.
#[tokio::test]
async fn a_bounded_lookahead_truncates_and_says_so() {
    let rest = run(&format!(r#"@"results"!({PLUS_TWO_THREE})[3]"#)).await;
    assert_every_request_was_served(&rest);

    assert!(
        on(&rest, "results").is_empty(),
        "three steps do not reach `plus 2 3`'s normal form, so nothing may be delivered as one"
    );
    let truncated = on(&rest, SPEC_TRUNCATED_CHANNEL);
    assert!(!truncated.is_empty(), "…and the cut branch is PUBLISHED, not dropped");

    use models::rhoapi::expr::ExprInstance;
    let Some(ExprInstance::EListBody(entry)) = truncated[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("a truncated datum must be an EList");
    };
    assert_eq!(entry.ps.len(), 3, "[trace, handle, |E(S)|]");
    assert!(
        matches!(
            entry.ps[1].exprs.first().and_then(|e| e.expr_instance.as_ref()),
            Some(ExprInstance::GByteArray(bytes)) if bytes.len() == 32
        ),
        "the handle is a 32-byte trace digest"
    );
    let Some(ExprInstance::GInt(frontier)) = entry.ps[2]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the frontier must be a ground integer");
    };
    assert!(*frontier > 0, "a truncated branch had somewhere left to go");
    eprintln!("[X7] the `[3]` cut left a frontier of {frontier}");
}

/// ★ A reflected foreign subject with NO registered evaluator is refused on `^spec-err`, and
/// **nothing is delivered**.
///
/// This is the failure this whole design is arranged around. A reflected term is inert: an
/// engine that explored it anyway would find exactly one leaf — the subject, unreduced — and
/// publish it on the reply channel, where it is indistinguishable from a normal form. The
/// program would look correct and would be reporting its own input back to itself.
#[tokio::test]
async fn an_unregistered_guest_is_refused_loudly() {
    let program = lower(&format!(r#"@"results"!({PLUS_TWO_THREE})[*]"#));
    // An engine with NO guests — the Lambda prelude is deliberately not registered.
    let engine = LookaheadEngine::new();
    let rest = run_normalized_par_with_lookahead_engine(&program, &engine, &observed())
        .await
        .expect("the program still runs; the REQUEST is what is refused");

    assert!(
        on(&rest, "results").is_empty(),
        "★ nothing may be delivered for a subject no evaluator can reduce — a term published \
         here would be the SUBJECT masquerading as a normal form: {:?}",
        decoded(&rest, "results")
    );
    let refusals = on(&rest, SPEC_ERR_CHANNEL);
    assert_eq!(refusals.len(), 1, "…and the refusal is LOUD");
    let rendered = format!("{:?}", refusals[0]);
    assert!(
        rendered.contains("no evaluator is registered"),
        "the refusal must say what is missing: {rendered}"
    );
    // The request WAS consumed — the server is installed, it simply refuses this subject.
    assert!(
        on(&rest, SPEC_ALL_CHANNEL).is_empty(),
        "a refusal is an answer: the request must not also rest unserved"
    );
}

/// ★ **Non-interference.** Installing the request server changes nothing a program without a
/// `[*]` observes.
///
/// The server is two *installed* continuations on two reserved quoted channels. A program
/// that sends on neither cannot interact with them — but "cannot" is a claim about f1r3node's
/// installed-continuation semantics, and the `rhocalc` interpreter now routes **every**
/// process through the server-bearing runtime. So the claim is measured rather than reasoned:
/// the corpus below is the demo shapes that present tonight, run both ways, asserted equal
/// datum-for-datum.
///
/// This is also the cell that tells a future reader which side a demo regression is on. If a
/// demo publishes nothing, this test says whether the server is why.
#[tokio::test]
async fn installing_the_server_changes_nothing_a_lookahead_free_program_observes() {
    // Every shape the two bundled demo suites use: a plain FLT send + receive, a nested-hole
    // destructure, a `where`-guarded desk, and a nested-hole desk with a `where` guard.
    let corpus: [(&str, String); 4] = [
        (
            "plain send + receive",
            r#"@"r"!(lambda`lam f. lam x. (f, (f, x))`) | for(@lambda`${t}` <- @"r") { @"OUT"!(lambda`${t}`) }"#
                .to_string(),
        ),
        (
            "nested-hole destructure",
            r#"@"r"!(lambda`lam f. lam x. (f, (f, x))`) |
               for(@lambda`lam f. lam x. ${b}` <- @"r") { @"OUT"!(lambda`${b}`) }"#
                .to_string(),
        ),
        (
            "where-guarded desk (bare hole)",
            r#"@"r"!(lambda`lam f. lam x. (f, (f, x))`) |
               @"r"!(lambda`lam x. x`) |
               for(@lambda`${t}` <- @"r"
                   where lambda`${t}` == lambda`lam f. lam x. (f, (f, x))`) { @"OUT"!(lambda`${t}`) }"#
                .to_string(),
        ),
        (
            // ★ `demos/flt-lambda-lab/04-desk.rho`'s shape: a NESTED-hole pattern under a
            // `where` guard over the reconstructed term.
            "where-guarded desk (nested hole)",
            r#"@"r"!(lambda`lam f. lam x. (f, (f, x))`) |
               @"r"!(lambda`lam x. x`) |
               for(@lambda`lam f. lam x. ${b}` <- @"r"
                   where lambda`lam f. lam x. ${b}` == lambda`lam f. lam x. (f, (f, x))`) {
                 @"OUT"!(lambda`${b}`)
               }"#
            .to_string(),
        ),
    ];

    for (label, source) in corpus {
        let program = lower(&source);
        let with_server = run_normalized_par_with_lookahead_engine(
            &program,
            &lambda_engine(),
            &["OUT", "r"],
        )
        .await
        .expect("the program runs with the request server installed");
        let without_server =
            mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_par_channels(
                &program,
                &["OUT", "r"],
            )
            .await
            .expect("…and without it");

        for channel in ["OUT", "r"] {
            let served = with_server.get(channel).cloned().unwrap_or_default();
            let bare = without_server.get(channel).cloned().unwrap_or_default();
            eprintln!(
                "[X7] non-interference {label:?}: {channel} → {} with server, {} without",
                served.len(),
                bare.len()
            );
            assert_eq!(
                served, bare,
                "★ installing the `[*]` request server must not change what {label:?} \
                 observes on {channel}"
            );
        }
    }
}

/// ★ Ω under `[*]`: the branch reaches tuplespace quiescence having computed nothing, because
/// the guest's driver ran out of per-path fuel. That is published as a trace-keyed branch
/// FAILURE, not as silence.
///
/// Ω is the term whose only honest answer is "I could not finish". A server that published
/// only successful projections would deliver an empty `@"results"` here — the same thing it
/// delivers for a program that legitimately computed nothing — and the difference between
/// "no answer exists" and "I gave up" would be unobservable.
#[tokio::test]
async fn omega_reports_the_guest_evaluator_giving_up() {
    let rest = run(&format!(r#"@"results"!({OMEGA})[*]"#)).await;
    assert!(
        on(&rest, SPEC_ALL_CHANNEL).is_empty(),
        "the request was served — Ω is an answer, not an unserved request"
    );
    assert!(
        on(&rest, "results").is_empty(),
        "Ω has no normal form, so nothing may be delivered as one: {:?}",
        decoded(&rest, "results")
    );
    let failures = on(&rest, SPEC_FAILURE_CHANNEL);
    assert!(
        !failures.is_empty(),
        "★ the guest evaluator gave up and must SAY SO on {SPEC_FAILURE_CHANNEL}"
    );
    let rendered = format!("{:?}", failures[0]);
    eprintln!("[X7] Ω failure datum: {}", &rendered[..rendered.len().min(240)]);
    assert!(
        rendered.contains("^drive-fuel"),
        "the failure must name the guest channel the driver rested on: {rendered}"
    );
}
