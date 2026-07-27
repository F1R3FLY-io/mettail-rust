//! # The `[*]` / `[n]` ABI seam, end to end
//!
//! [`crate::lookahead`](mettail_rholang_runtime::lookahead) owns the wire — the
//! reserved request channels, the request-seed builders, and the fail-closed
//! unserved-request readback. [`LookaheadService`] owns the answer. This file is
//! the contract between them, measured: given a request's operands it must
//! produce, in `Par` form, exactly what each report channel carries.
//!
//! ```text
//!   x!(P)[*]  ⟿  @"^spec-all"!( ⟦P⟧ , x )
//!                        │
//!                        ▼            LookaheadService::serve
//!                 ┌──────────────────────────────────────────────┐
//!                 │  fresh sandbox ─ fund from the host deploy    │
//!                 │  inject `prelude | subject` ─ saturate        │
//!                 │  BFS over E(S) ─ conflict classes ─ leaves    │
//!                 └──────────────────────────────────────────────┘
//!                        │
//!    ┌───────────────────┼────────────────────┬──────────────────┐
//!    ▼                   ▼                    ▼                  ▼
//!   x                ^spec-success       ^spec-failure     ^spec-truncated
//!  bare term          [trace, term]     [trace,[code,msg]]  [trace,handle,|E(S)|]
//! ```
//!
//! The cells check the three things a caller can get wrong: that the reply
//! carries ONE datum per success branch (so an ordinary receive pattern matches
//! it verbatim), that a truncated branch is published with a handle the service
//! will take back, and that the handle really does resume.
#![cfg(feature = "runtime-report")]

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::{Par, ReceiveBind, Send};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gint_par, new_gstring_par, new_receive_par,
};

use mettail_rholang_runtime::lookahead::{
    spec_all_request, spec_n_request, unserved_requests, SPEC_ALL_CHANNEL,
};
use mettail_rholang_runtime::par_as_runtime_observation_value;
use mettail_rholang_runtime::speculation::search::{Lookahead, TraceMode};
use mettail_rholang_runtime::speculation::service::{
    LeafProjection, LookaheadRequest, LookaheadService,
};
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const OUT: &str = "OUT";

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "s2 service host deploy"));
    budget
}

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send(channel: &str, value: i64) -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(chan(channel)),
        data: vec![new_gint_par(value, Vec::new(), false)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

fn forward(source: &str, target: &str) -> Par {
    new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(chan(source)),
            remainder: None,
            free_count: 1,
        }],
        Par::default().with_sends(vec![Send {
            chan: Some(chan(target)),
            data: vec![new_boundvar_par(0, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }]),
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// The subject with a genuine tuplespace conflict: one receive, two data.
fn racing_subject() -> Par {
    send("c", 1).append(send("c", 2)).append(forward("c", OUT))
}

fn rand() -> Blake2b512Random {
    Blake2b512Random::create_from_length(128)
}

/// ★ `[*]` through the service: the reply channel gets ONE BARE TERM per success
/// branch, and the two branches deliver different terms.
///
/// The bare term (rather than a pair) is what makes an ordinary receive pattern
/// match a speculative result verbatim, which is what lets a program filter over
/// values the machine COMPUTED.
#[tokio::test]
async fn the_reply_carries_one_bare_term_per_success_branch() {
    let host = host_budget(1_000_000);
    let response = LookaheadService::serve(
        LookaheadRequest::new(racing_subject(), Lookahead::Unbounded)
            .with_projection(LeafProjection::resting_on(OUT)),
        rand(),
        &host,
    )
    .await
    .expect("the service must serve the request");

    let mut delivered: Vec<String> = response
        .reply
        .iter()
        .map(|par| match par_as_runtime_observation_value(par) {
            Some(value) => format!("{value:?}"),
            None => "<undecodable>".to_string(),
        })
        .collect();
    delivered.sort();
    eprintln!("[serve] reply={delivered:?} consumed={}", response.consumed.value);

    assert_eq!(response.exploration.success.len(), 2, "two branches");
    assert_eq!(delivered.len(), 2, "one datum per branch: {delivered:?}");
    assert_eq!(delivered, vec!["Int(1)".to_string(), "Int(2)".to_string()]);
    assert!(response.failure.is_empty(), "nothing aborted");
    assert!(response.truncated.is_empty(), "`[*]` runs to quiescence");
    assert!(response.error.is_none(), "the request itself was served");
    assert_eq!(
        response.success.len(),
        2,
        "and the provenance channel carries one [trace, term] per branch"
    );
    assert!(
        response.consumed.value > 0,
        "the exploration spent phlogiston the host must be charged for"
    );
}

/// The provenance datum is `[trace, term]` — an `EList` whose head is the trace
/// (itself an `EList` of 32-byte step digests) and whose tail is the branch's
/// term. Two branches carry two DIFFERENT traces.
#[tokio::test]
async fn the_provenance_datum_is_a_trace_and_a_term() {
    let host = host_budget(1_000_000);
    let response = LookaheadService::serve(
        LookaheadRequest::new(racing_subject(), Lookahead::Unbounded)
            .with_projection(LeafProjection::resting_on(OUT)),
        rand(),
        &host,
    )
    .await
    .expect("serve");

    use models::rhoapi::expr::ExprInstance;
    for report in response.success.iter() {
        let Some(ExprInstance::EListBody(entry)) = report
            .datum
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("a provenance datum must be an EList, got {:?}", report.datum);
        };
        assert_eq!(entry.ps.len(), 2, "[trace, term]");
        let Some(ExprInstance::EListBody(trace)) = entry.ps[0]
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
        else {
            panic!("the trace must be an EList of step digests");
        };
        assert_eq!(trace.ps.len(), 1, "each branch fired exactly one step");
        assert!(
            matches!(
                trace.ps[0].exprs.first().and_then(|e| e.expr_instance.as_ref()),
                Some(ExprInstance::GByteArray(bytes)) if bytes.len() == 32
            ),
            "a step is a 32-byte content digest"
        );
    }
    let mut handles: Vec<[u8; 32]> = response
        .success
        .iter()
        .map(|report| report.handle)
        .collect();
    handles.sort();
    handles.dedup();
    assert_eq!(handles.len(), 2, "the two branches have distinct handles");
}

/// ★ `[n]` through the service: a truncated branch is published on its OWN
/// channel with a handle and its remaining frontier, and the service takes the
/// handle back and resumes to what `[*]` reaches.
#[tokio::test]
async fn a_truncated_branch_is_published_with_a_resumable_handle() {
    let host = host_budget(1_000_000);
    let subject = send("c", 1)
        .append(forward("c", "d"))
        .append(forward("d", OUT));

    let cut = LookaheadService::serve(
        LookaheadRequest::new(subject.clone(), Lookahead::Steps(1))
            .with_projection(LeafProjection::resting_on(OUT)),
        rand(),
        &host,
    )
    .await
    .expect("serve `[1]`");
    assert_eq!(cut.truncated.len(), 1, "one truncated branch");
    assert!(cut.success.is_empty(), "…and it did not finish");
    assert_eq!(cut.handles.len(), 1, "the handle is retained host-side");

    // The published truncated datum is `[trace, handle, |E(S)|]`.
    use models::rhoapi::expr::ExprInstance;
    let Some(ExprInstance::EListBody(entry)) = cut.truncated[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("a truncated datum must be an EList");
    };
    assert_eq!(entry.ps.len(), 3, "[trace, handle, frontier]");
    let Some(ExprInstance::GByteArray(published)) = entry.ps[1]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the handle must be a GByteArray");
    };
    assert!(
        cut.handle(published).is_some(),
        "the published handle must name a retained configuration"
    );

    // Resume it: the answer must equal an unbroken `[*]`.
    let unbroken = LookaheadService::serve(
        LookaheadRequest::new(subject, Lookahead::Unbounded)
            .with_projection(LeafProjection::resting_on(OUT)),
        rand(),
        &host,
    )
    .await
    .expect("serve `[*]`");

    let handles: Vec<_> = cut
        .handles
        .iter()
        .map(|(_, branch)| branch.clone())
        .collect();
    let resumed = LookaheadService::resume(
        &handles,
        Lookahead::Unbounded,
        &LeafProjection::resting_on(OUT),
        TraceMode::default(),
        Vec::new(),
        &host,
    )
    .await
    .expect("resume");

    let render = |values: &[Par]| -> Vec<String> {
        let mut rendered: Vec<String> = values
            .iter()
            .map(|par| format!("{:?}", par_as_runtime_observation_value(par)))
            .collect();
        rendered.sort();
        rendered
    };
    eprintln!(
        "[resume] unbroken={:?} resumed={:?}",
        render(&unbroken.reply),
        render(&resumed.reply)
    );
    assert_eq!(
        render(&resumed.reply),
        render(&unbroken.reply),
        "resuming the published handle must reach what an unbroken `[*]` reaches"
    );
}

/// ★ An UNAFFORDABLE request produces branch FAILURES on the failure channel,
/// each `[trace, [code, message]]` — the FIPS's own leaf shape — and never a
/// quiet empty success set.
#[tokio::test]
async fn an_unaffordable_request_publishes_typed_branch_failures() {
    let host = host_budget(2);
    let response = LookaheadService::serve(
        LookaheadRequest::new(racing_subject(), Lookahead::Unbounded)
            .with_projection(LeafProjection::resting_on(OUT)),
        rand(),
        &host,
    )
    .await
    .expect("an unaffordable request is an ANSWER, not a fault");
    assert!(response.reply.is_empty(), "nothing was computed");
    assert!(!response.failure.is_empty(), "and the failure is REPORTED");

    use models::rhoapi::expr::ExprInstance;
    let Some(ExprInstance::EListBody(entry)) = response.failure[0]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("a failure datum must be an EList");
    };
    assert_eq!(entry.ps.len(), 2, "[trace, [code, message]]");
    let Some(ExprInstance::EListBody(reason)) = entry.ps[1]
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    else {
        panic!("the reason must be the FIPS's two-element [code, message] list");
    };
    assert_eq!(reason.ps.len(), 2);
    assert!(
        matches!(
            reason.ps[0]
                .exprs
                .first()
                .and_then(|e| e.expr_instance.as_ref()),
            Some(ExprInstance::GInt(1))
        ),
        "code 1 is out-of-phlogistons"
    );
}

/// The `Configuration` projection delivers the reified terminal configuration —
/// the FIPS's own leaf — rather than a channel's contents, and the two branches'
/// configurations differ.
#[tokio::test]
async fn the_configuration_projection_delivers_a_process() {
    let host = host_budget(1_000_000);
    let response = LookaheadService::serve(
        LookaheadRequest::new(racing_subject(), Lookahead::Unbounded)
            .with_projection(LeafProjection::Configuration),
        rand(),
        &host,
    )
    .await
    .expect("serve");
    assert_eq!(response.reply.len(), 2, "one configuration per branch");
    assert!(
        response.reply.iter().all(|par| !par.sends.is_empty()),
        "a terminal configuration with resting data reifies to sends"
    );
    assert_ne!(response.reply[0], response.reply[1], "two configurations, two processes");
}

/// The wire and the engine agree on what a request looks like: a seed built by
/// [`spec_all_request`] rests on [`SPEC_ALL_CHANNEL`] until something serves it,
/// and [`unserved_requests`] is what makes a missing engine loud. This pins the
/// two halves against each other rather than against their own documentation.
#[tokio::test]
async fn an_unserved_request_is_loud() {
    let subject = racing_subject();
    let seed = spec_all_request(subject.clone(), chan("results"));
    let bounded = spec_n_request(subject, 3, chan("results"));
    assert_ne!(seed, bounded, "`[*]` and `[n]` are distinct requests");

    let resting: Vec<(&'static str, Vec<Par>)> = vec![(SPEC_ALL_CHANNEL, vec![seed])];
    let unserved = unserved_requests(&resting);
    assert_eq!(unserved.len(), 1, "a resting request surfaces as unserved");
    assert_eq!(unserved[0].channel, SPEC_ALL_CHANNEL);
}
