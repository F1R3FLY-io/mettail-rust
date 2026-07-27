//! Where does a guest's non-determinism become a TUPLESPACE conflict?
//!
//! Measured, because the answer decides what `[*]` can return. Three cells:
//!
//! 1. a plain Rholang race — one receive, two candidate data — the control that
//!    proves the engine branches on a real conflict;
//! 2. two receives competing for one datum — the dual shape;
//! 3. `AmbDemo`'s structural-AC `OpenRule` MATCH receiver over the open race,
//!    which is the smallest lowering of the Ambient rule.
#![cfg(feature = "amb-demo-runtime")]

#[path = "../../languages/tests/definitions/ambdemo.rs"]
mod ambdemo;

use ambdemo::AmbDemoLanguage;
use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_rholang_runtime::speculation::delivery::resting_on_string;
use mettail_rholang_runtime::speculation::search::{Explorer, Lookahead, TraceMode};
use mettail_rholang_runtime::speculation::SpeculativeSandbox;
use mettail_rholang_runtime::{par_as_runtime_observation_value, PlannedRhoBackend};
use mettail_runtime::Language;
use models::rhoapi::{BindPattern, ReceiveBind};
use models::rhoapi::{Par, Send};
use models::rust::utils::{
    new_freevar_var, new_gint_par, new_gstring_par, new_receive_par, new_send_par,
};
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const OUT: &str = "OUT";

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "conflict probe host"));
    budget
}

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

fn send_int(channel: &str, value: i64) -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(chan(channel)),
        data: vec![new_gint_par(value, Vec::new(), false)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

/// `for(@x <- source) { OUT!(x) }` — a linear receive that forwards what it got.
fn forwarder(source: &str) -> Par {
    new_receive_par(
        vec![ReceiveBind {
            patterns: vec![models::rust::utils::new_freevar_par(0, Vec::new())],
            source: Some(chan(source)),
            remainder: None,
            free_count: 1,
        }],
        Par::default().with_sends(vec![Send {
            chan: Some(chan(OUT)),
            data: vec![models::rust::utils::new_boundvar_par(0, Vec::new(), false)],
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

async fn explore(program: Par, label: &str) -> usize {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(1_000_000));
    let mut explorer =
        Explorer::with_mode(&sandbox, TraceMode::IndependenceReduced).observing(move |report| {
            eprintln!(
                "  [{} level {}] degrees={:?} classes={:?} → frontier={} quiescent={}",
                label,
                report.level,
                report.out_degrees,
                report.class_sizes,
                report.frontier,
                report.quiescent
            );
        });
    let exploration = explorer
        .explore(program, Blake2b512Random::create_from_length(128), Lookahead::Unbounded)
        .await
        .expect("exploration");
    eprintln!(
        "[{label}] success={} failure={} max_out_degree={} max_conflict_class={}",
        exploration.success.len(),
        exploration.failure.len(),
        exploration.stats.max_out_degree,
        exploration.stats.max_conflict_class
    );
    for (index, leaf) in exploration.success.iter().enumerate() {
        let decoded: Vec<String> = resting_on_string(&leaf.state, OUT)
            .iter()
            .map(|par| match par_as_runtime_observation_value(par) {
                Some(value) => format!("{value:?}"),
                None => "<undecodable>".to_string(),
            })
            .collect();
        eprintln!("  [{label}] leaf {index}: OUT={decoded:?}");
    }
    exploration.success.len()
}

/// CONTROL 1 — one linear receive, two candidate data. The two selections share
/// the CONTINUATION, so they conflict: a genuine choice, and `[*]` must return
/// two.
#[tokio::test]
async fn one_receive_two_data_is_a_conflict() {
    let program = send_int("c", 1)
        .append(send_int("c", 2))
        .append(forwarder("c"));
    let leaves = explore(program, "1-recv-2-data").await;
    assert_eq!(leaves, 2, "one receive racing two data has TWO outcomes");
}

/// CONTROL 2 — two linear receives, one datum. The two selections share the
/// DATUM, so they conflict. Both forward to OUT, so the leaves differ only by
/// which receive is left resting — a real difference in the configuration.
#[tokio::test]
async fn two_receives_one_datum_is_a_conflict() {
    let program = send_int("c", 1)
        .append(forwarder("c"))
        .append(forwarder("d"))
        .append(send_int("d", 9));
    let leaves = explore(program, "2-recv-1-datum").await;
    eprintln!("[2-recv-1-datum] leaves={leaves}");
}

/// CONTROL 3 — two INDEPENDENT COMMs. No shared resource, so no choice: one
/// leaf, and the reduction says so with `max_conflict_class == 1`.
#[tokio::test]
async fn two_independent_comms_are_not_a_choice() {
    let program = send_int("c", 1)
        .append(forwarder("c"))
        .append(send_int("d", 2))
        .append(forwarder("d"));
    let leaves = explore(program, "independent").await;
    assert_eq!(leaves, 1, "independent COMMs are not alternatives");
}

// ── AmbDemo's structural-AC OpenRule receiver over the open race ───────────

fn amb_demo_backend() -> PlannedRhoBackend {
    let source = AmbDemoLanguage
        .metadata()
        .definition_source()
        .expect("definition_source");
    let def = mettail_rholang_codegen::reconstruct_language_def(source).expect("reconstruct");
    let lowering = mettail_rholang_codegen::lower_language_def(&def);
    let requirements = mettail_rholang_codegen::RhoDefaultBackendRequirements {
        coverage: mettail_rholang_codegen::RhoCoverageEvidence::CoveredRejectedRules(
            mettail_rholang_codegen::suggest_rejected_rule_dispositions(&def, &lowering),
        ),
        guard_coverage: mettail_rholang_codegen::RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = mettail_rholang_codegen::plan_rho_default_backend(&def, requirements).expect("plan");
    PlannedRhoBackend::from_plan(plan)
}

/// `AmbDemo`'s open race `{ open(na, A) | na[B] | open(na, 0) }` through the
/// structural-AC MATCH receiver — the smallest in-Rho lowering of the Ambient
/// `OpenRule`. Reports whether the two legal pairings become a tuplespace
/// CONFLICT (a choice) or two independent firings.
#[tokio::test]
async fn ambdemo_open_race_conflict_structure() {
    mettail_runtime::clear_var_cache();
    let backend = amb_demo_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] | open(na, 0) }")
        .expect("AmbDemo must parse the open race");
    let invocation = match AmbDemoLanguage::rho_net_match_invocation_to(term.as_ref(), OUT) {
        Ok(invocation) => invocation,
        Err(detail) => {
            eprintln!("[ambdemo] the match path REJECTED the race: {detail}");
            return;
        },
    };
    let leaves = explore(installed.append(invocation.call.clone()), "ambdemo-race").await;
    eprintln!("[ambdemo-race] leaves={leaves}");
}

/// The SPREAD-match lowering of the same race: `rho_net_match_invocation_from_dovetail_to`
/// publishes the subject's ground bag elements on the site-keyed AC carrier and
/// the co-installed receiver binds the two structured elements + `rest` ON the
/// reducer. If the elements are separate data on one channel, the two legal
/// pairings are two SELECTIONS sharing the ambient datum — a real conflict.
#[tokio::test]
async fn ambdemo_open_race_through_the_spread() {
    mettail_runtime::clear_var_cache();
    let backend = amb_demo_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let term = AmbDemoLanguage
        .parse_term("{ open(na, A) | na[B] | open(na, 0) }")
        .expect("AmbDemo must parse the open race");
    let report = AmbDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("AmbDemo Dovetail report must compile");
    eprintln!(
        "[spread] the host report records {} firing(s)",
        report.rewrite_justifications.len()
    );
    let invocation = match AmbDemoLanguage::rho_net_match_invocation_from_dovetail_to(
        term.as_ref(),
        &report,
        OUT,
    ) {
        Ok(invocation) => invocation,
        Err(detail) => {
            eprintln!("[spread] the spread-match path REJECTED the race: {detail}");
            return;
        },
    };
    let leaves = explore(installed.append(invocation.call.clone()), "ambdemo-spread").await;
    eprintln!("[ambdemo-spread] leaves={leaves}");
}

// Silence the unused-import lint for helpers kept for symmetry.
#[allow(dead_code)]
fn unused(_: fn(i32, Vec<u8>) -> models::rhoapi::Var, _: BindPattern) {
    let _ = new_freevar_var;
    let _ = new_send_par;
}
