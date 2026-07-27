//! # ★ Ambient's open race under `[*]` — what the LOWERING exposes
//!
//! The intended acceptance gate for the branching engine was: Ambient's open
//! race has two normal forms, so `[*]` over it must return two. This file is
//! that measurement, and it **refutes the premise on which the gate rested** —
//! not the engine, the *lowering*.
//!
//! ## The subject and its two normal forms
//!
//! Over the PRODUCTION `Ambient` language (`languages/src/ambient.rs`,
//! `OpenRule` at lines 67-68):
//!
//! ```text
//!     { open(n, a[0]) | n[b[0]] | open(n, c[0]) }
//!
//!     ─ pair (open(n,a[0]), n[b[0]]) ⟹  { a[0] , b[0] , open(n, c[0]) }   leaf A
//!     ─ pair (open(n,c[0]), n[b[0]]) ⟹  { c[0] , b[0] , open(n, a[0]) }   leaf B
//! ```
//!
//! `N` is genuinely non-linear (the same ambient name must appear in the
//! capability and in the ambient), both pairings dissolve the one ambient, and
//! `A ≠ B`. The rewrite system really does have **two** normal forms — pinned
//! independently by `tests/rho_net_ambient_full.rs::non_confluent_open_rests_in_the_valid_nf_set`,
//! whose host mirror enumerates the valid-NF set and asserts `len() == 2`.
//!
//! ## ★★ What is measured here, and it is the finding
//!
//! **Not one of the three in-Rho lowerings of `OpenRule` presents that choice to
//! the tuplespace.** Every one of them resolves the pairing inside the matcher —
//! the set automaton, the host report, or the drive's own redex arm — and hands
//! the reducer a *single* admissible rendezvous:
//!
//! | lowering | `max_out_degree` | `max_conflict_class` | leaves | why |
//! |---|---|---|---|---|
//! | `^drive` quiescence driver | **12** | **1** | 1 | every enabled rendezvous is the SAME persistent dispatcher continuation taking a DISTINCT datum — a work queue being served, never a choice |
//! | report-free `rho_net_match_invocation_to` | 2 | 1 | 1 | locate-ALL: both redexes are located and both fire, independently |
//! | spread `rho_net_match_invocation_from_dovetail_to` | 1 | 1 | 1 | the located redex is published as one carrier datum |
//!
//! `max_conflict_class == 1` at every node of every one of them is a
//! machine-checkable statement that **no choice was ever made**: every pair of
//! enabled rendezvous was resource-disjoint, so all of them fire and the order
//! is not a decision. That is exactly consistent with the independently recorded
//! measurement that the production Ambient drive lands on Leaf A in 48 runs out
//! of 48, content-driven rather than arrival-ordered.
//!
//! **So `[*]` over the Ambient open race returns ONE, and that is the correct
//! answer for the program it is given.** The engine is not the limitation, and
//! the way to see that is [`tests/s2_speculative_branching.rs`], where the same
//! engine over `c!(1) | c!(2) | for(@x <- c){ OUT!(x) }` — a genuine
//! tuplespace conflict — returns **two**, delivering `Int(1)` on one branch and
//! `Int(2)` on the other, with `max_conflict_class == 2`.
//!
//! ## What would have to change
//!
//! For `[*]` to return two here, an `OpenRule` lowering would have to publish the
//! subject's bag elements as **separate linear data on one carrier channel** and
//! let a receiver bind `(capability, ambient)` from them. The two legal pairings
//! would then be two admissible selections **sharing the ambient datum**, hence
//! conflicting, hence a real branch. That is a change to the rho_net codegen, not
//! to the speculation engine, and it is stated here rather than worked around.
#![cfg(feature = "ambient-runtime")]

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_languages::ambient::AmbientLanguage;
use mettail_rholang_codegen::{
    reflect_ground_term_par, rho_net_drive_call_par_with_fuel, CollectionType, GroundTerm,
    DRIVE_DEFAULT_FUEL, FREE_VAR_REFLECT_LABEL,
};
use mettail_rholang_runtime::speculation::delivery::{deliver, reify, resting_on_string};
use mettail_rholang_runtime::speculation::search::{Exploration, Explorer, Lookahead, TraceMode};
use mettail_rholang_runtime::speculation::SpeculativeSandbox;
use mettail_rholang_runtime::{
    par_as_runtime_observation_value, DriveObservationChannels, PlannedRhoBackend,
};
use mettail_runtime::Language;
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const OUT: &str = "OUT";
const HOST_UNITS: i64 = 4_000_000;

// ══════════════════════════════════════════════════════════════════════════
// Backend + subject
// ══════════════════════════════════════════════════════════════════════════

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

fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
fn g_zero() -> GroundTerm {
    GroundTerm::nullary("PZero")
}
fn g_name(atom: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(atom)])
}
fn g_bag(elements: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::collection(CollectionType::HashBag, "PPar", elements)
}
fn g_amb(name: GroundTerm, body: GroundTerm) -> GroundTerm {
    g_node("PAmb", vec![name, body])
}
fn g_open(name: GroundTerm, cont: GroundTerm) -> GroundTerm {
    g_node("POpen", vec![name, cont])
}
fn g_leaf_amb(atom: &str) -> GroundTerm {
    g_amb(g_name(atom), g_bag(vec![g_zero()]))
}

/// ★ THE SUBJECT: `{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }`.
fn open_race() -> GroundTerm {
    g_bag(vec![
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("a")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("b")])),
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
    ])
}

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "s2 ambient host deploy"));
    budget
}

/// The drive-lowered program: the installed Rho-net program (σ-receivers,
/// `^drive` family, per-rule AC carriers) in parallel with the drive seed.
/// Byte-for-byte the program an ordinary run injects.
fn drive_program(
    backend: &PlannedRhoBackend,
    fingerprint: &str,
    subject: &GroundTerm,
) -> models::rhoapi::Par {
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("the installed Rho-net program must lower");
    let seed = rho_net_drive_call_par_with_fuel(
        fingerprint,
        reflect_ground_term_par(subject, fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    installed.append(seed)
}

/// The randomness an ordinary run uses (`run.rs::inj_on_runtime`), held equal
/// across the two arms so an ordinary-vs-speculative comparison is valid.
fn ordinary_rand() -> Blake2b512Random {
    Blake2b512Random::create_from_length(128)
}

async fn explore(
    program: models::rhoapi::Par,
    mode: TraceMode,
    lookahead: Lookahead,
) -> Exploration {
    let sandbox = SpeculativeSandbox::new()
        .await
        .expect("the speculative sandbox must build");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    let mut explorer = Explorer::with_mode(&sandbox, mode);
    let exploration = explorer
        .explore(program, ordinary_rand(), lookahead)
        .await
        .expect("the exploration must not fail at the infrastructure level");
    exploration
}

/// The DECODED terms a branch rested on `OUT`, sorted.
fn outcome(state: &mettail_rholang_runtime::speculation::SpeculativeState) -> Vec<String> {
    let mut rendered: Vec<String> = resting_on_string(state, OUT)
        .iter()
        .map(|par| match par_as_runtime_observation_value(par) {
            Some(value) => format!("{value:?}"),
            None => "<undecodable>".to_string(),
        })
        .collect();
    rendered.sort();
    rendered
}

fn outcomes(exploration: &Exploration) -> Vec<Vec<String>> {
    let mut all: Vec<Vec<String>> = exploration
        .success
        .iter()
        .map(|leaf| outcome(&leaf.state))
        .collect();
    all.sort();
    all.dedup();
    all
}

// ══════════════════════════════════════════════════════════════════════════
// ★★ THE MEASUREMENT
// ══════════════════════════════════════════════════════════════════════════

/// ★★ `[*]` over the `^drive`-lowered open race terminates with **one** leaf,
/// and every conflict class it ever saw was a **singleton** — the machine's own
/// statement that no choice was made.
///
/// `max_out_degree` climbs to double digits, so the tuplespace really is
/// offering many rendezvous at once; `max_conflict_class == 1` says every one of
/// them was independent of every other, i.e. a persistent dispatcher serving its
/// work queue. A rewrite choice would have shown up as a class of size 2.
#[tokio::test]
async fn the_drive_lowering_makes_no_choice() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let exploration = explore(
        drive_program(&backend, &fingerprint, &open_race()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    eprintln!(
        "[drive] success={} truncated={} failure={} stats={:?}",
        exploration.success.len(),
        exploration.truncated.len(),
        exploration.failure.len(),
        exploration.stats
    );
    eprintln!("[drive] outcomes={:?}", outcomes(&exploration));

    assert!(exploration.failure.is_empty(), "{:?}", exploration.failure);
    assert!(exploration.truncated.is_empty(), "`[*]` runs to quiescence");
    assert_eq!(
        exploration.success.len(),
        1,
        "the drive resolves the pairing itself, so `[*]` sees ONE branch"
    );
    assert!(
        exploration.stats.max_out_degree >= 2,
        "the tuplespace DID offer several rendezvous at once: {:?}",
        exploration.stats
    );
    // ★ THE FINDING.
    assert_eq!(
        exploration.stats.max_conflict_class, 1,
        "…and NONE of them was a choice: every pair was resource-disjoint. A rewrite \
         choice would be a conflict class of size 2. {:?}",
        exploration.stats
    );
    // Every rendezvous the drive ever enabled was independent, so the reduction
    // pruned a great many redundant interleavings — that is why this terminates.
    assert!(
        exploration.stats.independence_pruned > 100,
        "the reduction did the work: {:?}",
        exploration.stats
    );
}

/// The single leaf `[*]` finds is exactly what an ORDINARY run of the same
/// program reaches. The two machines agree, which is what "the drive is
/// deterministic" means operationally.
#[tokio::test]
async fn the_drive_leaf_is_what_an_ordinary_run_reaches() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();

    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&open_race(), &fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, OUT);
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .expect("the ordinary drive runs to quiescence on the reducer");
    assert_eq!(set.out_values.len(), 1, "an ordinary run rests one term");
    let ordinary = vec![format!("{:?}", set.out_values[0])];

    let exploration = explore(
        drive_program(&backend, &fingerprint, &open_race()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    let speculative = outcomes(&exploration);
    eprintln!("[agreement] ordinary={ordinary:?} speculative={speculative:?}");
    assert_eq!(
        speculative,
        vec![ordinary],
        "the speculative leaf and the ordinary run's resting term must agree"
    );
}

/// The **report-free** in-Rho match lowering: locate-ALL. Both redexes are
/// located and both fire, so there are two firings and still no choice.
#[tokio::test]
async fn the_report_free_match_lowering_makes_no_choice() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let term = AmbientLanguage
        .parse_term("{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }")
        .expect("production Ambient must parse the open race");
    let Ok(invocation) = AmbientLanguage::rho_net_match_invocation_to(term.as_ref(), OUT) else {
        // A rejection is itself a fact about the lowering, not a test failure.
        eprintln!("[match] the report-free match path rejected the race");
        return;
    };
    let exploration = explore(
        installed.append(invocation.call.clone()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    eprintln!("[match] success={} stats={:?}", exploration.success.len(), exploration.stats);
    assert_eq!(
        exploration.stats.max_conflict_class, 1,
        "locate-all fires every located redex: no selection competes with another"
    );
    assert_eq!(exploration.success.len(), 1);
}

/// The **spread** match lowering: the located redex is published as one carrier
/// datum, so the receiver has a single admissible selection.
#[tokio::test]
async fn the_spread_match_lowering_makes_no_choice() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let term = AmbientLanguage
        .parse_term("{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }")
        .expect("production Ambient must parse the open race");
    let report = AmbientLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("the Dovetail report must compile");
    let Ok(invocation) =
        AmbientLanguage::rho_net_match_invocation_from_dovetail_to(term.as_ref(), &report, OUT)
    else {
        eprintln!("[spread] the spread-match path rejected the race");
        return;
    };
    let exploration = explore(
        installed.append(invocation.call.clone()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    eprintln!("[spread] success={} stats={:?}", exploration.success.len(), exploration.stats);
    assert_eq!(exploration.stats.max_conflict_class, 1);
    assert_eq!(exploration.success.len(), 1);
}

// ══════════════════════════════════════════════════════════════════════════
// `[n]` and delivery over a REAL guest program
// ══════════════════════════════════════════════════════════════════════════

/// `[0]` over the drive-lowered race fires nothing and returns one TRUNCATED
/// branch carrying a resumable handle — over a real, large guest program rather
/// than a fixture.
#[tokio::test]
async fn zero_lookahead_truncates_the_drive() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let exploration = explore(
        drive_program(&backend, &fingerprint, &open_race()),
        TraceMode::IndependenceReduced,
        Lookahead::Steps(0),
    )
    .await;
    assert_eq!(exploration.stats.edges_fired, 0, "`[0]` fires nothing");
    assert_eq!(exploration.truncated.len(), 1);
    assert!(exploration.success.is_empty());
    assert!(exploration.failure.is_empty());
    assert!(exploration.truncated[0].trace().is_empty());
    assert!(exploration.truncated[0].branch.frontier >= 1);

    // The retained configuration reifies, and it still holds the whole installed
    // receiver network plus the drive seed — the work that has not been done.
    let process = reify(&exploration.truncated[0].branch.state)
        .expect("the retained configuration must reify");
    assert!(!process.receives.is_empty(), "the installed receiver network is still waiting");
    assert!(!process.sends.is_empty(), "and the seed is still resting");
}

/// A truncated drive RESUMES to exactly what an unbroken `[*]` reaches — over
/// the full production program, 98 stratified steps deep.
#[tokio::test]
async fn a_truncated_drive_resumes_to_the_unbroken_result() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let unbroken = explore(
        drive_program(&backend, &fingerprint, &open_race()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    let unbroken_outcomes = outcomes(&unbroken);

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    let mut explorer = Explorer::new(&sandbox);
    let cut = explorer
        .explore(
            drive_program(&backend, &fingerprint, &open_race()),
            ordinary_rand(),
            Lookahead::Steps(20),
        )
        .await
        .expect("the bounded exploration must run");
    assert_eq!(cut.truncated.len(), 1, "20 steps is not enough to finish");

    let resumed = explorer
        .resume(&cut.handles(), Lookahead::Unbounded)
        .await
        .expect("the handle must resume");
    eprintln!("[resume] unbroken={unbroken_outcomes:?} resumed={:?}", outcomes(&resumed));
    assert_eq!(
        outcomes(&resumed),
        unbroken_outcomes,
        "resuming a truncated drive must reach what an unbroken one reaches"
    );
    assert!(
        resumed.success[0].trace.len() > 20,
        "the resumed branch continued the trace it inherited"
    );
}

/// The three collections assemble over a real guest program's exploration.
#[tokio::test]
async fn the_three_collections_assemble_over_the_drive() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let exploration = explore(
        drive_program(&backend, &fingerprint, &open_race()),
        TraceMode::IndependenceReduced,
        Lookahead::Unbounded,
    )
    .await;
    let delivery = deliver(&exploration).expect("every leaf of a real program must reify");

    use models::rhoapi::expr::ExprInstance;
    let count = |collection: &models::rhoapi::Par| match collection
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    {
        Some(ExprInstance::ESetBody(set)) => set.ps.len(),
        other => panic!("a delivered collection must be an ESet, got {other:?}"),
    };
    assert_eq!(count(&delivery.success), 1);
    assert_eq!(count(&delivery.truncated), 0);
    assert_eq!(count(&delivery.failure), 0);
}
