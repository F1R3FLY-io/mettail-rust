//! # ★★ THE Stage-2 GATE — the branching engine returns EVERY outcome
//!
//! λ-calculus is confluent, so a `[*]` that drives once and wraps the answer
//! returns the right answer for every λ term and looks perfect. The only thing
//! that separates a real enumerator from that is a guest whose reduction is
//! genuinely non-deterministic — and non-determinism, in a tuplespace, means one
//! precise thing: **two enabled rendezvous that compete for a resource**.
//!
//! ```text
//!        c!(1)  ──┐                        ┌── OUT!(1)     leaf A
//!                 ├─▶ for(@x <- c){ … } ───┤
//!        c!(2)  ──┘   ONE continuation,    └── OUT!(2)     leaf B
//!                     TWO candidate data
//!                     ⇒ the two selections SHARE the continuation
//!                     ⇒ they CONFLICT ⇒ a real choice ⇒ TWO outcomes
//! ```
//!
//! Every cell below is measured on the live f1r3node reducer through
//! [`SpeculativeSandbox`]: nothing is mocked, no host mirror decides anything,
//! and the branching comes from `E(S)` on the store itself.
//!
//! ## What the cells establish
//!
//! | cell | shape | expected | what a failure would mean |
//! |---|---|---|---|
//! | [`one_receive_two_data_returns_two`] | one continuation, two data | **2** | the engine cannot branch at all |
//! | [`one_receive_three_data_returns_three`] | one continuation, three data | **3** | it branches but not exhaustively |
//! | [`two_independent_comms_return_one`] | disjoint resources | **1** | it manufactures branches out of scheduling noise |
//! | [`a_sequential_chain_returns_one`] | forced order | **1** | ditto, for a chain |
//! | [`the_reduction_agrees_with_the_unreduced_search`] | the whole corpus, both modes | **equal** | the partial-order reduction is unsound |
//! | [`every_trace_mode_sees_the_interleavings_the_others_merge`] | corpus, tree mode | **≥** | the three modes are not related as claimed |
//!
//! ## ★ Conflict, not concurrency
//!
//! Two **independent** rendezvous are not alternatives — they are both going to
//! happen, and the order is not a decision the program makes. So the branch
//! factor of a stratified step is the size of a *conflict class*, never
//! `|E(S)|`, and [`ExplorationStats::max_conflict_class`] is the honest measure
//! of how much choice a guest actually had. A guest whose every class is a
//! singleton is deterministic however large its enabled set grew — that is a
//! machine-checkable statement, and
//! [`two_independent_comms_return_one`] pins it.
#![cfg(feature = "runtime-report")]

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::rhoapi::{Par, ReceiveBind, Send};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gint_par, new_gstring_par, new_receive_par,
};

use mettail_rholang_runtime::par_as_runtime_observation_value;
use mettail_rholang_runtime::speculation::delivery::{deliver, reify, resting_on_string};
use mettail_rholang_runtime::speculation::search::{
    ErrorCode, Exploration, Explorer, Lookahead, TraceMode,
};
use mettail_rholang_runtime::speculation::SpeculativeSandbox;
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const OUT: &str = "OUT";
const HOST_UNITS: i64 = 1_000_000;

// ══════════════════════════════════════════════════════════════════════════
// Program fixtures — hand-built `Par`s, so the SHAPE under test is exactly the
// shape written here and no lowering can quietly change it
// ══════════════════════════════════════════════════════════════════════════

fn chan(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// `@"channel"!(value)`.
fn send(channel: &str, value: i64) -> Par {
    Par::default().with_sends(vec![Send {
        chan: Some(chan(channel)),
        data: vec![new_gint_par(value, Vec::new(), false)],
        persistent: false,
        locally_free: Vec::new(),
        connective_used: false,
    }])
}

/// `for(@x <- source) { @"target"!(x) }` — a linear receive that forwards.
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

/// A named corpus cell: a program and how many distinct outcomes it has.
struct Cell {
    name: &'static str,
    program: Par,
}

/// The corpus both trace modes are compared over. Deliberately small and
/// hand-built: every cell's outcome count is derivable by hand, so a
/// disagreement is a defect in the engine and not an unknown.
fn corpus() -> Vec<Cell> {
    vec![
        Cell {
            // ONE continuation, TWO data: the selections share the continuation.
            name: "conflict/1-recv-2-data",
            program: send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
        },
        Cell {
            // ONE continuation, THREE data.
            name: "conflict/1-recv-3-data",
            program: send("c", 1)
                .append(send("c", 2))
                .append(send("c", 3))
                .append(forward("c", OUT)),
        },
        Cell {
            // TWO continuations, TWO data, all on one channel: every selection
            // conflicts with some other, but both receives fire either way.
            name: "conflict/2-recv-2-data",
            program: send("c", 1)
                .append(send("c", 2))
                .append(forward("c", OUT))
                .append(forward("c", OUT)),
        },
        Cell {
            // Disjoint resources: no choice.
            name: "independent/2-comms",
            program: send("c", 1)
                .append(forward("c", OUT))
                .append(send("d", 2))
                .append(forward("d", OUT)),
        },
        Cell {
            // A forced order: the second COMM does not exist until the first
            // fires.
            name: "sequential/chain",
            program: send("c", 1)
                .append(forward("c", "d"))
                .append(forward("d", OUT)),
        },
        Cell {
            // A conflict AND an independent COMM in one program: the reduction
            // must branch on the first and not on the second.
            name: "mixed/conflict-plus-independent",
            program: send("c", 1)
                .append(send("c", 2))
                .append(forward("c", OUT))
                .append(send("d", 9))
                .append(forward("d", OUT)),
        },
    ]
}

// ══════════════════════════════════════════════════════════════════════════
// Harness
// ══════════════════════════════════════════════════════════════════════════

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "s2 gate host deploy"));
    budget
}

async fn explore_with(program: Par, mode: TraceMode, lookahead: Lookahead) -> Exploration {
    let sandbox = SpeculativeSandbox::new()
        .await
        .expect("the speculative sandbox must build");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    let mut explorer = Explorer::with_mode(&sandbox, mode);
    let exploration = explorer
        .explore(program, Blake2b512Random::create_from_length(128), lookahead)
        .await
        .expect("the exploration must not fail at the infrastructure level");
    exploration
}

async fn explore(program: Par) -> Exploration {
    explore_with(program, TraceMode::IndependenceReduced, Lookahead::Unbounded).await
}

/// The DECODED data a branch rested on `OUT`, sorted — the observable an
/// audience sees, and the discriminator "distinct outcome" means.
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

/// The SET of outcomes a search found, sorted and deduplicated.
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
// ★★ THE GATE — a real conflict yields every outcome
// ══════════════════════════════════════════════════════════════════════════

/// ★★ One receive racing TWO data has **two** outcomes, and `[*]` returns both.
///
/// The decisive cell. An implementation that drove once and wrapped the answer
/// would return one, and would be indistinguishable from a correct one on any
/// confluent guest.
#[tokio::test]
async fn one_receive_two_data_returns_two() {
    let exploration = explore(send("c", 1).append(send("c", 2)).append(forward("c", OUT))).await;
    let found = outcomes(&exploration);
    eprintln!("[1-recv-2-data] {:?} stats={:?}", found, exploration.stats);

    assert!(exploration.failure.is_empty(), "{:?}", exploration.failure);
    assert!(exploration.truncated.is_empty(), "`[*]` runs to quiescence");
    assert_eq!(found.len(), 2, "two candidate data ⟹ TWO outcomes, got {found:?}");
    assert!(
        found.contains(&vec!["Int(1)".to_string()]),
        "one branch must deliver 1: {found:?}"
    );
    assert!(
        found.contains(&vec!["Int(2)".to_string()]),
        "the OTHER branch must deliver 2 — the one an ordinary run never takes: {found:?}"
    );

    // The branch was a genuine CHOICE, not scheduling noise: the two selections
    // competed for the continuation.
    assert_eq!(
        exploration.stats.max_conflict_class, 2,
        "the two selections must CONFLICT (they share the continuation): {:?}",
        exploration.stats
    );
    // And the traces differ, so the two leaves are keyed apart.
    assert_eq!(exploration.success.len(), 2, "two branches, two entries");
    assert_ne!(
        exploration.success[0].trace, exploration.success[1].trace,
        "the two branches named DIFFERENT selections"
    );
}

/// Three candidate data ⟹ **three** outcomes. Branching is exhaustive, not
/// binary.
#[tokio::test]
async fn one_receive_three_data_returns_three() {
    let exploration = explore(
        send("c", 1)
            .append(send("c", 2))
            .append(send("c", 3))
            .append(forward("c", OUT)),
    )
    .await;
    let found = outcomes(&exploration);
    eprintln!("[1-recv-3-data] {found:?}");
    assert_eq!(found.len(), 3, "three candidate data ⟹ THREE outcomes: {found:?}");
    for value in ["Int(1)", "Int(2)", "Int(3)"] {
        assert!(
            found.contains(&vec![value.to_string()]),
            "{value} must be one of the outcomes: {found:?}"
        );
    }
    assert_eq!(exploration.stats.max_conflict_class, 3);
}

/// ★ Two INDEPENDENT COMMs are **not** a choice: one outcome, and the engine
/// says so — `max_out_degree` is 2 (both were enabled at once) while
/// `max_conflict_class` is 1 (neither was an alternative to the other).
///
/// This is the teeth on the branching: without it, an engine that branched on
/// every enabled rendezvous would pass every cell above by manufacturing
/// interleavings, and would be exponential in the concurrency width for no
/// semantic gain.
#[tokio::test]
async fn two_independent_comms_return_one() {
    let exploration = explore(
        send("c", 1)
            .append(forward("c", OUT))
            .append(send("d", 2))
            .append(forward("d", OUT)),
    )
    .await;
    let found = outcomes(&exploration);
    eprintln!("[independent] {found:?} stats={:?}", exploration.stats);
    assert_eq!(found.len(), 1, "independent COMMs are not alternatives: {found:?}");
    assert_eq!(found[0], vec!["Int(1)".to_string(), "Int(2)".to_string()], "and BOTH happen");
    assert_eq!(exploration.stats.max_out_degree, 2, "both were enabled at once");
    assert_eq!(exploration.stats.max_conflict_class, 1, "…and neither was a choice");
}

/// A chain forces its own order: one outcome, and every conflict class is a
/// singleton.
#[tokio::test]
async fn a_sequential_chain_returns_one() {
    let exploration = explore(
        send("c", 1)
            .append(forward("c", "d"))
            .append(forward("d", OUT)),
    )
    .await;
    let found = outcomes(&exploration);
    eprintln!("[chain] {found:?} stats={:?}", exploration.stats);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0], vec!["Int(1)".to_string()]);
    assert_eq!(exploration.stats.max_conflict_class, 1);
}

/// A conflict AND an independent COMM together: branch on the first, not on the
/// second. Both outcomes carry the independent COMM's result, because it happens
/// either way.
#[tokio::test]
async fn a_conflict_beside_an_independent_comm_branches_only_on_the_conflict() {
    let exploration = explore(
        send("c", 1)
            .append(send("c", 2))
            .append(forward("c", OUT))
            .append(send("d", 9))
            .append(forward("d", OUT)),
    )
    .await;
    let found = outcomes(&exploration);
    eprintln!("[mixed] {found:?} stats={:?}", exploration.stats);
    assert_eq!(found.len(), 2, "one conflict ⟹ two outcomes: {found:?}");
    for branch in found.iter() {
        assert!(
            branch.contains(&"Int(9)".to_string()),
            "the independent COMM happens on EVERY branch: {branch:?}"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════
// ★ The partial-order reduction is SOUND — measured, not asserted
// ══════════════════════════════════════════════════════════════════════════

/// ★ The reduced search finds exactly the outcomes the UNREDUCED one finds.
///
/// [`TraceMode::IndependenceReduced`] expands only the conflict class of
/// `E(S)[0]`; [`TraceMode::DistinctConfigurations`] expands all of `E(S)`. The
/// reduction's soundness claim is that they agree on the set of terminal
/// outcomes, and this measures it on every corpus cell rather than arguing it.
///
/// A failure here means the independence relation is too permissive — that two
/// rendezvous judged independent do not in fact commute — and it is the single
/// most important thing this file checks, because every other cell would still
/// pass with an unsound reduction.
#[tokio::test]
async fn the_reduction_agrees_with_the_unreduced_search() {
    for cell in corpus() {
        let reduced = explore_with(
            cell.program.clone(),
            TraceMode::IndependenceReduced,
            Lookahead::Unbounded,
        )
        .await;
        let unreduced = explore_with(
            cell.program.clone(),
            TraceMode::DistinctConfigurations,
            Lookahead::Unbounded,
        )
        .await;
        let reduced_outcomes = outcomes(&reduced);
        let unreduced_outcomes = outcomes(&unreduced);
        eprintln!(
            "[{}] reduced={} (nodes {}) unreduced={} (nodes {})",
            cell.name,
            reduced_outcomes.len(),
            reduced.stats.nodes_expanded,
            unreduced_outcomes.len(),
            unreduced.stats.nodes_expanded
        );
        assert_eq!(
            reduced_outcomes, unreduced_outcomes,
            "[{}] the partial-order reduction must not change the OUTCOMES",
            cell.name
        );
        assert!(
            reduced.failure.is_empty() && unreduced.failure.is_empty(),
            "[{}] no branch may abort",
            cell.name
        );
    }
}

/// The three trace modes are related as claimed: every-trace sees at least as
/// many branches as distinct-configurations, which sees at least as many as the
/// reduced search — and all three agree on the OUTCOMES.
#[tokio::test]
async fn every_trace_mode_sees_the_interleavings_the_others_merge() {
    for cell in corpus() {
        let reduced = explore_with(
            cell.program.clone(),
            TraceMode::IndependenceReduced,
            Lookahead::Unbounded,
        )
        .await;
        let merged = explore_with(
            cell.program.clone(),
            TraceMode::DistinctConfigurations,
            Lookahead::Unbounded,
        )
        .await;
        let every =
            explore_with(cell.program.clone(), TraceMode::EveryTrace, Lookahead::Unbounded).await;
        eprintln!(
            "[{}] branches reduced={} merged={} every={} | outcomes {}/{}/{}",
            cell.name,
            reduced.success.len(),
            merged.success.len(),
            every.success.len(),
            outcomes(&reduced).len(),
            outcomes(&merged).len(),
            outcomes(&every).len(),
        );
        assert!(
            every.success.len() >= merged.success.len(),
            "[{}] every-trace must see at least as many branches as the graph search",
            cell.name
        );
        assert!(
            merged.success.len() >= reduced.success.len(),
            "[{}] the graph search must see at least as many branches as the reduced one",
            cell.name
        );
        assert_eq!(
            outcomes(&every),
            outcomes(&reduced),
            "[{}] …and all three agree on the OUTCOMES",
            cell.name
        );
        assert_eq!(
            every.stats.merged_configurations, 0,
            "[{}] EveryTrace never merges, by construction",
            cell.name
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════
// `[n]` — the bounded bracket as a first-class mode
// ══════════════════════════════════════════════════════════════════════════

/// `[0]` fires nothing and TRUNCATES: not success, not failure. The FIPS calls
/// `n = 0` *"isomorphic to the current semantics"* — this is that, with the
/// honest statement that a normal form was not reached.
#[tokio::test]
async fn zero_lookahead_fires_nothing_and_truncates() {
    let exploration = explore_with(
        send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
        TraceMode::IndependenceReduced,
        Lookahead::Steps(0),
    )
    .await;
    eprintln!("[n=0] stats={:?}", exploration.stats);
    assert_eq!(exploration.stats.edges_fired, 0, "`[0]` fires nothing");
    assert!(exploration.success.is_empty(), "nothing reached quiescence");
    assert!(exploration.failure.is_empty(), "{:?}", exploration.failure);
    assert_eq!(exploration.truncated.len(), 1, "one truncated branch");
    assert!(exploration.truncated[0].trace().is_empty());
    assert_eq!(
        exploration.truncated[0].branch.frontier, 2,
        "the retained frontier records how many ways it could have continued"
    );
}

/// `[1]` on the two-data race: one step on each of the two paths, and both
/// happen to reach quiescence, so both are successes rather than truncations —
/// truncation is decided by `E(S)`, never by "the bound was reached".
#[tokio::test]
async fn one_step_lookahead_reaches_both_leaves() {
    let exploration = explore_with(
        send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
        TraceMode::IndependenceReduced,
        Lookahead::Steps(1),
    )
    .await;
    eprintln!(
        "[n=1] success={} truncated={}",
        exploration.success.len(),
        exploration.truncated.len()
    );
    assert_eq!(exploration.success.len(), 2, "both branches finished in one step");
    assert!(exploration.truncated.is_empty());
    for leaf in exploration.success.iter() {
        assert_eq!(leaf.trace.len(), 1);
    }
}

/// A TRUNCATED branch RESUMES to exactly what an unbroken run reaches. The
/// handle carries the whole `HotStoreState`, so every datum's
/// `Blake2b512Random` and every continuation's source survive the round trip —
/// which a reified process could not have preserved.
#[tokio::test]
async fn a_truncated_branch_resumes_to_the_unbroken_result() {
    let program = send("c", 1)
        .append(forward("c", "d"))
        .append(forward("d", OUT));
    let unbroken = explore(program.clone()).await;
    let unbroken_outcomes = outcomes(&unbroken);

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    let mut explorer = Explorer::new(&sandbox);
    let cut = explorer
        .explore(program, Blake2b512Random::create_from_length(128), Lookahead::Steps(1))
        .await
        .expect("the bounded exploration must run");
    assert_eq!(cut.truncated.len(), 1, "the chain is cut mid-way");

    let resumed = explorer
        .resume(&cut.handles(), Lookahead::Unbounded)
        .await
        .expect("the handle must resume");
    eprintln!("[resume] unbroken={unbroken_outcomes:?} resumed={:?}", outcomes(&resumed));
    assert_eq!(
        outcomes(&resumed),
        unbroken_outcomes,
        "resuming a truncated handle must reach exactly what an unbroken run reaches"
    );
    // And the resumed trace continues the truncated one rather than restarting.
    assert!(
        resumed.success[0].trace.len() > cut.truncated[0].trace().len(),
        "the resumed branch appends to the trace it inherited"
    );
}

/// Beam search's second half, literally: run `[1]`, keep the handles, run
/// forward. Two rounds of `[1]` reach what `[2]` reaches.
#[tokio::test]
async fn two_bounded_rounds_equal_one_double_bounded_round() {
    let program = send("c", 1)
        .append(forward("c", "d"))
        .append(forward("d", OUT));
    let direct =
        explore_with(program.clone(), TraceMode::IndependenceReduced, Lookahead::Steps(2)).await;

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(HOST_UNITS));
    let mut explorer = Explorer::new(&sandbox);
    let first = explorer
        .explore(program, Blake2b512Random::create_from_length(128), Lookahead::Steps(1))
        .await
        .expect("round one");
    let second = explorer
        .resume(&first.handles(), Lookahead::Steps(1))
        .await
        .expect("round two");
    eprintln!("[beam] direct={:?} staged={:?}", outcomes(&direct), outcomes(&second));
    assert_eq!(
        outcomes(&second),
        outcomes(&direct),
        "`[1]` then resume-`[1]` must reach what `[2]` reaches"
    );
}

// ══════════════════════════════════════════════════════════════════════════
// Metering — the bound, and the charge-back
// ══════════════════════════════════════════════════════════════════════════

/// ★ Metering IS the bound. An under-funded sandbox does not hang and does not
/// quietly return a partial success set: its branches arrive as
/// [`ErrorCode::OutOfPhlogistons`] failures and the exploration terminates.
#[tokio::test]
async fn an_exhausted_budget_aborts_rather_than_hangs() {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    // Two units: enough to evaluate a send or two, not enough for the program.
    sandbox.fund_from(&host_budget(2));
    let mut explorer = Explorer::new(&sandbox);
    let exploration = explorer
        .explore(
            send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
            Blake2b512Random::create_from_length(128),
            Lookahead::Unbounded,
        )
        .await
        .expect("an exhausted budget is an ANSWER, not an infrastructure fault");
    eprintln!(
        "[starved] success={} failure={:?}",
        exploration.success.len(),
        exploration
            .failure
            .iter()
            .map(|leaf| leaf.code)
            .collect::<Vec<_>>()
    );
    assert!(
        !exploration.failure.is_empty(),
        "a starved exploration must REPORT, not quietly succeed"
    );
    assert!(
        exploration
            .failure
            .iter()
            .all(|leaf| leaf.code == ErrorCode::OutOfPhlogistons),
        "and the code must say why: {:?}",
        exploration
            .failure
            .iter()
            .map(|leaf| (leaf.code, leaf.message.clone()))
            .collect::<Vec<_>>()
    );
}

/// ★ An UNFUNDED sandbox refuses to evaluate anything at all — the fail-shut
/// direction, and what makes an unmetered speculative evaluation
/// unrepresentable rather than merely discouraged.
#[tokio::test]
async fn an_unfunded_sandbox_refuses() {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    // No `fund_from`: `create_rho_runtime` leaves the budget at zero.
    let mut explorer = Explorer::new(&sandbox);
    let exploration = explorer
        .explore(
            send("c", 1).append(forward("c", OUT)),
            Blake2b512Random::create_from_length(128),
            Lookahead::Unbounded,
        )
        .await
        .expect("the refusal is an answer");
    assert!(exploration.success.is_empty(), "an unfunded sandbox computes nothing");
    assert_eq!(exploration.failure.len(), 1);
    assert_eq!(exploration.failure[0].code, ErrorCode::OutOfPhlogistons);
    assert!(exploration.failure[0].trace.is_empty(), "it refused before any COMM");
}

/// ★ The charge-back is `consumed()` CALLS to `reserve_comm`, not one call
/// passing `consumed()` — a budget unit is one COMM regardless of the `Cost`
/// argument. The host's remaining budget falls by exactly the COMM count.
#[tokio::test]
async fn the_host_is_charged_one_per_comm() {
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    let host = host_budget(HOST_UNITS);
    sandbox.fund_from(&host);
    let mut explorer = Explorer::new(&sandbox);
    let _ = explorer
        .explore(
            send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
            Blake2b512Random::create_from_length(128),
            Lookahead::Unbounded,
        )
        .await
        .expect("the exploration must run");

    let owed = sandbox.consumed().value;
    assert!(owed > 1, "the exploration spent several COMMs, got {owed}");
    let before = host.remaining().value;
    let charged = explorer
        .charge_host(&host, Cost::create(1, "speculation charge-back"))
        .expect("the host can afford it");
    let after = host.remaining().value;
    eprintln!("[charge] owed={owed} charged={charged} Δhost={}", before - after);
    assert_eq!(charged as i64, owed, "one call per COMM");
    assert_eq!(before - after, owed, "a single call passing consumed() would have charged 1");
}

// ══════════════════════════════════════════════════════════════════════════
// Delivery
// ══════════════════════════════════════════════════════════════════════════

/// The three collections assemble as set-mode `EPathMap`s with one entry per branch, and a
/// truncated branch is never folded into `failure`.
#[tokio::test]
async fn the_three_collections_are_separate_and_complete() {
    let exploration = explore_with(
        send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
        TraceMode::IndependenceReduced,
        Lookahead::Steps(0),
    )
    .await;
    let delivery = deliver(&exploration).expect("every leaf must reify");
    assert_eq!(pathmap_len(&delivery.success), 0, "nothing finished under `[0]`");
    assert_eq!(pathmap_len(&delivery.truncated), 1, "one truncated entry");
    assert_eq!(pathmap_len(&delivery.failure), 0, "and it is NOT a failure");

    let finished = explore(send("c", 1).append(send("c", 2)).append(forward("c", OUT))).await;
    let delivered = deliver(&finished).expect("reify");
    assert_eq!(pathmap_len(&delivered.success), 2, "two success entries");
    assert_eq!(pathmap_len(&delivered.truncated), 0);
    assert_eq!(pathmap_len(&delivered.failure), 0);
}

fn pathmap_len(collection: &Par) -> usize {
    use models::rhoapi::expr::ExprInstance;
    match collection
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    {
        Some(ExprInstance::EPathmapBody(pathmap)) => pathmap.len(),
        other => panic!("a delivered collection must be an EPathMap, got {other:?}"),
    }
}

/// A leaf reifies to a PROCESS, and two distinct configurations reify to two
/// distinct processes — so the delivered leaf really does discriminate the
/// branches.
#[tokio::test]
async fn a_leaf_reifies_to_a_process_and_the_two_differ() {
    let exploration = explore(send("c", 1).append(send("c", 2)).append(forward("c", OUT))).await;
    assert_eq!(exploration.success.len(), 2);
    let first = reify(&exploration.success[0].state).expect("leaf 0 reifies");
    let second = reify(&exploration.success[1].state).expect("leaf 1 reifies");
    assert!(!first.sends.is_empty(), "a configuration with resting data reifies to sends");
    assert_ne!(first, second, "two configurations, two processes");
}

/// A truncated leaf's reified configuration still contains the work that was
/// not done — the receive and both data are all still there — which is what
/// makes the handle resumable and what a beam-search ranker inspects.
///
/// ## ★ …and the two sends come out in a CONTENT order, not the store's
///
/// This cell used to assert `process.sends.len() == 2` and stop. A count passes under either
/// order, and this leaf is the one shape in the whole suite that puts **two data on one
/// channel** — so it was the single place in the suite where `reify`'s within-channel
/// ordering was observable at all, and it observed nothing.
///
/// A channel's `Vec` is *reverse-arrival* order: `HotStore::put_datum` prepends, and every
/// branch of a `|` is a detached `tokio::spawn`. So the second half of this cell permutes the
/// retained configuration's data — which is what a differently-scheduled node would hand back
/// — and requires the reified bytes not to move. The two data carry different `random_state`s
/// and therefore different `Produce` hashes, so they are genuinely distinguishable and the
/// assertion can fail.
#[tokio::test]
async fn a_truncated_leaf_reifies_the_work_that_remains() {
    use prost::Message;

    let exploration = explore_with(
        send("c", 1).append(send("c", 2)).append(forward("c", OUT)),
        TraceMode::IndependenceReduced,
        Lookahead::Steps(0),
    )
    .await;
    let leaf = &exploration.truncated[0];
    let process = reify(&leaf.branch.state).expect("the retained configuration reifies");
    assert_eq!(process.sends.len(), 2, "both data are still resting");
    assert_eq!(process.receives.len(), 1, "and the receive is still waiting");

    // The premise the assertion below rests on: the two data really are distinguishable.
    let mut sources: Vec<Vec<u8>> = leaf
        .branch
        .state
        .data
        .values()
        .flat_map(|data| data.iter().map(|datum| datum.source.hash.bytes()))
        .collect();
    sources.sort();
    sources.dedup();
    assert_eq!(sources.len(), 2, "the two staged data must have distinct Produce hashes");

    let mut permuted = leaf.branch.state.clone();
    for data in permuted.data.values_mut() {
        data.reverse();
    }
    assert_eq!(
        reify(&permuted)
            .expect("the permuted configuration reifies")
            .encode_to_vec(),
        process.encode_to_vec(),
        "★ reversing the order of the two data ON ONE CHANNEL changed the reified bytes. That \
         order is the scheduler's — `HotStore` prepends — and this process is published inside \
         `^spec-truncated` and the FIPS `truncated` collection."
    );
}
