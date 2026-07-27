//! Diagnostic probe (not a gate): the SHAPE of the speculative reduction graph
//! for the Ambient open race, level by level.
//!
//! Reports `|E(S)|` per node, the frontier size per BFS level, how many children
//! merged into an already-seen configuration, and the wall time — the data the
//! search's cost is a function of. It exists because "the exploration did not
//! finish" is not a diagnosis, and the two candidate causes (a large out-degree
//! from the drive's concurrent descent versus configurations that never
//! re-converge) are distinguished by exactly these numbers.
#![cfg(feature = "ambient-runtime")]

use std::collections::HashSet;
use std::time::Instant;

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use mettail_languages::ambient::AmbientLanguage;
use mettail_rholang_codegen::{
    reflect_ground_term_par, rho_net_drive_call_par_with_fuel, CollectionType, GroundTerm,
    DRIVE_DEFAULT_FUEL, FREE_VAR_REFLECT_LABEL,
};
use mettail_rholang_runtime::speculation::search::{Explorer, Lookahead, TraceMode};
use mettail_rholang_runtime::speculation::{
    content_fingerprint, RendezvousName, SpeculativeSandbox, SpeculativeState,
};
use mettail_rholang_runtime::PlannedRhoBackend;
use mettail_runtime::Language;
use rholang::rust::interpreter::accounting::cost_accounting::CostAccounting;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::RuntimeBudget;

const OUT: &str = "OUT";

fn ambient_backend() -> (PlannedRhoBackend, String) {
    let source = AmbientLanguage
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

fn open_race() -> GroundTerm {
    g_bag(vec![
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("a")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("b")])),
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("c")])),
    ])
}

fn host_budget(units: i64) -> RuntimeBudget {
    let budget = CostAccounting::empty_cost();
    budget.set(Cost::create(units, "probe host"));
    budget
}

/// A hand-rolled BFS with per-level reporting, stopping at `max_levels` so the
/// probe always terminates and always prints.
#[tokio::test]
async fn graph_shape_of_the_open_race() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed program");
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&open_race(), &fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    let program = installed.append(seed);

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(4_000_000));

    let started = Instant::now();
    sandbox
        .load(SpeculativeState::default())
        .await
        .expect("load");
    sandbox
        .saturate(program, Blake2b512Random::create_from_length(128))
        .await
        .expect("saturate");
    let root = sandbox.snapshot();
    eprintln!(
        "[root] saturated in {:?}; data channels={} continuation groups={} installed={} consumed={}",
        started.elapsed(),
        root.data.len(),
        root.continuations.len(),
        root.installed_continuations.len(),
        sandbox.consumed().value
    );

    let mut visited: HashSet<Vec<String>> = HashSet::new();
    visited.insert(content_fingerprint(&root));
    let mut frontier: Vec<(SpeculativeState, Vec<RendezvousName>)> = vec![(root, Vec::new())];

    const MAX_LEVELS: usize = 12;
    let mut quiescent = 0usize;
    for level in 0..MAX_LEVELS {
        let level_started = Instant::now();
        let mut next = Vec::new();
        let mut degrees = Vec::with_capacity(frontier.len());
        let mut merged = 0usize;
        for (state, trace) in frontier.drain(..) {
            sandbox.load(state.clone()).await.expect("load");
            let enabled = sandbox.enabled();
            degrees.push(enabled.len());
            if enabled.is_empty() {
                quiescent += 1;
                continue;
            }
            for index in 0..enabled.len() {
                if index > 0 {
                    sandbox.load(state.clone()).await.expect("load");
                }
                let live = sandbox.enabled();
                let Ok(step) = sandbox.fire(live[index].clone()).await else {
                    continue;
                };
                let child = sandbox.snapshot();
                if !visited.insert(content_fingerprint(&child)) {
                    merged += 1;
                    continue;
                }
                let mut child_trace = trace.clone();
                child_trace.push(step.name);
                next.push((child, child_trace));
            }
        }
        eprintln!(
            "[level {level}] out-degrees={degrees:?} → next={} merged={} quiescent-so-far={} \
             visited={} consumed={} in {:?}",
            next.len(),
            merged,
            quiescent,
            visited.len(),
            sandbox.consumed().value,
            level_started.elapsed()
        );
        frontier = next;
        if frontier.is_empty() {
            eprintln!("[done] frontier empty at level {level}");
            break;
        }
    }
    eprintln!(
        "[summary] quiescent={quiescent} remaining-frontier={} visited={} total={:?}",
        frontier.len(),
        visited.len(),
        started.elapsed()
    );
}

/// The same subject through the PRODUCTION engine under partial-order reduction,
/// reported as counters. This is the A/B against the hand-rolled unreduced walk
/// above: same graph, same guest, the only difference is whether independent
/// rendezvous are explored in one order or in all of them.
#[tokio::test]
async fn independence_reduced_exploration_terminates() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed program");
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&open_race(), &fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    let program = installed.append(seed);

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(4_000_000));
    let started = Instant::now();
    let mut explorer =
        Explorer::with_mode(&sandbox, TraceMode::IndependenceReduced).observing(|report| {
            eprintln!(
                "  [level {}] expanded={} degrees={:?} classes={:?} → frontier={} merged={} \
                 pruned={} quiescent={} aborted={} consumed={}",
                report.level,
                report.expanded,
                report.out_degrees,
                report.class_sizes,
                report.frontier,
                report.merged,
                report.pruned,
                report.quiescent,
                report.aborted,
                report.consumed.value
            );
        });
    let exploration = explorer
        .explore(program, Blake2b512Random::create_from_length(128), Lookahead::Unbounded)
        .await
        .expect("exploration");
    eprintln!(
        "[POR] success={} truncated={} failure={} in {:?}\n      stats={:?}",
        exploration.success.len(),
        exploration.truncated.len(),
        exploration.failure.len(),
        started.elapsed(),
        exploration.stats
    );
    for (index, leaf) in exploration.success.iter().enumerate() {
        eprintln!("  leaf {index}: |trace|={}", leaf.trace.len());
    }
    for leaf in exploration.failure.iter().take(5) {
        eprintln!("  ABORT {:?}: {}", leaf.code, leaf.message);
    }
}

/// What is actually ENABLED at a mid-depth node, by channel. The unreduced and
/// reduced walks agree on the frontier size, so the growth is not re-converging
/// diamonds; this asks the store what the transitions ARE.
#[tokio::test]
async fn what_is_enabled_at_depth() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&open_race(), &fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(4_000_000));
    sandbox
        .load(SpeculativeState::default())
        .await
        .expect("load");
    sandbox
        .saturate(installed.append(seed), Blake2b512Random::create_from_length(128))
        .await
        .expect("saturate");

    // Walk the least element repeatedly (one path) and report the enabled set's
    // channels at each depth.
    for depth in 0..16 {
        let enabled = sandbox.enabled();
        let mut rows: Vec<String> = Vec::with_capacity(enabled.len());
        for rendezvous in enabled.iter() {
            let channels: Vec<String> = rendezvous.channels.iter().map(render_channel).collect();
            rows.push(format!(
                "{}{}",
                channels.join("&"),
                match rendezvous.continuation.persist {
                    true => "[P]",
                    false => "",
                }
            ));
        }
        rows.sort();
        eprintln!("[depth {depth}] |E(S)|={} :: {}", enabled.len(), rows.join("  "));
        // ★ THE DECIDING DETAIL: do the enabled rendezvous COMPETE for a
        // resource (a linear continuation or a linear datum), or are they
        // independent? A conflict is a genuine choice; independence is not.
        for (index, rendezvous) in enabled.iter().enumerate() {
            let data: Vec<String> = rendezvous
                .data_candidates
                .iter()
                .map(|candidate| {
                    format!(
                        "{}{}",
                        short(&candidate.datum.source.hash.bytes()),
                        match candidate.datum.persist {
                            true => "!P",
                            false => "",
                        }
                    )
                })
                .collect();
            eprintln!(
                "    r{index}: cont={}{} data=[{}]",
                short(&rendezvous.continuation.source.hash.bytes()),
                match rendezvous.continuation.persist {
                    true => "!P",
                    false => "",
                },
                data.join(", ")
            );
        }
        if enabled.is_empty() {
            break;
        }
        sandbox.fire(enabled[0].clone()).await.expect("fire");
    }
}

fn short(bytes: &[u8]) -> String {
    let mut rendered = String::with_capacity(8);
    for byte in bytes.iter().take(4) {
        rendered.push_str(&format!("{byte:02x}"));
    }
    rendered
}

/// A channel rendered for a diagnostic: a `GString` by its text, an unforgeable
/// by a short digest, anything else by its shape.
fn render_channel(channel: &models::rhoapi::Par) -> String {
    use models::rhoapi::expr::ExprInstance;
    use prost::Message;
    if let Some(ExprInstance::GString(text)) = channel
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    {
        return format!("@\"{text}\"");
    }
    let bytes = channel.encode_to_vec();
    let digest: u32 = bytes
        .iter()
        .fold(2166136261u32, |hash, byte| (hash ^ *byte as u32).wrapping_mul(16777619));
    match channel.unforgeables.is_empty() {
        false => format!("priv:{digest:08x}"),
        true => format!("par:{digest:08x}"),
    }
}

/// ★ THE OTHER LOWERING: the single-shot in-Rho MATCH path over the open race.
///
/// The drive publishes work items on a PERSISTENT dispatcher and serves them, so
/// its rewrite choice is content-driven and never reaches the tuplespace. The
/// match path instead publishes the subject's bag elements on the site-keyed AC
/// carrier and lets a co-installed receiver bind them — so the two legal
/// `OpenRule` pairings become two admissible SELECTIONS over the same resting
/// data, which COMPETE. That is the shape `[*]` is for.
#[tokio::test]
async fn match_path_conflict_structure() {
    mettail_runtime::clear_var_cache();
    let (backend, _fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let term = AmbientLanguage
        .parse_term("{ open(n, a[0]) | n[b[0]] | open(n, c[0]) }")
        .expect("production Ambient must parse the open race");
    let invocation = match AmbientLanguage::rho_net_match_invocation_to(term.as_ref(), OUT) {
        Ok(invocation) => invocation,
        Err(detail) => {
            eprintln!("[match] the report-free match path REJECTED the race: {detail}");
            return;
        },
    };

    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(4_000_000));
    let mut explorer =
        Explorer::with_mode(&sandbox, TraceMode::IndependenceReduced).observing(|report| {
            eprintln!(
                "  [match level {}] degrees={:?} classes={:?} → frontier={} merged={} \
                 pruned={} quiescent={}",
                report.level,
                report.out_degrees,
                report.class_sizes,
                report.frontier,
                report.merged,
                report.pruned,
                report.quiescent
            );
        });
    let exploration = explorer
        .explore(
            installed.append(invocation.call.clone()),
            Blake2b512Random::create_from_length(128),
            Lookahead::Unbounded,
        )
        .await
        .expect("exploration");
    eprintln!(
        "[match] success={} truncated={} failure={} stats={:?}",
        exploration.success.len(),
        exploration.truncated.len(),
        exploration.failure.len(),
        exploration.stats
    );
    for (index, leaf) in exploration.success.iter().enumerate() {
        let resting =
            mettail_rholang_runtime::speculation::delivery::resting_on_string(&leaf.state, OUT);
        let decoded: Vec<String> = resting
            .iter()
            .map(|par| {
                format!("{:?}", mettail_rholang_runtime::par_as_runtime_observation_value(par))
            })
            .collect();
        eprintln!("  leaf {index}: |trace|={} OUT={:?}", leaf.trace.len(), decoded);
    }
}

/// The SAME drive over a subject with NO race (one legal pairing). If the
/// frontier still grows, the growth is the driver's own concurrency and has
/// nothing to do with the guest's non-determinism.
#[tokio::test]
async fn frontier_growth_without_any_race() {
    mettail_runtime::clear_var_cache();
    let (backend, fingerprint) = ambient_backend();
    let installed = backend
        .plan()
        .installed_rho_net_program_par()
        .expect("installed");
    let subject = g_bag(vec![
        g_open(g_name("n"), g_bag(vec![g_leaf_amb("a")])),
        g_amb(g_name("n"), g_bag(vec![g_leaf_amb("b")])),
    ]);
    let seed = rho_net_drive_call_par_with_fuel(
        &fingerprint,
        reflect_ground_term_par(&subject, &fingerprint),
        DRIVE_DEFAULT_FUEL,
        OUT,
    );
    let sandbox = SpeculativeSandbox::new().await.expect("sandbox");
    sandbox.fund_from(&host_budget(4_000_000));
    let mut explorer =
        Explorer::with_mode(&sandbox, TraceMode::IndependenceReduced).observing(|report| {
            eprintln!(
                "  [no-race level {}] expanded={} → frontier={} merged={} pruned={} quiescent={}",
                report.level,
                report.expanded,
                report.frontier,
                report.merged,
                report.pruned,
                report.quiescent
            );
        });
    let exploration = explorer
        .explore(
            installed.append(seed),
            Blake2b512Random::create_from_length(128),
            Lookahead::Steps(14),
        )
        .await
        .expect("exploration");
    eprintln!("[no-race] stats={:?}", exploration.stats);
}
