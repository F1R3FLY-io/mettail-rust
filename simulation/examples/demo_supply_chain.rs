//! # Supply Chain Simulation with Predicated Typing + Adaptive τ-leaping Customer
//!
//! A 4-actor end-to-end supply chain modeled as a single Rholang-like
//! source program plus a **compound-Poisson customer** layered on top of
//! the store place by a bespoke τ-leaping driver.
//!
//! ## Pipeline topology
//!
//! ```text
//!                certified?               capacity_ok?           customer (driver-side)
//!                    │                        │                      λ_c
//!   ┌─────────┐  ┌───▼───┐  ┌───────────┐  ┌──▼────┐  ┌─────────┐  ┌───▼──────────┐
//!   │ Factory │──▶  @1   │──▶ Warehouse │──▶  @2   │──▶  Store  │──▶ @3 (shelf)   │──▶ ★ sold
//!   └─────────┘  └───────┘  └───────────┘  └───────┘  └─────────┘  └──────────────┘
//!                place       transition      place       transition     place       compound-Poisson
//!                                                                                   batch ~ N(μ, σ²)
//! ```
//!
//! Source program (three channels, two receives):
//!
//! ```rholang
//! { @1!(Nil)
//! | for(x ← @1 where certified(x))   { @2!(*x) }
//! | for(y ← @2 where capacity_ok(y)) { @3!(*y) }
//! }
//! ```
//!
//! The customer is **not** a `PReceive` — it lives in the driver. Compound-
//! Poisson batch withdrawals (Normal-distributed N) are not process-
//! algebraic and would be dishonest to represent as a receive.
//!
//! ## Gates (all dynamic at runtime)
//!
//! - `certified(x)` — always seeded true (symbolic gate; retained for
//!   pedagogy of the SeedFacts path).
//! - `capacity_ok(y)` — its source-level predicate is **overridden** by a
//!   marking-backed guard closure: `marking[@3] < STORE_CAPACITY`. This
//!   demonstrates the guard-closure-over-marking path and replaces the
//!   previous scenario-based boolean toggling.
//!
//! ## Simulation: adaptive τ-leaping (Cao–Petzold 2006)
//!
//! Per leap:
//!
//! ```text
//! 1. Compute propensities a_j = rate_j · h_j(m) for all Petri transitions
//!    (guards respected). Add virtual customer a_c = λ_c if m(@3) ≥ 1.
//! 2. Choose τ bounding expected per-place and per-transition change by ε:
//!        τ_p = ε · max(1, m(p)) / |flux(p)|   (per place)
//!        τ_j = ε · h_j(m) / a_j               (per transition)
//!    τ = clamp(min τ_*, TAU_MIN, TAU_MAX).
//! 3. Sample K_j ∼ Poisson(a_j · τ) for each transition simultaneously,
//!    K_c ∼ Poisson(a_c · τ) for the customer.
//! 4. Apply all firings atomically. If store goes above capacity, bounce
//!    excess back to warehouse and record overflow clip.
//!    Sample K_c customer batches from Normal(μ, σ²), clamp each to
//!    available store inventory.
//! 5. If any place would go negative, halve τ and retry (≤ MAX_RETRIES).
//! 6. Advance time by τ, record stats, repeat until MAX_TIME / MAX_LEAPS /
//!    deadlock.
//! ```
//!
//! Worked example of one leap with τ=0.4 and all stages flowing:
//!
//! ```text
//!   before leap: m = [@1=30, @2=5, @3=4, sold=6]
//!   a_pn = [t₁=1·30=30, t₂=1·5=5]  a_c = 0.3  a₀ = 35.3
//!   K₁ ∼ Poisson(30·0.4)=Poisson(12)   →  K₁=11  (factory→warehouse)
//!   K₂ ∼ Poisson(5·0.4)=Poisson(2)     →  K₂=3   (warehouse→store)
//!   K_c ∼ Poisson(0.3·0.4)=Poisson(0.12) → K_c=1 with batch N(3,1)=3
//!   after leap (no overflow): m = [@1=19, @2=13, @3=4, sold=9]
//!   all three stages fired in the SAME leap — concurrency made explicit.
//! ```
//!
//! ## Part A (rewriter) preserved as a single fact-configured evaluation
//!
//! The Ascent-based rewriter still runs once with both relations seeded
//! true, showing the symbolic rewriting pedagogy paired with the
//! stochastic simulation.
//!
//! ## Running
//!
//! ```sh
//! cargo run -p mettail-simulation --example demo_supply_chain
//! ```

#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

pub use ascent_byods_rels::eqrel;
pub mod dual_indexed {
    pub use mettail_languages::dual_indexed::*;
}

use mettail_macros::language;
use mettail_prattail::petri::Marking;
use mettail_runtime::{
    clear_pred_fact_snapshot, evaluate_pred_with_bindings, set_pred_fact_snapshot, BehavioralPred,
    Language, Quantifier, SeedFacts,
};
use mettail_simulation::stochastic_petri::StochasticPetriNet;
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_distr::{Distribution, Normal, Poisson};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// ── Language definition ─────────────────────────────────────────────

language! {
    name: SupplyChain,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
        Name
        ![i64] as Int
    },

    guards {
        channels {
            channel Name;
            join PReceive(loc: Name);
        }
    },

    terms {
        PNil . |- "Nil" : Proc ;
        CastInt . k:Int |- k : Proc ;
        PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
        POutput . dst:Name, goods:Proc
            |- dst "!" "(" goods ")" : Proc ;
        PReceive . loc:Name, ?guard:Guard, ^x.p:[Name -> Proc]
            |- "for" "(" x "<-" loc "where" guard ")" "{" p "}" : Proc ;
        NQuote . p:Proc |- "@" p : Name ;
        PDrop . n:Name |- "*" n : Proc ;
    },

    equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N ;
        ExecEq . |- (PDrop (NQuote P)) = P ;
    },

    logic {
        relation certified(Name);
        relation capacity_ok(Name);
    },
}

// ── Source program ───────────────────────────────────────────────────

/// A 4-actor supply chain:
///   1. Factory ships goods into @1 (warehouse inbox).
///   2. Warehouse @1 inspects — forwards certified goods to @2.
///   3. Store @2 accepts — if capacity available, shelves goods at @3.
///   4. Customer (driver-side) withdraws Normal-distributed batches
///      from @3 as a Poisson process.
const SOURCE: &str = "\
    { @1!(Nil) \
    | for(x <- @1 where certified(x)){ @2!(*x) } \
    | for(y <- @2 where capacity_ok(y)){ @3!(*y) } \
    }";

// ── Simulation parameters ────────────────────────────────────────────

const FACTORY_INVENTORY: u64 = 50;
const STORE_CAPACITY: u64 = 10;
const LAMBDA_PN: f64 = 1.0;
const LAMBDA_CUSTOMER: f64 = 0.3;
const BATCH_MU: f64 = 3.0;
const BATCH_SIGMA: f64 = 1.0;
const MAX_TIME: f64 = 200.0;
const MAX_LEAPS: usize = 10_000;
const SEED: u64 = 42;

// τ-leaping parameters (Cao–Petzold 2006 adaptive step control)
//
// ε controls the mean firings per leap: for unit-arc / constant-rate
// systems the per-transition bound reduces to τ_j = ε · h_j / a_j = ε/λ,
// so mean firings per leap per transition ≈ ε · h_j. We use ε = 0.1 (vs
// Cao–Petzold canonical 0.03) to make concurrent firings visible in the
// event log without meaningful accuracy loss at O(1) rates. Drop to 0.03
// if you need the canonical conservative regime.
const EPSILON: f64 = 0.10;
const TAU_MIN: f64 = 1e-4;
const TAU_MAX: f64 = 1.0;
const MAX_RETRIES: usize = 5;

// ── Petri net construction from a parsed term ───────────────────────

#[allow(dead_code)]
struct PetriNetResult {
    net: StochasticPetriNet,
    place_ids: HashMap<Name, usize>,
    send_channels: Vec<Name>,
}

fn petri_net_from_proc(proc: &Proc, facts: &SeedFacts, rate: f64) -> PetriNetResult {
    let mut net = StochasticPetriNet::new();
    let mut place_ids: HashMap<Name, usize> = HashMap::new();

    let mut send_channels: Vec<Name> = Vec::new();
    let mut receives: Vec<(Name, BehavioralPred, Vec<Name>, String)> = Vec::new();

    let get_place = |net: &mut StochasticPetriNet,
                     place_ids: &mut HashMap<Name, usize>,
                     name: &Name|
     -> usize {
        if let Some(&id) = place_ids.get(name) {
            id
        } else {
            let label = channel_label(name);
            let id = net.add_place(label);
            place_ids.insert(name.clone(), id);
            id
        }
    };

    collect_top_level(proc, &mut send_channels, &mut receives);

    for ch in &send_channels {
        get_place(&mut net, &mut place_ids, ch);
    }
    for (ch, _, output_chs, _) in &receives {
        get_place(&mut net, &mut place_ids, ch);
        for dst in output_chs {
            get_place(&mut net, &mut place_ids, dst);
        }
    }

    for ch in &send_channels {
        let place = place_ids[ch];
        net.set_initial_tokens(place, 1);
    }

    let snapshot: HashMap<String, HashSet<Vec<String>>> = facts
        .iter()
        .map(|(k, v)| (k.clone(), v.iter().cloned().collect()))
        .collect();

    for (ch, pred, output_chs, binder_name) in &receives {
        let pred_name = predicate_name(pred);
        let label = format!("{} [{}]", channel_label(ch), pred_name);

        let t = if matches!(pred, BehavioralPred::Top) {
            net.add_transition(label, rate)
        } else {
            let pred_clone = pred.clone();
            let binder = binder_name.clone();
            let snap_clone = snapshot.clone();
            let guard = Arc::new(move |_marking: &Marking| {
                set_pred_fact_snapshot(snap_clone.clone());
                let bindings = vec![(binder.clone(), "@Nil".to_string())];
                let result = evaluate_pred_with_bindings(&pred_clone, &bindings);
                clear_pred_fact_snapshot();
                result
            });
            net.add_guarded_transition(label, rate, guard)
        };
        net.add_input(t, place_ids[ch], 1);

        if output_chs.is_empty() {
            let sink_label = format!("delivered@{}", channel_label(ch));
            let sink_id = net.add_place(sink_label);
            net.add_output(t, sink_id, 1);
        } else {
            for dst in output_chs {
                net.add_output(t, place_ids[dst], 1);
            }
        }
    }

    PetriNetResult { net, place_ids, send_channels }
}

fn collect_top_level(
    proc: &Proc,
    sends: &mut Vec<Name>,
    receives: &mut Vec<(Name, BehavioralPred, Vec<Name>, String)>,
) {
    match proc {
        Proc::PPar(bag) => {
            for (elem, _) in bag.iter() {
                collect_top_level(elem, sends, receives);
            }
        },
        Proc::POutput(dst, _) => {
            if matches!(**dst, Name::NQuote(_)) {
                sends.push((**dst).clone());
            }
        },
        Proc::PReceive(loc, pred, scope) => {
            if matches!(**loc, Name::NQuote(_)) {
                let body = scope.unsafe_body();
                let output_chs = collect_output_channels(body);
                let binder_name = scope
                    .unsafe_pattern()
                    .0
                    .pretty_name
                    .as_ref()
                    .map(|s| s.to_string())
                    .unwrap_or_default();
                receives.push(((**loc).clone(), pred.clone(), output_chs, binder_name));
            }
        },
        _ => {},
    }
}

fn collect_output_channels(proc: &Proc) -> Vec<Name> {
    let mut channels = Vec::new();
    collect_outputs_recursive(proc, &mut channels);
    channels
}

fn collect_outputs_recursive(proc: &Proc, channels: &mut Vec<Name>) {
    match proc {
        Proc::POutput(dst, _) => {
            if matches!(**dst, Name::NQuote(_)) {
                channels.push((**dst).clone());
            }
        },
        Proc::PPar(bag) => {
            for (elem, _) in bag.iter() {
                collect_outputs_recursive(elem, channels);
            }
        },
        _ => {},
    }
}

fn channel_label(name: &Name) -> String {
    format!("{}", name)
}

fn predicate_name(pred: &BehavioralPred) -> String {
    match pred {
        BehavioralPred::Top => "true".to_string(),
        BehavioralPred::RelationQuery { relation_name, .. } => relation_name.clone(),
        BehavioralPred::And(a, b) => format!("{} & {}", predicate_name(a), predicate_name(b)),
        BehavioralPred::Or(a, b) => format!("{} | {}", predicate_name(a), predicate_name(b)),
        BehavioralPred::Not(inner) => format!("!{}", predicate_name(inner)),
        BehavioralPred::Implies(p, c) => format!("{} => {}", predicate_name(p), predicate_name(c)),
        BehavioralPred::Quantified { quantifier, var, body, .. } => {
            let q = match quantifier {
                Quantifier::ForAll => "forall",
                Quantifier::Exists => "exists",
            };
            format!("{}({}, {})", q, var, predicate_name(body))
        },
        BehavioralPred::AcMatch { .. } => "ac_match(...)".to_string(),
    }
}

// ── Helpers for net lookup and capacity guard installation ──────────

fn find_place_by_label(net: &StochasticPetriNet, label: &str) -> Option<usize> {
    net.places.iter().position(|p| p.name == label)
}

fn find_transition_by_label_substring(net: &StochasticPetriNet, substr: &str) -> Option<usize> {
    net.transitions
        .iter()
        .position(|t| t.transition.name.contains(substr))
}

/// Replace a transition's guard with a marking-backed closure enforcing
/// `marking[store_place] < capacity`. Used to override the SeedFacts-
/// backed `capacity_ok` predicate with dynamic runtime capacity control.
fn install_capacity_guard(
    net: &mut StochasticPetriNet,
    transition_id: usize,
    store_place_id: usize,
    capacity: u64,
) {
    let guard = Arc::new(move |m: &Marking| m.get(store_place_id) < capacity);
    net.transitions[transition_id].guard = Some(guard);
}

// ── τ-leaping driver ────────────────────────────────────────────────

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct CustomerLeap {
    arrivals: u64,
    batches: Vec<u64>,
    units_sold: u64,
    blocked: u64,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct LeapRecord {
    t_start: f64,
    tau: f64,
    pn_firings: Vec<u64>,
    customer: CustomerLeap,
    overflow_clip: u64,
    retries: u32,
    marking_after: Marking,
}

#[derive(Debug, Clone)]
struct Stats {
    place_time_integrals: Vec<f64>,
    units_sold: u64,
    customer_arrivals: u64,
    blocked_arrivals: u64,
    batch_size_sum: u64,
    gate_blocked_time: f64,
    overflow_clips: u64,
    tau_sum: f64,
    tau_min_seen: f64,
    tau_max_seen: f64,
    leaps: u64,
    multi_firing_leaps: u64,
    max_firings_in_leap: u64,
    total_retries: u32,
    final_time: f64,
}

struct SupplyChainTrace {
    leaps: Vec<LeapRecord>,
    final_marking: Marking,
    stats: Stats,
    deadlocked: bool,
}

/// Sample one batch per customer arrival from Normal(μ, σ²); clamp to
/// `[1, remaining inventory]`. Returns (batches, blocked_count) where
/// `blocked_count` is the number of arrivals that met an empty store.
fn sample_customer_batches(
    rng: &mut StdRng,
    arrivals: u64,
    initial_available: u64,
) -> (Vec<u64>, u64) {
    let normal = Normal::new(BATCH_MU, BATCH_SIGMA).expect("invalid Normal parameters");
    let mut remaining = initial_available;
    let mut batches = Vec::with_capacity(arrivals as usize);
    let mut blocked = 0u64;
    for _ in 0..arrivals {
        if remaining == 0 {
            blocked += 1;
            batches.push(0);
            continue;
        }
        let raw = normal.sample(rng);
        let desired = raw.round().max(1.0) as u64;
        let batch = desired.min(remaining);
        remaining -= batch;
        batches.push(batch);
    }
    (batches, blocked)
}

/// Cao–Petzold adaptive τ. Bounds per-place and per-transition expected
/// change to ε of the current state.
fn adaptive_tau(
    net: &StochasticPetriNet,
    marking: &Marking,
    pn_props: &[f64],
    a_cust: f64,
    store_place_id: usize,
) -> f64 {
    let num_places = net.places.len();
    let mut flux = vec![0f64; num_places];
    for (j, st) in net.transitions.iter().enumerate() {
        let a_j = pn_props[j];
        if a_j <= 0.0 {
            continue;
        }
        for (p, w) in &st.transition.inputs {
            flux[*p] -= a_j * (*w as f64);
        }
        for (p, w) in &st.transition.outputs {
            flux[*p] += a_j * (*w as f64);
        }
    }
    // Customer contributes -λ_c · E[batch] at the store place.
    if store_place_id < num_places {
        flux[store_place_id] -= a_cust * BATCH_MU;
    }

    // Cao–Petzold: bound expected per-place change to max(ε · m(p), 1)
    // tokens — i.e., the leap should not be expected to move a place by
    // more than max(ε·m, 1) tokens. The "1" floor prevents pathologically
    // small τ at empty-but-receiving places.
    let mut tau = TAU_MAX;
    for p in 0..num_places {
        let f = flux[p].abs();
        if f > 0.0 {
            let bound = (EPSILON * marking.get(p) as f64).max(1.0);
            let tau_p = bound / f;
            if tau_p < tau {
                tau = tau_p;
            }
        }
    }

    // Per-transition multiplicity bound: no more than max(ε·h_j, 1)
    // expected firings per transition.
    for (j, st) in net.transitions.iter().enumerate() {
        let a_j = pn_props[j];
        if a_j <= 0.0 {
            continue;
        }
        let h_j = st
            .transition
            .inputs
            .iter()
            .map(|(p, w)| {
                if *w == 0 {
                    u64::MAX
                } else {
                    marking.get(*p) / w
                }
            })
            .min()
            .unwrap_or(1) as f64;
        let bound = (EPSILON * h_j).max(1.0);
        let tau_j = bound / a_j;
        if tau_j < tau {
            tau = tau_j;
        }
    }

    tau.clamp(TAU_MIN, TAU_MAX)
}

fn sample_pn_firings(pn_props: &[f64], tau: f64, rng: &mut StdRng) -> Vec<u64> {
    let mut firings = Vec::with_capacity(pn_props.len());
    for &a_j in pn_props {
        if a_j <= 0.0 {
            firings.push(0);
        } else {
            let mean = a_j * tau;
            let k = Poisson::new(mean)
                .expect("invalid Poisson rate")
                .sample(rng) as u64;
            firings.push(k);
        }
    }
    firings
}

/// Apply Petri-net firings to a trial marking using saturating arithmetic.
/// Returns `Some(new_marking)` if all firings were consistent (no place
/// went negative), else `None` — caller halves τ and retries.
fn apply_pn_firings(
    net: &StochasticPetriNet,
    marking: &Marking,
    firings: &[u64],
) -> Option<Marking> {
    let mut trial = marking.clone();
    for (j, &k) in firings.iter().enumerate() {
        if k == 0 {
            continue;
        }
        let t = &net.transitions[j].transition;
        for (p, w) in &t.inputs {
            let need = k.checked_mul(*w).expect("arc weight overflow");
            if trial.tokens[*p] < need {
                return None;
            }
            trial.tokens[*p] -= need;
        }
        for (p, w) in &t.outputs {
            let gain = k.checked_mul(*w).expect("arc weight overflow");
            trial.tokens[*p] = trial.tokens[*p].saturating_add(gain);
        }
    }
    Some(trial)
}

/// If the warehouse→store transition pushed the store above capacity,
/// bounce the excess tokens back to the warehouse place (conserves
/// token count: each bounced firing is undone in both directions).
/// Returns the number of clipped firings.
fn clip_overflow_to_capacity(
    net: &StochasticPetriNet,
    trial: &mut Marking,
    store_place_id: usize,
    cap_transition_id: usize,
) -> u64 {
    let store_tokens = trial.tokens[store_place_id];
    if store_tokens <= STORE_CAPACITY {
        return 0;
    }
    let excess = store_tokens - STORE_CAPACITY;
    trial.tokens[store_place_id] = STORE_CAPACITY;

    // Bounce excess back to input place(s) of the capacity transition.
    let t = &net.transitions[cap_transition_id].transition;
    for (p_in, w_in) in &t.inputs {
        let returned = excess.saturating_mul(*w_in);
        trial.tokens[*p_in] = trial.tokens[*p_in].saturating_add(returned);
    }
    excess
}

fn simulate_with_customer_tau_leap(
    net: &StochasticPetriNet,
    store_place_id: usize,
    cap_transition_id: usize,
    rng: &mut StdRng,
) -> SupplyChainTrace {
    let num_places = net.places.len();
    let mut marking = net.initial_marking.clone();
    let mut time = 0.0f64;
    let mut leaps: Vec<LeapRecord> = Vec::new();
    let mut stats = Stats {
        place_time_integrals: vec![0.0; num_places],
        units_sold: 0,
        customer_arrivals: 0,
        blocked_arrivals: 0,
        batch_size_sum: 0,
        gate_blocked_time: 0.0,
        overflow_clips: 0,
        tau_sum: 0.0,
        tau_min_seen: f64::INFINITY,
        tau_max_seen: 0.0,
        leaps: 0,
        multi_firing_leaps: 0,
        max_firings_in_leap: 0,
        total_retries: 0,
        final_time: 0.0,
    };
    let mut deadlocked = false;

    while time < MAX_TIME && leaps.len() < MAX_LEAPS {
        let pn_props = net.propensities(&marking);
        let a_pn: f64 = pn_props.iter().sum();
        let a_cust = if marking.get(store_place_id) >= 1 {
            LAMBDA_CUSTOMER
        } else {
            0.0
        };
        let a0 = a_pn + a_cust;
        if a0 <= 0.0 {
            deadlocked = true;
            break;
        }

        let mut tau = adaptive_tau(net, &marking, &pn_props, a_cust, store_place_id);
        if time + tau > MAX_TIME {
            tau = MAX_TIME - time;
        }
        if tau <= 0.0 {
            break;
        }

        let mut retries: u32 = 0;
        let (pn_firings, customer, overflow_clip, new_marking, actual_tau) = loop {
            let pn_firings = sample_pn_firings(&pn_props, tau, rng);
            match apply_pn_firings(net, &marking, &pn_firings) {
                Some(mut trial) => {
                    let overflow_clip = clip_overflow_to_capacity(
                        net,
                        &mut trial,
                        store_place_id,
                        cap_transition_id,
                    );

                    // Sample customer arrivals & batches.
                    let cust_arr: u64 = if a_cust > 0.0 {
                        Poisson::new(a_cust * tau)
                            .expect("invalid Poisson rate")
                            .sample(rng) as u64
                    } else {
                        0
                    };
                    let (batches, blocked) =
                        sample_customer_batches(rng, cust_arr, trial.tokens[store_place_id]);
                    let units_sold: u64 = batches.iter().sum();
                    trial.tokens[store_place_id] -= units_sold;

                    let customer = CustomerLeap {
                        arrivals: cust_arr,
                        batches,
                        units_sold,
                        blocked,
                    };

                    break (pn_firings, customer, overflow_clip, trial, tau);
                },
                None => {
                    retries += 1;
                    if retries as usize >= MAX_RETRIES {
                        // Fallback: take a single direct-SSA step.
                        let u1: f64 = rng.gen_range(1e-12..1.0);
                        let fallback_tau = (-u1.ln() / a0).min(TAU_MAX);
                        let u2: f64 = rng.gen::<f64>() * a0;
                        let mut cum = 0.0f64;
                        let mut fallback_firings = vec![0u64; pn_props.len()];
                        let mut fallback_customer = CustomerLeap {
                            arrivals: 0,
                            batches: Vec::new(),
                            units_sold: 0,
                            blocked: 0,
                        };
                        let mut picked_j: Option<usize> = None;
                        for (j, &a) in pn_props.iter().enumerate() {
                            cum += a;
                            if u2 <= cum {
                                picked_j = Some(j);
                                break;
                            }
                        }
                        let mut trial = marking.clone();
                        let mut overflow_clip = 0u64;
                        if let Some(j) = picked_j {
                            fallback_firings[j] = 1;
                            if let Some(fired) = net.fire(j, &trial) {
                                trial = fired;
                            }
                            overflow_clip = clip_overflow_to_capacity(
                                net,
                                &mut trial,
                                store_place_id,
                                cap_transition_id,
                            );
                        } else if a_cust > 0.0 && trial.tokens[store_place_id] > 0 {
                            let normal = Normal::new(BATCH_MU, BATCH_SIGMA).unwrap();
                            let raw = normal.sample(rng).round().max(1.0) as u64;
                            let batch = raw.min(trial.tokens[store_place_id]);
                            trial.tokens[store_place_id] -= batch;
                            fallback_customer = CustomerLeap {
                                arrivals: 1,
                                batches: vec![batch],
                                units_sold: batch,
                                blocked: 0,
                            };
                        }
                        break (
                            fallback_firings,
                            fallback_customer,
                            overflow_clip,
                            trial,
                            fallback_tau,
                        );
                    }
                    tau = (tau * 0.5).max(TAU_MIN);
                },
            }
        };

        // Accumulate time-weighted stats using the PRE-leap marking.
        for p in 0..num_places {
            stats.place_time_integrals[p] += marking.get(p) as f64 * actual_tau;
        }
        if marking.get(store_place_id) >= STORE_CAPACITY {
            stats.gate_blocked_time += actual_tau;
        }

        // Count simultaneity.
        let active_firings = pn_firings.iter().filter(|&&k| k > 0).count() as u64
            + if customer.arrivals > 0 { 1 } else { 0 };
        if active_firings >= 2 {
            stats.multi_firing_leaps += 1;
        }
        let total_firings: u64 = pn_firings.iter().sum::<u64>() + customer.arrivals;
        if total_firings > stats.max_firings_in_leap {
            stats.max_firings_in_leap = total_firings;
        }

        stats.customer_arrivals += customer.arrivals;
        stats.blocked_arrivals += customer.blocked;
        stats.units_sold += customer.units_sold;
        stats.batch_size_sum += customer.units_sold;
        stats.overflow_clips += overflow_clip;
        stats.tau_sum += actual_tau;
        stats.tau_min_seen = stats.tau_min_seen.min(actual_tau);
        stats.tau_max_seen = stats.tau_max_seen.max(actual_tau);
        stats.leaps += 1;
        stats.total_retries += retries;

        // Commit.
        marking = new_marking;
        time += actual_tau;

        leaps.push(LeapRecord {
            t_start: time - actual_tau,
            tau: actual_tau,
            pn_firings,
            customer,
            overflow_clip,
            retries,
            marking_after: marking.clone(),
        });
    }

    stats.final_time = time;
    if stats.tau_min_seen.is_infinite() {
        stats.tau_min_seen = 0.0;
    }

    SupplyChainTrace {
        leaps,
        final_marking: marking,
        stats,
        deadlocked,
    }
}

// ── Per-leap inventory trace ────────────────────────────────────────

fn render_customer_cell(cl: &CustomerLeap) -> String {
    if cl.arrivals == 0 {
        "·".to_string()
    } else {
        let batches: Vec<String> = cl.batches.iter().map(|b| b.to_string()).collect();
        format!("{}({})", cl.arrivals, batches.join(","))
    }
}

fn render_clip_cell(clip: u64) -> String {
    if clip == 0 {
        "·".to_string()
    } else {
        clip.to_string()
    }
}

fn render_firing_cell(k: u64) -> String {
    if k == 0 {
        "·".to_string()
    } else {
        k.to_string()
    }
}

/// Build a human-readable comment describing the actions in a single
/// leap. Semicolon-joined fragments cover: factory shipments, warehouse
/// deliveries to the store, customer purchases (with batch sizes), and
/// overflow clips. An idle leap reads "idle".
fn render_comment_cell(
    leap: &LeapRecord,
    factory_tx_id: Option<usize>,
    store_tx_id: Option<usize>,
) -> String {
    let mut parts: Vec<String> = Vec::new();

    if let Some(id) = factory_tx_id {
        let k = leap.pn_firings.get(id).copied().unwrap_or(0);
        if k > 0 {
            parts.push(format!("factory shipped {}", k));
        }
    }
    if let Some(id) = store_tx_id {
        let k = leap.pn_firings.get(id).copied().unwrap_or(0);
        let clipped = leap.overflow_clip;
        let net_delivered = k.saturating_sub(clipped);
        if net_delivered > 0 {
            parts.push(format!("warehouse stocked {}", net_delivered));
        }
        if clipped > 0 {
            parts.push(format!("bounced {} (store full)", clipped));
        }
    }

    if leap.customer.arrivals > 0 {
        let purchased = leap.customer.units_sold;
        let batches: Vec<String> = leap
            .customer
            .batches
            .iter()
            .filter(|&&b| b > 0)
            .map(|b| b.to_string())
            .collect();
        if leap.customer.arrivals == 1 {
            parts.push(format!("customer bought {}", purchased));
        } else if !batches.is_empty() {
            parts.push(format!(
                "{} customers bought {} ({})",
                leap.customer.arrivals,
                purchased,
                batches.join(","),
            ));
        } else {
            parts.push(format!("{} customers arrived (store empty)", leap.customer.arrivals));
        }
        if leap.customer.blocked > 0 && leap.customer.units_sold > 0 {
            parts.push(format!("{} blocked (store empty)", leap.customer.blocked));
        }
    }

    if parts.is_empty() {
        "idle".to_string()
    } else {
        parts.join("; ")
    }
}

/// Widths (character counts, display width) for every column in the
/// trace table. Each is the max of its header label width and the
/// widest rendered data value across all leaps.
struct ColumnWidths {
    leap: usize,
    t_start: usize,
    tau: usize,
    tx: Vec<usize>,
    customer: usize,
    clip: usize,
    places: Vec<usize>,
    factory_loc: usize,
    store_loc: usize,
    customer_loc: usize,
    comment: usize,
}

fn compute_column_widths(
    trace: &SupplyChainTrace,
    net: &StochasticPetriNet,
    tx_labels: &[String],
    place_labels: &[String],
    factory_place_id: Option<usize>,
    store_place_id: Option<usize>,
    factory_tx_id: Option<usize>,
    store_tx_id: Option<usize>,
) -> ColumnWidths {
    let char_len = |s: &str| s.chars().count();

    let max_leap_idx = trace.leaps.len().saturating_sub(1);
    let leap_w = char_len("leap").max(max_leap_idx.to_string().len());

    // t_start printed as "{:.3}" — up to "999.999" plus sign = 7 chars is enough.
    let t_start_w = char_len("t_start").max(7);
    // τ printed as "{:.4}" — up to "1.0000" = 6 chars.
    let tau_w = char_len("τ").max(6);

    let mut tx_w: Vec<usize> = tx_labels.iter().map(|l| char_len(l)).collect();
    for leap in &trace.leaps {
        for (j, &k) in leap.pn_firings.iter().enumerate() {
            let v = render_firing_cell(k);
            if char_len(&v) > tx_w[j] {
                tx_w[j] = char_len(&v);
            }
        }
    }

    let mut cust_w = char_len("customer (batches)");
    for leap in &trace.leaps {
        let v = render_customer_cell(&leap.customer);
        if char_len(&v) > cust_w {
            cust_w = char_len(&v);
        }
    }

    let mut clip_w = char_len("clip");
    for leap in &trace.leaps {
        let v = render_clip_cell(leap.overflow_clip);
        if char_len(&v) > clip_w {
            clip_w = char_len(&v);
        }
    }

    let mut place_w: Vec<usize> = place_labels.iter().map(|l| char_len(l)).collect();
    for leap in &trace.leaps {
        for (p, w) in place_w.iter_mut().enumerate().take(net.places.len()) {
            let v = leap.marking_after.get(p).to_string();
            if char_len(&v) > *w {
                *w = char_len(&v);
            }
        }
    }

    // Location inventory: factory (@1), store (@3), customer (cumulative sold).
    let mut factory_w = char_len("factory");
    let mut store_w = char_len("store");
    let mut customer_loc_w = char_len("customer");
    let mut cum_sold: u64 = 0;
    for leap in &trace.leaps {
        cum_sold += leap.customer.units_sold;
        if let Some(fid) = factory_place_id {
            let v = leap.marking_after.get(fid).to_string();
            if char_len(&v) > factory_w {
                factory_w = char_len(&v);
            }
        }
        if let Some(sid) = store_place_id {
            let v = leap.marking_after.get(sid).to_string();
            if char_len(&v) > store_w {
                store_w = char_len(&v);
            }
        }
        let v = cum_sold.to_string();
        if char_len(&v) > customer_loc_w {
            customer_loc_w = char_len(&v);
        }
    }

    let mut comment_w = char_len("comment");
    for leap in &trace.leaps {
        let v = render_comment_cell(leap, factory_tx_id, store_tx_id);
        if char_len(&v) > comment_w {
            comment_w = char_len(&v);
        }
    }

    ColumnWidths {
        leap: leap_w,
        t_start: t_start_w,
        tau: tau_w,
        tx: tx_w,
        customer: cust_w,
        clip: clip_w,
        places: place_w,
        factory_loc: factory_w,
        store_loc: store_w,
        customer_loc: customer_loc_w,
        comment: comment_w,
    }
}

/// Print a compact per-leap table showing which transitions fired,
/// customer arrivals/batches, any capacity overflow, and the marking
/// after the leap. One row per leap. Every column's width is computed
/// to fit both its header label and the widest rendered value.
fn print_leap_trace(trace: &SupplyChainTrace, net: &StochasticPetriNet) {
    let tx_labels: Vec<String> = net
        .transitions
        .iter()
        .enumerate()
        .map(|(j, st)| format!("t{}[{}]", j, short_tx_label(&st.transition.name)))
        .collect();
    let place_labels: Vec<String> = net.places.iter().map(|p| p.name.clone()).collect();

    let factory_place_id = find_place_by_label(net, "@1");
    let store_place_id = find_place_by_label(net, "@3");
    let factory_tx_id = find_transition_by_label_substring(net, "certified");
    let store_tx_id = find_transition_by_label_substring(net, "capacity_ok");
    let w = compute_column_widths(
        trace,
        net,
        &tx_labels,
        &place_labels,
        factory_place_id,
        store_place_id,
        factory_tx_id,
        store_tx_id,
    );

    // Header.
    print!(
        "  {:>lw$}  {:>tw$}  {:>uw$}  ",
        "leap",
        "t_start",
        "τ",
        lw = w.leap,
        tw = w.t_start,
        uw = w.tau,
    );
    for (lbl, &cw) in tx_labels.iter().zip(&w.tx) {
        print!(" {:>cw$}", lbl, cw = cw);
    }
    print!(
        "  │ {:>cc$}  {:>cl$}  │",
        "customer (batches)",
        "clip",
        cc = w.customer,
        cl = w.clip,
    );
    for (lbl, &pw) in place_labels.iter().zip(&w.places) {
        print!(" {:>pw$}", lbl, pw = pw);
    }
    print!(
        "  │ {:>fw$}  {:>sw$}  {:>kw$}",
        "factory",
        "store",
        "customer",
        fw = w.factory_loc,
        sw = w.store_loc,
        kw = w.customer_loc,
    );
    print!("  │ {:<mw$}", "comment", mw = w.comment);
    println!();

    // Divider.
    print!(
        "  {:->lw$}  {:->tw$}  {:->uw$}  ",
        "",
        "",
        "",
        lw = w.leap,
        tw = w.t_start,
        uw = w.tau,
    );
    for &cw in &w.tx {
        print!(" {:->cw$}", "", cw = cw);
    }
    print!("  │ {:->cc$}  {:->cl$}  │", "", "", cc = w.customer, cl = w.clip,);
    for &pw in &w.places {
        print!(" {:->pw$}", "", pw = pw);
    }
    print!(
        "  │ {:->fw$}  {:->sw$}  {:->kw$}",
        "",
        "",
        "",
        fw = w.factory_loc,
        sw = w.store_loc,
        kw = w.customer_loc,
    );
    print!("  │ {:-<mw$}", "", mw = w.comment);
    println!();

    // Rows.
    let mut cum_sold: u64 = 0;
    for (i, leap) in trace.leaps.iter().enumerate() {
        cum_sold += leap.customer.units_sold;
        print!(
            "  {:>lw$}  {:>tw$.3}  {:>uw$.4}  ",
            i,
            leap.t_start,
            leap.tau,
            lw = w.leap,
            tw = w.t_start,
            uw = w.tau,
        );
        for (j, &k) in leap.pn_firings.iter().enumerate() {
            let cell = render_firing_cell(k);
            print!(" {:>cw$}", cell, cw = w.tx[j]);
        }
        let cust_col = render_customer_cell(&leap.customer);
        let clip_col = render_clip_cell(leap.overflow_clip);
        print!("  │ {:>cc$}  {:>cl$}  │", cust_col, clip_col, cc = w.customer, cl = w.clip,);
        for p in 0..net.places.len() {
            let tok = leap.marking_after.get(p).to_string();
            print!(" {:>pw$}", tok, pw = w.places[p]);
        }
        let factory_inv = factory_place_id
            .map(|id| leap.marking_after.get(id))
            .unwrap_or(0);
        let store_inv = store_place_id
            .map(|id| leap.marking_after.get(id))
            .unwrap_or(0);
        print!(
            "  │ {:>fw$}  {:>sw$}  {:>kw$}",
            factory_inv,
            store_inv,
            cum_sold,
            fw = w.factory_loc,
            sw = w.store_loc,
            kw = w.customer_loc,
        );
        let comment = render_comment_cell(leap, factory_tx_id, store_tx_id);
        print!("  │ {:<mw$}", comment, mw = w.comment);
        println!();
    }

    // Legend.
    println!();
    println!("  Legend:");
    println!("    tN[…]    = transition N fired K_N ∼ Poisson(λ·τ) times this leap (· = 0)");
    println!("    customer (batches) = {{K_c}}({{batch₁,batch₂,…}}) — arrivals and clamped Normal batch sizes");
    println!(
        "    clip     = warehouse→store firings bounced back (post-Poisson capacity enforcement)"
    );
    println!("    @N       = tokens queued in channel @N *after* this leap");
    println!(
        "    factory  = inventory at the factory (= tokens at @1, waiting for warehouse intake)"
    );
    println!("    store    = inventory on the store shelf (= tokens at @3, ≤ STORE_CAPACITY)");
    println!(
        "    customer = cumulative units purchased by customers up to and including this leap"
    );
    println!("    comment  = human-readable summary of actions in the leap (semicolon-joined)");
}

/// Shorten a transition name like "@2 [capacity_ok]" → "@2:cap_ok" for compact columns.
fn short_tx_label(full: &str) -> String {
    // Keep up to first "[" or space, then append a compact pred tag.
    let (ch, pred) = full
        .split_once('[')
        .map(|(a, b)| (a.trim(), b.trim_end_matches(']').trim()))
        .unwrap_or((full, ""));
    let pred_short = match pred {
        "certified" => "cert",
        "capacity_ok" => "cap",
        "" => "",
        other => other,
    };
    if pred_short.is_empty() {
        ch.to_string()
    } else {
        format!("{}:{}", ch, pred_short)
    }
}

// ── Stats printing ──────────────────────────────────────────────────

fn print_stats(trace: &SupplyChainTrace, net: &StochasticPetriNet) {
    let s = &trace.stats;
    let t = s.final_time.max(1e-12);

    // Per-transition total firings (for per-stage throughput).
    let num_transitions = net.transitions.len();
    let mut total_firings = vec![0u64; num_transitions];
    for leap in &trace.leaps {
        for (j, &k) in leap.pn_firings.iter().enumerate() {
            total_firings[j] += k;
        }
    }

    println!(
        "  Simulation time: {:.2} ATU   Leaps: {}   Deadlocked: {}",
        s.final_time, s.leaps, trace.deadlocked
    );
    let mean_tau = if s.leaps > 0 {
        s.tau_sum / s.leaps as f64
    } else {
        0.0
    };
    println!(
        "  Mean τ: {:.4} ATU   [τ_min={:.4}, τ_max={:.4}]   retries={}",
        mean_tau, s.tau_min_seen, s.tau_max_seen, s.total_retries
    );

    // Per-place time-averaged inventory.
    let avg = |p: usize| -> f64 { s.place_time_integrals[p] / t };

    // Emit per-actor metrics. Labels match the Petri net place/transition names.
    println!();
    for (j, st) in net.transitions.iter().enumerate() {
        println!(
            "  Transition t{}: {:<25}  fired {}  (avg {:.2}/ATU)",
            j,
            st.transition.name,
            total_firings[j],
            total_firings[j] as f64 / t
        );
    }

    println!();
    for (i, place) in net.places.iter().enumerate() {
        let final_tokens = trace.final_marking.get(i);
        println!(
            "  Place p{}: {:<25}  avg inventory = {:.2}   final = {}",
            i,
            place.name,
            avg(i),
            final_tokens
        );
    }

    // Store-specific stats.
    if let Some(store_idx) = net.places.iter().position(|p| p.name == "@3") {
        let pct_full = 100.0 * s.gate_blocked_time / t;
        println!();
        println!(
            "  Store ({}) capacity = {}   time at capacity = {:.2} ATU ({:.1}%)",
            net.places[store_idx].name, STORE_CAPACITY, s.gate_blocked_time, pct_full
        );
        println!(
            "  Overflow-clipped deliveries (bounced back to warehouse) = {}",
            s.overflow_clips
        );
    }

    // Customer stats.
    let mean_batch = if s.customer_arrivals - s.blocked_arrivals > 0 {
        s.units_sold as f64 / (s.customer_arrivals - s.blocked_arrivals) as f64
    } else {
        0.0
    };
    println!();
    println!("  Customer:");
    println!(
        "    arrivals = {}   blocked (empty store) = {}",
        s.customer_arrivals, s.blocked_arrivals
    );
    println!(
        "    units purchased = {}   mean batch = {:.2}   (Normal μ={:.1}, σ={:.1})",
        s.units_sold, mean_batch, BATCH_MU, BATCH_SIGMA
    );

    // Simultaneity.
    let pct_multi = if s.leaps > 0 {
        100.0 * s.multi_firing_leaps as f64 / s.leaps as f64
    } else {
        0.0
    };
    println!();
    println!("  Simultaneity: {:.1}% of leaps had ≥2 transitions firing (max {} firings in a single leap)",
        pct_multi, s.max_firings_in_leap);

    // Conservation check: factory_dispatched = warehouse_forwarded = sold + remaining.
    let factory_final = trace.final_marking.tokens[0];
    let remaining_in_pipeline: u64 = trace.final_marking.tokens.iter().sum();
    let conservation_lhs = FACTORY_INVENTORY;
    let conservation_rhs = remaining_in_pipeline + s.units_sold;
    let ok = conservation_lhs == conservation_rhs;
    println!();
    println!(
        "  Conservation: initial({}) = remaining({}) + sold({}) = {}   {}",
        conservation_lhs,
        remaining_in_pipeline,
        s.units_sold,
        conservation_rhs,
        if ok { "✓" } else { "✗ MISMATCH" }
    );
    let _ = factory_final;
}

// ── Main ────────────────────────────────────────────────────────────

fn main() {
    println!("=== Supply Chain with Customer (τ-leaping) ===\n");
    println!("  Factory ──(@1)──▶ Warehouse ──(@2)──▶ Store ──(@3)──▶ Customer");
    println!("                    certified?          capacity_ok?         λ_c compound-Poisson\n");
    println!("Source:\n  {}\n", SOURCE);

    println!("Configuration:");
    println!("  Initial factory inventory: {}", FACTORY_INVENTORY);
    println!("  Store capacity:            {}", STORE_CAPACITY);
    println!("  λ(pipeline transitions):   {}", LAMBDA_PN);
    println!("  λ(customer arrivals):      {}", LAMBDA_CUSTOMER);
    println!(
        "  Batch ~ Normal(μ={:.1}, σ={:.1}), clamped to [1, store inventory]",
        BATCH_MU, BATCH_SIGMA
    );
    println!("  max_time: {:.1} ATU   max_leaps: {}   seed: {}", MAX_TIME, MAX_LEAPS, SEED);
    println!(
        "  τ-leap ε: {:.2}   τ ∈ [{:.0e}, {:.1}]   max_retries: {}\n",
        EPSILON, TAU_MIN, TAU_MAX, MAX_RETRIES
    );

    let lang = SupplyChainLanguage;
    let term = match lang.parse_term(SOURCE) {
        Ok(t) => t,
        Err(e) => {
            println!("[parse error] {}", e);
            return;
        },
    };
    println!("Parsed: {}\n", lang.format_term(&*term));

    let typed = term
        .as_any()
        .downcast_ref::<SupplyChainTerm>()
        .expect("expected SupplyChainTerm");
    let proc = match &typed.0 {
        SupplyChainTermInner::Proc(p) => p,
        _ => {
            println!("[error] expected Proc, got {:?}", typed.0);
            return;
        },
    };

    // Both source-level predicates are seeded true permanently. The
    // capacity_ok(y) predicate's effective semantics are overridden
    // below by a marking-backed guard closure.
    let facts = build_facts(true, true);

    // ─── Part A: Rewriter (single run) ─────────────────────────────
    println!("─── Part A: Rewriter (single run, both relations seeded true) ───\n");
    let results = lang
        .run_ascent_with_facts(&*term, &facts)
        .expect("ascent failed");
    let rewrites = results.rewrites.len();
    let rewrite_targets: std::collections::HashSet<_> =
        results.rewrites.iter().map(|rw| rw.to_id).collect();
    let produced: Vec<_> = results
        .all_terms
        .iter()
        .filter(|t| rewrite_targets.contains(&t.term_id))
        .collect();
    if produced.is_empty() {
        println!("  rewrites={}  → (unchanged)\n", rewrites);
    } else {
        let displays: Vec<_> = produced.iter().map(|t| t.display.as_str()).collect();
        println!("  rewrites={}  → {}\n", rewrites, displays.join(", "));
    }

    // ─── Part B: τ-leap simulation ─────────────────────────────────
    println!("─── Part B: τ-leap simulation (parallel firings per step) ───\n");

    let mut result = petri_net_from_proc(proc, &facts, LAMBDA_PN);

    // Locate the store place (@3) and the capacity-gated transition.
    let store_place_id = find_place_by_label(&result.net, "@3")
        .expect("store place @3 must exist after net construction");
    let cap_transition_id = find_transition_by_label_substring(&result.net, "capacity_ok")
        .expect("warehouse→store transition with capacity_ok guard must exist");

    // Override the SeedFacts-backed capacity guard with a marking-backed
    // closure: the gate closes dynamically when the store fills up.
    install_capacity_guard(&mut result.net, cap_transition_id, store_place_id, STORE_CAPACITY);

    // Seed factory inventory at @1 only (not @3). Overwrites the
    // one-token default placed by petri_net_from_proc.
    let factory_place_id = find_place_by_label(&result.net, "@1")
        .expect("factory place @1 must exist after net construction");
    result
        .net
        .set_initial_tokens(factory_place_id, FACTORY_INVENTORY);
    // Clear any stray seed tokens at @3 (shouldn't exist, defensive).
    result.net.set_initial_tokens(store_place_id, 0);

    let mut rng = StdRng::seed_from_u64(SEED);
    let trace =
        simulate_with_customer_tau_leap(&result.net, store_place_id, cap_transition_id, &mut rng);

    println!("Per-leap inventory trace:\n");
    print_leap_trace(&trace, &result.net);
    println!("\nSummary:\n");

    print_stats(&trace, &result.net);

    println!("\n=== Demo complete ===");
}

/// Build seed facts. Both relations are seeded true for the entire run;
/// dynamic capacity control is done by the guard-closure override
/// installed on the warehouse→store transition after construction.
fn build_facts(certified: bool, capacity_ok: bool) -> SeedFacts {
    let mut facts = SeedFacts::new();
    if certified {
        facts.insert("certified".to_string(), vec![vec!["@Nil".to_string()]]);
    }
    if capacity_ok {
        facts.insert("capacity_ok".to_string(), vec![vec!["@Nil".to_string()]]);
    }
    facts
}
