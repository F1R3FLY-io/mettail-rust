//! Track B — B2: the EMPIRICAL same-CLTS equivalence gate between the OPTIMIZED
//! set-automaton matcher and the NAIVE Knotted-Topoi Appendix-A baseline, run on
//! the live in-memory f1r3node Rho machine.
//!
//! # What this suite is
//!
//! The empirical counterpart of
//! `formal/rocq/advanced_automata/theories/InRhoSameCLTSWeakBisim.v`
//! (`same_clts_weak_bisim`): the optimized (shared, tc-keyed) and sound
//! (per-location) channel schemes are WEAKLY BISIMILAR — every visible `fire`
//! event of one is matched by the other, while the τ-COMM channel schedules
//! between them differ (that is the theorem's entire point: the schemes differ
//! ONLY in erased τ structure). Here the two schemes are the production drivers
//! (`in_rho_match_call_par` / `in_rho_match_all_sites_call_par` /
//! `contextual_match_call_par`) and the quarantined naive Appendix-A emitter
//! (`naive_kt_match_call_par` / `naive_kt_contextual_match_call_par` from the
//! shared `rho_net_pattern_guard` engine,
//! `bench-naive-baseline`), which share the spread + accept ABI BY FUNCTION
//! IDENTITY (`spread_term_par`, `build_accept_send`) and differ only in the
//! matching network between them. The bisimulation's visible agreement is
//! therefore checked as: for the same subject, against the SAME installed
//! σ-receiver program, the observed OUT value MULTISETS are equal — sorted
//! before comparison, because the τ-COMM schedules (and hence the arrival
//! orders) are allowed to differ.
//!
//! # Drive discipline (the B0 admission constraint)
//!
//! `rholang-codegen/tests/rho_net_admission_matrix.rs` proves λ-chains with
//! n ≥ 2 App nodes and nested entries with k ≥ 2 head-matching candidate sites
//! FAIL CLOSED on the optimized locate-all
//! (`AutomatonUnsupported::NestedEntryMultiSite`), so β-chain equivalence is
//! driven PER-STEP at the root redex through `in_rho_match_call_par`, with the
//! naive side restricted to the same single root occurrence (the Appendix-A
//! per-site comprehension instantiated at exactly the root site —
//! `naive_kt_entry_receiver_par` ∥ the one spread). The UNRESTRICTED
//! comprehension (`naive_kt_match_call_par`) fires every head-matching
//! occurrence simultaneously; on λ-chains that is a capability the optimized
//! locate-all fails closed on, and it is pinned separately as a labeled
//! divergent-admission observation, never conflated with the per-step equality.
#![cfg(all(
    feature = "swap-demo-runtime",
    feature = "lambda-demo-runtime",
    feature = "ctx-demo-runtime",
    feature = "bench-naive-baseline"
))]

use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};
// Task #11 (extended 2026-07-26): `CtxDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/ctxdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `ctxdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/ctxdemo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/ctxdemo.rs"]
mod ctxdemo;

// Task #11 (extended 2026-07-26): `LambdaDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/lambdademo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `lambdademo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/lambdademo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/lambdademo.rs"]
mod lambdademo;

// Task #11 (extended 2026-07-26): `SwapDemo` is a DEMONSTRATION grammar — its definition lives
// in `languages/tests/definitions/swapdemo.rs`, not in the `languages` library, so it is
// `#[path]`-included here. The `swapdemo_generated_tests!` wrapper the expansion also defines is
// deliberately NOT invoked: this binary is a consumer, not the definition's designated host
// (`languages/tests/swapdemo.rs` is), so the generated suite stays single-instanced.
#[path = "../../languages/tests/definitions/swapdemo.rs"]
mod swapdemo;

use ctxdemo::CtxDemoLanguage;
use lambdademo::LambdaDemoLanguage;
use mettail_rholang_codegen::{
    compile_in_rho_matching_ruleset, contextual_match_call_par, in_rho_match_all_sites_call_par,
    in_rho_match_call_par, lower_language_def, multi_pattern_receiver_network_par,
    naive_kt_contextual_match_call_par, naive_kt_entry_receiver_par, naive_kt_match_call_par,
    plan_rho_default_backend, reconstruct_language_def, spread_term_par,
    suggest_rejected_rule_dispositions, AutomatonAcceptTarget, AutomatonUnsupported, GroundTerm,
    InRhoMatchingRuleset, NaiveGuardEncoding, RhoCoverageEvidence, RhoDefaultBackendRequirements,
    RhoGuardCoverageEvidence, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    bench_inj_and_read, bench_runtime_with_counters, count_receive_nodes, count_send_nodes,
    par_as_runtime_observation_value, run_normalized_par_for_oracle_and_read_runtime_values,
    BenchWorkloadParams, PlannedRhoBackend,
};
use mettail_runtime::{Language, RuntimeObservationValue};
use swapdemo::SwapDemoLanguage;

/// The shared root-site nonce for every drive in this suite (each run executes
/// on its own isolated in-memory runtime, so a fixed nonce cannot collide).
const SITE: &str = "site0";

/// Plan a demo language's Rho-default backend from its generated
/// `definition_source()` — the same reconstruction every reference firing test
/// performs — and return the planned backend plus the compiled in-Rho matching
/// ruleset (one fingerprint shared by the installed σ-receiver program, the
/// optimized drivers, and the naive emitter: the interface-coherence anchor the
/// equivalence rests on).
fn planned_backend_and_ruleset(
    language: &impl Language,
    what: &str,
) -> (PlannedRhoBackend, InRhoMatchingRuleset) {
    let source = language
        .metadata()
        .definition_source()
        .expect("a generated demo language must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("the demo definition_source must reconstruct as a LanguageDef");
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .unwrap_or_else(|error| panic!("{what} must flip to the Rho backend: {error:?}"));
    let ruleset = compile_in_rho_matching_ruleset(&def);
    assert_eq!(
        ruleset.language_fingerprint,
        plan.definition_fingerprint(),
        "{what}: the compiled ruleset and the planned backend must share ONE fingerprint"
    );
    (PlannedRhoBackend::from_plan(plan), ruleset)
}

fn obs(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}

fn onullary(constructor: &str) -> RuntimeObservationValue {
    obs(constructor, Vec::new())
}

/// Sort an observation multiset into its canonical (debug-render) order. The
/// two matchers' τ-COMM schedules differ, so OUT arrival order differs — the
/// MULTISET is the visible-firing content the same-CLTS claim constrains.
fn sorted_multiset(mut values: Vec<RuntimeObservationValue>) -> Vec<RuntimeObservationValue> {
    values.sort_by_key(|value| format!("{value:?}"));
    values
}

/// The observation a `GroundTerm` subject decodes back to on OUT (the decoder
/// counterpart of `reflect_ground_term_par` over a positional tree).
fn ground_to_observation(term: &GroundTerm) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: term.constructor.clone(),
        children: term.children.iter().map(ground_to_observation).collect(),
    }
}

/// Rebuild an observed OUT value into the `GroundTerm` subject of the NEXT
/// β-chain step (the per-step drive is fed by what the reducer actually landed,
/// not by a host-side prediction). The β-chain reducts are pure positional
/// constructor terms, so every other observation variant is a hard failure.
fn observation_to_ground(value: &RuntimeObservationValue) -> GroundTerm {
    match value {
        RuntimeObservationValue::Term { constructor, children } => GroundTerm::new(
            constructor.clone(),
            children.iter().map(observation_to_ground).collect(),
        ),
        other => panic!("a β-chain reduct must be a pure constructor term, got {other:?}"),
    }
}

/// The accept channel of the compiled entry at view index `entry` — the
/// `InRhoMatchingRuleset` invariant lookup (`accept_channels` is built in
/// lockstep with the compiled entries), mirrored here for the root-restricted
/// naive drive and the ablation probes.
fn entry_accept_channel(ruleset: &InRhoMatchingRuleset, entry: usize) -> String {
    let pid = ruleset.automaton.view().entry_id(entry);
    ruleset
        .accept_channels
        .iter()
        .find(|(entry_pid, _)| *entry_pid == pid)
        .map(|(_, channel)| channel.clone())
        .expect("every compiled automaton entry has an accept channel")
}

// ── SwapDemo subjects ──────────────────────────────────────────────────────────

fn g_swap(a: &str, b: &str) -> GroundTerm {
    GroundTerm::new("Swap", vec![GroundTerm::nullary(a), GroundTerm::nullary(b)])
}

fn opair(a: RuntimeObservationValue, b: RuntimeObservationValue) -> RuntimeObservationValue {
    obs("Pair", vec![a, b])
}

/// The four DISTINCT Swap redexes the comb subjects draw from, paired with
/// their contracta (`Swap(a, b) ~> Pair(b, a)`), so every comb width yields a
/// multiset of pairwise-distinct expected values — the strongest discriminating
/// shape SwapDemo's two leaves allow.
const COMB_LEAVES: [(&str, &str); 4] = [("A", "B"), ("B", "A"), ("A", "A"), ("B", "B")];

/// A wide flat multi-redex comb: a right-leaning INERT `Pair` spine carrying
/// `m` distinct `Swap` redexes (`Pair` is not a rule LHS root, so exactly the
/// `m` Swaps are candidate sites), plus the directly-computed expected
/// contracta multiset.
fn swap_comb(m: usize) -> (GroundTerm, Vec<RuntimeObservationValue>) {
    assert!((1..=COMB_LEAVES.len()).contains(&m), "the comb widths are 1..=4");
    let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(m);
    for (a, b) in &COMB_LEAVES[..m] {
        expected.push(opair(onullary(b), onullary(a)));
    }
    let (last_a, last_b) = COMB_LEAVES[m - 1];
    let mut subject = g_swap(last_a, last_b);
    for (a, b) in COMB_LEAVES[..m - 1].iter().rev() {
        subject = GroundTerm::new("Pair", vec![g_swap(a, b), subject]);
    }
    (subject, expected)
}

// ── LambdaDemo subjects (reflected form, as the M-reflect spread carries them) ─

/// The identity function `λ.x` in reflected de-Bruijn form:
/// `^lambda(^bound(Z))`.
fn identity_lambda() -> GroundTerm {
    GroundTerm::new(
        LAMBDA_REFLECT_LABEL,
        vec![GroundTerm::new(
            BOUND_VAR_REFLECT_LABEL,
            vec![GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL)],
        )],
    )
}

/// The `App(Lam(^x. x), ·)` chain spine of depth `n` (reflected):
/// `App(^lambda(^bound Z), App(^lambda(^bound Z), … App(^lambda(^bound Z), A)))`.
/// Each root β-step substitutes the argument for the identity's bound variable,
/// so the reduct IS the remaining chain — the whole spine reduces in exactly
/// `n` sequential root steps to the terminal `A`.
fn lambda_chain(n: usize) -> GroundTerm {
    let mut term = GroundTerm::nullary("A");
    for _ in 0..n {
        term = GroundTerm::new("App", vec![identity_lambda(), term]);
    }
    term
}

// ═══════════════════════════════════════════════════════════════════════════════
// 1. Fired-set multiset equality, SwapDemo (root / nested / multi-redex comb)
// ═══════════════════════════════════════════════════════════════════════════════

/// (1a) ROOT redex `Swap(A, B)`: the optimized single-root drive
/// (`in_rho_match_call_par`) and the naive Appendix-A call
/// (`naive_kt_match_call_par`) against the SAME installed σ-receiver program
/// observe the same single firing `Pair(B, A)`. `Swap(A, B) ≠ Pair(B, A)`, so
/// the agreement is non-vacuous: both networks matched, captured σ, and fired
/// the shared σ-receiver in Rho.
#[tokio::test]
async fn fired_sets_agree_for_the_root_swap_redex() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let subject = g_swap("A", "B");

    let optimized_call = in_rho_match_call_par(&ruleset, &subject, SITE, "OUT")
        .expect("the optimized single-root drive serializes Swap(A, B)");
    let optimized = backend
        .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
        .await
        .expect("the optimized root drive executes on the Rho runtime");

    let (naive_call, installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("the naive Appendix-A call admits the flat Swap ruleset");
    assert_eq!(installed, 1, "one head-Swap position ⇒ one installed naive receiver");
    let naive = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the naive drive executes on the Rho runtime");

    let optimized_values = sorted_multiset(optimized.values);
    let naive_values = sorted_multiset(naive.values);
    assert_eq!(
        optimized_values, naive_values,
        "same-CLTS gate: the two matchers' observed OUT multisets must agree at the root redex"
    );
    assert_eq!(
        optimized_values,
        vec![opair(onullary("B"), onullary("A"))],
        "both matchers fired the SwapStep σ-receiver exactly once → Pair(B, A)"
    );
}

/// (1b) ONE NESTED occurrence `Pair(Swap(A, B), B)`: the optimized locate-all
/// drive (`in_rho_match_all_sites_call_par`, 1 located site) and the naive
/// per-site comprehension (1 installed receiver at `Pair.0`) observe the same
/// single firing `Pair(B, A)` — the nested-position half of the visible-firing
/// agreement.
#[tokio::test]
async fn fired_sets_agree_for_a_nested_swap_occurrence() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let subject = GroundTerm::new("Pair", vec![g_swap("A", "B"), GroundTerm::nullary("B")]);

    let (optimized_call, sites) = in_rho_match_all_sites_call_par(&ruleset, &subject, SITE, "OUT")
        .expect("the flat Swap ruleset locates the nested redex");
    assert_eq!(sites, 1, "exactly one head-Swap position (at Pair.0)");
    let optimized = backend
        .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
        .await
        .expect("the optimized locate-all drive executes on the Rho runtime");

    let (naive_call, installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("the naive Appendix-A call admits the flat Swap ruleset");
    assert_eq!(installed, 1, "the naive comprehension installs at the same one position");
    let naive = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the naive drive executes on the Rho runtime");

    let optimized_values = sorted_multiset(optimized.values);
    let naive_values = sorted_multiset(naive.values);
    assert_eq!(
        optimized_values, naive_values,
        "same-CLTS gate: the observed OUT multisets must agree at the nested occurrence"
    );
    assert_eq!(
        optimized_values,
        vec![opair(onullary("B"), onullary("A"))],
        "the nested Swap(A, B) fired once on both sides → Pair(B, A)"
    );
}

/// (1c) MULTI-REDEX combs, m ∈ {2, 3, 4}: the optimized locate-all co-installs
/// one shared network per located site; the naive comprehension installs one
/// per-rule receiver per site. All m redexes fire on BOTH sides, and the
/// observed OUT multisets are equal — sorted before comparison, because the
/// parallel accepts land in nondeterministic (and generally different) order:
/// exactly the τ-schedule freedom `same_clts_weak_bisim` erases. The multiset
/// is also pinned to the directly-computed contracta, so the agreement cannot
/// be a shared miss.
#[tokio::test]
async fn fired_sets_agree_for_multi_redex_combs() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");

    for m in 2..=4usize {
        let (subject, expected) = swap_comb(m);

        let (optimized_call, sites) =
            in_rho_match_all_sites_call_par(&ruleset, &subject, SITE, "OUT")
                .expect("the flat Swap ruleset co-installs at every comb site");
        assert_eq!(sites, m, "the comb of {m} Swaps locates exactly {m} sites");
        let optimized = backend
            .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
            .await
            .expect("the optimized locate-all drive executes on the Rho runtime");

        let (naive_call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            SITE,
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the naive Appendix-A call admits the flat comb");
        assert_eq!(installed, m, "the naive comprehension installs at the same {m} positions");
        let naive = backend
            .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
            .await
            .expect("the naive drive executes on the Rho runtime");

        let optimized_values = sorted_multiset(optimized.values);
        let naive_values = sorted_multiset(naive.values);
        assert_eq!(
            optimized_values, naive_values,
            "same-CLTS gate: the m = {m} comb's observed OUT multisets must agree"
        );
        assert_eq!(
            optimized_values,
            sorted_multiset(expected),
            "the m = {m} comb's agreed multiset is exactly the per-site contracta"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2. β-chain per-step equality, LambdaDemo (root-redex drive, B0 constraint)
// ═══════════════════════════════════════════════════════════════════════════════

/// The root-restricted NAIVE β drive: the Appendix-A comprehension instantiated
/// at EXACTLY the root occurrence — the entry's per-site receiver at the root
/// site ∥ the ONE spread of the whole subject. This is the naive counterpart of
/// the optimized single-root `in_rho_match_call_par` (which likewise installs
/// only at the root site): the B0 admission matrix proves λ-chains n ≥ 2 fail
/// closed on the optimized locate-all, so the CHAIN equivalence is driven
/// per-step at the root redex on BOTH sides. The unrestricted
/// `naive_kt_match_call_par` would install at every head-`App` position of the
/// remaining chain and fire them all simultaneously — a capability divergence
/// pinned separately in
/// [`naive_full_comprehension_fires_the_whole_lambda_spine`], not a per-step
/// root drive.
fn naive_root_beta_call(
    ruleset: &InRhoMatchingRuleset,
    subject: &GroundTerm,
) -> models::rhoapi::Par {
    let view = ruleset.automaton.view();
    let accept_channel = entry_accept_channel(ruleset, 0);
    let receiver = naive_kt_entry_receiver_par(
        &view,
        0,
        subject,
        SITE,
        &accept_channel,
        "OUT",
        &ruleset.language_fingerprint,
        NaiveGuardEncoding::PatternGuard,
    )
    .expect("the β entry App(^lambda(fun), arg) emits a naive receiver");
    receiver.append(spread_term_par(subject, &ruleset.language_fingerprint, SITE))
}

/// (2) β-CHAIN PER-STEP equality, n ∈ {1, 2, 3, 4}: at every step both matchers
/// are pointed at the ROOT redex of the remaining `App(Lam(^x. x), ·)` spine —
/// optimized via `in_rho_match_call_par`, naive via the root-restricted
/// Appendix-A receiver ∥ spread — and both must land the SAME single reduct on
/// OUT: the matched network fires the installed `Beta` SEED σ-receiver, whose
/// `^subst(⟦Z⟧, arg, body, @OUT)` send drives the installed de-Bruijn subst TRS
/// to `arg` (the identity body `^bound Z` compares `Eq` at depth `Z`, and
/// `shiftk(Z, arg) = arg`). The NEXT step's subject is rebuilt from the
/// OBSERVED reduct (not a host-side prediction), each step is ALSO anchored to
/// the ground-truth remaining chain, and after n steps both sides sit at the
/// terminal normal form `A`.
#[tokio::test]
async fn beta_chain_per_step_root_drives_agree_to_the_same_normal_form() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&LambdaDemoLanguage, "LambdaDemo");
    assert_eq!(
        ruleset.automaton.view().entry_count(),
        1,
        "LambdaDemo compiles exactly the Beta entry (the workload precondition)"
    );

    for n in 1..=4usize {
        let mut subject = lambda_chain(n);
        for step in 0..n {
            let optimized_call = in_rho_match_call_par(&ruleset, &subject, SITE, "OUT")
                .expect("the optimized single-root drive serializes the β redex");
            let optimized = backend
                .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
                .await
                .expect("the optimized root β step executes on the Rho runtime");
            assert_eq!(
                optimized.observed_count(),
                1,
                "chain n = {n}, step {step}: the optimized root drive fires exactly once (got {:?})",
                optimized.values
            );

            let naive_call = naive_root_beta_call(&ruleset, &subject);
            let naive = backend
                .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
                .await
                .expect("the naive root β step executes on the Rho runtime");
            assert_eq!(
                naive.observed_count(),
                1,
                "chain n = {n}, step {step}: the naive root drive fires exactly once (got {:?})",
                naive.values
            );

            assert_eq!(
                optimized.values[0], naive.values[0],
                "same-CLTS gate: chain n = {n}, step {step} — the per-step β reducts must agree"
            );
            // Ground-truth anchor: the agreed reduct IS the remaining chain (the
            // subst TRS substituted the identity body, not some shared artifact).
            assert_eq!(
                optimized.values[0],
                ground_to_observation(&lambda_chain(n - step - 1)),
                "chain n = {n}, step {step}: the agreed reduct is the remaining chain"
            );

            // Feed the NEXT step from what the reducer actually landed.
            subject = observation_to_ground(&optimized.values[0]);
        }
        assert_eq!(
            ground_to_observation(&subject),
            onullary("A"),
            "after {n} root steps both matchers reached the terminal normal form A"
        );
    }
}

/// DIVERGENT-ADMISSION capability case for λ-chains (labeled as such — NOT an
/// equivalence violation): the optimized locate-all FAILS CLOSED on every chain
/// n ≥ 2 (`NestedEntryMultiSite`, the B0 admission matrix), while the naive
/// Appendix-A comprehension admits the chain and fires EXACTLY the true redex
/// occurrence set — every `App(Lam(^x. x), ·)` spine node simultaneously,
/// landing the multiset { remaining-chain₀, …, remaining-chain₍ₙ₋₁₎ }. The
/// per-site channel reads are disjoint (each receiver descends only its own
/// site's `loc:`/`cap:` derivation and the entry's internal `^lambda` op is no
/// entry's root op), so nothing starves; the fired set is asserted against the
/// directly-computed expected multiset.
#[tokio::test]
async fn naive_full_comprehension_fires_the_whole_lambda_spine() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&LambdaDemoLanguage, "LambdaDemo");

    for n in 2..=4usize {
        let subject = lambda_chain(n);
        assert_eq!(
            in_rho_match_all_sites_call_par(&ruleset, &subject, SITE, "OUT"),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "the optimized locate-all fails closed on the n = {n} λ-chain (B0)"
        );

        let (naive_call, installed) = naive_kt_match_call_par(
            &ruleset,
            &subject,
            SITE,
            "OUT",
            NaiveGuardEncoding::PatternGuard,
        )
        .expect("the naive comprehension admits the λ-chain (^lambda is no entry's root op)");
        assert_eq!(installed, n, "one naive receiver per head-App spine position");
        let naive = backend
            .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
            .await
            .expect("the naive full-spine drive executes on the Rho runtime");

        let mut expected: Vec<RuntimeObservationValue> = Vec::with_capacity(n);
        for depth in 0..n {
            expected.push(ground_to_observation(&lambda_chain(depth)));
        }
        assert_eq!(
            sorted_multiset(naive.values),
            sorted_multiset(expected),
            "the naive comprehension fired the n = {n} spine's TRUE redex set — every \
             App occurrence's reduct is its remaining chain"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// 3. Contextual equality, CtxDemo
// ═══════════════════════════════════════════════════════════════════════════════

/// (3) CONTEXTUAL agreement on `Wrap(Swap(A, B))`: the optimized
/// `contextual_match_call_par` and the naive
/// `naive_kt_contextual_match_call_par` locate the hole's premise redex, route
/// the reduced hole through the SHARED bridge to the installed `WrapCong`
/// join's premise channel, and both land the reassembled context
/// `Wrap(Pair(B, A))` on OUT — equal observed multisets against the same
/// installed program (Flip σ-receiver ∥ WrapCong join).
#[tokio::test]
async fn contextual_fired_sets_agree_for_wrap_swap() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&CtxDemoLanguage, "CtxDemo");
    let subject = GroundTerm::new("Wrap", vec![g_swap("A", "B")]);

    let optimized_call = contextual_match_call_par(&ruleset, &subject, SITE, "OUT")
        .expect("the optimized contextual driver admits Wrap(Swap(A, B))");
    let optimized = backend
        .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
        .await
        .expect("the optimized contextual drive executes on the Rho runtime");

    let naive_call = naive_kt_contextual_match_call_par(
        &ruleset,
        &subject,
        SITE,
        "OUT",
        NaiveGuardEncoding::PatternGuard,
    )
    .expect("the naive contextual driver admits Wrap(Swap(A, B))");
    let naive = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the naive contextual drive executes on the Rho runtime");

    let optimized_values = sorted_multiset(optimized.values);
    let naive_values = sorted_multiset(naive.values);
    assert_eq!(
        optimized_values, naive_values,
        "same-CLTS gate: the contextual observed OUT multisets must agree"
    );
    assert_eq!(
        optimized_values,
        vec![obs("Wrap", vec![opair(onullary("B"), onullary("A"))])],
        "both drivers reassembled the reduced context Wrap(Pair(B, A)) via the shared join"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 4. Zero-firing subjects (a normal form fires NOTHING on both sides)
// ═══════════════════════════════════════════════════════════════════════════════

/// (4) A NORMAL-FORM subject (`Pair(A, B)` — `Pair` is not a rule LHS root):
/// the optimized locate-all admits with ZERO located sites (its call is the
/// bare spread), the naive comprehension admits with ZERO installed receivers
/// (its call is likewise the bare spread), and BOTH runs observe an EMPTY OUT —
/// no receiver fires, no error is raised. The zero-firing side of the
/// visible-multiset agreement.
#[tokio::test]
async fn zero_firing_normal_form_observes_empty_out_on_both_sides() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let subject = GroundTerm::new("Pair", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]);

    let (optimized_call, sites) = in_rho_match_all_sites_call_par(&ruleset, &subject, SITE, "OUT")
        .expect("a normal form is a valid locate-all no-op, not an error");
    assert_eq!(sites, 0, "Pair(A, B) has no head-Swap position");
    let optimized = backend
        .run_rho_net_with_call_and_observe_runtime_values(&optimized_call, "OUT")
        .await
        .expect("the optimized zero-firing drive executes on the Rho runtime");
    assert_eq!(
        optimized.observed_count(),
        0,
        "the optimized side fires nothing on a normal form (got {:?})",
        optimized.values
    );

    let (naive_call, installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("a normal form is a valid naive no-op, not an error");
    assert_eq!(installed, 0, "the naive comprehension installs no receiver on a normal form");
    let naive = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the naive zero-firing drive executes on the Rho runtime");
    assert_eq!(
        naive.observed_count(),
        0,
        "the naive side fires nothing on a normal form (got {:?})",
        naive.values
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 5. The naive σ comes from the SPREAD (the corrupted-σ analogue, by ablation)
// ═══════════════════════════════════════════════════════════════════════════════

/// (5) TWO ABLATIONS on `Swap(A, B)` — the naive analogue of
/// `m_reflect_sigma_is_produced_by_the_automaton_not_the_report`
/// (`rho_net_equivalence.rs`): (i) the naive RECEIVER WITHOUT the spread (the
/// emitter fuses receivers ∥ spread in `naive_kt_match_call_par`, so the
/// receivers-only side is built via the entry emitter + manual composition, as
/// the module's own tests do) observes an EMPTY OUT — the receiver's head-tag
/// demand starves with no spread to read; (ii) the SPREAD WITHOUT receivers
/// observes an EMPTY OUT — the spread's `loc:`/`cap:` publications reach no
/// consumer and the installed σ-receiver never sees an accept. Together with
/// test (1a), which observes `Pair(B, A)` when BOTH halves are present, this
/// proves the naive σ is derived from the SUBJECT SPREAD through the naive
/// receivers — never from any host computation.
#[tokio::test]
async fn naive_sigma_is_derived_from_the_spread_not_the_host() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let subject = g_swap("A", "B");
    let accept_channel = entry_accept_channel(&ruleset, 0);

    // (i) Receivers WITHOUT the spread: the persistent per-site receiver alone.
    let view = ruleset.automaton.view();
    let receiver_only = naive_kt_entry_receiver_par(
        &view,
        0,
        &subject,
        SITE,
        &accept_channel,
        "OUT",
        &ruleset.language_fingerprint,
        NaiveGuardEncoding::PatternGuard,
    )
    .expect("the flat Swap entry emits a naive receiver");
    assert!(
        !receiver_only.receives.is_empty(),
        "the ablation installs a real receiver (it must starve, not be absent)"
    );
    let no_spread = backend
        .run_rho_net_with_call_and_observe_runtime_values(&receiver_only, "OUT")
        .await
        .expect("the receiver-only ablation executes on the Rho runtime");
    assert_eq!(
        no_spread.observed_count(),
        0,
        "without the spread the naive receiver has no tag to consume — empty OUT (got {:?})",
        no_spread.values
    );

    // (ii) The spread WITHOUT receivers: the subject's publications alone.
    let spread_only = spread_term_par(&subject, &ruleset.language_fingerprint, SITE);
    assert!(
        !spread_only.sends.is_empty(),
        "the ablation publishes a real spread (it must go unread, not be absent)"
    );
    let no_receivers = backend
        .run_rho_net_with_call_and_observe_runtime_values(&spread_only, "OUT")
        .await
        .expect("the spread-only ablation executes on the Rho runtime");
    assert_eq!(
        no_receivers.observed_count(),
        0,
        "without the naive receivers the spread reaches no consumer — empty OUT (got {:?})",
        no_receivers.values
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 6. Determinism of the naive multiset (schedule-independence of the content)
// ═══════════════════════════════════════════════════════════════════════════════

/// (6) DETERMINISM: two independent runs of test (1c)'s widest naive drive
/// (the m = 4 comb) land byte-identical SORTED observation multisets. The
/// τ-COMM schedule inside each run is free (arrival ORDER may differ), but the
/// visible-firing CONTENT is a function of the subject — the empirical
/// counterpart of the bisimulation's schedule-erasure.
#[tokio::test]
async fn naive_comb_multiset_is_deterministic_across_runs() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let (subject, expected) = swap_comb(4);

    let (naive_call, installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("the naive Appendix-A call admits the m = 4 comb");
    assert_eq!(installed, 4, "four head-Swap positions");

    let first = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the first naive run executes on the Rho runtime");
    let second = backend
        .run_rho_net_with_call_and_observe_runtime_values(&naive_call, "OUT")
        .await
        .expect("the second naive run executes on the Rho runtime");

    let first_sorted = sorted_multiset(first.values);
    let second_sorted = sorted_multiset(second.values);
    assert_eq!(
        first_sorted, second_sorted,
        "the sorted naive observation multisets must be identical across runs"
    );
    assert_eq!(
        format!("{first_sorted:?}"),
        format!("{second_sorted:?}"),
        "…and byte-identical under the canonical rendering"
    );
    assert_eq!(
        first_sorted,
        sorted_multiset(expected),
        "the deterministic multiset is exactly the comb's per-site contracta"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 7. Divergent-admission capability case (nested entry, k = 2 candidate sites)
// ═══════════════════════════════════════════════════════════════════════════════

/// A σ-echo observer for a direct-construction accept (mirrors
/// `rho_net_equivalence.rs`): `for(y_0,…,y_{k-1}, o <- accept){ o!(y_0) | … }`
/// forwards each σ slot to the accept's dynamic out channel. ONE-SHOT — the
/// two-accept case below appends two copies, one per expected firing.
fn sigma_echo_receiver(accept_channel: &str, arity: usize) -> models::rhoapi::Par {
    use models::create_bit_vector;
    use models::rhoapi::{Par, ReceiveBind};
    use models::rust::utils::{
        new_boundvar_par, new_freevar_par, new_gstring_par, new_receive_par, new_send_par,
    };

    let mut body = Par::default();
    for i in 0..arity {
        let yi = arity - i; // y_i = BoundVar(arity - i); o = BoundVar(0).
        let send = new_send_par(
            new_boundvar_par(0, create_bit_vector(&[0]), false),
            vec![new_boundvar_par(yi as i32, create_bit_vector(&[yi]), false)],
            false,
            create_bit_vector(&[0, yi]),
            false,
            create_bit_vector(&[0, yi]),
            false,
        );
        body = body.append(send);
    }
    if arity > 0 {
        body.locally_free = create_bit_vector(&(0..=arity).collect::<Vec<_>>());
    }
    new_receive_par(
        vec![ReceiveBind {
            patterns: (0..arity + 1)
                .map(|i| new_freevar_par(i as i32, Vec::new()))
                .collect(),
            source: Some(new_gstring_par(accept_channel.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: (arity + 1) as i32,
        }],
        body,
        false,
        false,
        (arity + 1) as i32,
        Vec::new(),
        false,
        Vec::new(),
        false,
    )
}

/// D-E5's deterministic COMM/accounting gate. Two alpha-renamed nested entries
/// share one slotted state and one matcher network, while retaining their two
/// independent accept continuations. The exact counter vector is the production
/// successor receipt. D3 charges one token per evaluated send/receive prefix;
/// the counting-space vector separately counts RSpace rendezvous that commit.
#[tokio::test]
async fn alpha_shared_nested_network_has_an_exact_comm_profile() {
    mettail_runtime::clear_var_cache();
    let shape = |name: &str| {
        Pattern::app("f".to_string(), vec![Pattern::app("g".to_string(), vec![Pattern::var(name)])])
    };
    let automaton = SetAutomaton::compile_structural([
        (PatternId(0), shape("x")),
        (PatternId(1), shape("alpha")),
    ])
    .expect("alpha-renamed nested states compile");
    assert_eq!(automaton.view().entry_root_state(0), automaton.view().entry_root_state(1));

    let targets = [
        AutomatonAcceptTarget {
            pattern: PatternId(0),
            accept_channel: "sa:d-e5-one".to_string(),
            out_channel: "OUT".to_string(),
        },
        AutomatonAcceptTarget {
            pattern: PatternId(1),
            accept_channel: "sa:d-e5-two".to_string(),
            out_channel: "OUT".to_string(),
        },
    ];
    let subject = GroundTerm::new("f", vec![GroundTerm::new("g", vec![GroundTerm::nullary("A")])]);
    let network = multi_pattern_receiver_network_par(
        &automaton.view(),
        &subject,
        SITE,
        &targets,
        "d-e5-fingerprint",
    )
    .expect("the shared nested network serializes");
    let program = sigma_echo_receiver("sa:d-e5-one", 1)
        .append(sigma_echo_receiver("sa:d-e5-two", 1))
        .append(network)
        .append(spread_term_par(&subject, "d-e5-fingerprint", SITE));
    let static_sends = count_send_nodes(&program);
    let static_receives = count_receive_nodes(&program);
    assert_eq!((static_sends, static_receives), (13, 7));

    let (mut runtime, comm, matches) = bench_runtime_with_counters(Vec::new(), "OUT")
        .await
        .expect("counting runtime starts");
    let result = bench_inj_and_read(
        &mut runtime,
        &program,
        "OUT",
        BenchWorkloadParams {
            name: "d_e5_alpha_shared".to_string(),
            matcher: "sa".to_string(),
            encoding: "-".to_string(),
            n: 2,
            rep: 0,
        },
        &comm,
        &matches,
    )
    .await
    .expect("the shared nested alpha network executes");
    let observed = result
        .observed
        .iter()
        .map(|par| {
            par_as_runtime_observation_value(par)
                .expect("every shared-alpha OUT datum is a closed runtime value")
        })
        .collect::<Vec<_>>();
    assert_eq!(sorted_multiset(observed), vec![onullary("A"), onullary("A")]);
    assert_eq!(result.program_encoded_len, 2_318);
    assert_eq!(result.program_receiver_count, static_receives);
    assert_eq!(result.consumed_cost_units, 20);
    assert_eq!(result.consumed_cost_units as usize, static_sends + static_receives);
    assert_eq!(result.comm.matching_tau, 5);
    assert_eq!(result.comm.firing_visible, 2);
    assert_eq!(result.comm.subst_tau, 0);
    assert_eq!(result.comm.respread_tau, 0);
    assert_eq!(result.comm.drive_tau, 0);
    assert_eq!(result.comm.ac_carrier, 0);
    assert_eq!(result.comm.pathmap_index, 0);
    assert_eq!(result.comm.contextual_plumbing, 0);
    assert_eq!(result.comm.observation, 0);
    assert_eq!(result.comm.other, 0);
    assert_eq!(result.comm.join_arity_gt1, 0);
    assert!(result.comm.unknown_channel_samples.is_empty());
    assert_eq!(result.matches.attempts, 7);
    assert_eq!(result.matches.successes, 7);
}

/// (7) DIVERGENT-ADMISSION CAPABILITY CASE — labeled as such: this is NOT an
/// equivalence violation, it is the admission-envelope difference the B0 matrix
/// pins. A NESTED entry `f(g(x))` over a subject with k = 2 head-`f` candidate
/// sites (`Pair(f(g(A)), f(g(B)))`, direct construction — no demo language,
/// admission-matrix style): the optimized locate-all FAILS CLOSED
/// (`NestedEntryMultiSite` — two co-installed nested networks could contend for
/// one `loc:` head-tag send), while the naive comprehension ADMITS (its
/// per-site receivers read disjoint site-derived channels and `g` is no entry's
/// root op) and fires EXACTLY the true redex set: σ[x] ∈ {A, B}, observed via
/// two one-shot σ-echoes and asserted against the directly-computed expected
/// multiset. The same-CLTS claim is about agreement WHERE BOTH ADMIT; where the
/// optimized side fails closed it defers (to the σ-replay path in production),
/// and the naive side demonstrates the redex set that a matcher CAN fire here.
#[tokio::test]
async fn divergent_admission_nested_two_sites_naive_fires_the_true_redex_set() {
    mettail_runtime::clear_var_cache();

    // Direct construction (admission-matrix style): the nested f(g(x)) entry.
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app("f".to_string(), vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])]),
    )])
    .expect("f(g(x)) compiles to a positional automaton");
    let ruleset = InRhoMatchingRuleset {
        automaton,
        accept_channels: vec![(PatternId(0), "sa:fg".to_string())],
        language_fingerprint: "fp".to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    };
    let fg = |leaf: &str| {
        GroundTerm::new("f", vec![GroundTerm::new("g", vec![GroundTerm::nullary(leaf)])])
    };
    let subject = GroundTerm::new("Pair", vec![fg("A"), fg("B")]);

    // The OPTIMIZED locate-all fails closed on k = 2 nested candidate sites.
    assert_eq!(
        in_rho_match_all_sites_call_par(&ruleset, &subject, SITE, "OUT"),
        Err(AutomatonUnsupported::NestedEntryMultiSite),
        "the optimized locate-all must fail closed on two nested candidate sites (B0)"
    );

    // The NAIVE comprehension admits and fires both true redexes.
    let (naive_call, installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("the naive comprehension admits the nested two-site subject");
    assert_eq!(installed, 2, "one naive receiver per head-f position");

    // Two one-shot σ-echoes (k = 1 capture each) forward each accept's σ[x] to OUT.
    let program = sigma_echo_receiver("sa:fg", 1)
        .append(sigma_echo_receiver("sa:fg", 1))
        .append(naive_call);
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the naive two-site drive executes on the Rho runtime");

    assert_eq!(
        sorted_multiset(observed),
        vec![onullary("A"), onullary("B")],
        "the naive comprehension fired EXACTLY the true redex set: σ[x] ∈ {{A, B}}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 8. ConsumeTest encoding spot-check (single-candidate only)
// ═══════════════════════════════════════════════════════════════════════════════

/// (8) The PAPER-LITERAL `ConsumeTest` encoding, SINGLE-CANDIDATE spot-check:
/// `Swap(A, B)` driven through `naive_kt_match_call_par` under
/// `NaiveGuardEncoding::ConsumeTest` observes the SAME OUT as `PatternGuard`
/// (`Pair(B, A)`). SINGLE-CANDIDATE ONLY, by design: `ConsumeTest` binds each
/// head tag FREE and tests it in a `Match` whose else-arm republishes only the
/// FAILING receive's tag — the tags consumed by EARLIER receives of the same
/// chain stay held by their continuations, so any OTHER candidate demanding one
/// of them would starve (the partial-fire hazard on the encoding's rustdoc).
/// The `OverlappingTagDemand` gate excludes cross-RULE contention statically,
/// and B2 additionally restricts the encoding to single-candidate SUBJECTS so
/// the hazard regime (several candidate consumers racing one site's tags) is
/// excluded outright rather than exercised; the multi-candidate regimes above
/// all run `PatternGuard`, whose reject path never consumes.
#[tokio::test]
async fn consume_test_encoding_agrees_on_the_single_candidate_swap() {
    mettail_runtime::clear_var_cache();
    let (backend, ruleset) = planned_backend_and_ruleset(&SwapDemoLanguage, "SwapDemo");
    let subject = g_swap("A", "B");

    let (guard_call, guard_installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::PatternGuard)
            .expect("the PatternGuard call admits Swap(A, B)");
    let (consume_call, consume_installed) =
        naive_kt_match_call_par(&ruleset, &subject, SITE, "OUT", NaiveGuardEncoding::ConsumeTest)
            .expect("the ConsumeTest call admits Swap(A, B)");
    assert_eq!(guard_installed, 1, "one candidate site under PatternGuard");
    assert_eq!(consume_installed, 1, "one candidate site under ConsumeTest");

    let guard = backend
        .run_rho_net_with_call_and_observe_runtime_values(&guard_call, "OUT")
        .await
        .expect("the PatternGuard drive executes on the Rho runtime");
    let consume = backend
        .run_rho_net_with_call_and_observe_runtime_values(&consume_call, "OUT")
        .await
        .expect("the ConsumeTest drive executes on the Rho runtime");

    let guard_values = sorted_multiset(guard.values);
    let consume_values = sorted_multiset(consume.values);
    assert_eq!(
        consume_values, guard_values,
        "the two naive guard encodings must observe the same OUT on a single candidate"
    );
    assert_eq!(
        consume_values,
        vec![opair(onullary("B"), onullary("A"))],
        "ConsumeTest fired the SwapStep σ-receiver → Pair(B, A)"
    );
}
