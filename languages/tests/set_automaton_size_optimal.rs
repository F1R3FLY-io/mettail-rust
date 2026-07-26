//! Regression lock: the in-Rho set automaton is SIZE-OPTIMAL, so adaptive-`L`
//! (Stage 4 task #17 — a size-optimal *inspection order*) is UNNECESSARY in this
//! representation and correctly stays plan-deferred. This test converts that
//! finding from a claim into a locked invariant; do not delete without
//! re-deriving the measurement.
//!
//! ## Why this proves adaptive-`L` is a no-op here
//!
//! The `[optimal]` paper's `~n²+n → ~2n` state-shrinking that an adaptive
//! greedy-discrimination inspection order `L` buys applies to the Bouwman–Erkens
//! *set automaton* whose states are *sets of match goals* (partial-match
//! configurations). There, the ORDER in which positions are inspected multiplies
//! the number of distinct configuration-states, so a naive/lexicographic `L` is
//! worst-case quadratic and adaptive-`L` is what recovers linear size.
//!
//! This campaign's `dovetail::set_automaton::SetAutomaton` is NOT that object. Its
//! states are *interned sub-patterns* (`PatternState::Var | App { op, [StateId] }`,
//! built by `PatternCompiler::intern`): the O1/O3 channel-naming quotient `tc(K)`
//! that the FV theorem `TcChannelNamingQuotient` proves is the UNIQUE coarsest-sound
//! naming (`tc_sound` = O3, `tc_injective`, `tc_is_the_op_quotient`; obligation viii,
//! `formal/rocq/advanced_automata/theories/TcChannelNamingQuotient.v`). Hence
//! `state_count` equals the number of DISTINCT SUBTERMS in the LHS set — bounded by
//! the raw pattern-node count and INDEPENDENT of the inspection order `L`. There are
//! no partial-match configuration-states for any `L` to multiply, so the
//! "size-optimal automaton" that task #17 targets is ALREADY achieved by the
//! interning quotient itself: there is no super-linear size for adaptive-`L` to shrink.
//!
//! Swapping `L` later is provably safe because it stays observationally invisible:
//! the SOUND (runtime-location-keyed) and OPTIMAL (interned-`tc(K)`-keyed) channel
//! schemes induce the SAME CLTS — the `sa:`/`eq:` matching COMMs erase to `τ`. This
//! is the `rem:nonopt` claim (asserted in `knotted-topoi.tex`), discharged
//! zero-admission by `InRhoSameCLTSWeakBisim` (obligation iii,
//! `formal/rocq/advanced_automata/theories/InRhoSameCLTSWeakBisim.v`:
//! `optimal_visible_equals_sound` + `same_clts_weak_bisim`).
//!
//! ## What is locked
//!
//! 1. `per_language_in_rho_automaton_is_size_optimal` — for every bundled language:
//!    `state_count ≤ raw_pattern_nodes` (the interning quotient never grows the DAG)
//!    AND `state_count ≤ pinned_bound` (no absolute bloat) AND
//!    `state_count ≤ 1.5·entry_count + 8` (near-linear; the measured slope is ≈1.05).
//! 2. `diagonal_discrimination_set_is_linear_not_quadratic` — the textbook Θ(n²)
//!    discrimination worst case (the "diagonal": `n` patterns over an `n`-ary `g`, a
//!    nullary sentinel walking the `n` positions; Sekar–Ramesh–Ramakrishnan 1995)
//!    interns to EXACTLY `2n+1` states (`2` at the degenerate `n=1`) — LINEAR, no
//!    quadratic term, with the plain host inspection order and no adaptive-`L`.
//! 3. `spine_wide_and_multipattern_state_count_is_linear` — spines, wide arities, and
//!    multi-pattern sets are each exactly linear in size.
//!
//! Any regression to a match-goal-set representation, or a broken interner that loses
//! structural sharing, breaks (2)/(3) and inflates (1) past its pins.
//!
//! Measured baselines (2026-07, branch `codex/rho-native-set-automata`), pinned below:
//! RhoCalc 124 states / 117 entries / 314 raw nodes; Calculator 72 / 70 / 188; every
//! demo language ≤ 4 states.

// Task #11 (extended 2026-07-26): the DEMONSTRATION / fixture languages are test-hosted
// (`options { hosted_in: "tests/definitions/<lang>.rs" }`) — their definitions left the
// `languages` library, so they are `#[path]`-included here rather than named through
// `mettail_languages::<lang>`. This file does NOT invoke any `<lang>_generated_tests!`
// wrapper; each definition's DESIGNATED HOST binary (`languages/tests/<lang>.rs`) is the
// sole invoker, so the generated suites exist exactly once across the whole suite.
#[path = "definitions/nativefolddemo.rs"]
mod nativefolddemo;
#[path = "definitions/appsubst.rs"]
mod appsubst;
#[path = "definitions/guarded_rho.rs"]
mod guardedrho;
#[path = "definitions/swapdemo.rs"]
mod swapdemo;
#[path = "definitions/ctxdemo.rs"]
mod ctxdemo;
#[path = "definitions/bicongdemo.rs"]
mod bicongdemo;
#[path = "definitions/acdemo.rs"]
mod acdemo;
#[path = "definitions/acbagdemo.rs"]
mod acbagdemo;
#[path = "definitions/nlacdemo.rs"]
mod nlacdemo;
#[path = "definitions/commdemo.rs"]
mod commdemo;
#[path = "definitions/lambdademo.rs"]
mod lambdademo;
#[path = "definitions/nativedemo.rs"]
mod nativedemo;
#[path = "definitions/ambdemo.rs"]
mod ambdemo;
#[path = "definitions/ambnewdemo.rs"]
mod ambnewdemo;
#[path = "definitions/inoutdemo.rs"]
mod inoutdemo;

use dovetail::rules::Pattern;
use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomaton, SetAutomatonView, StateId};
use mettail_rholang_codegen::{compile_in_rho_matching_ruleset, reconstruct_language_def};
use mettail_runtime::Language;

/// Raw (structurally UNFOLDED) node count of one compiled entry's pattern tree —
/// the pre-interning size the interned `state_count` is measured against.
fn state_nodes(view: &SetAutomatonView<'_, String>, state: StateId) -> usize {
    match view.node(state) {
        AutomatonNode::Var(_) => 1,
        AutomatonNode::App { args, .. } => {
            1 + args.iter().map(|&a| state_nodes(view, a)).sum::<usize>()
        },
    }
}

/// `(entry_count, state_count, summed_raw_nodes)` for a language's definition source.
fn metrics_for(source: &str) -> (usize, usize, usize) {
    let def = reconstruct_language_def(source).expect("definition source reconstructs");
    let ruleset = compile_in_rho_matching_ruleset(&def);
    let view = ruleset.automaton.view();
    let entries = view.entry_count();
    let states = view.state_count();
    let mut raw_nodes = 0usize;
    for entry in 0..entries {
        raw_nodes += state_nodes(&view, view.entry_root_state(entry));
    }
    (entries, states, raw_nodes)
}

/// Assert the three size-optimality invariants for one bundled language, pinned to
/// `pin` (the measured `state_count`, used as an upper bound so only BLOAT fails; a
/// legitimate shrink from better sharing still passes).
fn assert_size_optimal(label: &str, source: Option<&str>, pin: usize) {
    let source =
        source.unwrap_or_else(|| panic!("{label}: language exposes no definition_source"));
    let (entries, states, raw_nodes) = metrics_for(source);

    // (a) The interning O1/O3 quotient never grows the DAG beyond the raw pattern nodes.
    assert!(
        states <= raw_nodes,
        "{label}: state_count {states} exceeds raw pattern nodes {raw_nodes} — the \
         interned-subterm quotient (TcChannelNamingQuotient) must never grow the DAG"
    );
    // (b) Absolute no-bloat regression lock. A match-goal-set / discrimination-net
    // regression, or lost interner sharing, blows this past the pin.
    assert!(
        states <= pin,
        "{label}: state_count {states} exceeds pinned bound {pin} — the in-Rho automaton \
         BLOATED. Update the pin ONLY after confirming this is not a super-linear \
         (match-goal-set) representation regression."
    );
    // (c) Near-linear in the entry count (measured slope ≈1.05; ceiling 1.5 + additive 8).
    // A quadratic representation (states ~ entries²) fails this for every non-trivial language.
    let linear_bound = entries * 3 / 2 + 8;
    assert!(
        states <= linear_bound,
        "{label}: state_count {states} is super-linear in entry_count {entries} \
         (near-linear bound {linear_bound}) — a quadratic representation regression"
    );

    println!(
        "{label:<16} entries={entries:<4} states={states:<4} raw_nodes={raw_nodes:<4} \
         (pin {pin}, linear_bound {linear_bound})"
    );
}

/// The interned `state_count` of a single-pattern automaton.
fn single_pattern_states(pattern: Pattern<String>) -> usize {
    SetAutomaton::compile_structural([(PatternId(0), pattern)])
        .expect("single positional pattern compiles")
        .view()
        .state_count()
}

/// The interned `state_count` of a multi-pattern automaton.
fn multi_pattern_states(patterns: Vec<(PatternId, Pattern<String>)>) -> usize {
    SetAutomaton::compile_structural(patterns)
        .expect("positional pattern set compiles")
        .view()
        .state_count()
}

#[test]
fn per_language_in_rho_automaton_is_size_optimal() {
    println!("\n=== per-language in-Rho set-automaton size (size-optimality lock) ===");

    // `pin` = the measured `state_count` used as an upper bound. Demo languages are
    // pinned to their exact measured size; the two large languages carry a small
    // margin (RhoCalc 124→130, Calculator 72→78). AC / contextual / binder-only
    // languages have NO positional entries (their redexes ride the AC / contextual /
    // nested-structural dispatch paths), so their automaton is empty — pin 0.
    macro_rules! check {
        ($label:literal, $path:path, $pin:expr) => {{
            use $path as L;
            assert_size_optimal($label, L.metadata().definition_source(), $pin);
        }};
    }

    check!("SwapDemo", crate::swapdemo::SwapDemoLanguage, 3);
    check!("CtxDemo", crate::ctxdemo::CtxDemoLanguage, 3);
    check!("BiCongDemo", crate::bicongdemo::BiCongDemoLanguage, 3);
    check!("AcDemo", crate::acdemo::AcDemoLanguage, 0);
    check!("AcBagDemo", crate::acbagdemo::AcBagDemoLanguage, 0);
    check!("NlAcDemo", crate::nlacdemo::NlAcDemoLanguage, 0);
    check!("CommDemo", crate::commdemo::CommDemoLanguage, 0);
    check!("LambdaDemo", crate::lambdademo::LambdaDemoLanguage, 4);
    check!("NativeDemo", crate::nativedemo::NativeDemoLanguage, 3);
    check!("NativeFoldDemo", crate::nativefolddemo::NativeFoldDemoLanguage, 3);
    check!("AmbDemo", crate::ambdemo::AmbDemoLanguage, 0);
    check!("AmbNewDemo", crate::ambnewdemo::AmbNewDemoLanguage, 0);
    check!("InOutDemo", crate::inoutdemo::InOutDemoLanguage, 0);
    check!("RhoCalc", mettail_languages::rhocalc::RhoCalcLanguage, 130);
    check!("Calculator", mettail_languages::calculator::CalculatorLanguage, 78);
    check!("Ambient", mettail_languages::ambient::AmbientLanguage, 0);
    check!("AppSubst", crate::appsubst::AppSubstLanguage, 4);
    check!("Lambda", mettail_languages::lambda::LambdaLanguage, 4);
    check!("GuardedRho", crate::guardedrho::GuardedRhoLanguage, 0);
}

#[test]
fn diagonal_discrimination_set_is_linear_not_quadratic() {
    // The classic discrimination-net Θ(n²) worst case (Sekar–Ramesh–Ramakrishnan,
    // "Adaptive pattern matching", 1995): `n` patterns over an `n`-ary constructor `g`,
    // where pattern `i` places a nullary sentinel constant at position `i` and a fresh
    // variable (named by position) at every other position. A left-to-right MATCH-GOAL-SET
    // automaton must branch on each position to find the sentinel → Θ(n²) states, and an
    // adaptive `L` is what recovers Θ(n). The interned-subterm representation here is
    // EXACTLY `2n+1` (n distinct `g`-apps + 1 sentinel + n distinct vars), with the plain
    // host inspection order and NO adaptive-`L`. The `n=1` case is degenerate (a single
    // pattern with no sibling variable positions) → `2`.
    println!("\n=== diagonal n-of-n interned states (linear, not quadratic) ===");
    for &n in &[1usize, 2, 4, 8, 16, 32, 64, 128] {
        let patterns: Vec<(PatternId, Pattern<String>)> = (0..n)
            .map(|i| {
                let args = (0..n)
                    .map(|j| {
                        if j == i {
                            Pattern::app("Sentinel".to_string(), vec![])
                        } else {
                            Pattern::var(format!("v{j}"))
                        }
                    })
                    .collect();
                (PatternId(i), Pattern::app("g".to_string(), args))
            })
            .collect();
        let states = multi_pattern_states(patterns);
        let expected = if n == 1 { 2 } else { 2 * n + 1 };
        assert_eq!(
            states, expected,
            "diagonal n={n}: interned state_count {states} != {expected} (linear 2n+1) — a \
             super-linear regression to a match-goal-set / discrimination-net representation"
        );
        println!("n={n:<4} states={states:<5} expected={expected} (2n+1 linear)");
    }
}

#[test]
fn spine_wide_and_multipattern_state_count_is_linear() {
    // Spines, wide arities, and multi-pattern sets are each exactly linear in size,
    // independent of any inspection order.
    for &n in &[1usize, 2, 4, 8, 16, 32, 64, 128] {
        // Spine `f(f(...f(x)))` of depth n → n App states + 1 Var = n+1.
        let mut spine = Pattern::var("x");
        for _ in 0..n {
            spine = Pattern::app("f".to_string(), vec![spine]);
        }
        assert_eq!(single_pattern_states(spine), n + 1, "spine depth {n} must intern to n+1");

        // Wide `f(x0, ..., x_{n-1})` → 1 App + n distinct Vars = n+1.
        let wide = Pattern::app(
            "f".to_string(),
            (0..n).map(|i| Pattern::var(format!("x{i}"))).collect(),
        );
        assert_eq!(single_pattern_states(wide), n + 1, "wide arity {n} must intern to n+1");

        // n distinct flat binary patterns f_i(x, y) sharing var names → n Apps + 2 Vars = n+2.
        let flat: Vec<(PatternId, Pattern<String>)> = (0..n)
            .map(|i| {
                (
                    PatternId(i),
                    Pattern::app(format!("f{i}"), vec![Pattern::var("x"), Pattern::var("y")]),
                )
            })
            .collect();
        assert_eq!(multi_pattern_states(flat), n + 2, "n={n} distinct flat patterns must intern to n+2");
    }
}
