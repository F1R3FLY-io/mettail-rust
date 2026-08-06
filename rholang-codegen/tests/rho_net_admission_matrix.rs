//! Track B — B0: the ADMISSION-MATRIX AUDIT for the planned benchmark workload
//! families.
//!
//! Each planned Track-B workload subject family is asserted against the driver
//! that is supposed to admit it TODAY (or fail closed with the exact typed
//! reason). The point of this audit is to RED-TEAM the benchmark workload
//! design BEFORE any baseline emitter exists: if an assertion here ever
//! contradicts the expected matrix, the benchmark workload design — not this
//! test — must change, so a deviation must be reported, never silently
//! adjusted.
//!
//! Placement: this test lives in `rholang-codegen` (not `rholang-runtime`)
//! because every type it needs is visible here — `InRhoMatchingRuleset` and the
//! three drivers are `pub` in this crate, and `dovetail` (for
//! `SetAutomaton::compile_structural`) and the `GroundTerm` subject type are
//! regular dependencies. No runtime execution is required: ADMISSION is a
//! serialization-time property (`Ok`/typed `Err` from the driver), so no
//! `RhoRuntime`, no demo language features, and no `required-features` gate.
//!
//! Construction style: DIRECT — hand-compiled `SetAutomaton` entries + hand
//! `GroundTerm` subjects (mirroring `rholang-runtime/tests/rho_net_equivalence.rs`'s
//! direct-construction pattern), never `language!` fixtures. The
//! `InRhoMatchingRuleset` is assembled field-by-field (every field is `pub`),
//! with the non-positional dispatch families empty except where the family
//! under audit needs one (the contextual row).

use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};
use mettail_rholang_codegen::{
    contextual_match_call_par, in_rho_match_all_sites_call_par, in_rho_match_call_par,
    AutomatonUnsupported, GroundTerm, InRhoMatchingRuleset, RhoNetContextualMatchEntry,
    LAMBDA_REFLECT_LABEL,
};

/// The shared audit fingerprint (a ground tag namespace; no language definition
/// is involved anywhere in this audit).
const FP: &str = "fp";

/// Assemble an `InRhoMatchingRuleset` DIRECTLY from hand-compiled automaton
/// entries + accept channels (+ optionally one contextual dispatch record) —
/// every non-positional dispatch family empty, `deferred` empty, exactly the
/// shape `compile_in_rho_matching_ruleset` produces for a purely positional
/// ruleset (its fields are all `pub`, so the direct construction is supported
/// API, not a test backdoor).
fn direct_ruleset(
    patterns: Vec<(PatternId, Pattern<String>)>,
    accepts: Vec<(PatternId, &str)>,
    contextual: Vec<RhoNetContextualMatchEntry>,
) -> InRhoMatchingRuleset {
    let automaton =
        SetAutomaton::compile_structural(patterns).expect("the audit patterns are AC-free");
    InRhoMatchingRuleset {
        automaton,
        accept_channels: accepts
            .into_iter()
            .map(|(pid, channel)| (pid, channel.to_string()))
            .collect(),
        language_fingerprint: FP.to_string(),
        deferred: Vec::new(),
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        contextual_dispatch: contextual,
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
    }
}

/// The flat `Swap(x, y)` single-entry ruleset (workload families i + ii).
fn swap_ruleset() -> InRhoMatchingRuleset {
    direct_ruleset(
        vec![(
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )],
        vec![(PatternId(0), "sa:swap")],
        Vec::new(),
    )
}

/// The nested `f(g(x))` single-entry ruleset (workload family iii).
fn nested_ruleset() -> InRhoMatchingRuleset {
    direct_ruleset(
        vec![(
            PatternId(0),
            Pattern::app(
                "f".to_string(),
                vec![Pattern::app("g".to_string(), vec![Pattern::var("x")])],
            ),
        )],
        vec![(PatternId(0), "sa:fg")],
        Vec::new(),
    )
}

/// The β-shaped `App(^lambda(fun), arg)` single-entry ruleset (workload family
/// iv) — the lambdademo-shaped subst LHS as a DIRECT pattern, with the binder
/// constructor already remapped to the reserved `^lambda` reflection tag
/// (exactly what `convert_subst_lhs` produces for `App(Lam(fun), arg)`).
fn lambda_app_ruleset() -> InRhoMatchingRuleset {
    direct_ruleset(
        vec![(
            PatternId(0),
            Pattern::app(
                "App".to_string(),
                vec![
                    Pattern::app(LAMBDA_REFLECT_LABEL.to_string(), vec![Pattern::var("fun")]),
                    Pattern::var("arg"),
                ],
            ),
        )],
        vec![(PatternId(0), "sa:beta")],
        Vec::new(),
    )
}

/// The contextual 1-hole ruleset (workload family v): the base `Swap` entry
/// reduces the hole; the `WrapCong` contextual family (`Wrap(S) ~> Wrap(T)` with
/// premise `S ~> T`) carries one premise channel + the `Wrap.0` hole position —
/// the same record `rho_net_contextual_match_entries` derives for
/// `WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T)`.
fn contextual_ruleset() -> InRhoMatchingRuleset {
    direct_ruleset(
        vec![(
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )],
        vec![(PatternId(0), "sa:flip")],
        vec![RhoNetContextualMatchEntry {
            fired_rule_label: "WrapCong".to_string(),
            premise_channels: vec!["ctx:WrapCong:p0".to_string()],
            hole_positions: vec![vec![("Wrap".to_string(), 0)]],
        }],
    )
}

fn nullary(label: &str) -> GroundTerm {
    GroundTerm::new(label, Vec::new())
}

fn swap(a: &str, b: &str) -> GroundTerm {
    GroundTerm::new("Swap", vec![nullary(a), nullary(b)])
}

/// `f(g(A))` — one head-`f` candidate site.
fn fg(leaf: &str) -> GroundTerm {
    GroundTerm::new("f", vec![GroundTerm::new("g", vec![nullary(leaf)])])
}

/// A λ-chain App-spine with `n ≥ 1` App nodes:
/// `App(^lambda(F), App(^lambda(F), … App(^lambda(F), A0)))`.
fn lambda_chain(n: usize) -> GroundTerm {
    let mut term = nullary("A0");
    for _ in 0..n {
        term = GroundTerm::new(
            "App",
            vec![GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![nullary("F")]), term],
        );
    }
    term
}

/// A wide flat comb: an inert right-leaning `Pair` spine carrying `m` `Swap`
/// redexes (`Pair` is NOT a rule root, so exactly the `m` Swaps are candidate
/// sites).
fn swap_comb(m: usize) -> GroundTerm {
    let mut term = swap("A", "B");
    for _ in 1..m {
        term = GroundTerm::new("Pair", vec![swap("A", "B"), term]);
    }
    term
}

/// One audited (workload family, driver) cell of the admission matrix: the
/// EXPECTED admission (`Ok(count)` = admitted, with the driver's located-site /
/// hole count where it reports one, `1` for the count-less single-root driver)
/// or the exact typed fail-closed reason.
struct MatrixRow {
    family: &'static str,
    driver: &'static str,
    expected: Result<usize, AutomatonUnsupported>,
    actual: Result<usize, AutomatonUnsupported>,
}

/// Run every driver over every planned workload family and collect the matrix.
fn audit_matrix() -> Vec<MatrixRow> {
    let mut rows: Vec<MatrixRow> = Vec::with_capacity(10);

    // (i) flat single-redex Swap(A, B) at the root.
    let flat = swap_ruleset();
    rows.push(MatrixRow {
        family: "(i) flat single-redex Swap(A,B) at root",
        driver: "in_rho_match_call_par (single root site)",
        expected: Ok(1),
        actual: in_rho_match_call_par(&flat, &swap("A", "B"), "site0", "OUT").map(|_| 1),
    });
    rows.push(MatrixRow {
        family: "(i) flat single-redex Swap(A,B) at root",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Ok(1),
        actual: in_rho_match_all_sites_call_par(&flat, &swap("A", "B"), "site0", "OUT")
            .map(|(_, sites)| sites),
    });

    // (ii) wide flat multi-redex: a comb of m = 4 Swaps under an inert Pair spine.
    rows.push(MatrixRow {
        family: "(ii) wide flat multi-redex comb (m = 4 Swaps)",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Ok(4),
        actual: in_rho_match_all_sites_call_par(&flat, &swap_comb(4), "site0", "OUT")
            .map(|(_, sites)| sites),
    });

    // (iii) nested-entry f(g(x)): 1 candidate site admits; k = 2 head-matching
    // candidate sites fail closed (co-installed nested networks would contend
    // for one `loc:` head-tag send).
    let nested = nested_ruleset();
    rows.push(MatrixRow {
        family: "(iii) nested-entry f(g(x)), k = 1 candidate site",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Ok(1),
        actual: in_rho_match_all_sites_call_par(&nested, &fg("A"), "site0", "OUT")
            .map(|(_, sites)| sites),
    });
    rows.push(MatrixRow {
        family: "(iii) nested-entry f(g(x)), k = 2 candidate sites",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Err(AutomatonUnsupported::NestedEntryMultiSite),
        actual: in_rho_match_all_sites_call_par(
            &nested,
            &GroundTerm::new("Pair", vec![fg("A"), fg("B")]),
            "site0",
            "OUT",
        )
        .map(|(_, sites)| sites),
    });

    // (iv) λ-chain App-spine (the lambdademo-shaped LHS App(^lambda(fun), arg)):
    // n ≥ 2 App nodes fail closed on locate-all (the entry is NESTED — its
    // ^lambda descent could contend with a co-installed App-root attempt); the
    // single-site ROOT drive still admits the root redex; n = 1 locates fine.
    let beta = lambda_app_ruleset();
    rows.push(MatrixRow {
        family: "(iv) λ-chain App-spine, n = 2 App nodes",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Err(AutomatonUnsupported::NestedEntryMultiSite),
        actual: in_rho_match_all_sites_call_par(&beta, &lambda_chain(2), "site0", "OUT")
            .map(|(_, sites)| sites),
    });
    rows.push(MatrixRow {
        family: "(iv) λ-chain App-spine, n = 2 App nodes",
        driver: "in_rho_match_call_par (single root site)",
        expected: Ok(1),
        actual: in_rho_match_call_par(&beta, &lambda_chain(2), "site0", "OUT").map(|_| 1),
    });
    rows.push(MatrixRow {
        family: "(iv) λ-chain single App redex (n = 1)",
        driver: "in_rho_match_all_sites_call_par (locate-all)",
        expected: Ok(1),
        actual: in_rho_match_all_sites_call_par(&beta, &lambda_chain(1), "site0", "OUT")
            .map(|(_, sites)| sites),
    });

    // (v) contextual 1-hole rule: Wrap(Swap(A, B)) admits (the hole redex is
    // exactly the one expected hole position); a normal-form hole fails closed
    // (the bijection check — the join could never bind that hole).
    let ctx = contextual_ruleset();
    rows.push(MatrixRow {
        family: "(v) contextual 1-hole Wrap(Swap(A,B))",
        driver: "contextual_match_call_par",
        expected: Ok(1),
        actual: contextual_match_call_par(
            &ctx,
            &GroundTerm::new("Wrap", vec![swap("A", "B")]),
            "site0",
            "OUT",
        )
        .map(|_| 1),
    });
    rows.push(MatrixRow {
        family: "(v) contextual 1-hole, hole is a normal form",
        driver: "contextual_match_call_par",
        expected: Err(AutomatonUnsupported::ContextualHoleMismatch),
        actual: contextual_match_call_par(
            &ctx,
            &GroundTerm::new(
                "Wrap",
                vec![GroundTerm::new("Pair", vec![nullary("A"), nullary("B")])],
            ),
            "site0",
            "OUT",
        )
        .map(|_| 1),
    });

    rows
}

/// THE admission matrix: every (workload family, driver) cell must admit / fail
/// closed exactly as the Track-B benchmark design expects. On ANY deviation the
/// whole matrix is printed and the test panics — the deviation changes the
/// benchmark workload design and must be surfaced, never silently adjusted.
#[test]
fn admission_matrix_matches_the_track_b_workload_design() {
    let rows = audit_matrix();
    let mut deviations: Vec<String> = Vec::with_capacity(rows.len());
    for row in &rows {
        if row.expected != row.actual {
            deviations.push(format!(
                "  DEVIATION {} × {}: expected {:?}, got {:?}",
                row.family, row.driver, row.expected, row.actual
            ));
        }
    }
    if !deviations.is_empty() {
        let mut report = String::from(
            "ADMISSION-MATRIX DEVIATION — the Track-B workload design assumptions do NOT hold:\n",
        );
        for line in &deviations {
            report.push_str(line);
            report.push('\n');
        }
        report.push_str("full audited matrix:\n");
        for row in &rows {
            report.push_str(&format!(
                "  {} × {} → expected {:?}, actual {:?}\n",
                row.family, row.driver, row.expected, row.actual
            ));
        }
        panic!("{report}");
    }
}

/// Family (ii) detail: the locate-all count scales with the comb width (the
/// benchmark's independent variable), and the flat ruleset never trips the
/// nested-multi-site gate at any width.
#[test]
fn flat_comb_locate_all_scales_with_width() {
    let flat = swap_ruleset();
    for m in 1..=8usize {
        let (_, sites) = in_rho_match_all_sites_call_par(&flat, &swap_comb(m), "site0", "OUT")
            .expect("a flat-only ruleset co-installs at any number of sites");
        assert_eq!(sites, m, "the comb of {m} Swaps must locate exactly {m} sites");
    }
}

/// Family (iv) detail: the λ-chain locate-all fail-closes for EVERY chain length
/// n ≥ 2 (not just n = 2) — the benchmark's App-spine workloads must therefore
/// drive nested entries through the single-root driver (or one redex at a time).
#[test]
fn lambda_chain_locate_all_fails_closed_for_every_n_at_least_2() {
    let beta = lambda_app_ruleset();
    for n in 2..=6usize {
        assert_eq!(
            in_rho_match_all_sites_call_par(&beta, &lambda_chain(n), "site0", "OUT"),
            Err(AutomatonUnsupported::NestedEntryMultiSite),
            "a λ-chain of {n} App nodes has {n} head-matching candidate sites — locate-all must fail closed"
        );
    }
}

/// Family (iv) detail: the single-root drive admits the root redex for every
/// chain length (serialization does not inspect the subject), so the sequential
/// root-drive benchmark leg is well-defined for the whole λ-chain family.
#[test]
fn lambda_chain_single_root_drive_admits_every_n() {
    let beta = lambda_app_ruleset();
    for n in 1..=6usize {
        let call = in_rho_match_call_par(&beta, &lambda_chain(n), "site0", "OUT")
            .expect("the single-root drive serializes the nested β entry");
        assert!(
            call.locally_free.is_empty() && !call.connective_used,
            "the emitted call is a closed Par"
        );
    }
}

/// Family (iii) detail: the k = 2 fail-closure is driven by the CANDIDATE-SITE
/// count (head-constructor pre-filter), not by whether the deep pattern would
/// actually match — f(f(A)) has 2 head-`f` candidate sites even though only the
/// outer one could ever match f(g(x)); locate-all still fails closed.
#[test]
fn nested_entry_candidate_sites_are_counted_by_head_constructor_only() {
    let nested = nested_ruleset();
    let two_candidates = GroundTerm::new("f", vec![fg("A")]);
    assert_eq!(
        in_rho_match_all_sites_call_par(&nested, &two_candidates, "site0", "OUT"),
        Err(AutomatonUnsupported::NestedEntryMultiSite),
        "f(f(g(A))) has two head-f candidate sites — the pre-filter counts heads, not full matches"
    );
}

/// Family (v) detail: the contextual driver's emitted call is closed, and the
/// deeper-redex boundary also fails closed (two premise redexes inside one
/// expected hole).
#[test]
fn contextual_boundaries_fail_closed_and_the_admitted_call_is_closed() {
    let ctx = contextual_ruleset();
    let admitted = contextual_match_call_par(
        &ctx,
        &GroundTerm::new("Wrap", vec![swap("A", "B")]),
        "site0",
        "OUT",
    )
    .expect("the 1-hole contextual workload admits");
    assert!(
        admitted.locally_free.is_empty() && !admitted.connective_used,
        "the contextual match call is a closed Par"
    );

    let two_in_hole = GroundTerm::new(
        "Wrap",
        vec![GroundTerm::new("Pair", vec![swap("A", "B"), swap("B", "A")])],
    );
    assert_eq!(
        contextual_match_call_par(&ctx, &two_in_hole, "site0", "OUT"),
        Err(AutomatonUnsupported::ContextualHoleMismatch),
        "located redexes that are not exactly the expected hole positions fail closed"
    );
}
