//! Stage 4 (Ambient In/Out) — the TYPED native lane produces the `InRule`/`OutRule` justification.
//!
//! `InOutDemo`'s DEPTH-2 nested structural non-linear AC rewrites route to the typed native lane
//! (`needs_typed_dovetail_path`, gated `!should_emit_binder_congruence`). `dovetail_report_for` must
//! FIRE the nested rule and record a `rewrite_justification` whose σ binds every LHS variable — the
//! provenance the nested structural-AC σ-injection reconstructs `⟦operand⟧` + `⟦reduct⟧` from.
#![cfg(feature = "in-out-demo")]

use mettail_languages::inoutdemo::InOutDemoLanguage;
use mettail_runtime::Language;

/// The `InRule` redex `{ na[{ in(nb, A) }] | nb[B] }` (the `in` target `nb` AND the sibling ambient
/// `nb` — a MATCHING cross-level name) reduces on the typed native lane: the sole firing is `InRule`,
/// and its σ binds `N = na`, `M = nb`, `P = A`, `R = B`, and the two remainders.
#[test]
fn inoutdemo_in_report_produces_the_in_justification() {
    mettail_runtime::clear_var_cache();
    let term = InOutDemoLanguage
        .parse_term("{ na[{ in(nb, A) }] | nb[B] }")
        .expect("InOutDemo must parse the InRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile on the typed native lane");
    assert!(
        report.is_complete(),
        "the acyclic InRule reduction must report Complete, got {:?}",
        report.completeness
    );
    assert_eq!(
        report.rewrite_justifications.len(),
        1,
        "exactly one InRule firing must be recorded, got {:?}",
        report.rewrite_justifications
    );
    let justification = &report.rewrite_justifications[0];
    assert_eq!(justification.rule_label, "InRule");
    for (name, subterm) in &justification.sigma {
        eprintln!("InRule σ[{name}] = {subterm:?}");
    }
    let sigma = |name: &str| {
        justification
            .sigma
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, s)| s)
            .unwrap_or_else(|| panic!("σ must bind {name}, got {:?}", justification.sigma))
    };
    assert_eq!(sigma("N").constructor, "Na", "the outer (moving) ambient name N is `na`");
    assert_eq!(sigma("M").constructor, "Nb", "the cross-level name M is `nb`");
    assert_eq!(sigma("P").constructor, "PA", "the carried process P is `A`");
    assert_eq!(sigma("R").constructor, "PB", "the sibling-ambient process R is `B`");
}

/// The `OutRule` redex `nb[{ na[{ out(nb, A) }] | B }]` (the `out` target `nb` = the root ambient
/// `nb`) reduces on the typed native lane: the sole firing is `OutRule`, σ binds the LHS variables.
#[test]
fn inoutdemo_out_report_produces_the_out_justification() {
    mettail_runtime::clear_var_cache();
    let term = InOutDemoLanguage
        .parse_term("nb[{ na[{ out(nb, A) }] | B }]")
        .expect("InOutDemo must parse the OutRule redex");
    let report = InOutDemoLanguage::dovetail_report_for(term.as_ref(), 64, 1_000_000)
        .expect("InOutDemo Dovetail report must compile on the typed native lane");
    assert!(
        report.is_complete(),
        "the acyclic OutRule reduction must report Complete, got {:?}",
        report.completeness
    );
    for justification in &report.rewrite_justifications {
        eprintln!("firing {}", justification.rule_label);
        for (name, subterm) in &justification.sigma {
            eprintln!("  σ[{name}] = {subterm:?}");
        }
    }
    assert!(
        report
            .rewrite_justifications
            .iter()
            .any(|j| j.rule_label == "OutRule"),
        "an OutRule firing must be recorded, got {:?}",
        report.rewrite_justifications
    );
}
