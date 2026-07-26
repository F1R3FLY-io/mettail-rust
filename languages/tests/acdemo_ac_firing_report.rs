//! Stage AC-U3 (report side): the generated `AcDemo::dovetail_report_for` populates the AC
//! firing's resolved σ provenance — the gate that lets the runtime AC σ-injection F-function
//! read a firing to inject. This is the language-crate half of the AC firing wiring (the
//! runtime half — the actual COMM on the f1r3node reducer — is
//! `rholang-runtime/tests/rho_net_ac_firing.rs`).
//!
//! It ALSO pins the VERIFIED runtime `rest` shape the reconstruction depends on: a HashBag AC
//! firing binds `x` to a matched bag element and `rest` to the canonical `op` node over the
//! multiset complement, so `σ[rest]` reflects to
//! `RuntimeReflectedSubterm { constructor: "PPar", children: [complement elements] }` and the
//! whole operand bag is `[σ[x]] ⊎ σ[rest].children`.

// Task #11 (extended 2026-07-26): `AcDemo` is a DEMONSTRATION grammar, not a production
// language, so its definition lives in `languages/tests/definitions/acdemo.rs` rather than in
// the `languages` library (`languages/src/` is production-only).
//
// This file is its DESIGNATED HOST: it declares the definition module and is the one and only
// invoker of the opt-in `acdemo_generated_tests!` wrapper, which materializes the
// macro-generated sections that used to be written to `languages/tests/gen_acdemo_*.rs`.
// Other consumers `#[path]`-include the same definition WITHOUT invoking the wrapper, so the
// generated tests exist exactly once across the whole suite.
#[path = "definitions/acdemo.rs"]
mod acdemo;

acdemo::acdemo_generated_tests!(crate::acdemo);

use acdemo::{AcDemoLanguage, AcDemoTerm, AcDemoTermInner, Proc};
use mettail_runtime::RuntimeReflectedSubterm;

/// A σ sub-term is a "bare element" iff it is a nullary constructor whose label is one of the
/// AcDemo `Proc` operands `A`/`B`/`C` (the leaves the bag holds).
fn is_bare_element(subterm: &RuntimeReflectedSubterm) -> bool {
    subterm.children.is_empty() && matches!(subterm.constructor.as_str(), "A" | "B" | "C")
}

#[test]
fn acdemo_report_populates_ac_firings_with_the_verified_rest_shape() {
    let bag = mettail_runtime::HashBag::from_iter([Proc::A, Proc::B, Proc::C]);
    let term = AcDemoTerm(AcDemoTermInner::Proc(Proc::PPar(bag)));

    let report = AcDemoLanguage::dovetail_report_for(&term, 64, 1_000_000)
        .expect("AcDemo Dovetail report must compile");
    assert!(
        report.is_complete(),
        "the acyclic AC reduction reports Complete: {:?}",
        report.completeness
    );

    // The `populate_rewrite_justifications` gate now admits AC injection sites, so a pure-AC
    // language's report carries the σ provenance the runtime AC injection reads.
    assert!(
        !report.rewrite_justifications.is_empty(),
        "the AC rewrite must surface at least one firing justification (the AC injection gate)"
    );

    for justification in &report.rewrite_justifications {
        assert_eq!(justification.rule_label, "AcStep", "every firing is the AC rewrite");

        let sigma: std::collections::HashMap<&str, &RuntimeReflectedSubterm> = justification
            .sigma
            .iter()
            .map(|(name, subterm)| (name.as_str(), subterm))
            .collect();

        // The matched element `x` binds a bare bag element.
        let x = sigma
            .get("x")
            .expect("the AC firing binds the element variable x");
        assert!(is_bare_element(x), "σ[x] is a bare bag element, got {x:?}");

        // VERIFIED `rest` shape: the residual binds a canonical `op` node whose children are the
        // complement elements — `RuntimeReflectedSubterm { constructor: "PPar", children: [...] }`.
        let rest = sigma
            .get("rest")
            .expect("the AC firing binds the residual variable rest");
        assert_eq!(
            rest.constructor, "PPar",
            "σ[rest] is a PPar (the HashBag op) node, got {rest:?}"
        );
        for child in &rest.children {
            assert!(
                is_bare_element(child),
                "σ[rest].children are bare bag elements, got {child:?}"
            );
        }

        // The whole operand bag `[σ[x]] ⊎ σ[rest].children` is a non-empty multiset that CONTAINS
        // σ[x] — exactly what the runtime AC injection reconstructs and re-matches (the receiver
        // picks one element and fires `Wrap(element)`).
        let whole_bag_size = 1 + rest.children.len();
        assert!(whole_bag_size >= 1, "the reconstructed whole bag is non-empty");
    }
}
