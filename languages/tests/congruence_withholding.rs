//! Generated-code witness for the three-state congruence model.
//!
//! This test exercises the public generated runtime, not the private classifier.  It proves that
//! a declared withholding becomes a payload-verbatim leaf in the e-graph, remains invertible at
//! extraction, and affects exactly the named field while an unwithheld sibling still propagates.

#![cfg(feature = "dovetail-codegen")]

#[path = "definitions/congruence_withholding_demo.rs"]
mod congruence_withholding_demo;

use congruence_withholding_demo::{
    CongruenceWithholdingDemoLanguage, CongruenceWithholdingDemoMetadata,
};
use mettail_runtime::{Language, LanguageMetadata, LoweredConstructKind, LoweringOutcomeKind};

const MAX_ITERS: usize = 32;
const MAX_NODES: usize = 100_000;

#[test]
fn withheld_field_is_severed_while_its_sibling_still_propagates() {
    let language = CongruenceWithholdingDemoLanguage;
    let input = language
        .parse_term("pair(box(a),box(a))")
        .expect("fixture term parses");
    let normal = CongruenceWithholdingDemoLanguage::dovetail_normal_term(
        input.as_ref(),
        MAX_ITERS,
        MAX_NODES,
    )
    .unwrap_or_else(|error| panic!("withholding fixture must normalize: {error}"));

    assert_eq!(
        language.format_term(normal.as_ref()),
        "pair(a , box(a))",
        "field 0 is an ordinary child and follows `box(a) -> a`; field 1 is the declared \
         payload-verbatim leaf and must retain `box(a)`"
    );
}

#[test]
fn withholding_has_a_named_suppressed_disposition_and_no_emitted_rewrite() {
    let inventory = CongruenceWithholdingDemoMetadata.lowering_dispositions();
    let rows: Vec<_> = inventory
        .iter()
        .filter(|row| {
            row.construct_kind == LoweredConstructKind::Rewrite
                && row.construct == "PairRightWithheld"
        })
        .collect();

    assert_eq!(rows.len(), 1, "every declaration has exactly one disposition: {inventory:#?}");
    assert_eq!(rows[0].outcome, LoweringOutcomeKind::Suppressed);
    assert!(
        rows[0].detail.contains("field 1")
            && rows[0].detail.contains("payload-verbatim")
            && rows[0].detail.contains("no rewrite rule is emitted"),
        "the disposition must name the derived position, carrier, and emission result: {}",
        rows[0].detail,
    );

    let kernel = inventory
        .iter()
        .find(|row| row.construct_kind == LoweredConstructKind::Rewrite && row.construct == "Unbox")
        .expect("positive control: the same rewrite walk sees the kernel");
    assert_eq!(kernel.outcome, LoweringOutcomeKind::Delivered);
}
