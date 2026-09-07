//! Exercise the public view against the normal (non-`cfg(test)`) library build.

use dovetail::{egraph::EGraph, egraph::ENode};
use mettail_dovetail_runtime::{
    theory_operator_to_machine, theory_positional_native_view, RuntimeLiteralRef,
    TheoryPositionalNativeView,
};
use mettail_grammar_core::{
    TheoryImageOperatorV1, TheoryJudgmentPatternAutomatonV1, TheoryLiteralCarrierV1,
    TheoryLiteralV1, TheoryPatternAutomatonV1, TheoryResourceProfileV1, TheorySemanticImageV1,
    TheorySortId, TheorySortImageV1, TheorySortKindImageV1, THEORY_IMAGE_COMPILER_ABI_CURRENT,
    THEORY_PRIMITIVE_SUBSTRATE_ABI_CURRENT, THEORY_SEMANTIC_IMAGE_ABI_CURRENT,
};

#[test]
fn positional_native_view_decodes_booleans_in_the_production_library() {
    // A local-view fixture, not an installation or action-authority fixture.
    let image = TheorySemanticImageV1 {
        abi: THEORY_SEMANTIC_IMAGE_ABI_CURRENT,
        compiler_abi: THEORY_IMAGE_COMPILER_ABI_CURRENT,
        primitive_substrate_abi: THEORY_PRIMITIVE_SUBSTRATE_ABI_CURRENT,
        language_fingerprint: [0; 32],
        grammar_fingerprint: [0; 32],
        theory_fingerprint: [0; 32],
        resource_profile: TheoryResourceProfileV1::Uncosted,
        sorts: vec![TheorySortImageV1 {
            id: TheorySortId(0),
            kind: TheorySortKindImageV1::Syntax {
                literal: Some(TheoryLiteralCarrierV1::Boolean),
            },
        }],
        constructors: vec![],
        rules: vec![],
        patterns: TheoryPatternAutomatonV1 { states: vec![], entries: vec![] },
        judgments: vec![],
        judgment_rules: vec![],
        judgment_patterns: TheoryJudgmentPatternAutomatonV1 { states: vec![], entries: vec![] },
        actions: vec![],
    };
    let mut egraph = EGraph::new();
    for value in [false, true] {
        let root =
            egraph.add(ENode::leaf(theory_operator_to_machine(&TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Boolean(value),
            })));
        let mut work = 0;
        assert_eq!(
            theory_positional_native_view(
                &image,
                &egraph,
                root,
                TheorySortId(0),
                &mut work,
                1,
                &mut || false,
            ),
            Ok(Some(TheoryPositionalNativeView::Literal {
                sort: TheorySortId(0),
                value: RuntimeLiteralRef::Boolean(value),
            }))
        );
        assert_eq!(work, 1);
    }
}
