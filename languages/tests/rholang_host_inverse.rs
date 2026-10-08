//! Exact generated V2 host-image inverse, never a source-text reparse.

use mettail_grammar_core::{
    DynamicTerm, DynamicValue, ProjectionHostCompoundProfileRecordV2, SemanticFieldSchemaV1,
    SemanticOperatorOriginV1, SourceSpan,
};
use mettail_languages::rholang::{
    reconstruct_host_proc_v2_with_meter, rholang_host_inverse_categories_v2,
    rholang_host_inverse_routes_v2, rholang_host_inverse_sequence_elements_v2, CostStack,
    CostStackChain, Proc,
    RholangHostInverseFieldV2, RholangHostInverseOriginV2, RholangHostReconstructErrorV2,
    RholangMetadata,
};
use mettail_runtime::LanguageMetadata;

fn profile() -> ProjectionHostCompoundProfileRecordV2 {
    ProjectionHostCompoundProfileRecordV2::decode_canonical(
        RholangMetadata
            .generated_projection_host_compound_profile_record_v2()
            .expect("generated V2 compound profile"),
    )
    .expect("exact V2 compound profile")
}

fn term(
    profile: &ProjectionHostCompoundProfileRecordV2,
    name: &str,
    fields: Vec<DynamicValue>,
) -> DynamicValue {
    let label = format!("Rholang::{name}");
    let route = profile
        .payload
        .codec
        .descriptor
        .operators
        .iter()
        .find(|route| route.label == label)
        .unwrap_or_else(|| panic!("missing selected route {label}"));
    DynamicValue::Term(Box::new(DynamicTerm {
        category: route.category,
        constructor: route.constructor,
        fields,
        span: SourceSpan::default(),
    }))
}

fn quoted_signature(profile: &ProjectionHostCompoundProfileRecordV2) -> DynamicValue {
    term(
        profile,
        "CostSig::CostSigGround",
        vec![term(profile, "Name::NQuote", vec![term(profile, "Proc::PZero", vec![])])],
    )
}

#[test]
fn compiled_typed_assembly_roster_matches_exact_profile() {
    let profile = profile();
    let descriptor = &profile.payload.codec.descriptor;
    let categories = rholang_host_inverse_categories_v2();
    assert_eq!(categories.len(), descriptor.categories.len());
    for (compiled, declared) in categories.iter().zip(&descriptor.categories) {
        assert_eq!(compiled.category, declared.category);
        assert_eq!(compiled.name, declared.name);
        assert_eq!(compiled.generated_category_tag, declared.generated_category_tag);
    }
    let routes = rholang_host_inverse_routes_v2();
    assert_eq!(routes.len(), descriptor.operators.len());
    for (compiled, declared) in routes.iter().zip(&descriptor.operators) {
        assert_eq!(compiled.operator, declared.operator);
        assert_eq!(compiled.category, declared.category);
        assert_eq!(compiled.constructor, declared.constructor);
        assert_eq!(compiled.generated_constructor_tag, declared.generated_constructor_tag);
        assert_eq!(compiled.stable_discriminant, declared.stable_discriminant);
        assert_eq!(compiled.label, declared.label);
        match (compiled.origin, &declared.origin) {
            (
                RholangHostInverseOriginV2::GrammarProduction(id),
                SemanticOperatorOriginV1::GrammarProduction(expected),
            ) => assert_eq!(id, expected.0),
            (
                RholangHostInverseOriginV2::Generated { family, ordinal },
                SemanticOperatorOriginV1::Generated {
                    family: expected_family,
                    ordinal: expected_ordinal,
                },
            ) => {
                assert_eq!(family, expected_family);
                assert_eq!(ordinal, *expected_ordinal);
            },
            _ => panic!("compiled typed origin differs from declared profile"),
        }
        assert_eq!(compiled.fields.len(), declared.fields.len());
        for (field, expected) in compiled.fields.iter().zip(&declared.fields) {
            match (field, expected) {
                (
                    RholangHostInverseFieldV2::Child(actual),
                    SemanticFieldSchemaV1::Child { category },
                ) => assert_eq!(actual, category),
                (
                    RholangHostInverseFieldV2::Sequence(actual),
                    SemanticFieldSchemaV1::Sequence { element },
                ) => assert_eq!(actual, element),
                _ => panic!("compiled typed field differs from declared profile"),
            }
        }
    }
    assert_eq!(
        rholang_host_inverse_sequence_elements_v2(),
        descriptor
            .sequences
            .iter()
            .map(|route| route.element)
            .collect::<Vec<_>>(),
    );
}

#[test]
fn exact_ids_reconstruct_nested_stack_branch_and_sequence() {
    let profile = profile();
    let signature = quoted_signature(&profile);
    let empty = || term(&profile, "CostStackChain::CostStackChainEmpty", vec![]);
    let left = term(
        &profile,
        "CostStackChain::CostStackChainCons",
        vec![signature.clone(), empty()],
    );
    let right = term(
        &profile,
        "CostStackChain::CostStackChainCons",
        vec![signature.clone(), empty()],
    );
    let left = term(&profile, "CostStack::CostStackLift", vec![left]);
    let fork = term(&profile, "CostStack::CostStackPar", vec![left, right]);
    let grouped = term(&profile, "CostStackChain::CostStackChainGroup", vec![fork]);
    let root = term(&profile, "Proc::PCostStackCons", vec![signature.clone(), grouped]);
    let mut work = 0usize;
    let decoded = reconstruct_host_proc_v2_with_meter(&root, |operations, _bytes| {
        work += operations;
        Ok::<(), ()>(())
    })
    .expect("checked selected tree reconstructs");
    assert!(work > 0);
    assert!(matches!(decoded, Proc::PCostStackCons(_, ref tail)
        if matches!(tail.as_ref(), CostStackChain::CostStackChainGroup(stack)
            if matches!(stack.as_ref(), CostStack::CostStackPar(..)))));

    let bind = term(
        &profile,
        "InputBind::InputBindCostSignedEmpty",
        vec![
            term(&profile, "Name::NQuote", vec![term(&profile, "Proc::PZero", vec![])]),
            signature,
        ],
    );
    let row = term(&profile, "ForRow::ForRowSingleNoWhere", vec![bind]);
    let receive = term(
        &profile,
        "Proc::PForCostSigned",
        vec![DynamicValue::Sequence(vec![row]), term(&profile, "Proc::PZero", vec![])],
    );
    assert!(matches!(
        reconstruct_host_proc_v2_with_meter(&receive, |_, _| Ok::<(), ()>(())),
        Ok(Proc::PForCostSigned(ref rows, _)) if rows.len() == 1
    ));
}

#[test]
fn malformed_or_unfunded_images_refuse_without_reparse() {
    let profile = profile();
    let good = term(&profile, "Proc::PZero", vec![]);
    assert!(matches!(
        reconstruct_host_proc_v2_with_meter(&good, |_, _| Err("budget")),
        Err(RholangHostReconstructErrorV2::Meter("budget"))
    ));
    let wrong_fields = term(&profile, "Proc::PZero", vec![DynamicValue::Unit]);
    assert!(matches!(
        reconstruct_host_proc_v2_with_meter(&wrong_fields, |_, _| Ok::<(), ()>(())),
        Err(RholangHostReconstructErrorV2::Malformed)
    ));
    let wrong_root = term(
        &profile,
        "CostStack::CostStackLift",
        vec![term(&profile, "CostStackChain::CostStackChainEmpty", vec![])],
    );
    assert!(matches!(
        reconstruct_host_proc_v2_with_meter(&wrong_root, |_, _| Ok::<(), ()>(())),
        Err(RholangHostReconstructErrorV2::Malformed)
    ));
}

#[test]
fn deep_linear_selected_image_reconstructs_iteratively() {
    let profile = profile();
    let signature = quoted_signature(&profile);
    let mut tail = term(&profile, "CostStackChain::CostStackChainEmpty", vec![]);
    for _ in 0..4096 {
        tail = term(
            &profile,
            "CostStackChain::CostStackChainCons",
            vec![signature.clone(), tail],
        );
    }
    let root = term(&profile, "Proc::PCostStackCons", vec![signature, tail]);
    let decoded = reconstruct_host_proc_v2_with_meter(&root, |_, _| Ok::<(), ()>(()))
        .expect("4096-deep image reconstructs without native recursion");
    let Proc::PCostStackCons(_, ref tail) = decoded else {
        panic!("wrong root")
    };
    let mut cells = 1usize;
    let mut current = tail.as_ref();
    while let CostStackChain::CostStackChainCons(_, next) = current {
        cells += 1;
        current = next.as_ref();
    }
    assert_eq!(cells, 4097);
    assert!(matches!(current, CostStackChain::CostStackChainEmpty));
}
