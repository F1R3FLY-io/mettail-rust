use mettail_grammar_core::{
    ProjectionHostCoverageV1, ProjectionHostProfileRecordV1, ProjectionHostScalarCodecDescriptorV1,
    ProjectionHostScalarDomainV1, ProjectionHostScalarRouteV1, TheoryLiteralCarrierV1,
    TheorySortKindV1,
};
use mettail_runtime::LanguageMetadata;

#[test]
fn generated_rholang_host_profile_is_a_checked_exact_fragment() {
    let metadata = mettail_languages::rholang::RholangMetadata;
    assert_eq!(metadata.version(), Some("1.4-preview.1"));
    let bytes = metadata
        .generated_projection_host_profile_record_v1()
        .unwrap_or_else(|| {
            panic!(
                "generated host profile refused: {:?}",
                metadata.generated_projection_host_profile_refusal_v1()
            )
        });
    let record = ProjectionHostProfileRecordV1::decode_canonical(bytes).unwrap();
    assert_eq!(record.payload.language_name, "Rholang");
    assert_eq!(record.payload.language_version, "1.4-preview.1");
    assert_eq!(record.payload.coverage, ProjectionHostCoverageV1::ExactFragment);
    assert_eq!(
        record.payload.definition_fingerprint,
        metadata.definition_fingerprint().unwrap()
    );
    assert!(record.payload.sorts.iter().any(|sort| {
        sort.name == "Bool"
            && matches!(
                &sort.kind,
                TheorySortKindV1::Syntax {
                    literal: Some(TheoryLiteralCarrierV1::Boolean)
                }
            )
    }));

    let descriptor: ProjectionHostScalarCodecDescriptorV1 =
        postcard::from_bytes(&record.payload.codec.descriptor).unwrap();
    assert_eq!(descriptor.semantic_key_abi, Some(2));
    assert!(descriptor.entries.iter().any(|entry| {
        entry.sort == "Bool"
            && entry.native_type == "bool"
            && entry.carrier == TheoryLiteralCarrierV1::Boolean
            && entry.domain == ProjectionHostScalarDomainV1::GroundLiteralOnly
            && matches!(&entry.route, ProjectionHostScalarRouteV1::SemanticTransit { .. })
    }));
    assert_eq!(record.payload.digests().unwrap(), record.claimed_digests);
}
