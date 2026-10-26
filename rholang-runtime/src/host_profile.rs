//! Compiled Rholang's exact, ground-Boolean-and-String host-profile provider.
//!
//! The checked `language!` expansion supplies the roster and generated typed
//! adapter commitment. This node-side provider pins the existing AST-first
//! `BoolLit`/`GBool` and `StringLit`/`GString` transports as an additional
//! implementation epoch. It does not parse source, stringify arbitrary values,
//! or claim non-ground inhabitants of either category are transportable.

use crate::{fold_contract::par_ground_to_proc, rholang_ast};
use mettail_grammar_core::{
    HostProfileInstallError, InstalledHostProfileGrant, InstalledLanguageTable, LanguageRights,
    ProjectedLanguageCoreV1, ProjectedTheorySemanticImageV1, ProjectionHostCodecProvider,
    ProjectionHostCompoundCodecDescriptorV2, ProjectionHostCompoundCodecProviderV2,
    ProjectionHostCompoundDomainV2, ProjectionHostCompoundProfileRecordV2,
    ProjectionHostCoverageV1, ProjectionHostProfileRecordV1, ProjectionHostScalarCodecDescriptorV1,
    ProjectionHostScalarDomainV1, ProjectionHostScalarRouteV1, ProjectionHostSignatureV1,
    ProjectionImageCompiler, RuntimeCapabilityKey, RuntimeCapabilityManifest, RuntimeEffect,
    RuntimeLogicalCost, SemanticFieldSchemaV1, SemanticOperatorOriginV1,
    TheoryImageAdmissionLimits, TheoryLiteralCarrierV1, TheorySemanticImageV1, TheorySortKindV1,
};
use mettail_languages::rholang::{
    rholang_host_inverse_categories_v2, rholang_host_inverse_routes_v2,
    rholang_host_inverse_sequence_elements_v2, Bool, Proc, RholangHostInverseFieldV2,
    RholangHostInverseOriginV2, RholangMetadata, Str,
};
use mettail_runtime::{GeneratedSemanticKeyAbiV1, LanguageMetadata};
use models::rhoapi::Par;
use std::{collections::BTreeSet, sync::Arc};

const PROVIDER_ABI: &str = "mettail-rholang-ground-scalar-provider/1";
const COMPOUND_PROVIDER_ABI: &str = "mettail-rholang-compound-host-provider/2";

/// Names expected in the generated candidate. This is a consistency check,
/// not an independent binding of numeric routes to compiled reconstruction.
const COMPOUND_ROUTES: &[(&str, &str)] = &[
    ("Proc", "PZero"),
    ("Proc", "PUnit"),
    ("Proc", "PCostSignedTerm"),
    ("Proc", "PCostStackCons"),
    ("Proc", "PForCostSigned"),
    ("CostSig", "CostSigTransfer"),
    ("CostSig", "CostSigCompound"),
    ("CostSig", "CostSigGround"),
    ("CostSig", "CostSigHash"),
    ("CostStack", "CostStackLift"),
    ("CostStack", "CostStackPar"),
    ("CostStackChain", "CostStackChainEmpty"),
    ("CostStackChain", "CostStackChainCons"),
    ("CostStackChain", "CostStackChainGroup"),
    ("Name", "NQuote"),
    ("InputBind", "InputBindCostSigned"),
    ("InputBind", "InputBindCostSignedEmpty"),
    ("ForRow", "ForRowWhere"),
    ("ForRow", "ForRowNoWhere"),
    ("ForRow", "ForRowSingleWhere"),
    ("ForRow", "ForRowSingleNoWhere"),
];

/// The already-established projected theory image compiler, injected through
/// grammar-core's callback boundary to preserve dependency direction.
pub struct SharedProjectedTheoryImageCompiler;

impl ProjectionImageCompiler for SharedProjectedTheoryImageCompiler {
    fn compile_projected(
        &self,
        language: &ProjectedLanguageCoreV1,
        host: &ProjectionHostSignatureV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<(TheorySemanticImageV1, ProjectedTheorySemanticImageV1), String> {
        mettail_dovetail_runtime::compile_projected_theory_semantic_image_with_base(
            language, host, limits,
        )
        .map_err(|error| format!("{error:?}"))
    }
}

#[derive(Debug)]
pub enum RholangHostProfileError {
    GeneratedProfileUnavailable(Option<&'static str>),
    InvalidGeneratedRecord(String),
    UnsupportedGeneratedFragment(&'static str),
    HostLowering(rholang_ast::RholangAstLowerError),
    Install(HostProfileInstallError),
}

/// An immutable, compiled provider for the generated Rholang ground scalar
/// fragments named by its exact checked descriptor.
pub struct RholangHostProfileProvider {
    record: Vec<u8>,
    descriptor: Vec<u8>,
    manifest: RuntimeCapabilityManifest,
}

impl RholangHostProfileProvider {
    /// Construct solely from generated checked metadata. The provider's own
    /// code epoch is committed in addition to the generated typed adapter.
    pub fn from_generated() -> Result<Arc<Self>, RholangHostProfileError> {
        let metadata = RholangMetadata;
        let source = metadata
            .generated_projection_host_profile_record_v1()
            .ok_or_else(|| {
                RholangHostProfileError::GeneratedProfileUnavailable(
                    metadata.generated_projection_host_profile_refusal_v1(),
                )
            })?;
        let generated =
            ProjectionHostProfileRecordV1::decode_canonical(source).map_err(|error| {
                RholangHostProfileError::InvalidGeneratedRecord(format!("{error:?}"))
            })?;
        let mut payload = generated.payload;
        if payload.language_name != metadata.name()
            || payload.language_version != metadata.version().unwrap_or_default()
            || payload.definition_fingerprint
                != metadata.definition_fingerprint().unwrap_or_default()
            || payload.coverage != ProjectionHostCoverageV1::ExactFragment
            || payload.sorts.len() != 2
            || !payload.sorts.iter().any(|sort| {
                sort.name == "Bool"
                    && sort.kind
                        == TheorySortKindV1::Syntax {
                            literal: Some(TheoryLiteralCarrierV1::Boolean),
                        }
            })
            || !payload.sorts.iter().any(|sort| {
                sort.name == "Str"
                    && sort.kind
                        == TheorySortKindV1::Syntax {
                            literal: Some(TheoryLiteralCarrierV1::String),
                        }
            })
            || !payload.constructors.is_empty()
        {
            return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                "generated profile is not the exact Rholang Boolean and String fragment",
            ));
        }
        let descriptor: ProjectionHostScalarCodecDescriptorV1 =
            postcard::from_bytes(&payload.codec.descriptor).map_err(|error| {
                RholangHostProfileError::InvalidGeneratedRecord(error.to_string())
            })?;
        if descriptor.semantic_key_abi != Some(GeneratedSemanticKeyAbiV1::StructuralV2 as u16)
            || descriptor.entries.len() != 2
            || !descriptor.entries.iter().any(|entry| {
                entry.sort == "Bool"
                    && entry.native_type == "bool"
                    && entry.carrier == TheoryLiteralCarrierV1::Boolean
                    && entry.domain == ProjectionHostScalarDomainV1::GroundLiteralOnly
                    && matches!(entry.route, ProjectionHostScalarRouteV1::SemanticTransit { .. })
            })
            || !descriptor.entries.iter().any(|entry| {
                entry.sort == "Str"
                    && entry.native_type == "str"
                    && entry.carrier == TheoryLiteralCarrierV1::String
                    && entry.domain == ProjectionHostScalarDomainV1::GroundLiteralOnly
                    && matches!(entry.route, ProjectionHostScalarRouteV1::SemanticTransit { .. })
            })
        {
            return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                "Boolean or String route, carrier, or value domain changed",
            ));
        }
        // Boolean has exactly two ground inhabitants, so admission can check
        // the complete concrete round-trip domain before granting authority.
        for value in [false, true] {
            let host = Self::bool_to_host(value)?;
            if Self::bool_from_host(&host) != Some(value) {
                return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                    "compiled Boolean host codec failed its complete ground round trip",
                ));
            }
        }
        // String is infinite, so the descriptor and generated type route seal
        // the admitted domain; these witnesses exercise escaping and Unicode.
        for value in ["", "plain", "a\0b", "line\nfeed", "\"quoted\"", "λ🦀"] {
            let host = Self::string_to_host(value)?;
            if Self::string_from_host(&host).as_deref() != Some(value) {
                return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                    "compiled String host codec failed a ground round trip witness",
                ));
            }
        }
        let mut commitment = blake3::Hasher::new();
        commitment.update(b"mettail-rholang-ground-scalar-provider/1\0");
        commitment.update(&payload.codec.implementation_commitment);
        commitment.update(include_bytes!("fold_contract.rs"));
        commitment.update(include_bytes!("rholang_ast.rs"));
        commitment.update(include_bytes!("host_profile.rs"));
        commitment.update(&payload.codec.descriptor);
        payload.codec.provider_abi = PROVIDER_ABI.into();
        payload.codec.implementation_commitment = *commitment.finalize().as_bytes();
        let descriptor = payload.codec.descriptor.clone();
        let manifest = RuntimeCapabilityManifest {
            key: RuntimeCapabilityKey::structural_codec(payload.grammar_fingerprint, PROVIDER_ABI),
            code_commitment: payload.codec.implementation_commitment,
            abi: PROVIDER_ABI.into(),
            effects: BTreeSet::from([RuntimeEffect::Reflect]),
            cost: RuntimeLogicalCost {
                base: 1,
                per_input_byte: 0,
                per_value: 1,
                maximum: 2,
            },
        };
        let record = ProjectionHostProfileRecordV1::new(payload)
            .and_then(|record| record.canonical_bytes())
            .map_err(|error| {
                RholangHostProfileError::InvalidGeneratedRecord(format!("{error:?}"))
            })?;
        Ok(Arc::new(Self { record, descriptor, manifest }))
    }

    pub fn install(
        self: &Arc<Self>,
        table: &InstalledLanguageTable,
        rights: LanguageRights,
    ) -> Result<InstalledHostProfileGrant, RholangHostProfileError> {
        table
            .install_host_profile(&self.record, self.clone(), rights)
            .map_err(RholangHostProfileError::Install)
    }

    /// The exact existing generated-`BoolLit` to host-`GBool` value route.
    pub fn bool_to_host(value: bool) -> Result<Par, RholangHostProfileError> {
        let term = Proc::CastBool(Arc::new(Bool::BoolLit(value)));
        rholang_ast::lower_rholang_proc(&term).map_err(RholangHostProfileError::HostLowering)
    }

    /// The existing ground-value decoder is the inverse on this fragment.
    /// A non-Boolean or non-ground process is outside the admitted domain.
    pub fn bool_from_host(value: &Par) -> Option<bool> {
        let decoded = par_ground_to_proc(value)?;
        match &decoded {
            Proc::CastBool(term) => match term.as_ref() {
                Bool::BoolLit(value) => Some(*value),
                _ => None,
            },
            _ => None,
        }
    }

    /// The checked `Str::StringLit` to host-`GString` route. This is an exact
    /// value transport, not a formatter for arbitrary guest terms.
    pub fn string_to_host(value: &str) -> Result<Par, RholangHostProfileError> {
        let term = Proc::CastStr(Arc::new(Str::StringLit(value.to_owned())));
        rholang_ast::lower_rholang_proc(&term).map_err(RholangHostProfileError::HostLowering)
    }

    /// Inverse of `string_to_host` on the ground String fragment only.
    pub fn string_from_host(value: &Par) -> Option<String> {
        let decoded = par_ground_to_proc(value)?;
        match &decoded {
            Proc::CastStr(term) => match term.as_ref() {
                Str::StringLit(value) => Some(value.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn record(&self) -> &[u8] {
        &self.record
    }
}

impl ProjectionHostCodecProvider for RholangHostProfileProvider {
    fn compiled_record(&self) -> &[u8] {
        &self.record
    }

    fn capability_manifest(&self, key: &RuntimeCapabilityKey) -> Option<RuntimeCapabilityManifest> {
        (key == &self.manifest.key).then(|| self.manifest.clone())
    }

    fn admits_exact_descriptor(&self, descriptor: &[u8]) -> bool {
        descriptor == self.descriptor
    }
}

/// A V2 typed-route record is only a candidate for a host codec. It is not an
/// installed codec, funding verifier, projected term, or purse authority.
#[derive(Debug)]
pub enum RholangHostCompoundProfileError {
    GeneratedProfileUnavailable(Option<&'static str>),
    InvalidGeneratedRecord(String),
    UnsupportedGeneratedFragment(&'static str),
    Install(HostProfileInstallError),
}

pub struct RholangHostCompoundProfileCandidate {
    record: Vec<u8>,
    descriptor: Vec<u8>,
}

impl RholangHostCompoundProfileCandidate {
    /// Inspect generated metadata without conferring executable authority.
    /// Category IDs/tags, constructor IDs/tags, discriminants, origins, and
    /// field schemas still require independent compiled-route comparison.
    pub fn from_generated() -> Result<Arc<Self>, RholangHostCompoundProfileError> {
        use RholangHostCompoundProfileError as Error;
        let metadata = RholangMetadata;
        let bytes = metadata
            .generated_projection_host_compound_profile_record_v2()
            .ok_or_else(|| {
                Error::GeneratedProfileUnavailable(
                    metadata.generated_projection_host_compound_profile_refusal_v2(),
                )
            })?;
        let generated = ProjectionHostCompoundProfileRecordV2::decode_canonical(bytes)
            .map_err(|error| Error::InvalidGeneratedRecord(format!("{error:?}")))?;
        let payload = generated.payload;
        if payload.language_name != metadata.name()
            || payload.language_version != metadata.version().unwrap_or_default()
            || payload.definition_fingerprint
                != metadata.definition_fingerprint().unwrap_or_default()
            || payload.coverage != ProjectionHostCoverageV1::ExactFragment
            || payload.codec.descriptor.domain != ProjectionHostCompoundDomainV2::SelectedRootRoutes
            || payload.codec.descriptor.semantic_key_abi
                != GeneratedSemanticKeyAbiV1::StructuralV2 as u16
        {
            return Err(Error::UnsupportedGeneratedFragment(
                "host definition identity or selected-root ABI changed",
            ));
        }
        let expected_categories: BTreeSet<_> =
            ["Proc", "CostSig", "CostStack", "CostStackChain", "Name", "InputBind", "ForRow"]
                .into_iter()
                .collect();
        let actual_categories: BTreeSet<_> = payload
            .codec
            .descriptor
            .categories
            .iter()
            .map(|route| route.name.as_str())
            .collect();
        if actual_categories != expected_categories {
            return Err(Error::UnsupportedGeneratedFragment(
                "selected host category roster changed",
            ));
        }
        let expected_operators: BTreeSet<_> = COMPOUND_ROUTES
            .iter()
            .map(|(category, constructor)| {
                format!("{}::{category}::{constructor}", metadata.name())
            })
            .collect();
        let actual_operators: BTreeSet<_> = payload
            .codec
            .descriptor
            .operators
            .iter()
            .map(|route| route.label.clone())
            .collect();
        if actual_operators != expected_operators
            || payload.codec.descriptor.operators.len() != COMPOUND_ROUTES.len()
        {
            return Err(Error::UnsupportedGeneratedFragment(
                "selected host constructor roster changed",
            ));
        }
        let descriptor = postcard::to_allocvec(&payload.codec.descriptor)
            .map_err(|error| Error::InvalidGeneratedRecord(error.to_string()))?;
        let record = ProjectionHostCompoundProfileRecordV2::new(payload)
            .and_then(|record| record.canonical_bytes())
            .map_err(|error| Error::InvalidGeneratedRecord(format!("{error:?}")))?;
        Ok(Arc::new(Self { record, descriptor }))
    }

    pub fn candidate_record(&self) -> &[u8] {
        &self.record
    }

    pub fn matches_declared_descriptor(&self, descriptor: &[u8]) -> bool {
        descriptor == self.descriptor
    }
}

/// Executable V2 host codec. Admission compares the complete generated
/// descriptor with the separately derived typed-assembly registry, including
/// every field and list algebra. A candidate record alone grants nothing.
pub struct RholangHostCompoundProfileProviderV2 {
    record: Vec<u8>,
    descriptor: ProjectionHostCompoundCodecDescriptorV2,
    manifest: RuntimeCapabilityManifest,
}

impl RholangHostCompoundProfileProviderV2 {
    pub fn from_generated() -> Result<Arc<Self>, RholangHostCompoundProfileError> {
        use RholangHostCompoundProfileError as Error;
        let candidate = RholangHostCompoundProfileCandidate::from_generated()?;
        let generated =
            ProjectionHostCompoundProfileRecordV2::decode_canonical(candidate.candidate_record())
                .map_err(|error| Error::InvalidGeneratedRecord(format!("{error:?}")))?;
        let mut payload = generated.payload;
        let descriptor = &payload.codec.descriptor;
        if !Self::compiled_routes_match(descriptor) {
            return Err(Error::UnsupportedGeneratedFragment(
                "compiled typed host inverse differs from selected profile",
            ));
        }
        let mut commitment = blake3::Hasher::new();
        commitment.update(b"mettail-rholang-compound-host-provider/2\0");
        commitment.update(&payload.codec.implementation_commitment);
        commitment
            .update(include_bytes!("../../macros/src/gen/runtime/dovetail_report/reconstruct.rs"));
        commitment.update(include_bytes!("semantic_service/funding_projection.rs"));
        commitment.update(include_bytes!("rholang_ast.rs"));
        payload.codec.provider_abi = COMPOUND_PROVIDER_ABI.into();
        payload.codec.implementation_commitment = *commitment.finalize().as_bytes();
        let manifest = RuntimeCapabilityManifest {
            key: RuntimeCapabilityKey::structural_codec(
                payload.grammar_fingerprint,
                COMPOUND_PROVIDER_ABI,
            ),
            code_commitment: payload.codec.implementation_commitment,
            abi: COMPOUND_PROVIDER_ABI.into(),
            effects: BTreeSet::from([RuntimeEffect::Reflect]),
            cost: RuntimeLogicalCost {
                base: 1,
                per_input_byte: 0,
                per_value: 1,
                maximum: u64::MAX,
            },
        };
        let descriptor = payload.codec.descriptor.clone();
        let record = ProjectionHostCompoundProfileRecordV2::new(payload)
            .and_then(|record| record.canonical_bytes())
            .map_err(|error| Error::InvalidGeneratedRecord(format!("{error:?}")))?;
        Ok(Arc::new(Self { record, descriptor, manifest }))
    }

    fn compiled_routes_match(descriptor: &ProjectionHostCompoundCodecDescriptorV2) -> bool {
        let categories = rholang_host_inverse_categories_v2();
        let routes = rholang_host_inverse_routes_v2();
        let sequences = rholang_host_inverse_sequence_elements_v2();
        if categories.len() != descriptor.categories.len()
            || routes.len() != descriptor.operators.len()
            || sequences.len() != descriptor.sequences.len()
        {
            return false;
        }
        if !categories
            .iter()
            .zip(&descriptor.categories)
            .all(|(compiled, declared)| {
                compiled.category == declared.category
                    && compiled.name == declared.name
                    && compiled.generated_category_tag == declared.generated_category_tag
            })
        {
            return false;
        }
        if !routes
            .iter()
            .zip(&descriptor.operators)
            .all(|(compiled, declared)| {
                compiled.operator == declared.operator
                    && compiled.category == declared.category
                    && compiled.constructor == declared.constructor
                    && compiled.generated_category_tag
                        == categories
                            .iter()
                            .find(|category| category.category == declared.category)
                            .map(|category| category.generated_category_tag)
                            .unwrap_or(u32::MAX)
                    && compiled.generated_constructor_tag == declared.generated_constructor_tag
                    && compiled.stable_discriminant == declared.stable_discriminant
                    && compiled.label == declared.label
                    && match (compiled.origin, &declared.origin) {
                        (
                            RholangHostInverseOriginV2::GrammarProduction(actual),
                            SemanticOperatorOriginV1::GrammarProduction(expected),
                        ) => actual == expected.0,
                        (
                            RholangHostInverseOriginV2::Generated { family, ordinal },
                            SemanticOperatorOriginV1::Generated {
                                family: expected,
                                ordinal: expected_ordinal,
                            },
                        ) => family == expected && ordinal == *expected_ordinal,
                        _ => false,
                    }
                    && compiled.fields.len() == declared.fields.len()
                    && compiled
                        .fields
                        .iter()
                        .zip(&declared.fields)
                        .all(|(field, expected)| match (field, expected) {
                            (
                                RholangHostInverseFieldV2::Child(actual),
                                SemanticFieldSchemaV1::Child { category },
                            ) => actual == category,
                            (
                                RholangHostInverseFieldV2::Sequence(actual),
                                SemanticFieldSchemaV1::Sequence { element },
                            ) => actual == element,
                            _ => false,
                        })
            })
        {
            return false;
        }
        sequences
            .iter()
            .zip(&descriptor.sequences)
            .all(|(element, declared)| {
                let Some(category) = descriptor
                    .categories
                    .iter()
                    .find(|route| route.category == *element)
                else {
                    return false;
                };
                let sort = format!("Rholang::Sequence::{}", category.name);
                *element == declared.element
                    && declared.sort_name == sort
                    && declared.nil_name == format!("{sort}::Nil")
                    && declared.cons_name == format!("{sort}::Cons")
            })
    }

    pub fn install(
        self: &Arc<Self>,
        table: &InstalledLanguageTable,
        rights: LanguageRights,
    ) -> Result<InstalledHostProfileGrant, RholangHostCompoundProfileError> {
        table
            .install_compound_host_profile_v2(&self.record, self.clone(), rights)
            .map_err(RholangHostCompoundProfileError::Install)
    }

    pub fn compiled_record(&self) -> &[u8] {
        &self.record
    }
}

impl ProjectionHostCompoundCodecProviderV2 for RholangHostCompoundProfileProviderV2 {
    fn compiled_record(&self) -> &[u8] {
        &self.record
    }

    fn capability_manifest(&self, key: &RuntimeCapabilityKey) -> Option<RuntimeCapabilityManifest> {
        (key == &self.manifest.key).then(|| self.manifest.clone())
    }

    fn admits_exact_descriptor(
        &self,
        descriptor: &ProjectionHostCompoundCodecDescriptorV2,
    ) -> bool {
        descriptor == &self.descriptor && Self::compiled_routes_match(descriptor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language_install::{
        EmptyRegistrySnapshot, LanguageInstallPolicy, LanguageInstallService,
    };
    use mettail_grammar_core::{
        HostProfileAccessError, LanguageRight, ProjectionHostCompoundCodecDescriptorV2,
        ProjectionHostCompoundCodecProviderV2,
    };

    // A test-only provider exercises table epochs and ABI separation. It is
    // deliberately not a production typed reconstruction implementation.
    struct TableTestCompoundProvider {
        record: Vec<u8>,
        descriptor: ProjectionHostCompoundCodecDescriptorV2,
        manifest: RuntimeCapabilityManifest,
    }

    impl ProjectionHostCompoundCodecProviderV2 for TableTestCompoundProvider {
        fn compiled_record(&self) -> &[u8] {
            &self.record
        }

        fn capability_manifest(
            &self,
            key: &RuntimeCapabilityKey,
        ) -> Option<RuntimeCapabilityManifest> {
            (key == &self.manifest.key).then(|| self.manifest.clone())
        }

        fn admits_exact_descriptor(
            &self,
            descriptor: &ProjectionHostCompoundCodecDescriptorV2,
        ) -> bool {
            descriptor == &self.descriptor
        }
    }

    #[test]
    fn generated_compound_fragment_is_a_non_authoritative_candidate() {
        let provider = RholangHostCompoundProfileCandidate::from_generated().unwrap();
        assert!(
            ProjectionHostProfileRecordV1::decode_canonical(provider.candidate_record()).is_err(),
            "a V2 compound candidate cannot enter the V1 installed host-profile route"
        );
        let record =
            ProjectionHostCompoundProfileRecordV2::decode_canonical(provider.candidate_record())
                .unwrap();
        assert_eq!(record.payload.language_version, "1.4-preview.1");
        assert_eq!(record.payload.codec.provider_abi, "mettail-generated-compound-host-provider/2");
        assert_eq!(
            record.payload.codec.descriptor.domain,
            ProjectionHostCompoundDomainV2::SelectedRootRoutes
        );
        assert_eq!(record.payload.codec.descriptor.operators.len(), COMPOUND_ROUTES.len());
        assert!(provider.matches_declared_descriptor(
            &postcard::to_allocvec(&record.payload.codec.descriptor).unwrap()
        ));
        let mut forged_descriptor =
            postcard::to_allocvec(&record.payload.codec.descriptor).unwrap();
        forged_descriptor.push(0);
        assert!(!provider.matches_declared_descriptor(&forged_descriptor));
        let scalar = RholangHostProfileProvider::from_generated().unwrap();
        assert_ne!(provider.candidate_record(), scalar.record());
    }

    #[test]
    fn compiled_compound_provider_binds_exact_typed_inverse_roster() {
        let provider = RholangHostCompoundProfileProviderV2::from_generated()
            .expect("compiled typed inverse must match generated route descriptor");
        let record =
            ProjectionHostCompoundProfileRecordV2::decode_canonical(provider.compiled_record())
                .expect("provider record is canonical");
        assert_eq!(record.payload.codec.provider_abi, COMPOUND_PROVIDER_ABI);
        assert!(provider.admits_exact_descriptor(&record.payload.codec.descriptor));

        let mut altered = record.payload.codec.descriptor.clone();
        altered.operators[0].generated_constructor_tag ^= 1;
        assert!(!provider.admits_exact_descriptor(&altered));
        let mut altered = record.payload.codec.descriptor.clone();
        altered.sequences[0].cons_name.push_str("-forged");
        assert!(!provider.admits_exact_descriptor(&altered));

        let table = InstalledLanguageTable::new();
        let rights =
            LanguageRights::from_rights([LanguageRight::Bridge, LanguageRight::ReflectAst]);
        let grant = provider
            .install(&table, rights)
            .expect("trusted codec installs");
        assert!(table
            .authorize_host_profile(&grant.handle, &[LanguageRight::Bridge])
            .is_ok());
    }

    #[test]
    fn factored_cost_stack_routes_are_admitted_by_the_compound_provider() {
        let provider = RholangHostCompoundProfileProviderV2::from_generated()
            .expect("factored CostStack and CostStackChain routes must be compiled");
        let record =
            ProjectionHostCompoundProfileRecordV2::decode_canonical(provider.compiled_record())
                .expect("provider record is canonical");
        let descriptor = &record.payload.codec.descriptor;
        let categories: BTreeSet<_> = descriptor
            .categories
            .iter()
            .map(|route| route.name.as_str())
            .collect();
        assert!(categories.contains("CostStackChain"));
        let stack_routes: BTreeSet<_> = descriptor
            .operators
            .iter()
            .filter_map(|route| route.label.strip_prefix("Rholang::CostStack::"))
            .collect();
        assert_eq!(stack_routes, BTreeSet::from(["CostStackLift", "CostStackPar"]));
        let chain_routes: BTreeSet<_> = descriptor
            .operators
            .iter()
            .filter_map(|route| route.label.strip_prefix("Rholang::CostStackChain::"))
            .collect();
        assert_eq!(
            chain_routes,
            BTreeSet::from([
                "CostStackChainEmpty",
                "CostStackChainCons",
                "CostStackChainGroup",
            ])
        );
    }

    #[test]
    fn scalar_and_compound_host_profile_epochs_are_separate() {
        let table = InstalledLanguageTable::new();
        let rights = LanguageRights::from_rights([LanguageRight::Bridge]);
        let scalar = RholangHostProfileProvider::from_generated().unwrap();
        let scalar_grant = scalar.install(&table, rights.clone()).unwrap();
        let candidate = RholangHostCompoundProfileCandidate::from_generated().unwrap();
        let record =
            ProjectionHostCompoundProfileRecordV2::decode_canonical(candidate.candidate_record())
                .unwrap();
        let key = RuntimeCapabilityKey::structural_codec(
            record.payload.grammar_fingerprint,
            record.payload.codec.provider_abi.clone(),
        );
        let provider = Arc::new(TableTestCompoundProvider {
            record: candidate.candidate_record().to_vec(),
            descriptor: record.payload.codec.descriptor.clone(),
            manifest: RuntimeCapabilityManifest {
                key,
                code_commitment: record.payload.codec.implementation_commitment,
                abi: record.payload.codec.provider_abi.clone(),
                effects: BTreeSet::from([RuntimeEffect::Reflect]),
                cost: RuntimeLogicalCost {
                    base: 1,
                    per_input_byte: 0,
                    per_value: 1,
                    maximum: 2,
                },
            },
        });
        let compound = table
            .install_compound_host_profile_v2(candidate.candidate_record(), provider, rights)
            .unwrap();
        assert!(table
            .authorize_host_profile(&scalar_grant.handle, &[LanguageRight::Bridge])
            .is_ok());
        assert!(table
            .authorize_compound_host_profile_v2(&compound.handle, &[LanguageRight::Bridge])
            .is_ok());
        assert!(matches!(
            table.authorize_host_profile(&compound.handle, &[LanguageRight::Bridge]),
            Err(HostProfileAccessError::WrongProfileVersion)
        ));
        assert!(matches!(
            table
                .authorize_compound_host_profile_v2(&scalar_grant.handle, &[LanguageRight::Bridge]),
            Err(HostProfileAccessError::WrongProfileVersion)
        ));
        table.revoke_host_profile(compound.revocation).unwrap();
        assert!(matches!(
            table.authorize_compound_host_profile_v2(&compound.handle, &[LanguageRight::Bridge]),
            Err(HostProfileAccessError::Revoked)
        ));
        assert!(table
            .authorize_host_profile(&scalar_grant.handle, &[LanguageRight::Bridge])
            .is_ok());
    }

    #[test]
    fn generated_scalar_fragment_installs_and_round_trips_ground_values() {
        let provider = RholangHostProfileProvider::from_generated().unwrap();
        let record = ProjectionHostProfileRecordV1::decode_canonical(provider.record()).unwrap();
        assert_eq!(record.payload.language_version, "1.4-preview.1");
        let table = InstalledLanguageTable::new();
        let grant = provider
            .install(
                &table,
                LanguageRights::from_rights([LanguageRight::Bridge, LanguageRight::ReflectAst]),
            )
            .unwrap();
        let selected = table
            .authorize_host_profile(&grant.handle, &[LanguageRight::Bridge])
            .unwrap();
        assert_eq!(selected.record(), &record);
        for value in [false, true] {
            let host = RholangHostProfileProvider::bool_to_host(value).unwrap();
            assert_eq!(RholangHostProfileProvider::bool_from_host(&host), Some(value));
        }
        for value in ["", "plain", "a\0b", "line\nfeed", "\"quoted\"", "λ🦀"] {
            let host = RholangHostProfileProvider::string_to_host(value).unwrap();
            assert_eq!(RholangHostProfileProvider::string_from_host(&host).as_deref(), Some(value));
            assert_eq!(RholangHostProfileProvider::bool_from_host(&host), None);
        }
        table.revoke_host_profile(grant.revocation).unwrap();
        assert!(matches!(
            table.authorize_host_profile(&grant.handle, &[LanguageRight::Bridge]),
            Err(HostProfileAccessError::Revoked)
        ));
    }

    #[test]
    fn service_binds_compiled_host_without_source_supplied_authority() {
        let registry = Arc::new(EmptyRegistrySnapshot);
        let service =
            LanguageInstallService::new(registry.clone(), LanguageInstallPolicy::default());
        let (handle, snapshot) = service.builtin_host_profile_binding().unwrap();
        assert_eq!(handle.fingerprint(), snapshot.record().claimed_digests.profile_fingerprint);
        assert_eq!(snapshot.record().payload.language_name, "Rholang");
        assert_eq!(service.installed_count().unwrap(), 0, "host profile is not a guest language");

        let no_bridge = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::ReflectAst]),
            mettail_grammar_core::RuntimePolicy::default(),
            crate::language_install::LANGUAGE_CAPABILITY_ABI_CURRENT,
        );
        let restricted = LanguageInstallService::new(registry, no_bridge);
        assert!(restricted.builtin_host_profile_binding().is_err());
    }

    #[test]
    fn projected_guest_uses_shared_parser_and_selected_semantic_image() {
        use mettail_grammar_core::{DefaultRuntimeHost, ExecutableProjectedLanguageInstall};
        use mettail_prattail::runtime_backend::{
            compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI,
        };
        let service = LanguageInstallService::new(
            Arc::new(EmptyRegistrySnapshot),
            LanguageInstallPolicy::default(),
        );
        let (host_handle, host) = service.builtin_host_profile_binding().unwrap();
        let signature = host.raw_signature().unwrap();
        let source = r#"
            Module Predicate {
              Theory T() {
                Types { noadmit Bool = bool; }
                Terms {
                  BTrue . |- "yes" : Bool;
                  BFalse . |- "no" : Bool;
                }
                Rewrites { projection Boolean : Bool <~> host::Bool via carrier; }
              }
              theory T()
            }
        "#;
        let module = mettail_elab::parse::parse_module(source).unwrap();
        let resolver = mettail_elab::resolve::MemResolver::new().with("Predicate.module", source);
        let elaborated =
            mettail_elab::elaborate_module_ast_with_host(module, &resolver, &signature).unwrap();
        let projected = elaborated
            .exports
            .into_iter()
            .next()
            .unwrap()
            .language
            .projected_language_core
            .unwrap();
        let parser = compile_parser_image(&projected.base.grammar).unwrap();
        let policy = service.policy();
        let grants = service
            .table()
            .install_projected_runtime_batch_with_artifact_limits_and_host(
                vec![ExecutableProjectedLanguageInstall {
                    projected,
                    parser_image: parser,
                    host_profile: host_handle,
                    granted_rights: LanguageRights::from_rights([
                        LanguageRight::Parse,
                        LanguageRight::Bridge,
                        LanguageRight::Reduce,
                    ]),
                }],
                RUNTIME_COMPILER_ABI,
                RUNTIME_UNICODE_ABI,
                &policy.capability_abi,
                policy.fingerprint,
                policy.parser_image,
                policy.semantic_image,
                &DefaultRuntimeHost,
            )
            .unwrap();
        let installed = service
            .table()
            .authorize_all(&grants[0].handle, &[LanguageRight::Parse])
            .unwrap();
        let image = installed
            .projected_image()
            .expect("projected image survives installation");
        let sealed = installed
            .verified_projected_image()
            .expect("installed image has one sealed execution fingerprint");
        assert!(sealed.same_image(image));
        assert_eq!(sealed.execution_fingerprint(), image.execution.fingerprint().unwrap());
        let equal_but_foreign = image.clone();
        assert_eq!(equal_but_foreign, *image);
        assert!(
            !sealed.same_image(&equal_but_foreign),
            "a structurally equal caller image cannot use the installed fast path"
        );
        let base_image = installed
            .base_semantic_image()
            .expect("compiled base is retained");
        assert_eq!(image.base_image_fingerprint, base_image.fingerprint().unwrap());
        assert_eq!(image.base_rule_count as usize, base_image.rules.len());
        assert_eq!(image.execution.rules[..base_image.rules.len()], base_image.rules);
        assert!(installed.cost_image().is_none(), "uncosted projection stays uncosted");
        assert!(
            installed.funding_projection_v2().is_none(),
            "V1 projection is not funding authority"
        );
        assert_eq!(installed.commitment().funding_selector_fingerprint, None);
        assert_eq!(image.execution.language_fingerprint, grants[0].handle.fingerprint());
        assert_eq!(
            installed.commitment().projected_language_fingerprint,
            Some(grants[0].handle.fingerprint())
        );
        assert_eq!(
            installed.commitment().host_profile_fingerprint,
            Some(host.record().claimed_digests.profile_fingerprint)
        );
        assert_eq!(installed.projected_core().unwrap().base, *installed.language_core());
    }

    #[test]
    fn rholang_service_installs_parsed_projected_module_without_reparsing() {
        use crate::language_install::InstallCandidate;
        use mettail_elab::wire::ParsedDdl;
        let service = LanguageInstallService::new(
            Arc::new(EmptyRegistrySnapshot),
            LanguageInstallPolicy::default(),
        );
        let source = r#"
            Module Predicate {
              Theory T() {
                Types { noadmit Bool = bool; }
                Terms {
                  BTrue . |- "yes" : Bool;
                  BFalse . |- "no" : Bool;
                }
                Rewrites { projection Boolean : Bool <~> host::Bool via carrier; }
              }
              theory T()
            }
        "#;
        let module = mettail_elab::parse::parse_module(source).unwrap();
        let receipt = service
            .install_all(InstallCandidate::Ddl(ParsedDdl::Module(module)))
            .unwrap();
        assert_eq!(receipt.exports.len(), 1);
        let installed = service
            .table()
            .authorize_all(&receipt.exports[0].receipt.handle, &[LanguageRight::Parse])
            .unwrap();
        assert!(installed.projected_image().is_some());
        assert_eq!(
            receipt.exports[0].receipt.semantic_cache_disposition,
            mettail_elab::registry::SemanticCacheDisposition::ProjectedCompiled
        );
    }

    #[test]
    fn projected_and_ordinary_exports_commit_in_one_module_batch() {
        use crate::language_install::InstallCandidate;
        use mettail_elab::wire::ParsedDdl;
        let service = LanguageInstallService::new(
            Arc::new(EmptyRegistrySnapshot),
            LanguageInstallPolicy::default(),
        );
        let source = r#"
            Module Mixed {
              Theory Predicate() {
                Types { noadmit Bool = bool; }
                Terms { BTrue . |- "yes" : Bool; BFalse . |- "no" : Bool; }
                Rewrites { projection Boolean : Bool <~> host::Bool via carrier; }
              }
              Theory Plain() {
                Types { P; }
                Terms { P0 . |- "p" : P; }
              }
              theory Predicate()
              theory Plain()
            }
        "#;
        let module = mettail_elab::parse::parse_module(source).unwrap();
        let batch = service
            .install_all(InstallCandidate::Ddl(ParsedDdl::Module(module)))
            .unwrap();
        assert_eq!(batch.exports.len(), 2);
        assert_eq!(service.installed_count().unwrap(), 2);
        for (ordinal, projected) in [(0, true), (1, false)] {
            let installed = service
                .table()
                .authorize_all(&batch.exports[ordinal].receipt.handle, &[LanguageRight::Parse])
                .unwrap();
            assert_eq!(installed.projected_image().is_some(), projected);
        }
    }
}
