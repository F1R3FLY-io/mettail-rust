//! Compiled Rholang's exact, ground-Boolean host-profile provider.
//!
//! The checked `language!` expansion supplies the roster and generated typed
//! adapter commitment. This node-side provider pins the existing AST-first
//! `BoolLit`/`GBool` transport as an additional implementation epoch. It does
//! not parse source, stringify a value, or claim the rest of Rholang's `Bool`
//! category (notably variables) is transportable.

use crate::{fold_contract::par_ground_to_proc, rholang_ast};
use mettail_grammar_core::{
    HostProfileInstallError, InstalledHostProfileGrant, InstalledLanguageTable, LanguageRights,
    ProjectionHostCodecProvider, ProjectionHostCoverageV1, ProjectionHostProfileRecordV1,
    ProjectionHostScalarCodecDescriptorV1, ProjectionHostScalarDomainV1,
    ProjectionHostScalarRouteV1, RuntimeCapabilityKey, RuntimeCapabilityManifest, RuntimeEffect,
    RuntimeLogicalCost, TheoryLiteralCarrierV1, TheorySortKindV1,
};
use mettail_languages::rholang::{Bool, Proc, RholangMetadata};
use mettail_runtime::{GeneratedSemanticKeyAbiV1, LanguageMetadata};
use models::rhoapi::Par;
use std::{collections::BTreeSet, sync::Arc};

const PROVIDER_ABI: &str = "mettail-rholang-ground-scalar-provider/1";

#[derive(Debug)]
pub enum RholangHostProfileError {
    GeneratedProfileUnavailable(Option<&'static str>),
    InvalidGeneratedRecord(String),
    UnsupportedGeneratedFragment(&'static str),
    HostLowering(rholang_ast::RholangAstLowerError),
    Install(HostProfileInstallError),
}

/// An immutable, compiled provider. Its only supported value domain is the
/// generated Rholang `Bool::BoolLit` ground fragment named by its descriptor.
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
            || payload.sorts.len() != 1
            || payload.sorts[0].name != "Bool"
            || payload.sorts[0].kind
                != (TheorySortKindV1::Syntax {
                    literal: Some(TheoryLiteralCarrierV1::Boolean),
                })
            || !payload.constructors.is_empty()
        {
            return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                "generated profile is not the exact Rholang Boolean fragment",
            ));
        }
        let descriptor: ProjectionHostScalarCodecDescriptorV1 =
            postcard::from_bytes(&payload.codec.descriptor).map_err(|error| {
                RholangHostProfileError::InvalidGeneratedRecord(error.to_string())
            })?;
        if descriptor.semantic_key_abi != Some(GeneratedSemanticKeyAbiV1::StructuralV2 as u16)
            || descriptor.entries.len() != 1
            || descriptor.entries[0].sort != "Bool"
            || descriptor.entries[0].native_type != "bool"
            || descriptor.entries[0].carrier != TheoryLiteralCarrierV1::Boolean
            || descriptor.entries[0].domain != ProjectionHostScalarDomainV1::GroundLiteralOnly
            || !matches!(
                descriptor.entries[0].route,
                ProjectionHostScalarRouteV1::SemanticTransit { .. }
            )
        {
            return Err(RholangHostProfileError::UnsupportedGeneratedFragment(
                "Boolean route, carrier, or value domain changed",
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language_install::{
        EmptyRegistrySnapshot, LanguageInstallPolicy, LanguageInstallService,
    };
    use mettail_grammar_core::{HostProfileAccessError, LanguageRight};

    #[test]
    fn generated_boolean_fragment_installs_and_round_trips_both_values() {
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
}
