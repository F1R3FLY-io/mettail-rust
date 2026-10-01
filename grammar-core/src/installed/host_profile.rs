//! Sealed admission of checked host profiles into the existing installation
//! table. Profile bytes and fingerprints are data; only a live table handle
//! bound to an independently compiled provider conveys authority.

use super::*;
use crate::{
    ProjectionHostProfileErrorV1, ProjectionHostProfileRecordV1, ProjectionHostSignatureV1,
    RuntimeCapabilityKey, RuntimeCapabilityManifest, RuntimeCapabilityRequirement,
};

/// Implemented by trusted node code, not by a Theory/Module source value.
/// The implementation must reject descriptors for which its executable codec
/// is not exact. `compiled_record` is emitted with that implementation from a
/// checked language definition; merely supplying matching source bytes is not
/// sufficient to implement this trait in a Rholang application.
pub trait ProjectionHostCodecProvider: Send + Sync {
    fn compiled_record(&self) -> &[u8];
    fn capability_manifest(&self, key: &RuntimeCapabilityKey) -> Option<RuntimeCapabilityManifest>;
    fn admits_exact_descriptor(&self, descriptor: &[u8]) -> bool;
}

#[derive(Clone)]
pub struct InstalledHostProfileHandle {
    registry_id: u64,
    entry_id: u64,
    epoch: u64,
    fingerprint: [u8; 32],
    rights: LanguageRights,
    seal: Arc<HandleSeal>,
}

impl InstalledHostProfileHandle {
    pub fn fingerprint(&self) -> [u8; 32] {
        self.fingerprint
    }

    pub fn rights(&self) -> &LanguageRights {
        &self.rights
    }

    pub fn attenuate(&self, requested: &LanguageRights) -> Self {
        let mut reduced = self.clone();
        reduced.rights = self.rights.attenuate(requested);
        reduced
    }
}

impl fmt::Debug for InstalledHostProfileHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("InstalledHostProfileHandle")
            .field("fingerprint", &self.fingerprint)
            .field("rights", &self.rights)
            .finish_non_exhaustive()
    }
}

impl PartialEq for InstalledHostProfileHandle {
    fn eq(&self, other: &Self) -> bool {
        self.registry_id == other.registry_id
            && self.entry_id == other.entry_id
            && self.epoch == other.epoch
            && self.fingerprint == other.fingerprint
            && self.rights == other.rights
            && Arc::ptr_eq(&self.seal, &other.seal)
    }
}

impl Eq for InstalledHostProfileHandle {}

pub struct HostProfileRevocationAuthority {
    registry_id: u64,
    entry_id: u64,
    fingerprint: [u8; 32],
    seal: Arc<HandleSeal>,
}

impl fmt::Debug for HostProfileRevocationAuthority {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("HostProfileRevocationAuthority")
            .field("fingerprint", &self.fingerprint)
            .finish_non_exhaustive()
    }
}

#[derive(Debug)]
pub struct InstalledHostProfileGrant {
    pub handle: InstalledHostProfileHandle,
    pub revocation: HostProfileRevocationAuthority,
}

#[derive(Clone, Debug)]
pub struct InstalledHostProfileSnapshot {
    record: Arc<ProjectionHostProfileRecordV1>,
    manifest: RuntimeCapabilityManifest,
}

impl InstalledHostProfileSnapshot {
    pub fn record(&self) -> &ProjectionHostProfileRecordV1 {
        &self.record
    }

    pub fn manifest(&self) -> &RuntimeCapabilityManifest {
        &self.manifest
    }

    pub fn raw_signature(&self) -> Result<ProjectionHostSignatureV1, ProjectionHostProfileErrorV1> {
        self.record.payload.raw_signature()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostProfileInstallError {
    InvalidRecord(ProjectionHostProfileErrorV1),
    ProviderRecordMismatch,
    ProviderCodecRefused,
    Capability(RuntimeCapabilityError),
    ManifestMismatch,
    ProviderChanged,
    InvalidRights,
    ConflictingVersion,
    IdentifierExhausted,
    Poisoned,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostProfileAccessError {
    UnknownHandle,
    Revoked,
    InsufficientRights,
    ProviderChanged,
    Poisoned,
}

pub(super) struct HostProfileEntry {
    pub(super) record: Arc<ProjectionHostProfileRecordV1>,
    manifest: RuntimeCapabilityManifest,
    provider: Arc<dyn ProjectionHostCodecProvider>,
    ceiling: LanguageRights,
    entry_id: u64,
    epoch: u64,
    seal: Arc<HandleSeal>,
    revoked: bool,
}

impl HostProfileEntry {
    pub(super) fn authorizes(
        &self,
        registry_id: u64,
        handle: &InstalledHostProfileHandle,
        right: LanguageRight,
    ) -> bool {
        !self.revoked
            && handle.registry_id == registry_id
            && handle.entry_id == self.entry_id
            && handle.epoch == self.epoch
            && Arc::ptr_eq(&handle.seal, &self.seal)
            && handle.rights.is_subset_of(&self.ceiling)
            && handle.rights.contains(right)
            && self
                .record
                .canonical_bytes()
                .is_ok_and(|bytes| self.provider.compiled_record() == bytes)
            && self
                .provider
                .admits_exact_descriptor(&self.record.payload.codec.descriptor)
            && self.provider.capability_manifest(&self.manifest.key) == Some(self.manifest.clone())
    }

    fn grant(&self, registry_id: u64, fingerprint: [u8; 32]) -> InstalledHostProfileGrant {
        InstalledHostProfileGrant {
            handle: InstalledHostProfileHandle {
                registry_id,
                entry_id: self.entry_id,
                epoch: self.epoch,
                fingerprint,
                rights: self.ceiling.clone(),
                seal: Arc::clone(&self.seal),
            },
            revocation: HostProfileRevocationAuthority {
                registry_id,
                entry_id: self.entry_id,
                fingerprint,
                seal: Arc::clone(&self.seal),
            },
        }
    }
}

impl InstalledLanguageTable {
    /// Verify data claims and compiled-provider evidence before entering the
    /// write lock. The final nominal-version conflict check and publication
    /// share the same lock as language installation.
    pub fn install_host_profile(
        &self,
        record_bytes: &[u8],
        provider: Arc<dyn ProjectionHostCodecProvider>,
        granted_rights: LanguageRights,
    ) -> Result<InstalledHostProfileGrant, HostProfileInstallError> {
        if !granted_rights
            .iter()
            .all(|right| matches!(right, LanguageRight::Bridge | LanguageRight::ReflectAst))
        {
            return Err(HostProfileInstallError::InvalidRights);
        }
        let record = ProjectionHostProfileRecordV1::decode_canonical(record_bytes)
            .map_err(HostProfileInstallError::InvalidRecord)?;
        let compiled = ProjectionHostProfileRecordV1::decode_canonical(provider.compiled_record())
            .map_err(HostProfileInstallError::InvalidRecord)?;
        if compiled != record {
            return Err(HostProfileInstallError::ProviderRecordMismatch);
        }
        if !provider.admits_exact_descriptor(&record.payload.codec.descriptor) {
            return Err(HostProfileInstallError::ProviderCodecRefused);
        }
        let key = RuntimeCapabilityKey::structural_codec(
            record.payload.grammar_fingerprint,
            record.payload.codec.provider_abi.clone(),
        );
        let requirement = RuntimeCapabilityRequirement {
            key: key.clone(),
            effect: RuntimeEffect::Reflect,
        };
        let bindings = RuntimeCapabilityBindings::bind(&[requirement], |requested| {
            provider.capability_manifest(requested)
        })
        .map_err(HostProfileInstallError::Capability)?;
        let manifest = bindings
            .get(&key)
            .cloned()
            .ok_or(HostProfileInstallError::ManifestMismatch)?;
        if manifest.abi != record.payload.codec.provider_abi
            || manifest.code_commitment != record.payload.codec.implementation_commitment
        {
            return Err(HostProfileInstallError::ManifestMismatch);
        }

        let fingerprint = record.claimed_digests.profile_fingerprint;
        let mut state = self
            .state
            .write()
            .map_err(|_| HostProfileInstallError::Poisoned)?;
        // The capability binder already compares two provider snapshots. Also
        // recheck at publication, so a provider that changed while validation
        // was in flight cannot publish a stale binding.
        if provider.compiled_record() != record_bytes
            || !provider.admits_exact_descriptor(&record.payload.codec.descriptor)
            || provider.capability_manifest(&manifest.key) != Some(manifest.clone())
        {
            return Err(HostProfileInstallError::ProviderChanged);
        }
        if state
            .host_profiles
            .iter()
            .any(|(existing_fingerprint, existing)| {
                !existing.revoked
                    && *existing_fingerprint != fingerprint
                    && existing.record.payload.language_name == record.payload.language_name
                    && existing.record.payload.language_version == record.payload.language_version
            })
        {
            return Err(HostProfileInstallError::ConflictingVersion);
        }
        if let Some(existing) = state.host_profiles.get(&fingerprint) {
            if !existing.revoked {
                if *existing.record != record
                    || existing.manifest != manifest
                    || existing.ceiling != granted_rights
                    || !Arc::ptr_eq(&existing.provider, &provider)
                {
                    return Err(HostProfileInstallError::ConflictingVersion);
                }
                return Ok(existing.grant(self.registry_id, fingerprint));
            }
        }
        let epoch = state
            .host_profiles
            .get(&fingerprint)
            .map_or(Ok(1u64), |old| {
                old.epoch
                    .checked_add(1)
                    .ok_or(HostProfileInstallError::IdentifierExhausted)
            })?;
        let entry_id = state.next_entry_id;
        state.next_entry_id = state
            .next_entry_id
            .checked_add(1)
            .ok_or(HostProfileInstallError::IdentifierExhausted)?;
        let entry = HostProfileEntry {
            record: Arc::new(record),
            manifest,
            provider,
            ceiling: granted_rights,
            entry_id,
            epoch,
            seal: Arc::new(HandleSeal),
            revoked: false,
        };
        let grant = entry.grant(self.registry_id, fingerprint);
        state.host_profiles.insert(fingerprint, entry);
        Ok(grant)
    }

    /// Return a snapshot only for a live, sealed, sufficiently authorized
    /// handle. Users must call this again immediately before publishing a
    /// result, because revocation can occur after the snapshot is obtained.
    pub fn authorize_host_profile(
        &self,
        handle: &InstalledHostProfileHandle,
        required: &[LanguageRight],
    ) -> Result<InstalledHostProfileSnapshot, HostProfileAccessError> {
        let state = self
            .state
            .read()
            .map_err(|_| HostProfileAccessError::Poisoned)?;
        let entry = state
            .host_profiles
            .get(&handle.fingerprint)
            .ok_or(HostProfileAccessError::UnknownHandle)?;
        if handle.registry_id != self.registry_id
            || handle.entry_id != entry.entry_id
            || handle.epoch != entry.epoch
            || !Arc::ptr_eq(&handle.seal, &entry.seal)
        {
            return Err(HostProfileAccessError::UnknownHandle);
        }
        if entry.revoked {
            return Err(HostProfileAccessError::Revoked);
        }
        if !handle.rights.is_subset_of(&entry.ceiling)
            || required.iter().any(|right| !handle.rights.contains(*right))
        {
            return Err(HostProfileAccessError::InsufficientRights);
        }
        if entry.provider.compiled_record()
            != entry
                .record
                .canonical_bytes()
                .map_err(|_| HostProfileAccessError::ProviderChanged)?
            || !entry
                .provider
                .admits_exact_descriptor(&entry.record.payload.codec.descriptor)
            || entry.provider.capability_manifest(&entry.manifest.key)
                != Some(entry.manifest.clone())
        {
            return Err(HostProfileAccessError::ProviderChanged);
        }
        Ok(InstalledHostProfileSnapshot {
            record: Arc::clone(&entry.record),
            manifest: entry.manifest.clone(),
        })
    }

    pub fn revoke_host_profile(
        &self,
        authority: HostProfileRevocationAuthority,
    ) -> Result<(), HostProfileAccessError> {
        let mut state = self
            .state
            .write()
            .map_err(|_| HostProfileAccessError::Poisoned)?;
        let entry = state
            .host_profiles
            .get_mut(&authority.fingerprint)
            .ok_or(HostProfileAccessError::UnknownHandle)?;
        if authority.registry_id != self.registry_id
            || authority.entry_id != entry.entry_id
            || !Arc::ptr_eq(&authority.seal, &entry.seal)
        {
            return Err(HostProfileAccessError::UnknownHandle);
        }
        if entry.revoked {
            return Err(HostProfileAccessError::Revoked);
        }
        entry.revoked = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ProjectionHostCodecProfileV1, ProjectionHostCoverageV1, ProjectionHostProfilePayloadV1,
        RuntimeLogicalCost, TheorySortKindV1, TheorySortV1, PROJECTION_HOST_CODEC_ABI_V1,
        PROJECTION_HOST_PROFILE_ABI_V1,
    };

    struct TestProvider {
        record: Vec<u8>,
        manifest: Mutex<Option<RuntimeCapabilityManifest>>,
        descriptor: Vec<u8>,
    }

    impl ProjectionHostCodecProvider for TestProvider {
        fn compiled_record(&self) -> &[u8] {
            &self.record
        }

        fn capability_manifest(
            &self,
            key: &RuntimeCapabilityKey,
        ) -> Option<RuntimeCapabilityManifest> {
            self.manifest
                .lock()
                .unwrap()
                .as_ref()
                .filter(|m| &m.key == key)
                .cloned()
        }

        fn admits_exact_descriptor(&self, descriptor: &[u8]) -> bool {
            descriptor == self.descriptor
        }
    }

    fn fixture() -> (Vec<u8>, Arc<TestProvider>) {
        let record = ProjectionHostProfileRecordV1::new(ProjectionHostProfilePayloadV1 {
            profile_abi: PROJECTION_HOST_PROFILE_ABI_V1,
            language_name: "Rholang".into(),
            language_version: "1.4-preview.1".into(),
            definition_fingerprint: "checked-fixture".into(),
            grammar_fingerprint: [3; 32],
            coverage: ProjectionHostCoverageV1::ExactFragment,
            sorts: vec![TheorySortV1 {
                name: "Bool".into(),
                kind: TheorySortKindV1::Syntax {
                    literal: Some(crate::TheoryLiteralCarrierV1::Boolean),
                },
            }],
            constructors: vec![],
            codec: ProjectionHostCodecProfileV1 {
                codec_abi: PROJECTION_HOST_CODEC_ABI_V1,
                provider_abi: "checked-provider/1".into(),
                implementation_commitment: [4; 32],
                descriptor: vec![1, 2, 3],
            },
        })
        .unwrap();
        let key = RuntimeCapabilityKey::structural_codec(
            record.payload.grammar_fingerprint,
            record.payload.codec.provider_abi.clone(),
        );
        let provider = Arc::new(TestProvider {
            record: record.canonical_bytes().unwrap(),
            manifest: Mutex::new(Some(RuntimeCapabilityManifest {
                key,
                code_commitment: record.payload.codec.implementation_commitment,
                abi: record.payload.codec.provider_abi.clone(),
                effects: [RuntimeEffect::Reflect].into(),
                cost: RuntimeLogicalCost::default(),
            })),
            descriptor: record.payload.codec.descriptor.clone(),
        });
        (provider.record.clone(), provider)
    }

    fn bridge_rights() -> LanguageRights {
        LanguageRights::from_rights([LanguageRight::Bridge, LanguageRight::ReflectAst])
    }

    #[test]
    fn host_profile_admission_is_sealed_stable_attenuable_and_revocable() {
        let table = InstalledLanguageTable::new();
        let (bytes, provider) = fixture();
        let grant = table
            .install_host_profile(&bytes, provider.clone(), bridge_rights())
            .unwrap();
        let duplicate = table
            .install_host_profile(&bytes, provider.clone(), bridge_rights())
            .unwrap();
        assert_eq!(grant.handle.entry_id, duplicate.handle.entry_id);
        assert_eq!(grant.handle.epoch, duplicate.handle.epoch);
        assert!(Arc::ptr_eq(&grant.handle.seal, &duplicate.handle.seal));
        assert!(table
            .authorize_host_profile(&grant.handle, &[LanguageRight::Bridge])
            .is_ok());
        let attenuated = grant
            .handle
            .attenuate(&LanguageRights::from_rights([LanguageRight::ReflectAst]));
        assert_eq!(
            table
                .authorize_host_profile(&attenuated, &[LanguageRight::Bridge])
                .unwrap_err(),
            HostProfileAccessError::InsufficientRights
        );
        assert_eq!(
            InstalledLanguageTable::new()
                .authorize_host_profile(&grant.handle, &[])
                .unwrap_err(),
            HostProfileAccessError::UnknownHandle
        );
        table.revoke_host_profile(grant.revocation).unwrap();
        assert_eq!(
            table
                .authorize_host_profile(&grant.handle, &[])
                .unwrap_err(),
            HostProfileAccessError::Revoked
        );
        let fresh = table
            .install_host_profile(&bytes, provider, bridge_rights())
            .unwrap();
        assert_ne!(fresh.handle.entry_id, grant.handle.entry_id);
        assert_ne!(fresh.handle.epoch, grant.handle.epoch);
        assert!(table
            .authorize_host_profile(&fresh.handle, &[LanguageRight::Bridge])
            .is_ok());
        assert_eq!(
            table
                .authorize_host_profile(&grant.handle, &[])
                .unwrap_err(),
            HostProfileAccessError::UnknownHandle
        );
    }

    #[test]
    fn host_profile_rejects_wrong_record_provider_and_manifest_before_publish() {
        let table = InstalledLanguageTable::new();
        let (bytes, provider) = fixture();
        assert_eq!(
            table
                .install_host_profile(&bytes, provider.clone(), LanguageRights::all())
                .unwrap_err(),
            HostProfileInstallError::InvalidRights
        );
        let mut tampered = bytes.clone();
        tampered.push(0);
        assert!(matches!(
            table.install_host_profile(&tampered, provider.clone(), bridge_rights()),
            Err(HostProfileInstallError::InvalidRecord(_))
        ));
        let mut changed = ProjectionHostProfileRecordV1::decode_canonical(&bytes)
            .unwrap()
            .payload;
        changed.language_version = "1.4-preview.2".into();
        let changed = ProjectionHostProfileRecordV1::new(changed)
            .unwrap()
            .canonical_bytes()
            .unwrap();
        assert_eq!(
            table
                .install_host_profile(&changed, provider.clone(), bridge_rights())
                .unwrap_err(),
            HostProfileInstallError::ProviderRecordMismatch
        );
        let other = Arc::new(TestProvider {
            record: bytes.clone(),
            manifest: Mutex::new(provider.manifest.lock().unwrap().clone()),
            descriptor: vec![9],
        });
        assert_eq!(
            table
                .install_host_profile(&bytes, other, bridge_rights())
                .unwrap_err(),
            HostProfileInstallError::ProviderCodecRefused
        );
        provider
            .manifest
            .lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .code_commitment = [5; 32];
        assert_eq!(
            table
                .install_host_profile(&bytes, provider.clone(), bridge_rights())
                .unwrap_err(),
            HostProfileInstallError::ManifestMismatch
        );
        assert_eq!(table.installed_count().unwrap(), 0);
        provider
            .manifest
            .lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .code_commitment = [4; 32];
        let grant = table
            .install_host_profile(&bytes, provider.clone(), bridge_rights())
            .unwrap();
        provider
            .manifest
            .lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .code_commitment = [5; 32];
        assert_eq!(
            table
                .authorize_host_profile(&grant.handle, &[])
                .unwrap_err(),
            HostProfileAccessError::ProviderChanged
        );
    }

    #[test]
    fn duplicate_profile_from_distinct_provider_is_not_authorized_as_same_epoch() {
        let table = InstalledLanguageTable::new();
        let (bytes, provider) = fixture();
        table
            .install_host_profile(&bytes, provider.clone(), bridge_rights())
            .unwrap();
        let distinct = Arc::new(TestProvider {
            record: bytes.clone(),
            manifest: Mutex::new(provider.manifest.lock().unwrap().clone()),
            descriptor: provider.descriptor.clone(),
        });
        assert_eq!(
            table
                .install_host_profile(&bytes, distinct, bridge_rights())
                .unwrap_err(),
            HostProfileInstallError::ConflictingVersion
        );
    }
}
