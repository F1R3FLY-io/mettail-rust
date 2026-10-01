//! Versioned, endpoint-bound GSLT projection declarations.
//!
//! The legacy `LanguageCoreV1` postcard shape and fingerprint remain exact.
//! A projected language has a distinct outer artifact and commitment; its
//! rule bodies reuse `TheoryRewriteV1`'s existing flat arena rather than a
//! second expression language.

use crate::{
    LanguageCoreV1, TheoryActionId, TheoryConstructorV1, TheoryRewriteV1, TheoryRuleProgramId,
    TheorySemanticImageV1, TheorySortId, TheorySortKindV1, TheorySortV1,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

pub const PROJECTED_LANGUAGE_CORE_ABI_V1: u16 = 1;
pub const PROJECTED_THEORY_IMAGE_ABI_V1: u16 = 1;
pub const PROJECTION_HOST_PROFILE_ABI_V1: u16 = 1;
pub const PROJECTION_HOST_CODEC_ABI_V1: u16 = 1;

const HOST_SIGNATURE_DOMAIN_V1: &[u8] = b"mettail-projection-host-signature/1\0";
const HOST_CODEC_DOMAIN_V1: &[u8] = b"mettail-projection-host-codec/1\0";
const HOST_PROFILE_DOMAIN_V1: &[u8] = b"mettail-projection-host-profile/1\0";

/// An exact codec declaration, not evidence that the named implementation is
/// installed or authorized. Admission must verify the provider and its
/// implementation commitment against an independently trusted installation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCodecProfileV1 {
    pub codec_abi: u16,
    pub provider_abi: String,
    pub implementation_commitment: [u8; 32],
    /// Provider-defined canonical descriptor bytes. The provider must check
    /// their meaning before admitting this profile; this layer commits to the
    /// exact bytes without interpreting them.
    pub descriptor: Vec<u8>,
}

/// Which part of the checked host grammar has an exact executable codec.
/// `ExactFragment` is not a claim that the omitted categories are absent from
/// the grammar: it identifies the selected, exact subset in `sorts`.  Only an
/// independently checked provider may attest either coverage claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionHostCoverageV1 {
    Complete,
    ExactFragment,
}

/// Raw, versioned host-profile evidence derived from a checked language
/// definition. This is never an installed trust root or a digital signature.
/// Vector order is significant: sort and constructor IDs are positional.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostProfilePayloadV1 {
    pub profile_abi: u16,
    pub language_name: String,
    /// The explicit version of the checked host language definition, distinct
    /// from the profile encoding ABI. Unversioned languages cannot form this
    /// trusted-profile candidate.
    pub language_version: String,
    pub definition_fingerprint: String,
    pub grammar_fingerprint: [u8; 32],
    /// A complete roster or a checked exact-codec fragment of that grammar.
    /// The whole-grammar fingerprint remains bound in both cases.
    pub coverage: ProjectionHostCoverageV1,
    pub sorts: Vec<TheorySortV1>,
    pub constructors: Vec<TheoryConstructorV1>,
    pub codec: ProjectionHostCodecProfileV1,
}

/// Content commitments only. None is an authorization or cryptographic
/// signature by a trusted principal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostProfileDigestsV1 {
    pub signature_fingerprint: [u8; 32],
    pub codec_profile_fingerprint: [u8; 32],
    pub profile_fingerprint: [u8; 32],
}

/// Portable data record with claims that must be recomputed on admission.
/// Successful decoding does not install a provider or confer authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostProfileRecordV1 {
    pub payload: ProjectionHostProfilePayloadV1,
    pub claimed_digests: ProjectionHostProfileDigestsV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionHostProfileErrorV1 {
    UnsupportedProfileAbi(u16),
    UnsupportedCodecAbi(u16),
    EmptyLanguageName,
    EmptyLanguageVersion,
    EmptyDefinitionFingerprint,
    EmptyProviderAbi,
    EmptyCodecDescriptor,
    MissingImplementationCommitment,
    EmptySorts,
    EmptySortName,
    DuplicateSort(String),
    EmptyConstructorName,
    DuplicateConstructor(String),
    UnknownSort(String),
    EmptyProduct(String),
    EmptyOpaqueAbi(String),
    Encoding(String),
    Decoding(String),
    NoncanonicalEncoding,
    ClaimedDigestMismatch,
}

fn host_commitment(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(domain);
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

impl ProjectionHostProfilePayloadV1 {
    /// Check closure of the declared signature roster, without asserting that
    /// its grammar or codec claims match an installed host implementation.
    pub fn validate(&self) -> Result<(), ProjectionHostProfileErrorV1> {
        use ProjectionHostProfileErrorV1 as Error;

        if self.profile_abi != PROJECTION_HOST_PROFILE_ABI_V1 {
            return Err(Error::UnsupportedProfileAbi(self.profile_abi));
        }
        if self.codec.codec_abi != PROJECTION_HOST_CODEC_ABI_V1 {
            return Err(Error::UnsupportedCodecAbi(self.codec.codec_abi));
        }
        if self.language_name.is_empty() {
            return Err(Error::EmptyLanguageName);
        }
        if self.language_version.is_empty() {
            return Err(Error::EmptyLanguageVersion);
        }
        if self.definition_fingerprint.is_empty() {
            return Err(Error::EmptyDefinitionFingerprint);
        }
        if self.codec.provider_abi.is_empty() {
            return Err(Error::EmptyProviderAbi);
        }
        if self.codec.descriptor.is_empty() {
            return Err(Error::EmptyCodecDescriptor);
        }
        if self.codec.implementation_commitment == [0; 32] {
            return Err(Error::MissingImplementationCommitment);
        }
        if self.sorts.is_empty() {
            return Err(Error::EmptySorts);
        }

        let mut sort_names = BTreeSet::new();
        for sort in &self.sorts {
            if sort.name.is_empty() {
                return Err(Error::EmptySortName);
            }
            if !sort_names.insert(sort.name.as_str()) {
                return Err(Error::DuplicateSort(sort.name.clone()));
            }
        }
        let require_sort = |name: &str| {
            if sort_names.contains(name) {
                Ok(())
            } else {
                Err(Error::UnknownSort(name.to_owned()))
            }
        };
        for sort in &self.sorts {
            match &sort.kind {
                TheorySortKindV1::Syntax { .. } => {},
                TheorySortKindV1::Collection { key, element, .. } => {
                    if let Some(key) = key {
                        require_sort(key)?;
                    }
                    require_sort(element)?;
                },
                TheorySortKindV1::Function { domain, codomain, .. } => {
                    require_sort(domain)?;
                    require_sort(codomain)?;
                },
                TheorySortKindV1::Product { factors } => {
                    if factors.is_empty() {
                        return Err(Error::EmptyProduct(sort.name.clone()));
                    }
                    for factor in factors {
                        require_sort(factor)?;
                    }
                },
                TheorySortKindV1::Opaque { abi } if abi.is_empty() => {
                    return Err(Error::EmptyOpaqueAbi(sort.name.clone()));
                },
                TheorySortKindV1::Opaque { .. } => {},
            }
        }
        let mut constructor_names = BTreeSet::new();
        for constructor in &self.constructors {
            if constructor.name.is_empty() {
                return Err(Error::EmptyConstructorName);
            }
            if !constructor_names.insert(constructor.name.as_str()) {
                return Err(Error::DuplicateConstructor(constructor.name.clone()));
            }
            for domain in &constructor.domain {
                require_sort(domain)?;
            }
            require_sort(&constructor.codomain)?;
        }
        Ok(())
    }

    /// Deterministic postcard payload bytes. These bind exact vector order,
    /// language version, checked-definition identity, grammar and codec data.
    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ProjectionHostProfileErrorV1> {
        self.validate()?;
        postcard::to_allocvec(self)
            .map_err(|error| ProjectionHostProfileErrorV1::Encoding(error.to_string()))
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ProjectionHostProfileErrorV1> {
        let payload: Self = postcard::from_bytes(bytes)
            .map_err(|error| ProjectionHostProfileErrorV1::Decoding(error.to_string()))?;
        let canonical = payload.canonical_bytes()?;
        if canonical != bytes {
            return Err(ProjectionHostProfileErrorV1::NoncanonicalEncoding);
        }
        Ok(payload)
    }

    /// Recompute all content commitments. The signature commitment excludes
    /// the codec, while the codec commitment binds both the signature and the
    /// exact codec descriptor, preventing cross-host codec substitution.
    pub fn digests(&self) -> Result<ProjectionHostProfileDigestsV1, ProjectionHostProfileErrorV1> {
        let profile_bytes = self.canonical_bytes()?;
        let signature_bytes = postcard::to_allocvec(&(
            self.profile_abi,
            &self.language_name,
            &self.language_version,
            &self.definition_fingerprint,
            &self.grammar_fingerprint,
            self.coverage,
            &self.sorts,
            &self.constructors,
        ))
        .map_err(|error| ProjectionHostProfileErrorV1::Encoding(error.to_string()))?;
        let signature_fingerprint = host_commitment(HOST_SIGNATURE_DOMAIN_V1, &signature_bytes);
        let codec_bytes =
            postcard::to_allocvec(&(self.profile_abi, &signature_fingerprint, &self.codec))
                .map_err(|error| ProjectionHostProfileErrorV1::Encoding(error.to_string()))?;
        Ok(ProjectionHostProfileDigestsV1 {
            signature_fingerprint,
            codec_profile_fingerprint: host_commitment(HOST_CODEC_DOMAIN_V1, &codec_bytes),
            profile_fingerprint: host_commitment(HOST_PROFILE_DOMAIN_V1, &profile_bytes),
        })
    }

    /// Produce the legacy-shaped raw fragment for projection compilation. A
    /// caller must still verify and admit this payload against its installed
    /// host and trust policy; this method grants no such authority.
    pub fn raw_signature(&self) -> Result<ProjectionHostSignatureV1, ProjectionHostProfileErrorV1> {
        let digests = self.digests()?;
        Ok(ProjectionHostSignatureV1 {
            signature_fingerprint: digests.signature_fingerprint,
            codec_profile_fingerprint: digests.codec_profile_fingerprint,
            sorts: self.sorts.clone(),
            constructors: self.constructors.clone(),
        })
    }
}

impl ProjectionHostProfileRecordV1 {
    pub fn new(
        payload: ProjectionHostProfilePayloadV1,
    ) -> Result<Self, ProjectionHostProfileErrorV1> {
        let claimed_digests = payload.digests()?;
        Ok(Self { payload, claimed_digests })
    }

    /// Validate content claims against the canonical payload; content equality
    /// alone is not proof of origin or of an installed executable codec.
    pub fn validate(&self) -> Result<(), ProjectionHostProfileErrorV1> {
        if self.payload.digests()? != self.claimed_digests {
            return Err(ProjectionHostProfileErrorV1::ClaimedDigestMismatch);
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ProjectionHostProfileErrorV1> {
        self.validate()?;
        postcard::to_allocvec(self)
            .map_err(|error| ProjectionHostProfileErrorV1::Encoding(error.to_string()))
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ProjectionHostProfileErrorV1> {
        let record: Self = postcard::from_bytes(bytes)
            .map_err(|error| ProjectionHostProfileErrorV1::Decoding(error.to_string()))?;
        let canonical = record.canonical_bytes()?;
        if canonical != bytes {
            return Err(ProjectionHostProfileErrorV1::NoncanonicalEncoding);
        }
        Ok(record)
    }
}

/// The host-side signature and codec profile must be supplied by the caller's
/// trusted registry. Naming them in a DDL grants neither code nor authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostEndpointV1 {
    pub signature_fingerprint: [u8; 32],
    pub category: String,
    pub codec_profile_fingerprint: [u8; 32],
}

/// An independently supplied immutable host-signature fragment. A projection
/// declaration only records its fingerprint and category; it cannot define or
/// replace this roster. The provider must bind it to the installed host
/// grammar and codec profile before projection compilation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostSignatureV1 {
    pub signature_fingerprint: [u8; 32],
    pub codec_profile_fingerprint: [u8; 32],
    pub sorts: Vec<TheorySortV1>,
    pub constructors: Vec<TheoryConstructorV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ProjectionDirectionV1 {
    GuestToHost,
    HostToGuest,
}

/// Both surface arrows are represented by two independently checked rows.
/// `source_occurrence` is the shared authored row identity, not a priority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectedProjectionRuleV1 {
    pub direction: ProjectionDirectionV1,
    pub source_occurrence: u32,
    pub rule: TheoryRewriteV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionBodyV1 {
    /// Requires an independently bound, exact-profile structural codec.
    Carrier,
    Rules(Vec<DirectedProjectionRuleV1>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryProjectionV1 {
    pub name: String,
    /// Resolved against the embedded guest theory and grammar, never invented
    /// as an alias for the host category.
    pub guest_category: String,
    pub host: ProjectionHostEndpointV1,
    pub directions: Vec<ProjectionDirectionV1>,
    pub body: ProjectionBodyV1,
}

/// A versioned semantic extension over the unchanged V1 artifact. Its
/// fingerprint binds the entire V1 core and all projection descriptors.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProjectedLanguageCoreV1 {
    pub abi: u16,
    pub base: LanguageCoreV1,
    pub projections: Vec<TheoryProjectionV1>,
}

/// The source occurrence and the exact flat-program entry remain paired;
/// neither the set automaton nor a request may collapse equal-pattern rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjectionRuleImageEntryV1 {
    pub program: TheoryRuleProgramId,
    pub source_occurrence: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionRelationBodyImageV1 {
    /// The installed exact-profile structural codec handles this direction.
    Carrier,
    /// Every authored occurrence remains in source order, even when patterns
    /// overlap or a direction is non-positional.
    Rules(Vec<ProjectionRuleImageEntryV1>),
}

/// An explicitly selected cross-endpoint relation. Input and output sorts
/// are independent; ordinary guest rewrites retain their same-sort contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionRelationImageV1 {
    pub projection: u32,
    pub direction: ProjectionDirectionV1,
    pub input_sort: TheorySortId,
    pub output_sort: TheorySortId,
    /// Private one-step action dispatch for rule-backed relations. This is
    /// never an authored guest action; publication replaces its internal
    /// action receipt with a projection-specific receipt.
    pub dispatch_action: Option<TheoryActionId>,
    pub body: ProjectionRelationBodyImageV1,
}

/// A separate versioned artifact over the unchanged V1 image. `execution`
/// reuses the V1 flat rule programs and set-automaton representation but must
/// only be entered through a selected projection relation; it is not a V1
/// language image and cannot pass V1 source admission by itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectedTheorySemanticImageV1 {
    pub abi: u16,
    pub projected_language_fingerprint: [u8; 32],
    pub base_image_fingerprint: [u8; 32],
    pub base_rule_count: u32,
    pub host_signature_fingerprint: [u8; 32],
    pub host_codec_profile_fingerprint: [u8; 32],
    pub execution: TheorySemanticImageV1,
    pub relations: Vec<ProjectionRelationImageV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionCoreHeaderError {
    UnsupportedAbi(u16),
    InvalidBase,
    EmptyProjections,
    EmptyName,
    DuplicateName(String),
    RewriteNameCollision(String),
    UnknownGuestCategory(String),
    EmptyHostCategory,
    EmptyDirections(String),
    DuplicateDirection(String),
    RowDirectionNotDeclared(String),
    EmptyRules(String),
    DuplicateRow(String),
}

impl ProjectedLanguageCoreV1 {
    /// This validates the closed header and legacy core. Rule typing, host
    /// signature admission, codec binding, and inverse laws are additional
    /// mandatory checks at projection-image compilation and installation.
    pub fn validate_header(&self) -> Result<(), ProjectionCoreHeaderError> {
        if self.abi != PROJECTED_LANGUAGE_CORE_ABI_V1 {
            return Err(ProjectionCoreHeaderError::UnsupportedAbi(self.abi));
        }
        if self.base.validate().is_err() {
            return Err(ProjectionCoreHeaderError::InvalidBase);
        }
        if self.projections.is_empty() {
            return Err(ProjectionCoreHeaderError::EmptyProjections);
        }
        let mut names = BTreeSet::new();
        for projection in &self.projections {
            if projection.name.is_empty() {
                return Err(ProjectionCoreHeaderError::EmptyName);
            }
            if !names.insert(projection.name.as_str()) {
                return Err(ProjectionCoreHeaderError::DuplicateName(projection.name.clone()));
            }
            if self
                .base
                .theory
                .rewrites
                .iter()
                .any(|rule| rule.name == projection.name)
            {
                return Err(ProjectionCoreHeaderError::RewriteNameCollision(
                    projection.name.clone(),
                ));
            }
            if !self
                .base
                .grammar
                .categories
                .iter()
                .any(|category| category.name == projection.guest_category)
            {
                return Err(ProjectionCoreHeaderError::UnknownGuestCategory(
                    projection.guest_category.clone(),
                ));
            }
            if projection.host.category.is_empty() {
                return Err(ProjectionCoreHeaderError::EmptyHostCategory);
            }
            if projection.directions.is_empty() {
                return Err(ProjectionCoreHeaderError::EmptyDirections(projection.name.clone()));
            }
            let mut directions = BTreeSet::new();
            for direction in &projection.directions {
                if !directions.insert(*direction) {
                    return Err(ProjectionCoreHeaderError::DuplicateDirection(
                        projection.name.clone(),
                    ));
                }
            }
            if let ProjectionBodyV1::Rules(rows) = &projection.body {
                if rows.is_empty() {
                    return Err(ProjectionCoreHeaderError::EmptyRules(projection.name.clone()));
                }
                let mut row_names = BTreeSet::new();
                for row in rows {
                    if !directions.contains(&row.direction) {
                        return Err(ProjectionCoreHeaderError::RowDirectionNotDeclared(
                            row.rule.name.clone(),
                        ));
                    }
                    if !row_names.insert((row.direction, row.rule.name.as_str())) {
                        return Err(ProjectionCoreHeaderError::DuplicateRow(row.rule.name.clone()));
                    }
                }
            }
        }
        Ok(())
    }

    pub fn fingerprint(&self) -> Result<[u8; 32], postcard::Error> {
        let base = self.base.fingerprint()?;
        let descriptors = postcard::to_allocvec(&self.projections)?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-projected-language-core/1\0");
        hasher.update(&self.abi.to_be_bytes());
        hasher.update(&base);
        hasher.update(&(descriptors.len() as u64).to_be_bytes());
        hasher.update(&descriptors);
        Ok(*hasher.finalize().as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Carrier, Category, CategoryId, GrammarCoreV1};

    fn host_profile() -> ProjectionHostProfilePayloadV1 {
        ProjectionHostProfilePayloadV1 {
            profile_abi: PROJECTION_HOST_PROFILE_ABI_V1,
            language_name: "Rholang".into(),
            language_version: "1.2.3".into(),
            definition_fingerprint: "checked-definition-v1".into(),
            grammar_fingerprint: [7; 32],
            coverage: ProjectionHostCoverageV1::Complete,
            sorts: vec![
                TheorySortV1 {
                    name: "Name".into(),
                    kind: TheorySortKindV1::Syntax { literal: None },
                },
                TheorySortV1 {
                    name: "Proc".into(),
                    kind: TheorySortKindV1::Syntax { literal: None },
                },
            ],
            constructors: vec![
                TheoryConstructorV1 {
                    name: "Nil".into(),
                    domain: vec![],
                    codomain: "Proc".into(),
                },
                TheoryConstructorV1 {
                    name: "Send".into(),
                    domain: vec!["Name".into(), "Proc".into()],
                    codomain: "Proc".into(),
                },
            ],
            codec: ProjectionHostCodecProfileV1 {
                codec_abi: PROJECTION_HOST_CODEC_ABI_V1,
                provider_abi: "rholang-structural-codec/1".into(),
                implementation_commitment: [8; 32],
                descriptor: vec![1, 2, 3],
            },
        }
    }

    #[test]
    fn host_profile_roundtrip_recomputes_domain_separated_commitments() {
        let payload = host_profile();
        let bytes = payload.canonical_bytes().unwrap();
        let decoded = ProjectionHostProfilePayloadV1::decode_canonical(&bytes).unwrap();
        assert_eq!(decoded, payload);
        assert_eq!(decoded.canonical_bytes().unwrap(), bytes);
        let digests = payload.digests().unwrap();
        assert_eq!(decoded.digests().unwrap(), digests);
        assert_ne!(digests.signature_fingerprint, digests.codec_profile_fingerprint);
        assert_ne!(digests.profile_fingerprint, digests.signature_fingerprint);
        assert_ne!(digests.profile_fingerprint, digests.codec_profile_fingerprint);

        let raw = payload.raw_signature().unwrap();
        assert_eq!(raw.signature_fingerprint, digests.signature_fingerprint);
        assert_eq!(raw.codec_profile_fingerprint, digests.codec_profile_fingerprint);
        assert_eq!(raw.sorts, payload.sorts);
        assert_eq!(raw.constructors, payload.constructors);

        let mut trailing = bytes;
        trailing.push(0);
        assert!(ProjectionHostProfilePayloadV1::decode_canonical(&trailing).is_err());
    }

    #[test]
    fn host_profile_record_rejects_spoofed_content_claims() {
        let record = ProjectionHostProfileRecordV1::new(host_profile()).unwrap();
        let bytes = record.canonical_bytes().unwrap();
        assert_eq!(ProjectionHostProfileRecordV1::decode_canonical(&bytes).unwrap(), record);

        let mut altered_payload = record.clone();
        altered_payload.payload.coverage = ProjectionHostCoverageV1::ExactFragment;
        assert_eq!(
            altered_payload.validate(),
            Err(ProjectionHostProfileErrorV1::ClaimedDigestMismatch)
        );

        let mut altered_claim = record.clone();
        altered_claim.claimed_digests.codec_profile_fingerprint[0] ^= 1;
        assert_eq!(
            altered_claim.validate(),
            Err(ProjectionHostProfileErrorV1::ClaimedDigestMismatch)
        );

        let mut trailing = bytes;
        trailing.push(0);
        assert!(ProjectionHostProfileRecordV1::decode_canonical(&trailing).is_err());
    }

    #[test]
    fn host_profile_commits_all_checked_identity_and_positional_rosters() {
        let payload = host_profile();
        let baseline = payload.digests().unwrap();
        let mutations: [fn(&mut ProjectionHostProfilePayloadV1); 9] = [
            |p| p.language_name.push('!'),
            |p| p.language_version.push('!'),
            |p| p.definition_fingerprint.push('!'),
            |p| p.grammar_fingerprint[0] ^= 1,
            |p| p.coverage = ProjectionHostCoverageV1::ExactFragment,
            |p| p.sorts.swap(0, 1),
            |p| p.sorts[0].kind = TheorySortKindV1::Opaque { abi: "name/1".into() },
            |p| p.constructors.swap(0, 1),
            |p| p.constructors[1].domain.swap(0, 1),
        ];
        for mutate in mutations {
            let mut changed = payload.clone();
            mutate(&mut changed);
            assert_ne!(
                changed.digests().unwrap().signature_fingerprint,
                baseline.signature_fingerprint
            );
        }

        let codec_mutations: [fn(&mut ProjectionHostProfilePayloadV1); 3] = [
            |p| p.codec.provider_abi.push('!'),
            |p| p.codec.implementation_commitment[0] ^= 1,
            |p| p.codec.descriptor.push(4),
        ];
        for mutate in codec_mutations {
            let mut changed = payload.clone();
            mutate(&mut changed);
            let digests = changed.digests().unwrap();
            assert_eq!(digests.signature_fingerprint, baseline.signature_fingerprint);
            assert_ne!(digests.codec_profile_fingerprint, baseline.codec_profile_fingerprint);
            assert_ne!(digests.profile_fingerprint, baseline.profile_fingerprint);
        }
    }

    #[test]
    fn host_profile_rejects_unversioned_and_unclosed_rosters() {
        let mut payload = host_profile();
        payload.language_version.clear();
        assert_eq!(payload.validate(), Err(ProjectionHostProfileErrorV1::EmptyLanguageVersion));

        let mut payload = host_profile();
        payload.profile_abi += 1;
        assert_eq!(payload.validate(), Err(ProjectionHostProfileErrorV1::UnsupportedProfileAbi(2)));

        let mut payload = host_profile();
        payload.codec.codec_abi += 1;
        assert_eq!(payload.validate(), Err(ProjectionHostProfileErrorV1::UnsupportedCodecAbi(2)));

        let mut payload = host_profile();
        payload.codec.descriptor.clear();
        assert_eq!(payload.validate(), Err(ProjectionHostProfileErrorV1::EmptyCodecDescriptor));

        let mut payload = host_profile();
        payload.codec.implementation_commitment = [0; 32];
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostProfileErrorV1::MissingImplementationCommitment)
        );

        let mut payload = host_profile();
        payload.sorts.push(payload.sorts[0].clone());
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostProfileErrorV1::DuplicateSort("Name".into()))
        );

        let mut payload = host_profile();
        payload.constructors[0].codomain = "Missing".into();
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostProfileErrorV1::UnknownSort("Missing".into()))
        );
    }

    #[test]
    fn projected_identity_is_versioned_and_legacy_bytes_are_unchanged() {
        let mut grammar = GrammarCoreV1::new("Example");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Bool".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: true,
        });
        let base = LanguageCoreV1::structural(grammar);
        let old_bytes = postcard::to_allocvec(&base).unwrap();
        let old_identity = base.fingerprint().unwrap();
        let projected = ProjectedLanguageCoreV1 {
            abi: PROJECTED_LANGUAGE_CORE_ABI_V1,
            base: base.clone(),
            projections: vec![TheoryProjectionV1 {
                name: "Boolean".into(),
                guest_category: "Bool".into(),
                host: ProjectionHostEndpointV1 {
                    signature_fingerprint: [1; 32],
                    category: "Bool".into(),
                    codec_profile_fingerprint: [2; 32],
                },
                directions: vec![
                    ProjectionDirectionV1::GuestToHost,
                    ProjectionDirectionV1::HostToGuest,
                ],
                body: ProjectionBodyV1::Carrier,
            }],
        };
        assert_eq!(postcard::to_allocvec(&base).unwrap(), old_bytes);
        assert_eq!(base.fingerprint().unwrap(), old_identity);
        assert_ne!(projected.fingerprint().unwrap(), old_identity);
        projected
            .validate_header()
            .expect("closed, exact projection header");
        let decoded: ProjectedLanguageCoreV1 =
            postcard::from_bytes(&postcard::to_allocvec(&projected).unwrap()).unwrap();
        assert_eq!(decoded.fingerprint().unwrap(), projected.fingerprint().unwrap());

        let mut changed_host = projected.clone();
        changed_host.projections[0].host.signature_fingerprint = [3; 32];
        assert_ne!(changed_host.fingerprint().unwrap(), projected.fingerprint().unwrap());
        let mut changed_codec = projected.clone();
        changed_codec.projections[0].host.codec_profile_fingerprint = [4; 32];
        assert_ne!(changed_codec.fingerprint().unwrap(), projected.fingerprint().unwrap());

        let mut missing_direction = projected.clone();
        missing_direction.projections[0].directions.clear();
        assert_eq!(
            missing_direction.validate_header(),
            Err(ProjectionCoreHeaderError::EmptyDirections("Boolean".into()))
        );
    }
}
