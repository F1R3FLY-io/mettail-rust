//! Versioned, data-only host signature fragment for typed compound carriers.
//!
//! This is separate from the V1 ground-scalar profile. A checked generator
//! emits exact selected routes from its grammar and typed adapter layout; an
//! independently installed provider must compare the complete canonical
//! record with its compiled route before any value can cross the boundary.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::{
    projection_core::validate_host_signature_roster, CategoryId, ConstructorId,
    ProjectionHostCoverageV1, ProjectionHostProfileErrorV1, ProjectionHostSignatureV1,
    SemanticAtomSchemaV1, SemanticFieldSchemaV1, SemanticOperatorId, SemanticOperatorOriginV1,
    TheoryConstructorV1, TheorySortV1,
};

pub const PROJECTION_HOST_COMPOUND_PROFILE_ABI_V2: u16 = 2;
pub const PROJECTION_HOST_COMPOUND_CODEC_ABI_V2: u16 = 2;

/// A selected constructor route is checked when used. This is deliberately
/// not an AllValues claim about recursively nested Proc, Name, or ForRow data.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProjectionHostCompoundDomainV2 {
    SelectedRootRoutes,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundCategoryRouteV2 {
    pub category: CategoryId,
    pub name: String,
    /// The exact category discriminant in the generated typed adapter.
    pub generated_category_tag: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundOperatorRouteV2 {
    /// IDs and discriminants are from the complete generated adapter layout,
    /// never renumbered within this fragment.
    pub operator: SemanticOperatorId,
    pub category: CategoryId,
    pub constructor: ConstructorId,
    pub generated_constructor_tag: u32,
    pub stable_discriminant: u32,
    pub label: String,
    pub origin: SemanticOperatorOriginV1,
    pub fields: Vec<SemanticFieldSchemaV1>,
}

/// A generated vector field is represented by an explicit positional list
/// algebra, never by one child of the element sort. The three names are
/// committed in the host signature and resolve to exact installed IDs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundSequenceRouteV2 {
    pub element: CategoryId,
    pub sort_name: String,
    pub nil_name: String,
    pub cons_name: String,
}

/// An exact fragment, not a fictitious complete SemanticSignatureV1. The
/// latter requires every grammar production and would be invalid if created
/// by dropping a structurally unsupported coefficient. An omitted route is
/// unavailable, never silently interpreted through opaque bytes or strings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundCodecDescriptorV2 {
    pub domain: ProjectionHostCompoundDomainV2,
    pub semantic_key_abi: u16,
    pub grammar_fingerprint: [u8; 32],
    pub proc_category: CategoryId,
    pub cost_signature_category: CategoryId,
    pub cost_stack_category: CategoryId,
    pub categories: Vec<ProjectionHostCompoundCategoryRouteV2>,
    pub atom_schemas: Vec<SemanticAtomSchemaV1>,
    pub operators: Vec<ProjectionHostCompoundOperatorRouteV2>,
    pub sequences: Vec<ProjectionHostCompoundSequenceRouteV2>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundCodecProfileV2 {
    pub codec_abi: u16,
    pub provider_abi: String,
    pub implementation_commitment: [u8; 32],
    pub descriptor: ProjectionHostCompoundCodecDescriptorV2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundProfilePayloadV2 {
    pub profile_abi: u16,
    pub language_name: String,
    pub language_version: String,
    pub definition_fingerprint: String,
    pub grammar_fingerprint: [u8; 32],
    pub coverage: ProjectionHostCoverageV1,
    pub sorts: Vec<TheorySortV1>,
    pub constructors: Vec<TheoryConstructorV1>,
    pub codec: ProjectionHostCompoundCodecProfileV2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundProfileDigestsV2 {
    pub signature_fingerprint: [u8; 32],
    pub codec_profile_fingerprint: [u8; 32],
    pub profile_fingerprint: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProjectionHostCompoundProfileRecordV2 {
    pub payload: ProjectionHostCompoundProfilePayloadV2,
    pub claimed_digests: ProjectionHostCompoundProfileDigestsV2,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProjectionHostCompoundProfileErrorV2 {
    UnsupportedProfileAbi(u16),
    UnsupportedCodecAbi(u16),
    InvalidHeader(&'static str),
    InvalidDescriptor(&'static str),
    InvalidSignature(ProjectionHostProfileErrorV1),
    Encoding(String),
    Decoding(String),
    NoncanonicalEncoding,
    ClaimedDigestMismatch,
}

fn commit(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(domain);
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

impl ProjectionHostCompoundCodecDescriptorV2 {
    fn validate(
        &self,
        grammar_fingerprint: [u8; 32],
    ) -> Result<(), ProjectionHostCompoundProfileErrorV2> {
        use ProjectionHostCompoundProfileErrorV2 as Error;
        if self.semantic_key_abi == 0 || self.grammar_fingerprint != grammar_fingerprint {
            return Err(Error::InvalidDescriptor("semantic key ABI or grammar fingerprint"));
        }
        let mut categories = BTreeSet::new();
        let mut category_names = BTreeSet::new();
        let mut category_tags = BTreeSet::new();
        for route in &self.categories {
            if route.name.is_empty()
                || !categories.insert(route.category)
                || !category_names.insert(route.name.as_str())
                || !category_tags.insert(route.generated_category_tag)
            {
                return Err(Error::InvalidDescriptor("category roster"));
            }
        }
        if self.proc_category == self.cost_signature_category
            || self.proc_category == self.cost_stack_category
            || self.cost_signature_category == self.cost_stack_category
            || !categories.contains(&self.proc_category)
            || !categories.contains(&self.cost_signature_category)
            || !categories.contains(&self.cost_stack_category)
        {
            return Err(Error::InvalidDescriptor("required compound categories"));
        }
        let mut operators = BTreeSet::new();
        let mut discriminants = BTreeSet::new();
        let mut constructor_routes = BTreeSet::new();
        for route in &self.operators {
            if route.label.is_empty()
                || !categories.contains(&route.category)
                || !operators.insert(route.operator)
                || !discriminants.insert(route.stable_discriminant)
                || !constructor_routes.insert((route.category, route.generated_constructor_tag))
            {
                return Err(Error::InvalidDescriptor("operator roster"));
            }
            for field in &route.fields {
                // The fragment may refer only to another explicitly routed
                // category; a missing structural child cannot become opaque.
                let child = match field {
                    SemanticFieldSchemaV1::Child { category }
                    | SemanticFieldSchemaV1::Optional { category }
                    | SemanticFieldSchemaV1::Variable { category } => Some(*category),
                    SemanticFieldSchemaV1::Sequence { element }
                    | SemanticFieldSchemaV1::OptionalSequence { element } => Some(*element),
                    SemanticFieldSchemaV1::Scope { domain, body, .. } => {
                        if !categories.contains(domain) || !categories.contains(body) {
                            return Err(Error::InvalidDescriptor("scope child outside fragment"));
                        }
                        None
                    },
                    SemanticFieldSchemaV1::Collection { key, value, .. } => {
                        if !categories.contains(value)
                            || key.is_some_and(|category| !categories.contains(&category))
                        {
                            return Err(Error::InvalidDescriptor(
                                "collection child outside fragment",
                            ));
                        }
                        None
                    },
                    SemanticFieldSchemaV1::PathMap { key, value } => {
                        if !categories.contains(key) || !categories.contains(value) {
                            return Err(Error::InvalidDescriptor("pathmap child outside fragment"));
                        }
                        None
                    },
                    SemanticFieldSchemaV1::Atom { schema } => {
                        if !matches!(
                            self.atom_schemas.get(*schema as usize),
                            Some(SemanticAtomSchemaV1::Builtin(_))
                        ) {
                            return Err(Error::InvalidDescriptor("non-native atom schema"));
                        }
                        None
                    },
                    SemanticFieldSchemaV1::Opaque { .. } => {
                        return Err(Error::InvalidDescriptor("opaque coefficient"));
                    },
                    _ => None,
                };
                if child.is_some_and(|category| !categories.contains(&category)) {
                    return Err(Error::InvalidDescriptor("child outside fragment"));
                }
            }
        }
        if self.operators.is_empty() {
            return Err(Error::InvalidDescriptor("empty operator fragment"));
        }
        let mut sequence_elements = BTreeSet::new();
        let mut sequence_names = BTreeSet::new();
        for route in &self.sequences {
            if route.sort_name.is_empty()
                || route.nil_name.is_empty()
                || route.cons_name.is_empty()
                || route.nil_name == route.cons_name
                || !categories.contains(&route.element)
                || !sequence_elements.insert(route.element)
                || !sequence_names.insert(route.sort_name.as_str())
                || !sequence_names.insert(route.nil_name.as_str())
                || !sequence_names.insert(route.cons_name.as_str())
            {
                return Err(Error::InvalidDescriptor("sequence route identity"));
            }
        }
        for route in &self.operators {
            for field in &route.fields {
                if let SemanticFieldSchemaV1::Sequence { element } = field {
                    if !sequence_elements.contains(element) {
                        return Err(Error::InvalidDescriptor("sequence field lacks list algebra"));
                    }
                }
            }
        }
        Ok(())
    }
}

impl ProjectionHostCompoundProfilePayloadV2 {
    pub fn validate(&self) -> Result<(), ProjectionHostCompoundProfileErrorV2> {
        use ProjectionHostCompoundProfileErrorV2 as Error;
        if self.profile_abi != PROJECTION_HOST_COMPOUND_PROFILE_ABI_V2 {
            return Err(Error::UnsupportedProfileAbi(self.profile_abi));
        }
        if self.codec.codec_abi != PROJECTION_HOST_COMPOUND_CODEC_ABI_V2 {
            return Err(Error::UnsupportedCodecAbi(self.codec.codec_abi));
        }
        if self.language_name.is_empty()
            || self.language_version.is_empty()
            || self.definition_fingerprint.is_empty()
            || self.codec.provider_abi.is_empty()
            || self.codec.implementation_commitment == [0; 32]
            || self.coverage != ProjectionHostCoverageV1::ExactFragment
        {
            return Err(Error::InvalidHeader("versioned identity, provider, or coverage"));
        }
        validate_host_signature_roster(&self.sorts, &self.constructors)
            .map_err(Error::InvalidSignature)?;
        self.codec.descriptor.validate(self.grammar_fingerprint)?;
        let sort_names: BTreeSet<_> = self.sorts.iter().map(|sort| sort.name.as_str()).collect();
        let descriptor = &self.codec.descriptor;
        let expected_sorts = descriptor
            .categories
            .len()
            .checked_add(descriptor.sequences.len());
        let expected_constructors = descriptor
            .sequences
            .len()
            .checked_mul(2)
            .and_then(|lists| descriptor.operators.len().checked_add(lists));
        if expected_sorts != Some(self.sorts.len())
            || expected_constructors != Some(self.constructors.len())
        {
            return Err(Error::InvalidDescriptor("compound signature route cardinality"));
        }
        for category in &self.codec.descriptor.categories {
            if !sort_names.contains(category.name.as_str()) {
                return Err(Error::InvalidDescriptor("category missing from host sort fragment"));
            }
        }
        for route in &descriptor.sequences {
            let Some(element) = descriptor
                .categories
                .iter()
                .find(|category| category.category == route.element)
            else {
                return Err(Error::InvalidDescriptor("sequence element category"));
            };
            if !self.sorts.iter().any(|sort| {
                sort.name == route.sort_name
                    && sort.kind == crate::TheorySortKindV1::Syntax { literal: None }
            }) || !self.constructors.iter().any(|constructor| {
                constructor.name == route.nil_name
                    && constructor.codomain == route.sort_name
                    && constructor.domain.is_empty()
            }) || !self.constructors.iter().any(|constructor| {
                constructor.name == route.cons_name
                    && constructor.codomain == route.sort_name
                    && constructor.domain == [element.name.clone(), route.sort_name.clone()]
            }) {
                return Err(Error::InvalidDescriptor("sequence Nil/Cons signatures"));
            }
        }
        for route in &descriptor.operators {
            let Some(category) = descriptor
                .categories
                .iter()
                .find(|category| category.category == route.category)
            else {
                return Err(Error::InvalidDescriptor("operator result category"));
            };
            let mut domain = Vec::new();
            for field in &route.fields {
                let name = match field {
                    SemanticFieldSchemaV1::Child { category } => descriptor
                        .categories
                        .iter()
                        .find(|candidate| candidate.category == *category)
                        .map(|candidate| candidate.name.as_str()),
                    SemanticFieldSchemaV1::Sequence { element } => descriptor
                        .sequences
                        .iter()
                        .find(|candidate| candidate.element == *element)
                        .map(|candidate| candidate.sort_name.as_str()),
                    SemanticFieldSchemaV1::Unit => continue,
                    _ => return Err(Error::InvalidDescriptor("unsupported selected field shape")),
                }
                .ok_or(Error::InvalidDescriptor("unrouted selected field"))?;
                domain.push(name.to_owned());
            }
            if !self.constructors.iter().any(|constructor| {
                constructor.name == route.label
                    && constructor.codomain == category.name
                    && constructor.domain == domain
            }) {
                return Err(Error::InvalidDescriptor("selected constructor field signature"));
            }
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ProjectionHostCompoundProfileErrorV2> {
        self.validate()?;
        postcard::to_allocvec(self)
            .map_err(|error| ProjectionHostCompoundProfileErrorV2::Encoding(error.to_string()))
    }

    pub fn digests(
        &self,
    ) -> Result<ProjectionHostCompoundProfileDigestsV2, ProjectionHostCompoundProfileErrorV2> {
        let payload = self.canonical_bytes()?;
        let signature = postcard::to_allocvec(&(
            self.profile_abi,
            &self.language_name,
            &self.language_version,
            &self.definition_fingerprint,
            &self.grammar_fingerprint,
            self.coverage,
            &self.sorts,
            &self.constructors,
        ))
        .map_err(|error| ProjectionHostCompoundProfileErrorV2::Encoding(error.to_string()))?;
        let signature_fingerprint = commit(b"mettail-projection-host-signature/2\0", &signature);
        let codec = postcard::to_allocvec(&(self.profile_abi, &signature_fingerprint, &self.codec))
            .map_err(|error| ProjectionHostCompoundProfileErrorV2::Encoding(error.to_string()))?;
        Ok(ProjectionHostCompoundProfileDigestsV2 {
            signature_fingerprint,
            codec_profile_fingerprint: commit(b"mettail-projection-host-codec/2\0", &codec),
            profile_fingerprint: commit(b"mettail-projection-host-profile/2\0", &payload),
        })
    }

    pub fn raw_signature(
        &self,
    ) -> Result<ProjectionHostSignatureV1, ProjectionHostCompoundProfileErrorV2> {
        let digests = self.digests()?;
        Ok(ProjectionHostSignatureV1 {
            signature_fingerprint: digests.signature_fingerprint,
            codec_profile_fingerprint: digests.codec_profile_fingerprint,
            sorts: self.sorts.clone(),
            constructors: self.constructors.clone(),
        })
    }
}

impl ProjectionHostCompoundProfileRecordV2 {
    pub fn new(
        payload: ProjectionHostCompoundProfilePayloadV2,
    ) -> Result<Self, ProjectionHostCompoundProfileErrorV2> {
        let claimed_digests = payload.digests()?;
        Ok(Self { payload, claimed_digests })
    }

    pub fn validate(&self) -> Result<(), ProjectionHostCompoundProfileErrorV2> {
        if self.claimed_digests != self.payload.digests()? {
            return Err(ProjectionHostCompoundProfileErrorV2::ClaimedDigestMismatch);
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ProjectionHostCompoundProfileErrorV2> {
        self.validate()?;
        postcard::to_allocvec(self)
            .map_err(|error| ProjectionHostCompoundProfileErrorV2::Encoding(error.to_string()))
    }

    pub fn decode_canonical(bytes: &[u8]) -> Result<Self, ProjectionHostCompoundProfileErrorV2> {
        let record: Self = postcard::from_bytes(bytes)
            .map_err(|error| ProjectionHostCompoundProfileErrorV2::Decoding(error.to_string()))?;
        if record.canonical_bytes()? != bytes {
            return Err(ProjectionHostCompoundProfileErrorV2::NoncanonicalEncoding);
        }
        Ok(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TheorySortKindV1;

    fn fixture() -> ProjectionHostCompoundProfilePayloadV2 {
        let signed_term_label = "Rholang::Proc::PCostSignedTerm";
        let categories = ["Proc", "CostSig", "CostStack"]
            .into_iter()
            .enumerate()
            .map(|(index, name)| ProjectionHostCompoundCategoryRouteV2 {
                category: CategoryId(index as u32),
                name: name.into(),
                generated_category_tag: index as u32,
            })
            .collect();
        ProjectionHostCompoundProfilePayloadV2 {
            profile_abi: PROJECTION_HOST_COMPOUND_PROFILE_ABI_V2,
            language_name: "Rholang".into(),
            language_version: "1.4-test".into(),
            definition_fingerprint: "checked-definition".into(),
            grammar_fingerprint: [1; 32],
            coverage: ProjectionHostCoverageV1::ExactFragment,
            sorts: ["Proc", "CostSig", "CostStack"]
                .into_iter()
                .map(|name| TheorySortV1 {
                    name: name.into(),
                    kind: TheorySortKindV1::Syntax { literal: None },
                })
                .collect(),
            constructors: vec![TheoryConstructorV1 {
                name: signed_term_label.into(),
                domain: vec!["Proc".into(), "CostSig".into()],
                codomain: "Proc".into(),
            }],
            codec: ProjectionHostCompoundCodecProfileV2 {
                codec_abi: PROJECTION_HOST_COMPOUND_CODEC_ABI_V2,
                provider_abi: "test/compound-codec/2".into(),
                implementation_commitment: [2; 32],
                descriptor: ProjectionHostCompoundCodecDescriptorV2 {
                    domain: ProjectionHostCompoundDomainV2::SelectedRootRoutes,
                    semantic_key_abi: 2,
                    grammar_fingerprint: [1; 32],
                    proc_category: CategoryId(0),
                    cost_signature_category: CategoryId(1),
                    cost_stack_category: CategoryId(2),
                    categories,
                    atom_schemas: Vec::new(),
                    operators: vec![ProjectionHostCompoundOperatorRouteV2 {
                        operator: SemanticOperatorId(11),
                        category: CategoryId(0),
                        constructor: ConstructorId(15),
                        generated_constructor_tag: 7,
                        stable_discriminant: 11,
                        label: signed_term_label.into(),
                        origin: SemanticOperatorOriginV1::Generated {
                            family: "generated-constructor".into(),
                            ordinal: 7,
                        },
                        fields: vec![
                            SemanticFieldSchemaV1::Child { category: CategoryId(0) },
                            SemanticFieldSchemaV1::Child { category: CategoryId(1) },
                        ],
                    }],
                    sequences: Vec::new(),
                },
            },
        }
    }

    #[test]
    fn v2_compound_profile_is_canonical_and_distinct_from_v1() {
        let payload = fixture();
        let record = ProjectionHostCompoundProfileRecordV2::new(payload.clone()).unwrap();
        let bytes = record.canonical_bytes().unwrap();
        assert_eq!(
            ProjectionHostCompoundProfileRecordV2::decode_canonical(&bytes).unwrap(),
            record
        );
        let signature = payload.raw_signature().unwrap();
        assert_eq!(signature.signature_fingerprint, record.claimed_digests.signature_fingerprint);
        assert_eq!(
            signature.codec_profile_fingerprint,
            record.claimed_digests.codec_profile_fingerprint
        );

        let mut changed = payload;
        changed.codec.descriptor.operators[0].stable_discriminant += 1;
        assert_ne!(
            changed.digests().unwrap().profile_fingerprint,
            record.claimed_digests.profile_fingerprint
        );
        let mut forged = record;
        forged.payload.codec.implementation_commitment = [9; 32];
        assert_eq!(
            forged.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::ClaimedDigestMismatch)
        );
    }

    #[test]
    fn compound_fragment_requires_exact_constructor_label() {
        let mut payload = fixture();
        assert!(payload.validate().is_ok());
        payload.constructors[0].name = "PCostSignedTerm".into();
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor(
                "selected constructor field signature"
            ))
        );
    }

    #[test]
    fn compound_fragment_rejects_missing_or_opaque_child_route() {
        let mut payload = fixture();
        payload.codec.descriptor.categories.pop();
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor(
                "required compound categories"
            ))
        );
        let mut payload = fixture();
        payload.codec.descriptor.operators[0].fields[1] =
            SemanticFieldSchemaV1::Child { category: CategoryId(99) };
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor(
                "child outside fragment"
            ))
        );
        let mut payload = fixture();
        payload.codec.descriptor.operators[0].fields[1] =
            SemanticFieldSchemaV1::Opaque { schema: 0 };
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor("opaque coefficient"))
        );
    }

    #[test]
    fn sequence_field_requires_exact_nil_cons_sort_and_order() {
        let mut payload = fixture();
        payload.codec.descriptor.operators[0].fields[0] =
            SemanticFieldSchemaV1::Sequence { element: CategoryId(0) };
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor(
                "sequence field lacks list algebra"
            ))
        );
        payload
            .codec
            .descriptor
            .sequences
            .push(ProjectionHostCompoundSequenceRouteV2 {
                element: CategoryId(0),
                sort_name: "Rholang::Sequence::Proc".into(),
                nil_name: "Rholang::Sequence::Proc::Nil".into(),
                cons_name: "Rholang::Sequence::Proc::Cons".into(),
            });
        payload.sorts.push(TheorySortV1 {
            name: "Rholang::Sequence::Proc".into(),
            kind: TheorySortKindV1::Syntax { literal: None },
        });
        payload.constructors[0].domain[0] = "Rholang::Sequence::Proc".into();
        payload.constructors.extend([
            TheoryConstructorV1 {
                name: "Rholang::Sequence::Proc::Nil".into(),
                domain: Vec::new(),
                codomain: "Rholang::Sequence::Proc".into(),
            },
            TheoryConstructorV1 {
                name: "Rholang::Sequence::Proc::Cons".into(),
                domain: vec!["Proc".into(), "Rholang::Sequence::Proc".into()],
                codomain: "Rholang::Sequence::Proc".into(),
            },
        ]);
        assert!(payload.validate().is_ok());
        payload.constructors[2].domain.reverse();
        assert_eq!(
            payload.validate(),
            Err(ProjectionHostCompoundProfileErrorV2::InvalidDescriptor(
                "sequence Nil/Cons signatures"
            ))
        );
    }
}
