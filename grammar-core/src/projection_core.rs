//! Versioned, endpoint-bound GSLT projection declarations.
//!
//! The legacy `LanguageCoreV1` postcard shape and fingerprint remain exact.
//! A projected language has a distinct outer artifact and commitment; its
//! rule bodies reuse `TheoryRewriteV1`'s existing flat arena rather than a
//! second expression language.

use crate::{
    LanguageCoreV1, TheoryConstructorV1, TheoryRewriteV1, TheoryRuleProgramId,
    TheorySemanticImageV1, TheorySortId, TheorySortV1,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

pub const PROJECTED_LANGUAGE_CORE_ABI_V1: u16 = 1;
pub const PROJECTED_THEORY_IMAGE_ABI_V1: u16 = 1;

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
