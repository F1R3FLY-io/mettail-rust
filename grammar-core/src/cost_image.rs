//! Source-exact grade roots for the separately checked `Cost(G)` image.
//!
//! The semantic image owns the compiled rewrite programs and flat term arenas.
//! This image adds only a fingerprint-bound mapping from each directed rewrite
//! to a signature-sort term in *that rewrite's own arena*. Its validation is
//! independent of the transition matcher: a grade cannot be fabricated from
//! an effect class, parser rank, host-work counter, or a caller's receipt.
//! Grade construction must reuse the successful rewrite's substitution.

use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::{
    LanguageCoreV1, TheoryConstructorId, TheoryImageAdmissionLimits, TheoryImageError,
    TheoryResourceProfileV1, TheoryRuleOriginV1, TheoryRuleProgramId, TheorySemanticImageV1,
    TheorySortId, TheoryTermId,
};

mod source_laws;
pub use source_laws::{
    SourceSignatureLawV1, SourceSignatureLawWitnessV1, VerifiedSourceSignatureAcuV1,
};

pub const COST_IMAGE_ABI_V1: u16 = 1;
pub const COST_IMAGE_ABI_CURRENT: u16 = COST_IMAGE_ABI_V1;
const COST_IMAGE_MAGIC: &[u8; 8] = b"MTCOST1\0";
const COST_IMAGE_HEADER_BYTES: usize = 8 + 2 + 32 + 32 + 32 + 4 + 4 + 4 + 4;
const COST_IMAGE_RULE_BYTES: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostRuleImageV1 {
    pub program: TheoryRuleProgramId,
    pub grade_term: TheoryTermId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CostImageV1 {
    pub abi: u16,
    pub language_fingerprint: [u8; 32],
    pub theory_fingerprint: [u8; 32],
    pub semantic_image_fingerprint: [u8; 32],
    pub grade_sort: TheorySortId,
    pub unit_constructor: TheoryConstructorId,
    pub product_constructor: TheoryConstructorId,
    /// Dense source-rewrite order; equations never receive a consumed grade.
    pub rules: Vec<CostRuleImageV1>,
}

/// A borrowed cost image admitted against one exact canonical language and
/// semantic image. The runtime grade path accepts this view, not raw cache
/// bytes or a caller-constructed `CostImageV1`.
#[derive(Clone, Copy, Debug)]
pub struct VerifiedCostImageV1<'a> {
    image: &'a CostImageV1,
    language: &'a LanguageCoreV1,
    semantic: &'a TheorySemanticImageV1,
    fingerprint: [u8; 32],
}

/// A private, immutable installation witness. Only a successful source-exact
/// compilation can mint it; a live caller cannot supply a validation marker.
/// The owned arcs keep the checked source and image identical to the objects
/// subsequently borrowed by the executor.
pub(crate) struct InstalledValidatedCostImageV1 {
    image: Arc<CostImageV1>,
    language: Arc<LanguageCoreV1>,
    semantic: Arc<TheorySemanticImageV1>,
    limits_fingerprint: [u8; 32],
    fingerprint: [u8; 32],
}

impl InstalledValidatedCostImageV1 {
    pub(crate) fn compile(
        language: Arc<LanguageCoreV1>,
        semantic: Arc<TheorySemanticImageV1>,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Option<Self>, CostImageError> {
        // Compilation performs the complete source, semantic-image, and grade
        // validation before an immutable witness can be created.
        let Some(image) = CostImageV1::compile(&language, &semantic, limits)? else {
            return Ok(None);
        };
        let fingerprint = image.fingerprint();
        Ok(Some(Self {
            image: Arc::new(image),
            language,
            semantic,
            limits_fingerprint: limits.fingerprint(),
            fingerprint,
        }))
    }

    pub(crate) fn image(&self) -> &CostImageV1 {
        &self.image
    }

    pub(crate) fn fingerprint(&self) -> [u8; 32] {
        self.fingerprint
    }

    pub(crate) fn limits_fingerprint(&self) -> [u8; 32] {
        self.limits_fingerprint
    }

    pub(crate) fn verified(
        &self,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<VerifiedCostImageV1<'_>, CostImageError> {
        if limits.fingerprint() != self.limits_fingerprint {
            return Err(CostImageError::FingerprintMismatch("admission profile"));
        }
        Ok(VerifiedCostImageV1 {
            image: &self.image,
            language: &self.language,
            semantic: &self.semantic,
            fingerprint: self.fingerprint,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CostImageError {
    InvalidSemanticImage(TheoryImageError),
    NotCosted,
    MissingInstalledImage,
    UnsupportedAbi(u16),
    FingerprintMismatch(&'static str),
    ResourceProfileMismatch,
    RuleCountMismatch,
    RuleMismatch(usize),
    GradeSortMismatch(usize),
    SignatureConstructorMismatch(&'static str),
    LengthOverflow,
    InvalidEncoding,
    EncodedLimitExceeded,
}

impl From<TheoryImageError> for CostImageError {
    fn from(error: TheoryImageError) -> Self {
        Self::InvalidSemanticImage(error)
    }
}

impl CostImageV1 {
    /// Compile only references into the already checked semantic image. No
    /// rewrite automaton, substitution engine, or grade evaluator is cloned.
    pub fn compile(
        language: &LanguageCoreV1,
        semantic: &TheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Option<Self>, CostImageError> {
        semantic.validate(language, limits)?;
        let Some(cost) = &language.theory.cost else {
            return Ok(None);
        };
        let TheoryResourceProfileV1::Costed { grade_sort } = semantic.resource_profile else {
            return Err(CostImageError::ResourceProfileMismatch);
        };
        let grade_roots: BTreeMap<&str, TheoryTermId> = cost
            .grade_rules
            .iter()
            .map(|row| (row.rewrite.as_str(), row.term))
            .collect();
        let mut rules = Vec::new();
        rules
            .try_reserve_exact(language.theory.rewrites.len())
            .map_err(|_| CostImageError::LengthOverflow)?;
        for program in &semantic.rules {
            let TheoryRuleOriginV1::Rewrite { source } = program.origin else {
                continue;
            };
            let source = usize::try_from(source).map_err(|_| CostImageError::LengthOverflow)?;
            let rewrite = language
                .theory
                .rewrites
                .get(source)
                .ok_or(CostImageError::RuleMismatch(source))?;
            let grade_term = *grade_roots
                .get(rewrite.name.as_str())
                .ok_or(CostImageError::RuleMismatch(source))?;
            if program
                .terms
                .get(grade_term.0 as usize)
                .map(|term| term.sort)
                != Some(grade_sort)
            {
                return Err(CostImageError::GradeSortMismatch(source));
            }
            rules.push(CostRuleImageV1 { program: program.id, grade_term });
        }
        let image = Self {
            abi: COST_IMAGE_ABI_CURRENT,
            language_fingerprint: semantic.language_fingerprint,
            theory_fingerprint: semantic.theory_fingerprint,
            semantic_image_fingerprint: semantic.fingerprint()?,
            grade_sort,
            unit_constructor: signature_constructor(language, &cost.unit, "unit")?,
            product_constructor: signature_constructor(language, &cost.product, "product")?,
            rules,
        };
        image.validate(language, semantic, limits)?;
        Ok(Some(image))
    }

    /// Independently check the image against the canonical source and the
    /// source-exact semantic image. Cache bytes alone are never authority.
    pub fn validate(
        &self,
        language: &LanguageCoreV1,
        semantic: &TheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<(), CostImageError> {
        semantic.validate(language, limits)?;
        if self.abi != COST_IMAGE_ABI_CURRENT {
            return Err(CostImageError::UnsupportedAbi(self.abi));
        }
        let Some(cost) = &language.theory.cost else {
            return Err(CostImageError::NotCosted);
        };
        let TheoryResourceProfileV1::Costed { grade_sort } = semantic.resource_profile else {
            return Err(CostImageError::ResourceProfileMismatch);
        };
        if self.grade_sort != grade_sort {
            return Err(CostImageError::ResourceProfileMismatch);
        }
        if self.unit_constructor != signature_constructor(language, &cost.unit, "unit")? {
            return Err(CostImageError::SignatureConstructorMismatch("unit"));
        }
        if self.product_constructor != signature_constructor(language, &cost.product, "product")? {
            return Err(CostImageError::SignatureConstructorMismatch("product"));
        }
        if self.language_fingerprint != semantic.language_fingerprint {
            return Err(CostImageError::FingerprintMismatch("language"));
        }
        if self.theory_fingerprint != semantic.theory_fingerprint {
            return Err(CostImageError::FingerprintMismatch("theory"));
        }
        if self.semantic_image_fingerprint != semantic.fingerprint()? {
            return Err(CostImageError::FingerprintMismatch("semantic image"));
        }
        if self.rules.len() != language.theory.rewrites.len() {
            return Err(CostImageError::RuleCountMismatch);
        }
        let grade_roots: BTreeMap<&str, TheoryTermId> = cost
            .grade_rules
            .iter()
            .map(|row| (row.rewrite.as_str(), row.term))
            .collect();
        let equation_programs = language
            .theory
            .equations
            .len()
            .checked_mul(2)
            .ok_or(CostImageError::LengthOverflow)?;
        for (source, rewrite) in language.theory.rewrites.iter().enumerate() {
            let program_index = equation_programs
                .checked_add(source)
                .ok_or(CostImageError::LengthOverflow)?;
            let program = semantic
                .rules
                .get(program_index)
                .ok_or(CostImageError::RuleMismatch(source))?;
            let source_id = u32::try_from(source).map_err(|_| CostImageError::LengthOverflow)?;
            if program.origin != (TheoryRuleOriginV1::Rewrite { source: source_id })
                || program.name != rewrite.name
            {
                return Err(CostImageError::RuleMismatch(source));
            }
            let expected_grade = *grade_roots
                .get(rewrite.name.as_str())
                .ok_or(CostImageError::RuleMismatch(source))?;
            let row = self
                .rules
                .get(source)
                .ok_or(CostImageError::RuleCountMismatch)?;
            if row.program != program.id || row.grade_term != expected_grade {
                return Err(CostImageError::RuleMismatch(source));
            }
            if program
                .terms
                .get(row.grade_term.0 as usize)
                .map(|term| term.sort)
                != Some(grade_sort)
            {
                return Err(CostImageError::GradeSortMismatch(source));
            }
        }
        Ok(())
    }

    pub fn verified<'a>(
        &'a self,
        language: &'a LanguageCoreV1,
        semantic: &'a TheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<VerifiedCostImageV1<'a>, CostImageError> {
        self.validate(language, semantic, limits)?;
        Ok(VerifiedCostImageV1 {
            image: self,
            language,
            semantic,
            fingerprint: self.fingerprint(),
        })
    }

    /// Domain-separated stable commitment without serializing a second copy.
    pub fn fingerprint(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mettail-cost-image/1\0");
        hasher.update(&self.abi.to_be_bytes());
        hasher.update(&self.language_fingerprint);
        hasher.update(&self.theory_fingerprint);
        hasher.update(&self.semantic_image_fingerprint);
        hasher.update(&self.grade_sort.0.to_be_bytes());
        hasher.update(&self.unit_constructor.0.to_be_bytes());
        hasher.update(&self.product_constructor.0.to_be_bytes());
        hasher.update(&(self.rules.len() as u64).to_be_bytes());
        for row in &self.rules {
            hasher.update(&row.program.0.to_be_bytes());
            hasher.update(&row.grade_term.0.to_be_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// Canonical flat cache encoding. The source and semantic image are
    /// checked before emission; the encoded byte count is independently
    /// bounded by admission limits.
    pub fn encode(
        &self,
        language: &LanguageCoreV1,
        semantic: &TheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Vec<u8>, CostImageError> {
        self.validate(language, semantic, limits)?;
        let length = encoded_length(self.rules.len())?;
        if length > limits.max_encoded_bytes {
            return Err(CostImageError::EncodedLimitExceeded);
        }
        let count = u32::try_from(self.rules.len()).map_err(|_| CostImageError::LengthOverflow)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(length)
            .map_err(|_| CostImageError::LengthOverflow)?;
        bytes.extend_from_slice(COST_IMAGE_MAGIC);
        bytes.extend_from_slice(&self.abi.to_be_bytes());
        bytes.extend_from_slice(&self.language_fingerprint);
        bytes.extend_from_slice(&self.theory_fingerprint);
        bytes.extend_from_slice(&self.semantic_image_fingerprint);
        bytes.extend_from_slice(&self.grade_sort.0.to_be_bytes());
        bytes.extend_from_slice(&self.unit_constructor.0.to_be_bytes());
        bytes.extend_from_slice(&self.product_constructor.0.to_be_bytes());
        bytes.extend_from_slice(&count.to_be_bytes());
        for row in &self.rules {
            bytes.extend_from_slice(&row.program.0.to_be_bytes());
            bytes.extend_from_slice(&row.grade_term.0.to_be_bytes());
        }
        debug_assert_eq!(bytes.len(), length);
        Ok(bytes)
    }

    /// Read an untrusted cache only at the exact source-derived length. This
    /// prevents an encoded count from triggering an unbounded allocation.
    pub fn decode(
        bytes: &[u8],
        language: &LanguageCoreV1,
        semantic: &TheorySemanticImageV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<Self, CostImageError> {
        if bytes.len() > limits.max_encoded_bytes {
            return Err(CostImageError::EncodedLimitExceeded);
        }
        let expected_count = language.theory.rewrites.len();
        if bytes.len() != encoded_length(expected_count)? {
            return Err(CostImageError::InvalidEncoding);
        }
        let mut cursor = 0;
        if &read_bytes::<8>(bytes, &mut cursor)? != COST_IMAGE_MAGIC {
            return Err(CostImageError::InvalidEncoding);
        }
        let abi = u16::from_be_bytes(read_bytes(bytes, &mut cursor)?);
        let language_fingerprint = read_bytes(bytes, &mut cursor)?;
        let theory_fingerprint = read_bytes(bytes, &mut cursor)?;
        let semantic_image_fingerprint = read_bytes(bytes, &mut cursor)?;
        let grade_sort = TheorySortId(u32::from_be_bytes(read_bytes(bytes, &mut cursor)?));
        let unit_constructor =
            TheoryConstructorId(u32::from_be_bytes(read_bytes(bytes, &mut cursor)?));
        let product_constructor =
            TheoryConstructorId(u32::from_be_bytes(read_bytes(bytes, &mut cursor)?));
        let count = u32::from_be_bytes(read_bytes(bytes, &mut cursor)?);
        if usize::try_from(count).map_err(|_| CostImageError::LengthOverflow)? != expected_count {
            return Err(CostImageError::InvalidEncoding);
        }
        let mut rules = Vec::new();
        rules
            .try_reserve_exact(expected_count)
            .map_err(|_| CostImageError::LengthOverflow)?;
        for _ in 0..expected_count {
            rules.push(CostRuleImageV1 {
                program: TheoryRuleProgramId(u32::from_be_bytes(read_bytes(bytes, &mut cursor)?)),
                grade_term: TheoryTermId(u32::from_be_bytes(read_bytes(bytes, &mut cursor)?)),
            });
        }
        if cursor != bytes.len() {
            return Err(CostImageError::InvalidEncoding);
        }
        let image = Self {
            abi,
            language_fingerprint,
            theory_fingerprint,
            semantic_image_fingerprint,
            grade_sort,
            unit_constructor,
            product_constructor,
            rules,
        };
        image.validate(language, semantic, limits)?;
        Ok(image)
    }
}

fn signature_constructor(
    language: &LanguageCoreV1,
    name: &str,
    role: &'static str,
) -> Result<TheoryConstructorId, CostImageError> {
    let position = language
        .theory
        .constructors
        .iter()
        .position(|constructor| constructor.name == name)
        .ok_or(CostImageError::SignatureConstructorMismatch(role))?;
    Ok(TheoryConstructorId(
        u32::try_from(position).map_err(|_| CostImageError::LengthOverflow)?,
    ))
}

fn encoded_length(rules: usize) -> Result<usize, CostImageError> {
    rules
        .checked_mul(COST_IMAGE_RULE_BYTES)
        .and_then(|bytes| bytes.checked_add(COST_IMAGE_HEADER_BYTES))
        .ok_or(CostImageError::LengthOverflow)
}

fn read_bytes<const N: usize>(bytes: &[u8], cursor: &mut usize) -> Result<[u8; N], CostImageError> {
    let end = cursor
        .checked_add(N)
        .ok_or(CostImageError::LengthOverflow)?;
    let value = bytes
        .get(*cursor..end)
        .ok_or(CostImageError::InvalidEncoding)?;
    *cursor = end;
    value
        .try_into()
        .map_err(|_| CostImageError::InvalidEncoding)
}

impl VerifiedCostImageV1<'_> {
    pub fn language(&self) -> &LanguageCoreV1 {
        self.language
    }

    pub fn semantic_image(&self) -> &TheorySemanticImageV1 {
        self.semantic
    }

    pub fn fingerprint(&self) -> [u8; 32] {
        self.fingerprint
    }

    pub fn grade_sort(&self) -> TheorySortId {
        self.image.grade_sort
    }

    pub fn unit_constructor(&self) -> TheoryConstructorId {
        self.image.unit_constructor
    }

    pub fn product_constructor(&self) -> TheoryConstructorId {
        self.image.product_constructor
    }

    /// The grade root for an already matched directed rewrite. The caller
    /// still must materialize it from that *same* match substitution.
    pub fn grade_root(&self, program: TheoryRuleProgramId) -> Option<TheoryTermId> {
        self.image
            .rules
            .binary_search_by_key(&program, |row| row.program)
            .ok()
            .map(|index| self.image.rules[index].grade_term)
    }
}
