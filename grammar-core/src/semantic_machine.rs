//! Checked projection from canonical semantic terms to a source-neutral
//! tree-automaton carrier.
//!
//! [`SemanticTermImageV1`] is the authoritative, lossless value. A
//! [`SemanticMachineImageV1`] is a replaceable derived artifact: it describes
//! how each typed field becomes a finite sequence of machine nodes without
//! embedding source text, executable callbacks, or authority. Projection is a
//! single forward pass over the canonical post-order arena, so native call
//! stack use is constant even for deeply nested terms.

use crate::semantic_term::{
    checked_add, checked_u32, copy_bytes, decode_collection_kind, empty_vec,
    encode_collection_kind, write_u16, write_u32, ImageReader,
};
use crate::{
    CategoryId, CollectionKind, GrammarCoreV1, PathMapModeV1, RuntimeCapabilityBindings,
    SemanticCollectionEntryV1, SemanticFieldSchemaV1, SemanticFieldV1, SemanticOperatorId,
    SemanticPathMapEntryV1, SemanticSignatureError, SemanticSignatureV1,
    SemanticTermAdmissionLimits, SemanticTermImageError, SemanticTermImageV1, SemanticVariableV1,
};
use std::collections::{BTreeMap, BTreeSet};

pub const SEMANTIC_MACHINE_IMAGE_ABI_V1: u16 = 1;

const SEMANTIC_MACHINE_IMAGE_MAGIC: &[u8; 8] = b"MTMIMG01";
const MAX_MACHINE_LABEL_BYTES: usize = 512;

/// Whether an e-node's children retain source order or are canonicalized by
/// their exact Dovetail class keys. Canonicalization changes representation,
/// never language meaning, and is admitted only for Bag and Set spines.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MachineChildOrderV1 {
    Ordered,
    CanonicalExactKey,
}

/// A machine operator before value-dependent payload segments are appended.
///
/// `label` is observation-only. Exact identity is the stable discriminant
/// followed by the framed payload segments. Validation requires one label per
/// discriminant and prevents auxiliary discriminants from colliding with
/// semantic constructor discriminants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineOperatorTemplateV1 {
    pub stable_discriminant: u32,
    pub fixed_payload_segments: Vec<Vec<u8>>,
    pub label: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineFieldProjectionV1 {
    Child,
    Sequence {
        spine: MachineOperatorTemplateV1,
        child_order: MachineChildOrderV1,
    },
    ValueCollection {
        kind: CollectionKind,
        spine: MachineOperatorTemplateV1,
        child_order: MachineChildOrderV1,
    },
    PairCollection {
        kind: CollectionKind,
        spine: MachineOperatorTemplateV1,
        pair: MachineOperatorTemplateV1,
        child_order: MachineChildOrderV1,
    },
    /// A whole-constructor value collection whose semantic constructor is
    /// already the machine spine. The collection entries become that main
    /// node's children directly, so no auxiliary node changes legacy shape.
    InlineValueCollection {
        kind: CollectionKind,
        child_order: MachineChildOrderV1,
    },
    /// A whole-constructor pair collection whose semantic constructor is the
    /// machine spine. Exact pair nodes preserve key-value boundaries while
    /// their roots become the main node's children directly.
    InlinePairCollection {
        kind: CollectionKind,
        pair: MachineOperatorTemplateV1,
        child_order: MachineChildOrderV1,
    },
    /// A whole-constructor PathMap. The first main child is an exact
    /// payload-tagged mode leaf. Set keys follow directly; map entries are
    /// represented by exact pair nodes.
    InlinePathMap {
        empty: MachineOperatorTemplateV1,
        set: MachineOperatorTemplateV1,
        map: MachineOperatorTemplateV1,
        pair: MachineOperatorTemplateV1,
    },
    Optional {
        none: MachineOperatorTemplateV1,
    },
    OptionalSequence {
        none: MachineOperatorTemplateV1,
        spine: MachineOperatorTemplateV1,
        child_order: MachineChildOrderV1,
    },
    OptionalTokenText {
        none: MachineOperatorTemplateV1,
        leaf: MachineOperatorTemplateV1,
    },
    Scope {
        arity: MachineOperatorTemplateV1,
    },
    Variable {
        leaf: MachineOperatorTemplateV1,
    },
    Atom {
        leaf: MachineOperatorTemplateV1,
    },
    TokenText {
        leaf: MachineOperatorTemplateV1,
    },
    Opaque {
        leaf: MachineOperatorTemplateV1,
    },
    Unit {
        leaf: MachineOperatorTemplateV1,
    },
    /// Project exact bytes as one framed dynamic payload segment. The machine
    /// never interprets the segment as text.
    Bytes {
        leaf: MachineOperatorTemplateV1,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineOperatorProjectionV1 {
    pub operator: SemanticOperatorId,
    pub main: MachineOperatorTemplateV1,
    pub fields: Vec<MachineFieldProjectionV1>,
}

/// Versioned, fingerprint-bound table which compiles semantic values into the
/// common WPDA/e-graph carrier. The table is data, not bytecode: every entry is
/// one constructor of a closed polynomial projection language.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticMachineImageV1 {
    pub abi: u16,
    pub signature_fingerprint: [u8; 32],
    pub operators: Vec<MachineOperatorProjectionV1>,
}

/// Architecture-facing name for [`SemanticMachineImageV1`].
pub type StructuralProjectionImageV1 = SemanticMachineImageV1;

/// Fully instantiated operator carried by a projected machine node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticMachineOperatorV1 {
    pub stable_discriminant: u32,
    pub payload_segments: Vec<Vec<u8>>,
    pub label: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticMachineNodeV1 {
    pub operator: SemanticMachineOperatorV1,
    pub children: Vec<u32>,
    pub child_order: MachineChildOrderV1,
}

/// Ephemeral flat output of projection. References point backward; roots retain
/// the semantic forest's order and multiplicity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticMachineTermV1 {
    pub nodes: Vec<SemanticMachineNodeV1>,
    pub roots: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticMachineAdmissionLimits {
    pub max_encoded_bytes: usize,
    pub max_operators: usize,
    pub max_fields_per_operator: usize,
    pub max_total_fields: usize,
    pub max_templates: usize,
    pub max_segments_per_template: usize,
    pub max_segment_bytes: usize,
    pub max_total_template_bytes: usize,
    pub max_projected_nodes: usize,
    pub max_projected_children: usize,
    pub max_projected_payload_bytes: usize,
}

impl Default for SemanticMachineAdmissionLimits {
    fn default() -> Self {
        Self {
            max_encoded_bytes: 64 * 1024 * 1024,
            max_operators: 1_000_000,
            max_fields_per_operator: 65_536,
            max_total_fields: 10_000_000,
            max_templates: 10_000_000,
            max_segments_per_template: 256,
            max_segment_bytes: 16 * 1024 * 1024,
            max_total_template_bytes: 64 * 1024 * 1024,
            max_projected_nodes: 10_000_000,
            max_projected_children: 20_000_000,
            max_projected_payload_bytes: 128 * 1024 * 1024,
        }
    }
}

/// Immutable checked-language context reused while projecting semantic terms.
///
/// Bundling the signature, grammar, capabilities, and admission limits makes
/// their common lifetime explicit and prevents call sites from accidentally
/// mixing independently configured projections.
#[derive(Clone, Copy)]
pub struct SemanticMachineProjectionContext<'a> {
    signature: &'a SemanticSignatureV1,
    grammar: &'a GrammarCoreV1,
    bindings: &'a RuntimeCapabilityBindings,
    term_limits: SemanticTermAdmissionLimits,
    machine_limits: SemanticMachineAdmissionLimits,
}

impl<'a> SemanticMachineProjectionContext<'a> {
    pub fn new(
        signature: &'a SemanticSignatureV1,
        grammar: &'a GrammarCoreV1,
        bindings: &'a RuntimeCapabilityBindings,
        term_limits: SemanticTermAdmissionLimits,
        machine_limits: SemanticMachineAdmissionLimits,
    ) -> Self {
        Self {
            signature,
            grammar,
            bindings,
            term_limits,
            machine_limits,
        }
    }

    pub fn machine_limits(self) -> SemanticMachineAdmissionLimits {
        self.machine_limits
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticMachineImageError {
    Signature(SemanticSignatureError),
    Term(SemanticTermImageError),
    Codec(SemanticTermImageError),
    UnsupportedAbi(u16),
    SignatureFingerprintMismatch,
    LimitExceeded(&'static str),
    NonDenseOperatorId {
        expected: u32,
        actual: u32,
    },
    OperatorCount {
        expected: usize,
        actual: usize,
    },
    MainDiscriminant {
        operator: SemanticOperatorId,
        expected: u32,
        actual: u32,
    },
    MainLabel {
        operator: SemanticOperatorId,
    },
    FieldCount {
        operator: SemanticOperatorId,
        expected: usize,
        actual: usize,
    },
    FieldProjection {
        operator: SemanticOperatorId,
        field: u32,
    },
    EmptyLabel(u32),
    LabelLimit(u32),
    DiscriminantLabelConflict(u32),
    DuplicateLabel(String),
    AuxiliaryMainCollision(u32),
    IncompatibleTemplateReuse(u32),
    InvalidMagic,
    InvalidTag(u8),
    InvalidUtf8,
    TrailingBytes,
    LengthOverflow,
    Allocation,
    UnknownOperator(SemanticOperatorId),
    ProjectedReference(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum AuxiliaryRole {
    Sequence(CategoryId),
    ValueCollection(CollectionKind, CategoryId),
    Pair(CollectionKind, CategoryId, CategoryId),
    PathMapMode(PathMapModeV1, CategoryId, CategoryId),
    PathMapPair(CategoryId, CategoryId),
    CollectionSpine(CollectionKind, CategoryId, Option<CategoryId>),
    Optional(CategoryId),
    OptionalSequence(CategoryId),
    OptionalTokenText,
    Scope(CategoryId, CategoryId),
    Variable(CategoryId),
    Atom(u32),
    TokenText,
    Opaque(u32),
    Unit,
    Bytes,
}

#[derive(Default)]
struct ValidationCounts {
    fields: usize,
    templates: usize,
    template_bytes: usize,
}

struct MachineValidation<'a> {
    main_discriminants: &'a BTreeSet<u32>,
    labels_by_discriminant: BTreeMap<u32, String>,
    discriminants_by_label: BTreeMap<String, u32>,
    auxiliary_roles: BTreeMap<(u32, Vec<Vec<u8>>), AuxiliaryRole>,
    counts: ValidationCounts,
    limits: SemanticMachineAdmissionLimits,
}

impl SemanticMachineImageV1 {
    pub fn validate(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticMachineAdmissionLimits,
    ) -> Result<(), SemanticMachineImageError> {
        signature
            .validate(grammar, bindings)
            .map_err(SemanticMachineImageError::Signature)?;
        if self.abi != SEMANTIC_MACHINE_IMAGE_ABI_V1 {
            return Err(SemanticMachineImageError::UnsupportedAbi(self.abi));
        }
        let expected_fingerprint = signature
            .fingerprint()
            .map_err(SemanticMachineImageError::Signature)?;
        if self.signature_fingerprint != expected_fingerprint {
            return Err(SemanticMachineImageError::SignatureFingerprintMismatch);
        }
        enforce_machine_limit(self.operators.len(), limits.max_operators, "operators")?;
        if self.operators.len() != signature.operators.len() {
            return Err(SemanticMachineImageError::OperatorCount {
                expected: signature.operators.len(),
                actual: self.operators.len(),
            });
        }

        let main_discriminants: BTreeSet<u32> = signature
            .operators
            .iter()
            .map(|operator| operator.stable_discriminant)
            .collect();
        let mut validation = MachineValidation {
            main_discriminants: &main_discriminants,
            labels_by_discriminant: BTreeMap::new(),
            discriminants_by_label: BTreeMap::new(),
            auxiliary_roles: BTreeMap::new(),
            counts: ValidationCounts::default(),
            limits,
        };

        for (index, (projection, declaration)) in
            self.operators.iter().zip(&signature.operators).enumerate()
        {
            let expected_id = u32::try_from(index)
                .map_err(|_| SemanticMachineImageError::LimitExceeded("operators"))?;
            if projection.operator.0 != expected_id {
                return Err(SemanticMachineImageError::NonDenseOperatorId {
                    expected: expected_id,
                    actual: projection.operator.0,
                });
            }
            if declaration.id != projection.operator {
                return Err(SemanticMachineImageError::NonDenseOperatorId {
                    expected: declaration.id.0,
                    actual: projection.operator.0,
                });
            }
            if projection.main.stable_discriminant != declaration.stable_discriminant {
                return Err(SemanticMachineImageError::MainDiscriminant {
                    operator: projection.operator,
                    expected: declaration.stable_discriminant,
                    actual: projection.main.stable_discriminant,
                });
            }
            if projection.main.label != declaration.label {
                return Err(SemanticMachineImageError::MainLabel { operator: projection.operator });
            }
            validation.validate_template(&projection.main)?;
            if projection.fields.len() != declaration.fields.len() {
                return Err(SemanticMachineImageError::FieldCount {
                    operator: projection.operator,
                    expected: declaration.fields.len(),
                    actual: projection.fields.len(),
                });
            }
            enforce_machine_limit(
                projection.fields.len(),
                limits.max_fields_per_operator,
                "fields per operator",
            )?;
            validation.counts.fields = validation
                .counts
                .fields
                .checked_add(projection.fields.len())
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
            enforce_machine_limit(
                validation.counts.fields,
                limits.max_total_fields,
                "total fields",
            )?;
            for (field_index, (field_projection, schema)) in projection
                .fields
                .iter()
                .zip(&declaration.fields)
                .enumerate()
            {
                validation.validate_field_projection(
                    projection.operator,
                    u32::try_from(field_index).map_err(|_| {
                        SemanticMachineImageError::LimitExceeded("fields per operator")
                    })?,
                    projection.fields.len(),
                    field_projection,
                    schema,
                )?;
            }
        }
        enforce_machine_limit(validation.counts.templates, limits.max_templates, "templates")?;
        enforce_machine_limit(
            validation.counts.template_bytes,
            limits.max_total_template_bytes,
            "template bytes",
        )?;
        Ok(())
    }
}

fn enforce_machine_limit(
    actual: usize,
    limit: usize,
    name: &'static str,
) -> Result<(), SemanticMachineImageError> {
    if actual > limit {
        return Err(SemanticMachineImageError::LimitExceeded(name));
    }
    Ok(())
}

impl MachineValidation<'_> {
    fn validate_template(
        &mut self,
        template: &MachineOperatorTemplateV1,
    ) -> Result<(), SemanticMachineImageError> {
        if template.label.is_empty() {
            return Err(SemanticMachineImageError::EmptyLabel(template.stable_discriminant));
        }
        if template.label.len() > MAX_MACHINE_LABEL_BYTES {
            return Err(SemanticMachineImageError::LabelLimit(template.stable_discriminant));
        }
        match self
            .labels_by_discriminant
            .get(&template.stable_discriminant)
        {
            Some(label) if label != &template.label => {
                return Err(SemanticMachineImageError::DiscriminantLabelConflict(
                    template.stable_discriminant,
                ));
            },
            Some(_) => {},
            None => {
                self.labels_by_discriminant
                    .insert(template.stable_discriminant, template.label.clone());
            },
        }
        match self.discriminants_by_label.get(&template.label) {
            Some(discriminant) if *discriminant != template.stable_discriminant => {
                return Err(SemanticMachineImageError::DuplicateLabel(template.label.clone()));
            },
            Some(_) => {},
            None => {
                self.discriminants_by_label
                    .insert(template.label.clone(), template.stable_discriminant);
            },
        }
        enforce_machine_limit(
            template.fixed_payload_segments.len(),
            self.limits.max_segments_per_template,
            "segments per template",
        )?;
        self.counts.templates = self
            .counts
            .templates
            .checked_add(1)
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        for segment in &template.fixed_payload_segments {
            enforce_machine_limit(segment.len(), self.limits.max_segment_bytes, "segment bytes")?;
            self.counts.template_bytes = self
                .counts
                .template_bytes
                .checked_add(segment.len())
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
        }
        Ok(())
    }

    fn validate_auxiliary(
        &mut self,
        template: &MachineOperatorTemplateV1,
        role: AuxiliaryRole,
    ) -> Result<(), SemanticMachineImageError> {
        if self
            .main_discriminants
            .contains(&template.stable_discriminant)
        {
            return Err(SemanticMachineImageError::AuxiliaryMainCollision(
                template.stable_discriminant,
            ));
        }
        self.validate_template(template)?;
        let identity = (template.stable_discriminant, template.fixed_payload_segments.clone());
        match self.auxiliary_roles.get(&identity) {
            Some(existing) if existing != &role => Err(
                SemanticMachineImageError::IncompatibleTemplateReuse(template.stable_discriminant),
            ),
            Some(_) => Ok(()),
            None => {
                self.auxiliary_roles.insert(identity, role);
                Ok(())
            },
        }
    }

    fn validate_field_projection(
        &mut self,
        operator: SemanticOperatorId,
        field: u32,
        field_count: usize,
        projection: &MachineFieldProjectionV1,
        schema: &SemanticFieldSchemaV1,
    ) -> Result<(), SemanticMachineImageError> {
        let invalid = || SemanticMachineImageError::FieldProjection { operator, field };
        match (projection, schema) {
            (MachineFieldProjectionV1::Child, SemanticFieldSchemaV1::Child { .. }) => Ok(()),
            (
                MachineFieldProjectionV1::Sequence { spine, child_order },
                SemanticFieldSchemaV1::Sequence { element },
            ) if *child_order == MachineChildOrderV1::Ordered => {
                self.validate_auxiliary(spine, AuxiliaryRole::Sequence(*element))
            },
            (
                MachineFieldProjectionV1::ValueCollection { kind, spine, child_order },
                SemanticFieldSchemaV1::Collection { kind: expected_kind, key: None, value },
            ) if kind == expected_kind && *child_order == collection_child_order(*kind) => {
                self.validate_auxiliary(spine, AuxiliaryRole::ValueCollection(*kind, *value))
            },
            (
                MachineFieldProjectionV1::PairCollection { kind, spine, pair, child_order },
                SemanticFieldSchemaV1::Collection {
                    kind: expected_kind,
                    key: Some(key),
                    value,
                },
            ) if kind == expected_kind
                && matches!(kind, CollectionKind::Map | CollectionKind::PathMap)
                && *child_order == MachineChildOrderV1::Ordered =>
            {
                self.validate_auxiliary(pair, AuxiliaryRole::Pair(*kind, *key, *value))?;
                self.validate_auxiliary(
                    spine,
                    AuxiliaryRole::CollectionSpine(*kind, *value, Some(*key)),
                )
            },
            (
                MachineFieldProjectionV1::InlineValueCollection { kind, child_order },
                SemanticFieldSchemaV1::Collection { kind: expected_kind, key: None, .. },
            ) if kind == expected_kind
                && field == 0
                && field_count == 1
                && *child_order == collection_child_order(*kind) =>
            {
                Ok(())
            },
            (
                MachineFieldProjectionV1::InlinePairCollection { kind, pair, child_order },
                SemanticFieldSchemaV1::Collection {
                    kind: expected_kind,
                    key: Some(key),
                    value,
                },
            ) if kind == expected_kind
                && matches!(kind, CollectionKind::Map | CollectionKind::PathMap)
                && field == 0
                && field_count == 1
                && *child_order == MachineChildOrderV1::Ordered =>
            {
                self.validate_auxiliary(pair, AuxiliaryRole::Pair(*kind, *key, *value))
            },
            (
                MachineFieldProjectionV1::InlinePathMap { empty, set, map, pair },
                SemanticFieldSchemaV1::PathMap { key, value },
            ) if field == 0 && field_count == 1 => {
                let templates = [empty, set, map, pair];
                for left in 0..templates.len() {
                    for right in left + 1..templates.len() {
                        if template_identities_equal(templates[left], templates[right]) {
                            return Err(SemanticMachineImageError::IncompatibleTemplateReuse(
                                templates[left].stable_discriminant,
                            ));
                        }
                    }
                }
                self.validate_auxiliary(
                    empty,
                    AuxiliaryRole::PathMapMode(PathMapModeV1::NeutralEmpty, *key, *value),
                )?;
                self.validate_auxiliary(
                    set,
                    AuxiliaryRole::PathMapMode(PathMapModeV1::Set, *key, *value),
                )?;
                self.validate_auxiliary(
                    map,
                    AuxiliaryRole::PathMapMode(PathMapModeV1::Map, *key, *value),
                )?;
                self.validate_auxiliary(pair, AuxiliaryRole::PathMapPair(*key, *value))
            },
            (
                MachineFieldProjectionV1::Optional { none },
                SemanticFieldSchemaV1::Optional { category },
            ) => self.validate_auxiliary(none, AuxiliaryRole::Optional(*category)),
            (
                MachineFieldProjectionV1::OptionalSequence { none, spine, child_order },
                SemanticFieldSchemaV1::OptionalSequence { element },
            ) if *child_order == MachineChildOrderV1::Ordered => {
                if none.stable_discriminant == spine.stable_discriminant {
                    return Err(SemanticMachineImageError::IncompatibleTemplateReuse(
                        none.stable_discriminant,
                    ));
                }
                self.validate_auxiliary(none, AuxiliaryRole::OptionalSequence(*element))?;
                self.validate_auxiliary(spine, AuxiliaryRole::Sequence(*element))
            },
            (
                MachineFieldProjectionV1::OptionalTokenText { none, leaf },
                SemanticFieldSchemaV1::OptionalTokenText,
            ) => {
                if none.stable_discriminant == leaf.stable_discriminant {
                    return Err(SemanticMachineImageError::IncompatibleTemplateReuse(
                        none.stable_discriminant,
                    ));
                }
                self.validate_auxiliary(none, AuxiliaryRole::OptionalTokenText)?;
                self.validate_auxiliary(leaf, AuxiliaryRole::TokenText)
            },
            (
                MachineFieldProjectionV1::Scope { arity },
                SemanticFieldSchemaV1::Scope { domain, body, .. },
            ) => self.validate_auxiliary(arity, AuxiliaryRole::Scope(*domain, *body)),
            (
                MachineFieldProjectionV1::Variable { leaf },
                SemanticFieldSchemaV1::Variable { category },
            ) => self.validate_auxiliary(leaf, AuxiliaryRole::Variable(*category)),
            (MachineFieldProjectionV1::Atom { leaf }, SemanticFieldSchemaV1::Atom { schema }) => {
                self.validate_auxiliary(leaf, AuxiliaryRole::Atom(*schema))
            },
            (MachineFieldProjectionV1::TokenText { leaf }, SemanticFieldSchemaV1::TokenText) => {
                self.validate_auxiliary(leaf, AuxiliaryRole::TokenText)
            },
            (
                MachineFieldProjectionV1::Opaque { leaf },
                SemanticFieldSchemaV1::Opaque { schema },
            ) => self.validate_auxiliary(leaf, AuxiliaryRole::Opaque(*schema)),
            (MachineFieldProjectionV1::Unit { leaf }, SemanticFieldSchemaV1::Unit) => {
                self.validate_auxiliary(leaf, AuxiliaryRole::Unit)
            },
            (MachineFieldProjectionV1::Bytes { leaf }, SemanticFieldSchemaV1::Bytes) => {
                self.validate_auxiliary(leaf, AuxiliaryRole::Bytes)
            },
            _ => Err(invalid()),
        }
    }
}

fn template_identities_equal(
    left: &MachineOperatorTemplateV1,
    right: &MachineOperatorTemplateV1,
) -> bool {
    left.stable_discriminant == right.stable_discriminant
        && left.fixed_payload_segments == right.fixed_payload_segments
}

fn collection_child_order(kind: CollectionKind) -> MachineChildOrderV1 {
    match kind {
        CollectionKind::Bag | CollectionKind::Set => MachineChildOrderV1::CanonicalExactKey,
        CollectionKind::List | CollectionKind::Map | CollectionKind::PathMap => {
            MachineChildOrderV1::Ordered
        },
    }
}

#[derive(Default)]
struct ProjectionCounts {
    children: usize,
    payload_bytes: usize,
}

struct ProjectionBuilder {
    nodes: Vec<SemanticMachineNodeV1>,
    counts: ProjectionCounts,
    limits: SemanticMachineAdmissionLimits,
}

impl ProjectionBuilder {
    fn new(limits: SemanticMachineAdmissionLimits) -> Self {
        Self {
            nodes: Vec::new(),
            counts: ProjectionCounts::default(),
            limits,
        }
    }

    fn push(
        &mut self,
        template: &MachineOperatorTemplateV1,
        dynamic_segments: Vec<Vec<u8>>,
        children: Vec<u32>,
        child_order: MachineChildOrderV1,
    ) -> Result<u32, SemanticMachineImageError> {
        let next_count = self
            .nodes
            .len()
            .checked_add(1)
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        enforce_machine_limit(next_count, self.limits.max_projected_nodes, "projected nodes")?;
        self.counts.children = self
            .counts
            .children
            .checked_add(children.len())
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        enforce_machine_limit(
            self.counts.children,
            self.limits.max_projected_children,
            "projected children",
        )?;
        let segment_count = template
            .fixed_payload_segments
            .len()
            .checked_add(dynamic_segments.len())
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        enforce_machine_limit(
            segment_count,
            self.limits.max_segments_per_template,
            "projected payload segments",
        )?;
        let mut payload_segments = machine_empty_vec(segment_count)?;
        for segment in &template.fixed_payload_segments {
            charge_projected_payload(&mut self.counts, segment.len(), self.limits)?;
            payload_segments.push(machine_copy_bytes(segment)?);
        }
        for segment in dynamic_segments {
            enforce_machine_limit(
                segment.len(),
                self.limits.max_segment_bytes,
                "projected segment bytes",
            )?;
            charge_projected_payload(&mut self.counts, segment.len(), self.limits)?;
            payload_segments.push(segment);
        }
        self.nodes
            .try_reserve(1)
            .map_err(|_| SemanticMachineImageError::Allocation)?;
        let node = u32::try_from(self.nodes.len())
            .map_err(|_| SemanticMachineImageError::LimitExceeded("projected nodes"))?;
        self.nodes.push(SemanticMachineNodeV1 {
            operator: SemanticMachineOperatorV1 {
                stable_discriminant: template.stable_discriminant,
                payload_segments,
                label: machine_copy_string(&template.label)?,
            },
            children,
            child_order,
        });
        Ok(node)
    }

    fn reserve_parent_children(
        &self,
        parent_children: &mut Vec<u32>,
        additional: usize,
    ) -> Result<(), SemanticMachineImageError> {
        let pending = parent_children
            .len()
            .checked_add(additional)
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        let projected = self
            .counts
            .children
            .checked_add(pending)
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        enforce_machine_limit(projected, self.limits.max_projected_children, "projected children")?;
        parent_children
            .try_reserve(additional)
            .map_err(|_| SemanticMachineImageError::Allocation)
    }
}

impl SemanticMachineImageV1 {
    /// Compile a canonical semantic forest without recursion or source parsing.
    /// Every semantic node is consumed once; auxiliary pair/spine/leaf nodes
    /// are emitted immediately before their parent.
    pub fn project(
        &self,
        term: &SemanticTermImageV1,
        context: SemanticMachineProjectionContext<'_>,
    ) -> Result<SemanticMachineTermV1, SemanticMachineImageError> {
        let SemanticMachineProjectionContext {
            signature,
            grammar,
            bindings,
            term_limits,
            machine_limits,
        } = context;
        self.validate(signature, grammar, bindings, machine_limits)?;
        term.verify(signature, grammar, bindings, term_limits)
            .map_err(SemanticMachineImageError::Term)?;
        let mut builder = ProjectionBuilder::new(machine_limits);
        let mut source_roots = machine_empty_vec(term.nodes.len())?;
        for (node_index, source_node) in term.nodes.iter().enumerate() {
            let projection = self
                .operators
                .get(source_node.operator.0 as usize)
                .filter(|projection| projection.operator == source_node.operator)
                .ok_or(SemanticMachineImageError::UnknownOperator(source_node.operator))?;
            let declaration = signature
                .operators
                .get(source_node.operator.0 as usize)
                .filter(|declaration| declaration.id == source_node.operator)
                .ok_or(SemanticMachineImageError::UnknownOperator(source_node.operator))?;
            let parent_capacity = source_node
                .fields
                .len()
                .checked_mul(2)
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
            let mut parent_children = machine_empty_vec(parent_capacity)?;
            let mut parent_child_order = MachineChildOrderV1::Ordered;
            for (field_index, ((field, field_projection), schema)) in source_node
                .fields
                .iter()
                .zip(&projection.fields)
                .zip(&declaration.fields)
                .enumerate()
            {
                project_field(
                    &mut builder,
                    FieldProjectionContext {
                        source_roots: &source_roots,
                        operator: source_node.operator,
                        field_index: u32::try_from(field_index).map_err(|_| {
                            SemanticMachineImageError::LimitExceeded("fields per operator")
                        })?,
                        schema,
                    },
                    field,
                    field_projection,
                    &mut parent_children,
                    &mut parent_child_order,
                )?;
            }
            let dynamic_payload = match &source_node.payload {
                None => Vec::new(),
                Some(atom) => machine_single_segment(machine_copy_bytes(&atom.bytes)?)?,
            };
            let root = builder.push(
                &projection.main,
                dynamic_payload,
                parent_children,
                parent_child_order,
            )?;
            debug_assert_eq!(source_roots.len(), node_index);
            source_roots.push(root);
        }
        let mut roots = machine_empty_vec(term.roots.len())?;
        for root in &term.roots {
            roots.push(resolve_machine_reference(&source_roots, *root)?);
        }
        Ok(SemanticMachineTermV1 { nodes: builder.nodes, roots })
    }
}

struct FieldProjectionContext<'a> {
    source_roots: &'a [u32],
    operator: SemanticOperatorId,
    field_index: u32,
    schema: &'a SemanticFieldSchemaV1,
}

fn project_field(
    builder: &mut ProjectionBuilder,
    context: FieldProjectionContext<'_>,
    field: &SemanticFieldV1,
    projection: &MachineFieldProjectionV1,
    parent_children: &mut Vec<u32>,
    parent_child_order: &mut MachineChildOrderV1,
) -> Result<(), SemanticMachineImageError> {
    let FieldProjectionContext {
        source_roots,
        operator,
        field_index,
        schema,
    } = context;
    let invalid = || SemanticMachineImageError::FieldProjection { operator, field: field_index };
    match (projection, schema, field) {
        (
            MachineFieldProjectionV1::Child,
            SemanticFieldSchemaV1::Child { .. },
            SemanticFieldV1::Child(target),
        ) => parent_children.push(resolve_machine_reference(source_roots, *target)?),
        (
            MachineFieldProjectionV1::Sequence { spine, child_order },
            SemanticFieldSchemaV1::Sequence { .. },
            SemanticFieldV1::Sequence(targets),
        ) => {
            let children = resolve_machine_references(source_roots, targets)?;
            let root = builder.push(spine, Vec::new(), children, *child_order)?;
            parent_children.push(root);
        },
        (
            MachineFieldProjectionV1::ValueCollection { kind, spine, child_order },
            SemanticFieldSchemaV1::Collection { key: None, .. },
            SemanticFieldV1::Collection { kind: actual_kind, entries },
        ) if kind == actual_kind => {
            let mut children = machine_empty_vec(entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::Value(target) = entry else {
                    return Err(invalid());
                };
                children.push(resolve_machine_reference(source_roots, *target)?);
            }
            let root = builder.push(spine, Vec::new(), children, *child_order)?;
            parent_children.push(root);
        },
        (
            MachineFieldProjectionV1::InlineValueCollection { kind, child_order },
            SemanticFieldSchemaV1::Collection { key: None, .. },
            SemanticFieldV1::Collection { kind: actual_kind, entries },
        ) if kind == actual_kind => {
            builder.reserve_parent_children(parent_children, entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::Value(target) = entry else {
                    return Err(invalid());
                };
                parent_children.push(resolve_machine_reference(source_roots, *target)?);
            }
            *parent_child_order = *child_order;
        },
        (
            MachineFieldProjectionV1::InlinePairCollection { kind, pair, child_order },
            SemanticFieldSchemaV1::Collection { key: Some(_), .. },
            SemanticFieldV1::Collection { kind: actual_kind, entries },
        ) if kind == actual_kind => {
            builder.reserve_parent_children(parent_children, entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::KeyValue { key, value } = entry else {
                    return Err(invalid());
                };
                let mut children = machine_empty_vec(2)?;
                children.push(resolve_machine_reference(source_roots, *key)?);
                children.push(resolve_machine_reference(source_roots, *value)?);
                parent_children.push(builder.push(
                    pair,
                    Vec::new(),
                    children,
                    MachineChildOrderV1::Ordered,
                )?);
            }
            *parent_child_order = *child_order;
        },
        (
            MachineFieldProjectionV1::PairCollection { kind, spine, pair, child_order },
            SemanticFieldSchemaV1::Collection { key: Some(_), .. },
            SemanticFieldV1::Collection { kind: actual_kind, entries },
        ) if kind == actual_kind => {
            let mut pair_roots = machine_empty_vec(entries.len())?;
            for entry in entries {
                let SemanticCollectionEntryV1::KeyValue { key, value } = entry else {
                    return Err(invalid());
                };
                let mut children = machine_empty_vec(2)?;
                children.push(resolve_machine_reference(source_roots, *key)?);
                children.push(resolve_machine_reference(source_roots, *value)?);
                pair_roots.push(builder.push(
                    pair,
                    Vec::new(),
                    children,
                    MachineChildOrderV1::Ordered,
                )?);
            }
            let root = builder.push(spine, Vec::new(), pair_roots, *child_order)?;
            parent_children.push(root);
        },
        (
            MachineFieldProjectionV1::InlinePathMap { empty, set, map, pair },
            SemanticFieldSchemaV1::PathMap { .. },
            SemanticFieldV1::PathMap { mode, entries },
        ) => {
            let additional = entries
                .len()
                .checked_add(1)
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
            builder.reserve_parent_children(parent_children, additional)?;
            let mode_template = match mode {
                PathMapModeV1::NeutralEmpty => empty,
                PathMapModeV1::Set => set,
                PathMapModeV1::Map => map,
            };
            parent_children.push(builder.push(
                mode_template,
                Vec::new(),
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
            match mode {
                PathMapModeV1::NeutralEmpty if entries.is_empty() => {},
                PathMapModeV1::NeutralEmpty => return Err(invalid()),
                PathMapModeV1::Set => {
                    for entry in entries {
                        let SemanticPathMapEntryV1::Key(key) = entry else {
                            return Err(invalid());
                        };
                        parent_children.push(resolve_machine_reference(source_roots, *key)?);
                    }
                },
                PathMapModeV1::Map => {
                    for entry in entries {
                        let SemanticPathMapEntryV1::KeyValue { key, value } = entry else {
                            return Err(invalid());
                        };
                        let mut children = machine_empty_vec(2)?;
                        children.push(resolve_machine_reference(source_roots, *key)?);
                        children.push(resolve_machine_reference(source_roots, *value)?);
                        parent_children.push(builder.push(
                            pair,
                            Vec::new(),
                            children,
                            MachineChildOrderV1::Ordered,
                        )?);
                    }
                },
            }
            *parent_child_order = MachineChildOrderV1::Ordered;
        },
        (
            MachineFieldProjectionV1::Optional { none },
            SemanticFieldSchemaV1::Optional { .. },
            SemanticFieldV1::Optional(target),
        ) => match target {
            Some(target) => {
                parent_children.push(resolve_machine_reference(source_roots, *target)?);
            },
            None => parent_children.push(builder.push(
                none,
                Vec::new(),
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?),
        },
        (
            MachineFieldProjectionV1::OptionalSequence { none, spine, child_order },
            SemanticFieldSchemaV1::OptionalSequence { .. },
            SemanticFieldV1::OptionalSequence(targets),
        ) => match targets {
            Some(targets) => {
                let children = resolve_machine_references(source_roots, targets)?;
                parent_children.push(builder.push(spine, Vec::new(), children, *child_order)?);
            },
            None => parent_children.push(builder.push(
                none,
                Vec::new(),
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?),
        },
        (
            MachineFieldProjectionV1::OptionalTokenText { none, leaf },
            SemanticFieldSchemaV1::OptionalTokenText,
            SemanticFieldV1::OptionalTokenText(text),
        ) => match text {
            Some(text) => parent_children.push(builder.push(
                leaf,
                machine_single_segment(machine_copy_bytes(text.as_bytes())?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?),
            None => parent_children.push(builder.push(
                none,
                Vec::new(),
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?),
        },
        (
            MachineFieldProjectionV1::Scope { arity: arity_template },
            SemanticFieldSchemaV1::Scope { domain, .. },
            SemanticFieldV1::Scope { domain: actual_domain, arity, body },
        ) if domain == actual_domain => {
            let arity_root = builder.push(
                arity_template,
                machine_single_segment(machine_u32_bytes(*arity)?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?;
            parent_children.push(arity_root);
            parent_children.push(resolve_machine_reference(source_roots, *body)?);
        },
        (
            MachineFieldProjectionV1::Variable { leaf },
            SemanticFieldSchemaV1::Variable { .. },
            SemanticFieldV1::Variable(variable),
        ) => {
            parent_children.push(builder.push(
                leaf,
                machine_single_segment(encode_variable(variable)?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        (
            MachineFieldProjectionV1::Atom { leaf },
            SemanticFieldSchemaV1::Atom { schema },
            SemanticFieldV1::Atom(atom),
        ) if *schema == atom.schema => {
            parent_children.push(builder.push(
                leaf,
                machine_single_segment(machine_copy_bytes(&atom.bytes)?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        (
            MachineFieldProjectionV1::TokenText { leaf },
            SemanticFieldSchemaV1::TokenText,
            SemanticFieldV1::TokenText(text),
        ) => {
            parent_children.push(builder.push(
                leaf,
                machine_single_segment(machine_copy_bytes(text.as_bytes())?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        (
            MachineFieldProjectionV1::Opaque { leaf },
            SemanticFieldSchemaV1::Opaque { schema },
            SemanticFieldV1::Opaque(atom),
        ) if *schema == atom.schema => {
            parent_children.push(builder.push(
                leaf,
                machine_single_segment(machine_copy_bytes(&atom.bytes)?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        (
            MachineFieldProjectionV1::Unit { leaf },
            SemanticFieldSchemaV1::Unit,
            SemanticFieldV1::Unit,
        ) => {
            parent_children.push(builder.push(
                leaf,
                Vec::new(),
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        (
            MachineFieldProjectionV1::Bytes { leaf },
            SemanticFieldSchemaV1::Bytes,
            SemanticFieldV1::Bytes(bytes),
        ) => {
            parent_children.push(builder.push(
                leaf,
                machine_single_segment(machine_copy_bytes(bytes)?)?,
                Vec::new(),
                MachineChildOrderV1::Ordered,
            )?);
        },
        _ => return Err(invalid()),
    }
    Ok(())
}

fn resolve_machine_reference(
    source_roots: &[u32],
    target: u32,
) -> Result<u32, SemanticMachineImageError> {
    source_roots
        .get(target as usize)
        .copied()
        .ok_or(SemanticMachineImageError::ProjectedReference(target))
}

fn resolve_machine_references(
    source_roots: &[u32],
    targets: &[u32],
) -> Result<Vec<u32>, SemanticMachineImageError> {
    let mut children = machine_empty_vec(targets.len())?;
    for target in targets {
        children.push(resolve_machine_reference(source_roots, *target)?);
    }
    Ok(children)
}

fn encode_variable(variable: &SemanticVariableV1) -> Result<Vec<u8>, SemanticMachineImageError> {
    match variable {
        SemanticVariableV1::Bound { scope_depth, slot } => {
            let mut bytes = machine_empty_vec(9)?;
            bytes.push(0);
            bytes.extend_from_slice(&scope_depth.to_le_bytes());
            bytes.extend_from_slice(&slot.to_le_bytes());
            Ok(bytes)
        },
        SemanticVariableV1::Free { identity } => {
            let capacity = identity
                .len()
                .checked_add(1)
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
            let mut bytes = machine_empty_vec(capacity)?;
            bytes.push(1);
            bytes.extend_from_slice(identity);
            Ok(bytes)
        },
    }
}

fn charge_projected_payload(
    counts: &mut ProjectionCounts,
    bytes: usize,
    limits: SemanticMachineAdmissionLimits,
) -> Result<(), SemanticMachineImageError> {
    counts.payload_bytes = counts
        .payload_bytes
        .checked_add(bytes)
        .ok_or(SemanticMachineImageError::LengthOverflow)?;
    enforce_machine_limit(
        counts.payload_bytes,
        limits.max_projected_payload_bytes,
        "projected payload bytes",
    )
}

fn machine_empty_vec<T>(capacity: usize) -> Result<Vec<T>, SemanticMachineImageError> {
    empty_vec(capacity).map_err(|error| match error {
        SemanticTermImageError::Allocation => SemanticMachineImageError::Allocation,
        other => SemanticMachineImageError::Codec(other),
    })
}

fn machine_copy_bytes(bytes: &[u8]) -> Result<Vec<u8>, SemanticMachineImageError> {
    copy_bytes(bytes).map_err(|error| match error {
        SemanticTermImageError::Allocation => SemanticMachineImageError::Allocation,
        other => SemanticMachineImageError::Codec(other),
    })
}

fn machine_single_segment(segment: Vec<u8>) -> Result<Vec<Vec<u8>>, SemanticMachineImageError> {
    let mut segments = machine_empty_vec(1)?;
    segments.push(segment);
    Ok(segments)
}

fn machine_u32_bytes(value: u32) -> Result<Vec<u8>, SemanticMachineImageError> {
    let mut bytes = machine_empty_vec(4)?;
    bytes.extend_from_slice(&value.to_le_bytes());
    Ok(bytes)
}

fn machine_copy_string(value: &str) -> Result<String, SemanticMachineImageError> {
    let mut output = String::new();
    output
        .try_reserve_exact(value.len())
        .map_err(|_| SemanticMachineImageError::Allocation)?;
    output.push_str(value);
    Ok(output)
}

impl SemanticMachineImageV1 {
    pub fn fingerprint(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticMachineAdmissionLimits,
    ) -> Result<[u8; 32], SemanticMachineImageError> {
        let bytes = self.encode(signature, grammar, bindings, limits)?;
        Ok(*blake3::hash(&bytes).as_bytes())
    }

    /// Encode only after complete structural admission. The format is flat and
    /// count-prefixed; serde cannot allocate from untrusted lengths here.
    pub fn encode(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticMachineAdmissionLimits,
    ) -> Result<Vec<u8>, SemanticMachineImageError> {
        self.validate(signature, grammar, bindings, limits)?;
        let encoded_len = encoded_machine_image_len(self)?;
        enforce_machine_limit(encoded_len, limits.max_encoded_bytes, "encoded bytes")?;
        let mut output = machine_empty_vec(encoded_len)?;
        output.extend_from_slice(SEMANTIC_MACHINE_IMAGE_MAGIC);
        write_u16(&mut output, self.abi);
        output.extend_from_slice(&self.signature_fingerprint);
        write_u32(&mut output, machine_checked_u32(self.operators.len())?);
        for projection in &self.operators {
            write_u32(&mut output, projection.operator.0);
            encode_template(&projection.main, &mut output)?;
            write_u32(&mut output, machine_checked_u32(projection.fields.len())?);
            for field in &projection.fields {
                encode_field_projection(field, &mut output)?;
            }
        }
        debug_assert_eq!(output.len(), encoded_len);
        Ok(output)
    }

    /// Decode an untrusted image under explicit allocation bounds and then
    /// re-run complete signature and projection validation.
    pub fn decode(
        bytes: &[u8],
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticMachineAdmissionLimits,
    ) -> Result<Self, SemanticMachineImageError> {
        enforce_machine_limit(bytes.len(), limits.max_encoded_bytes, "encoded bytes")?;
        let mut input = ImageReader::new(bytes);
        if machine_read_exact(&mut input, SEMANTIC_MACHINE_IMAGE_MAGIC.len())?
            != SEMANTIC_MACHINE_IMAGE_MAGIC
        {
            return Err(SemanticMachineImageError::InvalidMagic);
        }
        let abi = machine_read_u16(&mut input)?;
        if abi != SEMANTIC_MACHINE_IMAGE_ABI_V1 {
            return Err(SemanticMachineImageError::UnsupportedAbi(abi));
        }
        let signature_fingerprint = machine_read_array::<32>(&mut input)?;
        let expected_fingerprint = signature
            .fingerprint()
            .map_err(SemanticMachineImageError::Signature)?;
        if signature_fingerprint != expected_fingerprint {
            return Err(SemanticMachineImageError::SignatureFingerprintMismatch);
        }
        let operator_count = machine_read_count(&mut input, limits.max_operators, "operators")?;
        let mut operators = machine_empty_vec(operator_count)?;
        let mut counts = ValidationCounts::default();
        for _ in 0..operator_count {
            let operator = SemanticOperatorId(machine_read_u32(&mut input)?);
            let main = decode_template(&mut input, &mut counts, limits)?;
            let field_count = machine_read_count(
                &mut input,
                limits.max_fields_per_operator,
                "fields per operator",
            )?;
            counts.fields = counts
                .fields
                .checked_add(field_count)
                .ok_or(SemanticMachineImageError::LengthOverflow)?;
            enforce_machine_limit(counts.fields, limits.max_total_fields, "total fields")?;
            let mut fields = machine_empty_vec(field_count)?;
            for _ in 0..field_count {
                fields.push(decode_field_projection(&mut input, &mut counts, limits)?);
            }
            operators.push(MachineOperatorProjectionV1 { operator, main, fields });
        }
        if !input.is_empty() {
            return Err(SemanticMachineImageError::TrailingBytes);
        }
        let image = Self { abi, signature_fingerprint, operators };
        image.validate(signature, grammar, bindings, limits)?;
        Ok(image)
    }
}

fn encoded_machine_image_len(
    image: &SemanticMachineImageV1,
) -> Result<usize, SemanticMachineImageError> {
    let mut total = SEMANTIC_MACHINE_IMAGE_MAGIC.len() + 2 + 32 + 4;
    for projection in &image.operators {
        machine_checked_add(&mut total, 4)?;
        machine_checked_add(&mut total, encoded_template_len(&projection.main)?)?;
        machine_checked_add(&mut total, 4)?;
        for field in &projection.fields {
            machine_checked_add(&mut total, encoded_field_projection_len(field)?)?;
        }
    }
    Ok(total)
}

fn encoded_template_len(
    template: &MachineOperatorTemplateV1,
) -> Result<usize, SemanticMachineImageError> {
    let mut total = 4usize
        .checked_add(4)
        .and_then(|value| value.checked_add(template.label.len()))
        .and_then(|value| value.checked_add(4))
        .ok_or(SemanticMachineImageError::LengthOverflow)?;
    for segment in &template.fixed_payload_segments {
        machine_checked_add(&mut total, 4)?;
        machine_checked_add(&mut total, segment.len())?;
    }
    Ok(total)
}

fn encoded_field_projection_len(
    projection: &MachineFieldProjectionV1,
) -> Result<usize, SemanticMachineImageError> {
    match projection {
        MachineFieldProjectionV1::Child => Ok(1),
        MachineFieldProjectionV1::Sequence { spine, .. } => 2usize
            .checked_add(encoded_template_len(spine)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
        MachineFieldProjectionV1::ValueCollection { spine, .. } => 3usize
            .checked_add(encoded_template_len(spine)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
        MachineFieldProjectionV1::PairCollection { spine, pair, .. } => {
            let mut total = 3usize;
            machine_checked_add(&mut total, encoded_template_len(spine)?)?;
            machine_checked_add(&mut total, encoded_template_len(pair)?)?;
            Ok(total)
        },
        MachineFieldProjectionV1::InlineValueCollection { .. } => Ok(3),
        MachineFieldProjectionV1::InlinePairCollection { pair, .. } => 3usize
            .checked_add(encoded_template_len(pair)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
        MachineFieldProjectionV1::InlinePathMap { empty, set, map, pair } => {
            let mut total = 1usize;
            machine_checked_add(&mut total, encoded_template_len(empty)?)?;
            machine_checked_add(&mut total, encoded_template_len(set)?)?;
            machine_checked_add(&mut total, encoded_template_len(map)?)?;
            machine_checked_add(&mut total, encoded_template_len(pair)?)?;
            Ok(total)
        },
        MachineFieldProjectionV1::Optional { none } => 1usize
            .checked_add(encoded_template_len(none)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
        MachineFieldProjectionV1::OptionalSequence { none, spine, .. } => {
            let mut total = 2usize;
            machine_checked_add(&mut total, encoded_template_len(none)?)?;
            machine_checked_add(&mut total, encoded_template_len(spine)?)?;
            Ok(total)
        },
        MachineFieldProjectionV1::OptionalTokenText { none, leaf } => {
            let mut total = 1usize;
            machine_checked_add(&mut total, encoded_template_len(none)?)?;
            machine_checked_add(&mut total, encoded_template_len(leaf)?)?;
            Ok(total)
        },
        MachineFieldProjectionV1::Scope { arity } => 1usize
            .checked_add(encoded_template_len(arity)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
        MachineFieldProjectionV1::Variable { leaf }
        | MachineFieldProjectionV1::Atom { leaf }
        | MachineFieldProjectionV1::TokenText { leaf }
        | MachineFieldProjectionV1::Opaque { leaf }
        | MachineFieldProjectionV1::Unit { leaf }
        | MachineFieldProjectionV1::Bytes { leaf } => 1usize
            .checked_add(encoded_template_len(leaf)?)
            .ok_or(SemanticMachineImageError::LengthOverflow),
    }
}

fn encode_template(
    template: &MachineOperatorTemplateV1,
    output: &mut Vec<u8>,
) -> Result<(), SemanticMachineImageError> {
    write_u32(output, template.stable_discriminant);
    write_u32(output, machine_checked_u32(template.label.len())?);
    output.extend_from_slice(template.label.as_bytes());
    write_u32(output, machine_checked_u32(template.fixed_payload_segments.len())?);
    for segment in &template.fixed_payload_segments {
        write_u32(output, machine_checked_u32(segment.len())?);
        output.extend_from_slice(segment);
    }
    Ok(())
}

fn encode_field_projection(
    projection: &MachineFieldProjectionV1,
    output: &mut Vec<u8>,
) -> Result<(), SemanticMachineImageError> {
    match projection {
        MachineFieldProjectionV1::Child => output.push(0),
        MachineFieldProjectionV1::Sequence { spine, child_order } => {
            output.push(1);
            output.push(encode_child_order(*child_order));
            encode_template(spine, output)?;
        },
        MachineFieldProjectionV1::ValueCollection { kind, spine, child_order } => {
            output.push(2);
            output.push(encode_collection_kind(*kind));
            output.push(encode_child_order(*child_order));
            encode_template(spine, output)?;
        },
        MachineFieldProjectionV1::PairCollection { kind, spine, pair, child_order } => {
            output.push(3);
            output.push(encode_collection_kind(*kind));
            output.push(encode_child_order(*child_order));
            encode_template(spine, output)?;
            encode_template(pair, output)?;
        },
        MachineFieldProjectionV1::Optional { none } => {
            output.push(4);
            encode_template(none, output)?;
        },
        MachineFieldProjectionV1::Scope { arity } => {
            output.push(5);
            encode_template(arity, output)?;
        },
        MachineFieldProjectionV1::Variable { leaf } => {
            output.push(6);
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::Atom { leaf } => {
            output.push(7);
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::TokenText { leaf } => {
            output.push(8);
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::Opaque { leaf } => {
            output.push(9);
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::Unit { leaf } => {
            output.push(10);
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::OptionalSequence { none, spine, child_order } => {
            output.push(11);
            output.push(encode_child_order(*child_order));
            encode_template(none, output)?;
            encode_template(spine, output)?;
        },
        MachineFieldProjectionV1::OptionalTokenText { none, leaf } => {
            output.push(12);
            encode_template(none, output)?;
            encode_template(leaf, output)?;
        },
        MachineFieldProjectionV1::InlineValueCollection { kind, child_order } => {
            output.push(13);
            output.push(encode_collection_kind(*kind));
            output.push(encode_child_order(*child_order));
        },
        MachineFieldProjectionV1::InlinePairCollection { kind, pair, child_order } => {
            output.push(14);
            output.push(encode_collection_kind(*kind));
            output.push(encode_child_order(*child_order));
            encode_template(pair, output)?;
        },
        MachineFieldProjectionV1::InlinePathMap { empty, set, map, pair } => {
            output.push(15);
            encode_template(empty, output)?;
            encode_template(set, output)?;
            encode_template(map, output)?;
            encode_template(pair, output)?;
        },
        MachineFieldProjectionV1::Bytes { leaf } => {
            output.push(16);
            encode_template(leaf, output)?;
        },
    }
    Ok(())
}

fn decode_template(
    input: &mut ImageReader<'_>,
    counts: &mut ValidationCounts,
    limits: SemanticMachineAdmissionLimits,
) -> Result<MachineOperatorTemplateV1, SemanticMachineImageError> {
    let stable_discriminant = machine_read_u32(input)?;
    let label_len = machine_read_count(input, MAX_MACHINE_LABEL_BYTES, "label bytes")?;
    let label_bytes = machine_read_exact(input, label_len)?;
    let label = std::str::from_utf8(label_bytes)
        .map_err(|_| SemanticMachineImageError::InvalidUtf8)
        .and_then(machine_copy_string)?;
    let segment_count =
        machine_read_count(input, limits.max_segments_per_template, "segments per template")?;
    let mut fixed_payload_segments = machine_empty_vec(segment_count)?;
    for _ in 0..segment_count {
        let length = machine_read_count(input, limits.max_segment_bytes, "segment bytes")?;
        counts.template_bytes = counts
            .template_bytes
            .checked_add(length)
            .ok_or(SemanticMachineImageError::LengthOverflow)?;
        enforce_machine_limit(
            counts.template_bytes,
            limits.max_total_template_bytes,
            "template bytes",
        )?;
        fixed_payload_segments.push(machine_copy_bytes(machine_read_exact(input, length)?)?);
    }
    counts.templates = counts
        .templates
        .checked_add(1)
        .ok_or(SemanticMachineImageError::LengthOverflow)?;
    enforce_machine_limit(counts.templates, limits.max_templates, "templates")?;
    Ok(MachineOperatorTemplateV1 {
        stable_discriminant,
        fixed_payload_segments,
        label,
    })
}

fn decode_field_projection(
    input: &mut ImageReader<'_>,
    counts: &mut ValidationCounts,
    limits: SemanticMachineAdmissionLimits,
) -> Result<MachineFieldProjectionV1, SemanticMachineImageError> {
    Ok(match machine_read_u8(input)? {
        0 => MachineFieldProjectionV1::Child,
        1 => MachineFieldProjectionV1::Sequence {
            child_order: decode_child_order(machine_read_u8(input)?)?,
            spine: decode_template(input, counts, limits)?,
        },
        2 => MachineFieldProjectionV1::ValueCollection {
            kind: machine_decode_collection_kind(machine_read_u8(input)?)?,
            child_order: decode_child_order(machine_read_u8(input)?)?,
            spine: decode_template(input, counts, limits)?,
        },
        3 => MachineFieldProjectionV1::PairCollection {
            kind: machine_decode_collection_kind(machine_read_u8(input)?)?,
            child_order: decode_child_order(machine_read_u8(input)?)?,
            spine: decode_template(input, counts, limits)?,
            pair: decode_template(input, counts, limits)?,
        },
        4 => MachineFieldProjectionV1::Optional {
            none: decode_template(input, counts, limits)?,
        },
        5 => MachineFieldProjectionV1::Scope {
            arity: decode_template(input, counts, limits)?,
        },
        6 => MachineFieldProjectionV1::Variable {
            leaf: decode_template(input, counts, limits)?,
        },
        7 => MachineFieldProjectionV1::Atom {
            leaf: decode_template(input, counts, limits)?,
        },
        8 => MachineFieldProjectionV1::TokenText {
            leaf: decode_template(input, counts, limits)?,
        },
        9 => MachineFieldProjectionV1::Opaque {
            leaf: decode_template(input, counts, limits)?,
        },
        10 => MachineFieldProjectionV1::Unit {
            leaf: decode_template(input, counts, limits)?,
        },
        11 => MachineFieldProjectionV1::OptionalSequence {
            child_order: decode_child_order(machine_read_u8(input)?)?,
            none: decode_template(input, counts, limits)?,
            spine: decode_template(input, counts, limits)?,
        },
        12 => MachineFieldProjectionV1::OptionalTokenText {
            none: decode_template(input, counts, limits)?,
            leaf: decode_template(input, counts, limits)?,
        },
        13 => MachineFieldProjectionV1::InlineValueCollection {
            kind: machine_decode_collection_kind(machine_read_u8(input)?)?,
            child_order: decode_child_order(machine_read_u8(input)?)?,
        },
        14 => MachineFieldProjectionV1::InlinePairCollection {
            kind: machine_decode_collection_kind(machine_read_u8(input)?)?,
            child_order: decode_child_order(machine_read_u8(input)?)?,
            pair: decode_template(input, counts, limits)?,
        },
        15 => MachineFieldProjectionV1::InlinePathMap {
            empty: decode_template(input, counts, limits)?,
            set: decode_template(input, counts, limits)?,
            map: decode_template(input, counts, limits)?,
            pair: decode_template(input, counts, limits)?,
        },
        16 => MachineFieldProjectionV1::Bytes {
            leaf: decode_template(input, counts, limits)?,
        },
        tag => return Err(SemanticMachineImageError::InvalidTag(tag)),
    })
}

fn encode_child_order(order: MachineChildOrderV1) -> u8 {
    match order {
        MachineChildOrderV1::Ordered => 0,
        MachineChildOrderV1::CanonicalExactKey => 1,
    }
}

fn decode_child_order(tag: u8) -> Result<MachineChildOrderV1, SemanticMachineImageError> {
    match tag {
        0 => Ok(MachineChildOrderV1::Ordered),
        1 => Ok(MachineChildOrderV1::CanonicalExactKey),
        tag => Err(SemanticMachineImageError::InvalidTag(tag)),
    }
}

fn machine_decode_collection_kind(tag: u8) -> Result<CollectionKind, SemanticMachineImageError> {
    decode_collection_kind(tag).map_err(|error| match error {
        SemanticTermImageError::InvalidTag(tag) => SemanticMachineImageError::InvalidTag(tag),
        other => SemanticMachineImageError::Codec(other),
    })
}

fn machine_checked_u32(value: usize) -> Result<u32, SemanticMachineImageError> {
    checked_u32(value).map_err(|error| match error {
        SemanticTermImageError::LengthOverflow => SemanticMachineImageError::LengthOverflow,
        other => SemanticMachineImageError::Codec(other),
    })
}

fn machine_checked_add(
    total: &mut usize,
    additional: usize,
) -> Result<(), SemanticMachineImageError> {
    checked_add(total, additional).map_err(|error| match error {
        SemanticTermImageError::LengthOverflow => SemanticMachineImageError::LengthOverflow,
        other => SemanticMachineImageError::Codec(other),
    })
}

fn machine_read_exact<'a>(
    input: &mut ImageReader<'a>,
    length: usize,
) -> Result<&'a [u8], SemanticMachineImageError> {
    input
        .read_exact(length)
        .map_err(SemanticMachineImageError::Codec)
}

fn machine_read_array<const N: usize>(
    input: &mut ImageReader<'_>,
) -> Result<[u8; N], SemanticMachineImageError> {
    input.read_array().map_err(SemanticMachineImageError::Codec)
}

fn machine_read_u8(input: &mut ImageReader<'_>) -> Result<u8, SemanticMachineImageError> {
    input.read_u8().map_err(SemanticMachineImageError::Codec)
}

fn machine_read_u16(input: &mut ImageReader<'_>) -> Result<u16, SemanticMachineImageError> {
    input.read_u16().map_err(SemanticMachineImageError::Codec)
}

fn machine_read_u32(input: &mut ImageReader<'_>) -> Result<u32, SemanticMachineImageError> {
    input.read_u32().map_err(SemanticMachineImageError::Codec)
}

fn machine_read_count(
    input: &mut ImageReader<'_>,
    limit: usize,
    name: &'static str,
) -> Result<usize, SemanticMachineImageError> {
    input.read_count(limit, name).map_err(|error| match error {
        SemanticTermImageError::LimitExceeded(name) => {
            SemanticMachineImageError::LimitExceeded(name)
        },
        SemanticTermImageError::LengthOverflow => SemanticMachineImageError::LengthOverflow,
        other => SemanticMachineImageError::Codec(other),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Carrier, Category, ConstructorId, FieldSource, Precedence, Production, ProductionClass,
        ProductionId, ReductionPlan, SemanticAtomSchemaV1, SemanticAtomV1, SemanticBuiltinAtomV1,
        SemanticNodeV1, SemanticOperatorDeclV1, SemanticOperatorOriginV1, SyntaxItem,
        SEMANTIC_SIGNATURE_ABI_V1, SEMANTIC_TERM_IMAGE_ABI_V1,
    };

    fn add_production(
        grammar: &mut GrammarCoreV1,
        constructor: u32,
        label: &str,
        syntax: Vec<SyntaxItem>,
        input_arity: u16,
        fields: Vec<FieldSource>,
    ) {
        let production = u32::try_from(grammar.productions.len()).expect("production ID");
        let reduction = u32::try_from(grammar.reductions.len()).expect("reduction ID");
        grammar.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(constructor),
            input_arity,
            fields,
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        grammar.productions.push(Production {
            id: ProductionId(production),
            constructor: ConstructorId(constructor),
            label: label.into(),
            result: CategoryId(0),
            syntax,
            precedence: Precedence::default(),
            classification: ProductionClass::default(),
            reduction,
            provenance: None,
        });
    }

    fn fixture_with_collection_kind(
        collection_kind: CollectionKind,
    ) -> (GrammarCoreV1, SemanticSignatureV1, SemanticMachineImageV1) {
        let mut grammar = GrammarCoreV1::new("SemanticMachineFixture");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        add_production(&mut grammar, 0, "Leaf", Vec::new(), 0, vec![FieldSource::Unit]);
        add_production(
            &mut grammar,
            1,
            "Branch",
            vec![SyntaxItem::Category {
                category: CategoryId(0),
                slot: "child".into(),
            }],
            1,
            vec![FieldSource::Input(0)],
        );
        add_production(&mut grammar, 2, "Map", Vec::new(), 0, vec![FieldSource::Unit]);
        add_production(
            &mut grammar,
            3,
            "OptionalFields",
            Vec::new(),
            0,
            vec![FieldSource::Unit; 2],
        );
        add_production(&mut grammar, 4, "Bytes", Vec::new(), 0, vec![FieldSource::Unit]);
        grammar.validate().expect("grammar");
        let signature = SemanticSignatureV1 {
            abi: SEMANTIC_SIGNATURE_ABI_V1,
            grammar_fingerprint: grammar.fingerprint().expect("grammar fingerprint"),
            category_count: 1,
            constructor_count: 5,
            atom_schemas: vec![SemanticAtomSchemaV1::Builtin(
                SemanticBuiltinAtomV1::SignedInteger { bits: Some(32) },
            )],
            operators: vec![
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(0),
                    category: CategoryId(0),
                    constructor: ConstructorId(0),
                    stable_discriminant: 7,
                    label: "Term::Leaf".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(0)),
                    payload: Some(0),
                    fields: vec![SemanticFieldSchemaV1::Unit],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(1),
                    category: CategoryId(0),
                    constructor: ConstructorId(1),
                    stable_discriminant: 11,
                    label: "Term::Branch".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(1)),
                    payload: None,
                    fields: vec![SemanticFieldSchemaV1::Child { category: CategoryId(0) }],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(2),
                    category: CategoryId(0),
                    constructor: ConstructorId(2),
                    stable_discriminant: 13,
                    label: "Term::Map".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(2)),
                    payload: None,
                    fields: vec![SemanticFieldSchemaV1::Collection {
                        kind: collection_kind,
                        key: Some(CategoryId(0)),
                        value: CategoryId(0),
                    }],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(3),
                    category: CategoryId(0),
                    constructor: ConstructorId(3),
                    stable_discriminant: 17,
                    label: "Term::OptionalFields".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(3)),
                    payload: None,
                    fields: vec![
                        SemanticFieldSchemaV1::OptionalSequence { element: CategoryId(0) },
                        SemanticFieldSchemaV1::OptionalTokenText,
                    ],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(4),
                    category: CategoryId(0),
                    constructor: ConstructorId(4),
                    stable_discriminant: 19,
                    label: "Term::Bytes".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(4)),
                    payload: None,
                    fields: vec![SemanticFieldSchemaV1::Bytes],
                },
            ],
        };
        signature
            .validate(&grammar, &RuntimeCapabilityBindings::default())
            .expect("signature");
        let template = |stable_discriminant, label: &str, fixed: &[u8]| MachineOperatorTemplateV1 {
            stable_discriminant,
            fixed_payload_segments: if fixed.is_empty() {
                Vec::new()
            } else {
                vec![fixed.to_vec()]
            },
            label: label.into(),
        };
        let image = SemanticMachineImageV1 {
            abi: SEMANTIC_MACHINE_IMAGE_ABI_V1,
            signature_fingerprint: signature.fingerprint().expect("signature fingerprint"),
            operators: vec![
                MachineOperatorProjectionV1 {
                    operator: SemanticOperatorId(0),
                    main: template(7, "Term::Leaf", &[]),
                    fields: vec![MachineFieldProjectionV1::Unit {
                        leaf: template(101, "<unit>", b"unit"),
                    }],
                },
                MachineOperatorProjectionV1 {
                    operator: SemanticOperatorId(1),
                    main: template(11, "Term::Branch", &[]),
                    fields: vec![MachineFieldProjectionV1::Child],
                },
                MachineOperatorProjectionV1 {
                    operator: SemanticOperatorId(2),
                    main: template(13, "Term::Map", &[]),
                    fields: vec![MachineFieldProjectionV1::PairCollection {
                        kind: collection_kind,
                        spine: template(102, "<map>", b"map"),
                        pair: template(103, "<pair>", b"pair"),
                        child_order: MachineChildOrderV1::Ordered,
                    }],
                },
                MachineOperatorProjectionV1 {
                    operator: SemanticOperatorId(3),
                    main: template(17, "Term::OptionalFields", &[]),
                    fields: vec![
                        MachineFieldProjectionV1::OptionalSequence {
                            none: template(104, "<optional-sequence-none>", b"sequence-none"),
                            spine: template(105, "<optional-sequence>", b"sequence"),
                            child_order: MachineChildOrderV1::Ordered,
                        },
                        MachineFieldProjectionV1::OptionalTokenText {
                            none: template(106, "<optional-token-none>", b"token-none"),
                            leaf: template(107, "<optional-token>", b"token"),
                        },
                    ],
                },
                MachineOperatorProjectionV1 {
                    operator: SemanticOperatorId(4),
                    main: template(19, "Term::Bytes", &[]),
                    fields: vec![MachineFieldProjectionV1::Bytes {
                        leaf: template(110, "<bytes>", b"bytes"),
                    }],
                },
            ],
        };
        image
            .validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("machine image");
        (grammar, signature, image)
    }

    fn fixture() -> (GrammarCoreV1, SemanticSignatureV1, SemanticMachineImageV1) {
        fixture_with_collection_kind(CollectionKind::Map)
    }

    fn inline_collection_fixture(
        kind: CollectionKind,
    ) -> (GrammarCoreV1, SemanticSignatureV1, SemanticMachineImageV1) {
        let (grammar, mut signature, mut image) = fixture();
        signature.operators[2].fields =
            vec![SemanticFieldSchemaV1::Collection { kind, key: None, value: CategoryId(0) }];
        image.operators[2].fields = vec![MachineFieldProjectionV1::InlineValueCollection {
            kind,
            child_order: collection_child_order(kind),
        }];
        image.signature_fingerprint = signature.fingerprint().expect("signature fingerprint");
        image
            .validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("inline-collection machine image");
        (grammar, signature, image)
    }

    fn inline_pair_collection_fixture(
        kind: CollectionKind,
    ) -> (GrammarCoreV1, SemanticSignatureV1, SemanticMachineImageV1) {
        let (grammar, signature, mut image) = fixture_with_collection_kind(kind);
        let pair = match &image.operators[2].fields[0] {
            MachineFieldProjectionV1::PairCollection { pair, .. } => pair.clone(),
            _ => panic!("fixture map must begin with a pair collection"),
        };
        image.operators[2].fields = vec![MachineFieldProjectionV1::InlinePairCollection {
            kind,
            pair,
            child_order: MachineChildOrderV1::Ordered,
        }];
        image
            .validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("inline-pair machine image");
        (grammar, signature, image)
    }

    fn inline_pathmap_fixture() -> (GrammarCoreV1, SemanticSignatureV1, SemanticMachineImageV1) {
        let (grammar, mut signature, mut image) = fixture();
        signature.operators[2].fields =
            vec![SemanticFieldSchemaV1::PathMap { key: CategoryId(0), value: CategoryId(0) }];
        let mode = |tag| MachineOperatorTemplateV1 {
            stable_discriminant: 108,
            fixed_payload_segments: vec![vec![tag]],
            label: "<pathmap-mode>".into(),
        };
        image.operators[2].fields = vec![MachineFieldProjectionV1::InlinePathMap {
            empty: mode(0),
            set: mode(1),
            map: mode(2),
            pair: MachineOperatorTemplateV1 {
                stable_discriminant: 109,
                fixed_payload_segments: vec![b"pathmap-pair".to_vec()],
                label: "<pathmap-pair>".into(),
            },
        }];
        image.signature_fingerprint = signature.fingerprint().expect("signature fingerprint");
        image
            .validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("inline PathMap machine image");
        (grammar, signature, image)
    }

    fn leaf(value: i32) -> SemanticNodeV1 {
        SemanticNodeV1 {
            operator: SemanticOperatorId(0),
            payload: Some(SemanticAtomV1 {
                schema: 0,
                bytes: value.to_le_bytes().to_vec(),
            }),
            fields: vec![SemanticFieldV1::Unit],
        }
    }

    fn term(
        signature: &SemanticSignatureV1,
        nodes: Vec<SemanticNodeV1>,
        roots: Vec<u32>,
    ) -> SemanticTermImageV1 {
        SemanticTermImageV1 {
            abi: SEMANTIC_TERM_IMAGE_ABI_V1,
            signature_fingerprint: signature.fingerprint().expect("signature fingerprint"),
            nodes,
            roots,
        }
    }

    fn project_pair_collection(kind: CollectionKind) -> SemanticMachineTermV1 {
        let (grammar, signature, image) = fixture_with_collection_kind(kind);
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let raw = term(
            &signature,
            vec![
                leaf(1),
                leaf(2),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(2),
                    payload: None,
                    fields: vec![SemanticFieldV1::Collection {
                        kind,
                        entries: vec![SemanticCollectionEntryV1::KeyValue { key: 0, value: 1 }],
                    }],
                },
            ],
            vec![2],
        );
        let canonical = raw
            .canonicalize(&signature, &grammar, &bindings, term_limits)
            .expect("canonical term");
        image
            .project(
                &canonical,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    term_limits,
                    SemanticMachineAdmissionLimits::default(),
                ),
            )
            .expect("projection")
    }

    #[test]
    fn image_codec_is_canonical_and_fingerprint_bound() {
        let (grammar, signature, image) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticMachineAdmissionLimits::default();
        let bytes = image
            .encode(&signature, &grammar, &bindings, limits)
            .expect("encode");
        let decoded =
            SemanticMachineImageV1::decode(&bytes, &signature, &grammar, &bindings, limits)
                .expect("decode");
        assert_eq!(decoded, image);
        assert_eq!(
            decoded
                .fingerprint(&signature, &grammar, &bindings, limits)
                .expect("fingerprint"),
            image
                .fingerprint(&signature, &grammar, &bindings, limits)
                .expect("fingerprint")
        );
    }

    #[test]
    fn optional_sequence_and_token_projection_preserve_both_presence_arms() {
        let (grammar, signature, image) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let machine_limits = SemanticMachineAdmissionLimits::default();

        for (nodes, root, expected, rejected) in [
            (
                vec![
                    leaf(1),
                    SemanticNodeV1 {
                        operator: SemanticOperatorId(3),
                        payload: None,
                        fields: vec![
                            SemanticFieldV1::OptionalSequence(Some(vec![0])),
                            SemanticFieldV1::OptionalTokenText(Some("name".into())),
                        ],
                    },
                ],
                1,
                [105, 107],
                [104, 106],
            ),
            (
                vec![SemanticNodeV1 {
                    operator: SemanticOperatorId(3),
                    payload: None,
                    fields: vec![
                        SemanticFieldV1::OptionalSequence(None),
                        SemanticFieldV1::OptionalTokenText(None),
                    ],
                }],
                0,
                [104, 106],
                [105, 107],
            ),
        ] {
            let canonical = term(&signature, nodes, vec![root])
                .canonicalize(&signature, &grammar, &bindings, term_limits)
                .expect("canonical optional-field term");
            let projected = image
                .project(
                    &canonical,
                    SemanticMachineProjectionContext::new(
                        &signature,
                        &grammar,
                        &bindings,
                        term_limits,
                        machine_limits,
                    ),
                )
                .expect("optional fields project");
            let discriminants: Vec<_> = projected
                .nodes
                .iter()
                .map(|node| node.operator.stable_discriminant)
                .collect();
            for discriminant in expected {
                assert!(discriminants.contains(&discriminant));
            }
            for discriminant in rejected {
                assert!(!discriminants.contains(&discriminant));
            }
        }
    }

    #[test]
    fn map_projection_preserves_pair_boundaries_and_fixed_payloads() {
        let machine = project_pair_collection(CollectionKind::Map);
        let pair = machine
            .nodes
            .iter()
            .find(|node| node.operator.label == "<pair>")
            .expect("pair node");
        assert_eq!(pair.children.len(), 2);
        assert_eq!(pair.operator.payload_segments, vec![b"pair".to_vec()]);
        let map = machine
            .nodes
            .iter()
            .find(|node| node.operator.label == "<map>")
            .expect("map spine");
        assert_eq!(map.children.len(), 1);
        assert_eq!(machine.roots.len(), 1);
    }

    #[test]
    fn path_map_projection_preserves_pair_boundaries_and_fixed_payloads() {
        let machine = project_pair_collection(CollectionKind::PathMap);
        let pair = machine
            .nodes
            .iter()
            .find(|node| node.operator.label == "<pair>")
            .expect("pair node");
        assert_eq!(pair.children.len(), 2);
        assert_eq!(pair.operator.payload_segments, vec![b"pair".to_vec()]);
        let path_map = machine
            .nodes
            .iter()
            .find(|node| node.operator.label == "<map>")
            .expect("path-map spine");
        assert_eq!(path_map.children.len(), 1);
        assert_eq!(machine.roots.len(), 1);
    }

    #[test]
    fn inline_pathmap_projects_exact_mode_first_and_preserves_set_and_pair_shapes() {
        let (grammar, signature, image) = inline_pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let machine_limits = SemanticMachineAdmissionLimits::default();

        for (mode, entries, expected_tag, expects_pair) in [
            (PathMapModeV1::NeutralEmpty, Vec::new(), 0, false),
            (PathMapModeV1::Set, vec![SemanticPathMapEntryV1::Key(0)], 1, false),
            (
                PathMapModeV1::Map,
                vec![SemanticPathMapEntryV1::KeyValue { key: 0, value: 1 }],
                2,
                true,
            ),
        ] {
            let mut nodes = match mode {
                PathMapModeV1::NeutralEmpty => Vec::new(),
                PathMapModeV1::Set => vec![leaf(1)],
                PathMapModeV1::Map => vec![leaf(1), leaf(2)],
            };
            let root = u32::try_from(nodes.len()).expect("small fixture root");
            nodes.push(SemanticNodeV1 {
                operator: SemanticOperatorId(2),
                payload: None,
                fields: vec![SemanticFieldV1::PathMap { mode, entries }],
            });
            let canonical = term(&signature, nodes, vec![root])
                .canonicalize(&signature, &grammar, &bindings, term_limits)
                .expect("canonical PathMap term");
            let machine = image
                .project(
                    &canonical,
                    SemanticMachineProjectionContext::new(
                        &signature,
                        &grammar,
                        &bindings,
                        term_limits,
                        machine_limits,
                    ),
                )
                .expect("PathMap projection");
            let root = &machine.nodes[machine.roots[0] as usize];
            let mode_leaf = &machine.nodes[root.children[0] as usize];
            assert_eq!(mode_leaf.operator.stable_discriminant, 108);
            assert_eq!(mode_leaf.operator.payload_segments, vec![vec![expected_tag]]);
            assert_eq!(
                machine
                    .nodes
                    .iter()
                    .any(|node| node.operator.stable_discriminant == 109),
                expects_pair
            );
            if expects_pair {
                let pair = machine
                    .nodes
                    .iter()
                    .find(|node| node.operator.stable_discriminant == 109)
                    .expect("PathMap pair node");
                assert_eq!(pair.children.len(), 2);
            }
        }
    }

    #[test]
    fn inline_pathmap_image_codec_preserves_shared_mode_discriminant() {
        let (grammar, signature, image) = inline_pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticMachineAdmissionLimits::default();
        let bytes = image
            .encode(&signature, &grammar, &bindings, limits)
            .expect("encode PathMap machine image");
        let decoded =
            SemanticMachineImageV1::decode(&bytes, &signature, &grammar, &bindings, limits)
                .expect("decode PathMap machine image");
        assert_eq!(decoded, image);
    }

    #[test]
    fn inline_pathmap_rejects_colliding_exact_mode_templates() {
        let (grammar, signature, mut image) = inline_pathmap_fixture();
        let MachineFieldProjectionV1::InlinePathMap { empty, set, .. } =
            &mut image.operators[2].fields[0]
        else {
            panic!("PathMap projection fixture");
        };
        set.fixed_payload_segments = empty.fixed_payload_segments.clone();
        assert!(matches!(
            image.validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            ),
            Err(SemanticMachineImageError::IncompatibleTemplateReuse(108))
        ));
    }

    #[test]
    fn wide_pathmap_set_and_map_projection_is_iterative_and_bounded() {
        const WIDTH: usize = 20_000;
        let (grammar, signature, image) = inline_pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let machine_limits = SemanticMachineAdmissionLimits::default();

        for mode in [PathMapModeV1::Set, PathMapModeV1::Map] {
            let mut nodes = Vec::with_capacity(WIDTH + 1);
            for value in 0..WIDTH {
                nodes.push(leaf(i32::try_from(value).expect("fixture value fits i32")));
            }
            let entries = match mode {
                PathMapModeV1::Set => (0..WIDTH)
                    .map(|key| {
                        SemanticPathMapEntryV1::Key(
                            u32::try_from(key).expect("fixture key fits u32"),
                        )
                    })
                    .collect(),
                PathMapModeV1::Map => (0..WIDTH)
                    .map(|key| {
                        let key = u32::try_from(key).expect("fixture key fits u32");
                        SemanticPathMapEntryV1::KeyValue { key, value: key }
                    })
                    .collect(),
                PathMapModeV1::NeutralEmpty => unreachable!("loop contains only valued modes"),
            };
            nodes.push(SemanticNodeV1 {
                operator: SemanticOperatorId(2),
                payload: None,
                fields: vec![SemanticFieldV1::PathMap { mode, entries }],
            });
            let canonical =
                term(&signature, nodes, vec![u32::try_from(WIDTH).expect("fixture root fits u32")])
                    .canonicalize(&signature, &grammar, &bindings, term_limits)
                    .expect("wide PathMap canonicalizes iteratively");
            let machine = image
                .project(
                    &canonical,
                    SemanticMachineProjectionContext::new(
                        &signature,
                        &grammar,
                        &bindings,
                        term_limits,
                        machine_limits,
                    ),
                )
                .expect("wide PathMap projects iteratively");
            let root = &machine.nodes[machine.roots[0] as usize];
            assert_eq!(root.children.len(), WIDTH + 1);
            let mode_leaf = &machine.nodes[root.children[0] as usize];
            assert_eq!(mode_leaf.operator.stable_discriminant, 108);
            if mode == PathMapModeV1::Map {
                assert_eq!(
                    machine
                        .nodes
                        .iter()
                        .filter(|node| node.operator.stable_discriminant == 109)
                        .count(),
                    WIDTH
                );
            }
        }
    }

    #[test]
    fn inline_pathmap_checks_child_budget_before_projecting_mode_or_entries() {
        let (grammar, signature, image) = inline_pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let canonical = term(
            &signature,
            vec![SemanticNodeV1 {
                operator: SemanticOperatorId(2),
                payload: None,
                fields: vec![SemanticFieldV1::PathMap {
                    mode: PathMapModeV1::NeutralEmpty,
                    entries: Vec::new(),
                }],
            }],
            vec![0],
        )
        .canonicalize(&signature, &grammar, &bindings, term_limits)
        .expect("canonical empty PathMap");
        let machine_limits = SemanticMachineAdmissionLimits {
            max_projected_children: 0,
            ..SemanticMachineAdmissionLimits::default()
        };
        assert_eq!(
            image.project(
                &canonical,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    term_limits,
                    machine_limits,
                ),
            ),
            Err(SemanticMachineImageError::LimitExceeded("projected children"))
        );
    }

    #[test]
    fn inline_bag_reuses_the_main_constructor_as_its_only_spine() {
        let (grammar, signature, image) = inline_collection_fixture(CollectionKind::Bag);
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let raw = term(
            &signature,
            vec![
                leaf(2),
                leaf(1),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(2),
                    payload: None,
                    fields: vec![SemanticFieldV1::Collection {
                        kind: CollectionKind::Bag,
                        entries: vec![
                            SemanticCollectionEntryV1::Value(0),
                            SemanticCollectionEntryV1::Value(1),
                        ],
                    }],
                },
            ],
            vec![2],
        );
        let canonical = raw
            .canonicalize(&signature, &grammar, &bindings, term_limits)
            .expect("canonical bag");
        let projected = image
            .project(
                &canonical,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    term_limits,
                    SemanticMachineAdmissionLimits::default(),
                ),
            )
            .expect("inline bag projection");
        let root = &projected.nodes[projected.roots[0] as usize];
        assert_eq!(root.operator.label, "Term::Map");
        assert_eq!(root.children.len(), 2);
        assert_eq!(root.child_order, MachineChildOrderV1::CanonicalExactKey);
        assert_eq!(
            projected
                .nodes
                .iter()
                .filter(|node| node.operator.label == "Term::Map")
                .count(),
            1
        );
        assert!(!projected
            .nodes
            .iter()
            .any(|node| node.operator.label == "<map>"));

        let bytes = image
            .encode(&signature, &grammar, &bindings, SemanticMachineAdmissionLimits::default())
            .expect("inline image encode");
        assert_eq!(
            SemanticMachineImageV1::decode(
                &bytes,
                &signature,
                &grammar,
                &bindings,
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("inline image decode"),
            image
        );
    }

    #[test]
    fn inline_map_reuses_the_main_constructor_and_preserves_pair_boundaries() {
        let (grammar, signature, image) = inline_pair_collection_fixture(CollectionKind::Map);
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let raw = term(
            &signature,
            vec![
                leaf(1),
                leaf(2),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(2),
                    payload: None,
                    fields: vec![SemanticFieldV1::Collection {
                        kind: CollectionKind::Map,
                        entries: vec![SemanticCollectionEntryV1::KeyValue { key: 0, value: 1 }],
                    }],
                },
            ],
            vec![2],
        );
        let canonical = raw
            .canonicalize(&signature, &grammar, &bindings, term_limits)
            .expect("canonical map");
        let projected = image
            .project(
                &canonical,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    term_limits,
                    SemanticMachineAdmissionLimits::default(),
                ),
            )
            .expect("inline map projection");
        let root = &projected.nodes[projected.roots[0] as usize];
        assert_eq!(root.operator.label, "Term::Map");
        assert_eq!(root.children.len(), 1);
        assert_eq!(root.child_order, MachineChildOrderV1::Ordered);
        let pair = &projected.nodes[root.children[0] as usize];
        assert_eq!(pair.operator.label, "<pair>");
        assert_eq!(pair.children.len(), 2);
        assert!(!projected
            .nodes
            .iter()
            .any(|node| node.operator.label == "<map>"));

        let bytes = image
            .encode(&signature, &grammar, &bindings, SemanticMachineAdmissionLimits::default())
            .expect("inline-pair image encode");
        assert_eq!(
            SemanticMachineImageV1::decode(
                &bytes,
                &signature,
                &grammar,
                &bindings,
                SemanticMachineAdmissionLimits::default(),
            )
            .expect("inline-pair image decode"),
            image
        );
    }

    #[test]
    fn incompatible_map_projection_fails_closed() {
        let (grammar, signature, mut image) = fixture();
        image.operators[2].fields[0] = MachineFieldProjectionV1::ValueCollection {
            kind: CollectionKind::Map,
            spine: MachineOperatorTemplateV1 {
                stable_discriminant: 104,
                fixed_payload_segments: Vec::new(),
                label: "<invalid-map>".into(),
            },
            child_order: MachineChildOrderV1::Ordered,
        };
        assert!(matches!(
            image.validate(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticMachineAdmissionLimits::default(),
            ),
            Err(SemanticMachineImageError::FieldProjection { .. })
        ));
    }

    #[test]
    fn exact_non_utf8_bytes_project_as_one_framed_payload_segment() {
        let (grammar, signature, image) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let term_limits = SemanticTermAdmissionLimits::default();
        let machine_limits = SemanticMachineAdmissionLimits::default();
        let exact = vec![0x00, 0x7f, 0x80, 0xff];
        let canonical = term(
            &signature,
            vec![SemanticNodeV1 {
                operator: SemanticOperatorId(4),
                payload: None,
                fields: vec![SemanticFieldV1::Bytes(exact.clone())],
            }],
            vec![0],
        )
        .canonicalize(&signature, &grammar, &bindings, term_limits)
        .expect("canonical byte field");
        let projected = image
            .project(
                &canonical,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    term_limits,
                    machine_limits,
                ),
            )
            .expect("project byte field");

        assert_eq!(projected.nodes.len(), 2);
        assert_eq!(projected.roots, vec![1]);
        let leaf = &projected.nodes[0];
        assert_eq!(leaf.operator.stable_discriminant, 110);
        assert_eq!(leaf.operator.payload_segments, vec![b"bytes".to_vec(), exact]);
        assert!(leaf.children.is_empty());
    }

    #[test]
    fn projection_is_stack_safe_for_twenty_thousand_nodes() {
        let (grammar, signature, image) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let mut nodes = Vec::with_capacity(20_000);
        nodes.push(leaf(1));
        for target in 0..19_999u32 {
            nodes.push(SemanticNodeV1 {
                operator: SemanticOperatorId(1),
                payload: None,
                fields: vec![SemanticFieldV1::Child(target)],
            });
        }
        let term = term(&signature, nodes, vec![19_999]);
        let machine = image
            .project(
                &term,
                SemanticMachineProjectionContext::new(
                    &signature,
                    &grammar,
                    &bindings,
                    SemanticTermAdmissionLimits::default(),
                    SemanticMachineAdmissionLimits::default(),
                ),
            )
            .expect("deep projection");
        assert_eq!(machine.nodes.len(), 20_001);
        assert_eq!(machine.roots, vec![20_000]);
    }
}
