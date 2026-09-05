use crate::{
    CategoryId, CollectionKind, ConstructorId, GrammarCoreV1, ProductionId,
    RuntimeCapabilityBindings, RuntimeCapabilityKey, RuntimeCapabilityKind,
    RuntimeCapabilityRequirement, RuntimeEffect, ValidationError,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

mod canonical;

pub const SEMANTIC_SIGNATURE_ABI_V1: u16 = 1;
pub const SEMANTIC_TERM_IMAGE_ABI_V1: u16 = 1;

const SEMANTIC_TERM_IMAGE_MAGIC: &[u8; 8] = b"MTSIMG01";
const MAX_SIGNATURE_TEXT_BYTES: usize = 512;

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct SemanticOperatorId(pub u32);

/// Provenance of a constructor in the complete semantic signature.
///
/// Grammar constructors are checked against the authoritative
/// [`GrammarCoreV1`]. Generated constructors are reserved for mechanically
/// derived semantic families, such as higher-order application constructors;
/// they occupy IDs after the grammar constructor range.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SemanticOperatorOriginV1 {
    GrammarProduction(ProductionId),
    Generated { family: String, ordinal: u32 },
}

/// Built-in atom encodings have a single canonical byte representation.
/// Integers use little-endian bytes when `bits` is fixed. Arbitrary-width
/// integers use sign-and-minimal-magnitude form, and arbitrary-width unsigned
/// integers use a non-empty minimal big-endian magnitude.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SemanticBuiltinAtomV1 {
    Boolean,
    SignedInteger { bits: Option<u16> },
    UnsignedInteger { bits: Option<u16> },
    Float { bits: u16 },
    Utf8,
    Bytes,
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SemanticAtomSchemaV1 {
    Builtin(SemanticBuiltinAtomV1),
    /// Values outside the built-in encodings require an exact, installed,
    /// fingerprint-scoped codec. A declaration names authority but never
    /// grants it.
    External {
        codec: RuntimeCapabilityKey,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum SemanticFieldSchemaV1 {
    Child {
        category: CategoryId,
    },
    Sequence {
        element: CategoryId,
    },
    Collection {
        kind: CollectionKind,
        key: Option<CategoryId>,
        value: CategoryId,
    },
    Optional {
        category: CategoryId,
    },
    OptionalSequence {
        element: CategoryId,
    },
    OptionalTokenText,
    Scope {
        domain: CategoryId,
        body: CategoryId,
        minimum_arity: u32,
        maximum_arity: Option<u32>,
    },
    Variable {
        category: CategoryId,
    },
    Atom {
        schema: u32,
    },
    TokenText,
    Opaque {
        schema: u32,
    },
    Unit,
    /// A mode-preserving path map. Neutral empty, set, and map are distinct
    /// semantic values even when they contain no entries.
    PathMap {
        key: CategoryId,
        value: CategoryId,
    },
    /// An exact, uninterpreted byte string. Unlike [`Self::TokenText`], this
    /// carrier admits every octet sequence and never performs UTF-8
    /// validation or normalization.
    Bytes,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticOperatorDeclV1 {
    pub id: SemanticOperatorId,
    pub category: CategoryId,
    pub constructor: ConstructorId,
    /// Existing generated backends place this ordinal first in their semantic
    /// content key. Keeping it explicit lets an adapter preserve those bytes.
    pub stable_discriminant: u32,
    pub label: String,
    pub origin: SemanticOperatorOriginV1,
    pub payload: Option<u32>,
    pub fields: Vec<SemanticFieldSchemaV1>,
}

/// Source-neutral, complete signature for structural semantic values.
///
/// This artifact is derived from a checked grammar and its generated semantic
/// families. It contains no source text and cannot confer callback authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticSignatureV1 {
    pub abi: u16,
    pub grammar_fingerprint: [u8; 32],
    pub category_count: u32,
    pub constructor_count: u32,
    pub atom_schemas: Vec<SemanticAtomSchemaV1>,
    pub operators: Vec<SemanticOperatorDeclV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticSignatureError {
    UnsupportedAbi(u16),
    InvalidGrammar(Vec<ValidationError>),
    GrammarFingerprint,
    GrammarFingerprintMismatch,
    CategoryCountMismatch {
        expected: u32,
        actual: u32,
    },
    ConstructorCountTooSmall {
        grammar: u32,
        signature: u32,
    },
    NonDenseOperatorId {
        expected: u32,
        actual: u32,
    },
    NonDenseConstructorId {
        expected: u32,
        actual: u32,
    },
    DuplicateStableDiscriminant(u32),
    DuplicateOperatorPair {
        category: CategoryId,
        constructor: ConstructorId,
    },
    EmptyLabel(SemanticOperatorId),
    TextLimit(SemanticOperatorId),
    DuplicateLabel(String),
    UnknownCategory(CategoryId),
    UnknownAtomSchema(u32),
    DuplicateAtomSchema(u32),
    InvalidBuiltinAtomSchema(u32),
    InvalidProduction(ProductionId),
    ProductionMismatch(ProductionId),
    InvalidGeneratedOrigin(SemanticOperatorId),
    MissingGrammarConstructor {
        category: CategoryId,
        constructor: ConstructorId,
    },
    VariableForbidden(CategoryId),
    InvalidScopeArity(SemanticOperatorId),
    InvalidCodecKey(u32),
    MissingCodec(RuntimeCapabilityKey),
    CodecKind(RuntimeCapabilityKey),
    CodecEffect(RuntimeCapabilityKey),
    Encode(String),
}

impl SemanticSignatureV1 {
    pub fn fingerprint(&self) -> Result<[u8; 32], SemanticSignatureError> {
        let bytes = postcard::to_allocvec(self)
            .map_err(|error| SemanticSignatureError::Encode(error.to_string()))?;
        Ok(*blake3::hash(&bytes).as_bytes())
    }

    pub fn capability_requirements(&self) -> Vec<RuntimeCapabilityRequirement> {
        self.atom_schemas
            .iter()
            .filter_map(|schema| match schema {
                SemanticAtomSchemaV1::External { codec } => Some(RuntimeCapabilityRequirement {
                    key: codec.clone(),
                    effect: RuntimeEffect::Reflect,
                }),
                SemanticAtomSchemaV1::Builtin(_) => None,
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn validate(
        &self,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
    ) -> Result<(), SemanticSignatureError> {
        if self.abi != SEMANTIC_SIGNATURE_ABI_V1 {
            return Err(SemanticSignatureError::UnsupportedAbi(self.abi));
        }
        grammar
            .validate()
            .map_err(SemanticSignatureError::InvalidGrammar)?;
        let grammar_fingerprint = grammar
            .fingerprint()
            .map_err(|_| SemanticSignatureError::GrammarFingerprint)?;
        if self.grammar_fingerprint != grammar_fingerprint {
            return Err(SemanticSignatureError::GrammarFingerprintMismatch);
        }
        let grammar_category_count = u32::try_from(grammar.categories.len()).map_err(|_| {
            SemanticSignatureError::CategoryCountMismatch {
                expected: u32::MAX,
                actual: self.category_count,
            }
        })?;
        if self.category_count != grammar_category_count {
            return Err(SemanticSignatureError::CategoryCountMismatch {
                expected: grammar_category_count,
                actual: self.category_count,
            });
        }

        let grammar_constructors: BTreeSet<_> = grammar
            .productions
            .iter()
            .map(|production| production.constructor.0)
            .collect();
        let grammar_constructor_count =
            u32::try_from(grammar_constructors.len()).unwrap_or(u32::MAX);
        if self.constructor_count < grammar_constructor_count {
            return Err(SemanticSignatureError::ConstructorCountTooSmall {
                grammar: grammar_constructor_count,
                signature: self.constructor_count,
            });
        }

        let mut atom_schemas = BTreeSet::new();
        for (index, schema) in self.atom_schemas.iter().enumerate() {
            let index = u32::try_from(index).unwrap_or(u32::MAX);
            if !atom_schemas.insert(schema) {
                return Err(SemanticSignatureError::DuplicateAtomSchema(index));
            }
            match schema {
                SemanticAtomSchemaV1::Builtin(builtin) => {
                    if !valid_builtin_schema(builtin) {
                        return Err(SemanticSignatureError::InvalidBuiltinAtomSchema(index));
                    }
                },
                SemanticAtomSchemaV1::External { codec } => {
                    if codec.language_fingerprint != self.grammar_fingerprint
                        || codec.name.is_empty()
                        || codec.name.len() > MAX_SIGNATURE_TEXT_BYTES
                    {
                        return Err(SemanticSignatureError::InvalidCodecKey(index));
                    }
                    if codec.kind != RuntimeCapabilityKind::StructuralCodec {
                        return Err(SemanticSignatureError::CodecKind(codec.clone()));
                    }
                    let manifest = bindings
                        .get(codec)
                        .ok_or_else(|| SemanticSignatureError::MissingCodec(codec.clone()))?;
                    if manifest.key != *codec
                        || manifest.key.kind != RuntimeCapabilityKind::StructuralCodec
                    {
                        return Err(SemanticSignatureError::CodecKind(codec.clone()));
                    }
                    if !manifest.effects.contains(&RuntimeEffect::Reflect) {
                        return Err(SemanticSignatureError::CodecEffect(codec.clone()));
                    }
                },
            }
        }

        let mut stable_discriminants = BTreeSet::new();
        let mut pairs = BTreeSet::new();
        let mut labels = BTreeSet::new();
        let mut constructors = BTreeSet::new();
        for (index, operator) in self.operators.iter().enumerate() {
            let expected = u32::try_from(index).unwrap_or(u32::MAX);
            if operator.id.0 != expected {
                return Err(SemanticSignatureError::NonDenseOperatorId {
                    expected,
                    actual: operator.id.0,
                });
            }
            validate_category(operator.category, self.category_count)?;
            if operator.constructor.0 >= self.constructor_count {
                return Err(SemanticSignatureError::NonDenseConstructorId {
                    expected: self.constructor_count.saturating_sub(1),
                    actual: operator.constructor.0,
                });
            }
            constructors.insert(operator.constructor.0);
            if !stable_discriminants.insert(operator.stable_discriminant) {
                return Err(SemanticSignatureError::DuplicateStableDiscriminant(
                    operator.stable_discriminant,
                ));
            }
            if !pairs.insert((operator.category, operator.constructor)) {
                return Err(SemanticSignatureError::DuplicateOperatorPair {
                    category: operator.category,
                    constructor: operator.constructor,
                });
            }
            if operator.label.is_empty() {
                return Err(SemanticSignatureError::EmptyLabel(operator.id));
            }
            if operator.label.len() > MAX_SIGNATURE_TEXT_BYTES {
                return Err(SemanticSignatureError::TextLimit(operator.id));
            }
            if !labels.insert(operator.label.as_str()) {
                return Err(SemanticSignatureError::DuplicateLabel(operator.label.clone()));
            }
            if let Some(schema) = operator.payload {
                validate_atom_schema(schema, self.atom_schemas.len())?;
            }
            for field in &operator.fields {
                validate_field_schema(self, grammar, operator, field)?;
            }
            match &operator.origin {
                SemanticOperatorOriginV1::GrammarProduction(production_id) => {
                    let production = grammar
                        .productions
                        .get(production_id.0 as usize)
                        .ok_or(SemanticSignatureError::InvalidProduction(*production_id))?;
                    if production.id != *production_id
                        || production.result != operator.category
                        || production.constructor != operator.constructor
                    {
                        return Err(SemanticSignatureError::ProductionMismatch(*production_id));
                    }
                },
                SemanticOperatorOriginV1::Generated { family, .. } => {
                    if family.is_empty()
                        || family.len() > MAX_SIGNATURE_TEXT_BYTES
                        || operator.constructor.0 < grammar_constructor_count
                    {
                        return Err(SemanticSignatureError::InvalidGeneratedOrigin(operator.id));
                    }
                },
            }
        }
        for (expected, actual) in constructors.iter().copied().enumerate() {
            let expected = u32::try_from(expected).unwrap_or(u32::MAX);
            if actual != expected {
                return Err(SemanticSignatureError::NonDenseConstructorId { expected, actual });
            }
        }
        if u32::try_from(constructors.len()).unwrap_or(u32::MAX) != self.constructor_count {
            return Err(SemanticSignatureError::NonDenseConstructorId {
                expected: self.constructor_count.saturating_sub(1),
                actual: constructors.iter().next_back().copied().unwrap_or(u32::MAX),
            });
        }

        for production in &grammar.productions {
            if !pairs.contains(&(production.result, production.constructor)) {
                return Err(SemanticSignatureError::MissingGrammarConstructor {
                    category: production.result,
                    constructor: production.constructor,
                });
            }
        }
        Ok(())
    }
}

fn valid_builtin_schema(schema: &SemanticBuiltinAtomV1) -> bool {
    match schema {
        SemanticBuiltinAtomV1::SignedInteger { bits: Some(bits) }
        | SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(bits) } => {
            *bits > 0 && bits.is_multiple_of(8)
        },
        SemanticBuiltinAtomV1::Float { bits } => matches!(bits, 32 | 64),
        SemanticBuiltinAtomV1::Boolean
        | SemanticBuiltinAtomV1::SignedInteger { bits: None }
        | SemanticBuiltinAtomV1::UnsignedInteger { bits: None }
        | SemanticBuiltinAtomV1::Utf8
        | SemanticBuiltinAtomV1::Bytes
        | SemanticBuiltinAtomV1::Unit => true,
    }
}

fn validate_category(
    category: CategoryId,
    category_count: u32,
) -> Result<(), SemanticSignatureError> {
    if category.0 >= category_count {
        return Err(SemanticSignatureError::UnknownCategory(category));
    }
    Ok(())
}

fn validate_atom_schema(schema: u32, schema_count: usize) -> Result<(), SemanticSignatureError> {
    if usize::try_from(schema).map_or(true, |index| index >= schema_count) {
        return Err(SemanticSignatureError::UnknownAtomSchema(schema));
    }
    Ok(())
}

fn validate_field_schema(
    signature: &SemanticSignatureV1,
    grammar: &GrammarCoreV1,
    operator: &SemanticOperatorDeclV1,
    field: &SemanticFieldSchemaV1,
) -> Result<(), SemanticSignatureError> {
    match field {
        SemanticFieldSchemaV1::Child { category }
        | SemanticFieldSchemaV1::Sequence { element: category }
        | SemanticFieldSchemaV1::OptionalSequence { element: category }
        | SemanticFieldSchemaV1::Optional { category }
        | SemanticFieldSchemaV1::Variable { category } => {
            validate_category(*category, signature.category_count)?;
            if matches!(field, SemanticFieldSchemaV1::Variable { .. })
                && !grammar.categories[category.0 as usize].admits_variables
            {
                return Err(SemanticSignatureError::VariableForbidden(*category));
            }
        },
        SemanticFieldSchemaV1::Collection { kind, key, value } => {
            validate_category(*value, signature.category_count)?;
            if let Some(key) = key {
                validate_category(*key, signature.category_count)?;
            }
            let map_like = matches!(kind, CollectionKind::Map | CollectionKind::PathMap);
            if map_like != key.is_some() {
                return Err(SemanticSignatureError::InvalidGeneratedOrigin(operator.id));
            }
        },
        SemanticFieldSchemaV1::PathMap { key, value } => {
            validate_category(*key, signature.category_count)?;
            validate_category(*value, signature.category_count)?;
        },
        SemanticFieldSchemaV1::Scope {
            domain,
            body,
            minimum_arity,
            maximum_arity,
        } => {
            validate_category(*domain, signature.category_count)?;
            validate_category(*body, signature.category_count)?;
            if !grammar.categories[domain.0 as usize].admits_variables {
                return Err(SemanticSignatureError::VariableForbidden(*domain));
            }
            if maximum_arity.is_some_and(|maximum| maximum < *minimum_arity) {
                return Err(SemanticSignatureError::InvalidScopeArity(operator.id));
            }
        },
        SemanticFieldSchemaV1::Atom { schema } | SemanticFieldSchemaV1::Opaque { schema } => {
            validate_atom_schema(*schema, signature.atom_schemas.len())?;
            if matches!(field, SemanticFieldSchemaV1::Opaque { .. })
                && !matches!(
                    signature.atom_schemas[*schema as usize],
                    SemanticAtomSchemaV1::External { .. }
                )
            {
                return Err(SemanticSignatureError::InvalidCodecKey(*schema));
            }
        },
        SemanticFieldSchemaV1::TokenText
        | SemanticFieldSchemaV1::OptionalTokenText
        | SemanticFieldSchemaV1::Bytes
        | SemanticFieldSchemaV1::Unit => {},
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticAtomV1 {
    pub schema: u32,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticVariableV1 {
    /// `scope_depth == 0` denotes the innermost enclosing scope.
    Bound {
        scope_depth: u32,
        slot: u32,
    },
    Free {
        identity: Vec<u8>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticCollectionEntryV1 {
    Value(u32),
    KeyValue { key: u32, value: u32 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PathMapModeV1 {
    NeutralEmpty,
    Set,
    Map,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticPathMapEntryV1 {
    Key(u32),
    KeyValue { key: u32, value: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticFieldV1 {
    Child(u32),
    Sequence(Vec<u32>),
    Collection {
        kind: CollectionKind,
        entries: Vec<SemanticCollectionEntryV1>,
    },
    Optional(Option<u32>),
    OptionalSequence(Option<Vec<u32>>),
    OptionalTokenText(Option<String>),
    Scope {
        domain: CategoryId,
        arity: u32,
        body: u32,
    },
    Variable(SemanticVariableV1),
    Atom(SemanticAtomV1),
    TokenText(String),
    Opaque(SemanticAtomV1),
    Unit,
    PathMap {
        mode: PathMapModeV1,
        entries: Vec<SemanticPathMapEntryV1>,
    },
    Bytes(Vec<u8>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticNodeV1 {
    pub operator: SemanticOperatorId,
    pub payload: Option<SemanticAtomV1>,
    pub fields: Vec<SemanticFieldV1>,
}

/// Flat post-order semantic arena. Every node reference must point to an
/// earlier node. Roots are ordered because a semantic report can carry more
/// than one observed result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticTermImageV1 {
    pub abi: u16,
    pub signature_fingerprint: [u8; 32],
    pub nodes: Vec<SemanticNodeV1>,
    pub roots: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticTermAdmissionLimits {
    pub max_encoded_bytes: usize,
    pub max_nodes: usize,
    pub max_roots: usize,
    pub max_fields_per_node: usize,
    pub max_total_fields: usize,
    pub max_references: usize,
    pub max_sequence_length: usize,
    pub max_collection_entries: usize,
    pub max_scope_arity: u32,
    pub max_scope_depth: usize,
    pub max_scope_states: usize,
    pub max_atom_bytes: usize,
    pub max_total_atom_bytes: usize,
}

impl Default for SemanticTermAdmissionLimits {
    fn default() -> Self {
        Self {
            max_encoded_bytes: 64 * 1024 * 1024,
            max_nodes: 1_000_000,
            max_roots: 1_000_000,
            max_fields_per_node: 65_536,
            max_total_fields: 10_000_000,
            max_references: 10_000_000,
            max_sequence_length: 1_000_000,
            max_collection_entries: 1_000_000,
            max_scope_arity: 1_000_000,
            max_scope_depth: 65_536,
            max_scope_states: 10_000_000,
            max_atom_bytes: 16 * 1024 * 1024,
            max_total_atom_bytes: 64 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticTermImageError {
    Signature(SemanticSignatureError),
    UnsupportedAbi(u16),
    SignatureFingerprint,
    SignatureFingerprintMismatch,
    LimitExceeded(&'static str),
    UnknownOperator {
        node: u32,
        operator: SemanticOperatorId,
    },
    PayloadMismatch {
        node: u32,
    },
    FieldCount {
        node: u32,
        expected: usize,
        actual: usize,
    },
    FieldKind {
        node: u32,
        field: u32,
    },
    AtomSchema {
        node: u32,
        field: Option<u32>,
        expected: u32,
        actual: u32,
    },
    AtomEncoding {
        node: u32,
        field: Option<u32>,
    },
    Reference {
        node: u32,
        field: u32,
        target: u32,
    },
    Category {
        node: u32,
        field: u32,
        expected: CategoryId,
        actual: CategoryId,
    },
    CollectionKind {
        node: u32,
        field: u32,
    },
    PathMapMode {
        node: u32,
        field: u32,
    },
    PathMapEncoding,
    ScopeArity {
        node: u32,
        field: u32,
    },
    UnboundVariable {
        node: u32,
        field: u32,
    },
    EmptyFreeVariable {
        node: u32,
        field: u32,
    },
    NonCanonicalArena,
    DuplicateCollectionKey {
        node: u32,
        field: u32,
        key: u32,
    },
    Root(u32),
    UnreachableNode(u32),
    InvalidMagic,
    Truncated,
    InvalidTag(u8),
    InvalidUtf8,
    TrailingBytes,
    LengthOverflow,
    Allocation,
}

#[derive(Default)]
struct AdmissionCounts {
    fields: usize,
    references: usize,
    atom_bytes: usize,
}

#[derive(Clone, Copy)]
struct FieldLocation {
    node: u32,
    field: u32,
}

struct AdmissionState {
    counts: AdmissionCounts,
    limits: SemanticTermAdmissionLimits,
}

impl SemanticTermImageV1 {
    pub fn verify(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<(), SemanticTermImageError> {
        self.verify_well_formed(signature, grammar, bindings, limits)?;
        let canonical = canonical::canonicalize_well_formed(self, limits)?;
        if canonical != *self {
            return Err(SemanticTermImageError::NonCanonicalArena);
        }
        Ok(())
    }

    /// Construct the unique height-stratified, exactly interned arena for this
    /// semantic forest. Root order and multiplicity remain significant; node
    /// allocation order and optional structural sharing do not.
    pub fn canonicalize(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<Self, SemanticTermImageError> {
        self.verify_well_formed(signature, grammar, bindings, limits)?;
        let canonical = canonical::canonicalize_well_formed(self, limits)?;
        canonical.verify_well_formed(signature, grammar, bindings, limits)?;
        Ok(canonical)
    }

    fn verify_well_formed(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<(), SemanticTermImageError> {
        signature
            .validate(grammar, bindings)
            .map_err(SemanticTermImageError::Signature)?;
        if self.abi != SEMANTIC_TERM_IMAGE_ABI_V1 {
            return Err(SemanticTermImageError::UnsupportedAbi(self.abi));
        }
        let signature_fingerprint = signature
            .fingerprint()
            .map_err(SemanticTermImageError::Signature)?;
        if self.signature_fingerprint != signature_fingerprint {
            return Err(SemanticTermImageError::SignatureFingerprintMismatch);
        }
        enforce_limit(encoded_image_len(self)?, limits.max_encoded_bytes, "encoded bytes")?;
        enforce_limit(self.nodes.len(), limits.max_nodes, "nodes")?;
        enforce_limit(self.roots.len(), limits.max_roots, "roots")?;

        let mut admission = AdmissionState {
            counts: AdmissionCounts {
                references: self.roots.len(),
                ..AdmissionCounts::default()
            },
            limits,
        };
        enforce_limit(admission.counts.references, limits.max_references, "references")?;

        for (node_index, node) in self.nodes.iter().enumerate() {
            let node_index = u32::try_from(node_index)
                .map_err(|_| SemanticTermImageError::LimitExceeded("nodes"))?;
            let operator = signature
                .operators
                .get(node.operator.0 as usize)
                .filter(|operator| operator.id == node.operator)
                .ok_or(SemanticTermImageError::UnknownOperator {
                    node: node_index,
                    operator: node.operator,
                })?;
            match (operator.payload, &node.payload) {
                (None, None) => {},
                (Some(expected), Some(atom)) if expected == atom.schema => {
                    admission.validate_atom(signature, atom, node_index, None)?;
                },
                (Some(expected), Some(atom)) => {
                    return Err(SemanticTermImageError::AtomSchema {
                        node: node_index,
                        field: None,
                        expected,
                        actual: atom.schema,
                    });
                },
                _ => return Err(SemanticTermImageError::PayloadMismatch { node: node_index }),
            }
            if node.fields.len() != operator.fields.len() {
                return Err(SemanticTermImageError::FieldCount {
                    node: node_index,
                    expected: operator.fields.len(),
                    actual: node.fields.len(),
                });
            }
            enforce_limit(node.fields.len(), limits.max_fields_per_node, "fields per node")?;
            admission.counts.fields = admission
                .counts
                .fields
                .checked_add(node.fields.len())
                .ok_or(SemanticTermImageError::LengthOverflow)?;
            enforce_limit(admission.counts.fields, limits.max_total_fields, "total fields")?;
            for (field_index, (schema, field)) in
                operator.fields.iter().zip(&node.fields).enumerate()
            {
                let field_index = u32::try_from(field_index)
                    .map_err(|_| SemanticTermImageError::LimitExceeded("fields per node"))?;
                admission.validate_field(
                    signature,
                    &self.nodes,
                    FieldLocation { node: node_index, field: field_index },
                    schema,
                    field,
                )?;
            }
        }

        for root in &self.roots {
            if *root as usize >= self.nodes.len() {
                return Err(SemanticTermImageError::Root(*root));
            }
        }
        validate_reachability(self)?;
        validate_scope_uses(self, signature, limits)?;
        Ok(())
    }

    pub fn canonical_fingerprint(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<[u8; 32], SemanticTermImageError> {
        let canonical = self.canonicalize(signature, grammar, bindings, limits)?;
        let bytes = canonical.encode(signature, grammar, bindings, limits)?;
        Ok(*blake3::hash(&bytes).as_bytes())
    }
}

pub(crate) fn enforce_limit(
    actual: usize,
    limit: usize,
    name: &'static str,
) -> Result<(), SemanticTermImageError> {
    if actual > limit {
        return Err(SemanticTermImageError::LimitExceeded(name));
    }
    Ok(())
}

impl AdmissionState {
    fn validate_atom(
        &mut self,
        signature: &SemanticSignatureV1,
        atom: &SemanticAtomV1,
        node: u32,
        field: Option<u32>,
    ) -> Result<(), SemanticTermImageError> {
        self.charge_bytes(atom.bytes.len())?;
        let schema = signature.atom_schemas.get(atom.schema as usize).ok_or(
            SemanticTermImageError::AtomSchema {
                node,
                field,
                expected: atom.schema,
                actual: atom.schema,
            },
        )?;
        let valid = match schema {
            SemanticAtomSchemaV1::External { .. } => true,
            SemanticAtomSchemaV1::Builtin(builtin) => validate_builtin_atom(builtin, &atom.bytes),
        };
        if !valid {
            return Err(SemanticTermImageError::AtomEncoding { node, field });
        }
        Ok(())
    }
}

fn validate_builtin_atom(schema: &SemanticBuiltinAtomV1, bytes: &[u8]) -> bool {
    match schema {
        SemanticBuiltinAtomV1::Boolean => matches!(bytes, [0] | [1]),
        SemanticBuiltinAtomV1::SignedInteger { bits: Some(bits) }
        | SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(bits) } => {
            usize::from(*bits) / 8 == bytes.len()
        },
        SemanticBuiltinAtomV1::SignedInteger { bits: None } => match bytes {
            [sign, magnitude @ ..] if matches!(*sign, 0 | 1) && !magnitude.is_empty() => {
                if magnitude == [0] {
                    *sign == 0
                } else {
                    magnitude[0] != 0
                }
            },
            _ => false,
        },
        SemanticBuiltinAtomV1::UnsignedInteger { bits: None } => {
            !bytes.is_empty() && (bytes.len() == 1 || bytes[0] != 0)
        },
        SemanticBuiltinAtomV1::Float { bits: 32 } => {
            let Ok(raw) = <[u8; 4]>::try_from(bytes) else {
                return false;
            };
            let raw = u32::from_le_bytes(raw);
            let is_nan = raw & 0x7f80_0000 == 0x7f80_0000 && raw & 0x007f_ffff != 0;
            !is_nan || raw == f32::NAN.to_bits()
        },
        SemanticBuiltinAtomV1::Float { bits: 64 } => {
            let Ok(raw) = <[u8; 8]>::try_from(bytes) else {
                return false;
            };
            let raw = u64::from_le_bytes(raw);
            let is_nan = raw & 0x7ff0_0000_0000_0000 == 0x7ff0_0000_0000_0000
                && raw & 0x000f_ffff_ffff_ffff != 0;
            !is_nan || raw == f64::NAN.to_bits()
        },
        SemanticBuiltinAtomV1::Float { .. } => false,
        SemanticBuiltinAtomV1::Utf8 => std::str::from_utf8(bytes).is_ok(),
        SemanticBuiltinAtomV1::Bytes => true,
        SemanticBuiltinAtomV1::Unit => bytes.is_empty(),
    }
}

impl AdmissionState {
    fn validate_field(
        &mut self,
        signature: &SemanticSignatureV1,
        nodes: &[SemanticNodeV1],
        location: FieldLocation,
        schema: &SemanticFieldSchemaV1,
        field: &SemanticFieldV1,
    ) -> Result<(), SemanticTermImageError> {
        let FieldLocation { node, field: field_index } = location;
        match (schema, field) {
            (SemanticFieldSchemaV1::Child { category }, SemanticFieldV1::Child(target)) => {
                self.validate_reference(signature, nodes, location, *target, *category)?;
            },
            (SemanticFieldSchemaV1::Sequence { element }, SemanticFieldV1::Sequence(targets)) => {
                enforce_limit(targets.len(), self.limits.max_sequence_length, "sequence length")?;
                for target in targets {
                    self.validate_reference(signature, nodes, location, *target, *element)?;
                }
            },
            (
                SemanticFieldSchemaV1::Collection { kind, key, value },
                SemanticFieldV1::Collection { kind: actual_kind, entries },
            ) => {
                if kind != actual_kind {
                    return Err(SemanticTermImageError::CollectionKind {
                        node,
                        field: field_index,
                    });
                }
                enforce_limit(
                    entries.len(),
                    self.limits.max_collection_entries,
                    "collection entries",
                )?;
                for entry in entries {
                    match (key, entry) {
                        (None, SemanticCollectionEntryV1::Value(target)) => {
                            self.validate_reference(signature, nodes, location, *target, *value)?
                        },
                        (
                            Some(key_category),
                            SemanticCollectionEntryV1::KeyValue { key, value: item },
                        ) => {
                            self.validate_reference(
                                signature,
                                nodes,
                                location,
                                *key,
                                *key_category,
                            )?;
                            self.validate_reference(signature, nodes, location, *item, *value)?;
                        },
                        _ => {
                            return Err(SemanticTermImageError::CollectionKind {
                                node,
                                field: field_index,
                            });
                        },
                    }
                }
            },
            (
                SemanticFieldSchemaV1::PathMap { key, value },
                SemanticFieldV1::PathMap { mode, entries },
            ) => {
                enforce_limit(
                    entries.len(),
                    self.limits.max_collection_entries,
                    "collection entries",
                )?;
                match mode {
                    PathMapModeV1::NeutralEmpty if entries.is_empty() => {},
                    PathMapModeV1::NeutralEmpty => {
                        return Err(SemanticTermImageError::PathMapMode {
                            node,
                            field: field_index,
                        });
                    },
                    PathMapModeV1::Set => {
                        for entry in entries {
                            let SemanticPathMapEntryV1::Key(target) = entry else {
                                return Err(SemanticTermImageError::PathMapMode {
                                    node,
                                    field: field_index,
                                });
                            };
                            self.validate_reference(signature, nodes, location, *target, *key)?;
                        }
                    },
                    PathMapModeV1::Map => {
                        for entry in entries {
                            let SemanticPathMapEntryV1::KeyValue {
                                key: entry_key,
                                value: entry_value,
                            } = entry
                            else {
                                return Err(SemanticTermImageError::PathMapMode {
                                    node,
                                    field: field_index,
                                });
                            };
                            self.validate_reference(signature, nodes, location, *entry_key, *key)?;
                            self.validate_reference(
                                signature,
                                nodes,
                                location,
                                *entry_value,
                                *value,
                            )?;
                        }
                    },
                }
            },
            (SemanticFieldSchemaV1::Optional { category }, SemanticFieldV1::Optional(target)) => {
                if let Some(target) = target {
                    self.validate_reference(signature, nodes, location, *target, *category)?;
                }
            },
            (
                SemanticFieldSchemaV1::OptionalSequence { element },
                SemanticFieldV1::OptionalSequence(targets),
            ) => {
                if let Some(targets) = targets {
                    enforce_limit(
                        targets.len(),
                        self.limits.max_sequence_length,
                        "sequence length",
                    )?;
                    for target in targets {
                        self.validate_reference(signature, nodes, location, *target, *element)?;
                    }
                }
            },
            (
                SemanticFieldSchemaV1::Scope {
                    domain,
                    body,
                    minimum_arity,
                    maximum_arity,
                },
                SemanticFieldV1::Scope {
                    domain: actual_domain,
                    arity,
                    body: target,
                },
            ) => {
                if domain != actual_domain
                    || *arity < *minimum_arity
                    || maximum_arity.is_some_and(|maximum| *arity > maximum)
                    || *arity > self.limits.max_scope_arity
                {
                    return Err(SemanticTermImageError::ScopeArity { node, field: field_index });
                }
                self.validate_reference(signature, nodes, location, *target, *body)?;
            },
            (
                SemanticFieldSchemaV1::Variable { .. },
                SemanticFieldV1::Variable(SemanticVariableV1::Bound { scope_depth, .. }),
            ) => {
                enforce_limit(*scope_depth as usize, self.limits.max_scope_depth, "scope depth")?;
            },
            (
                SemanticFieldSchemaV1::Variable { .. },
                SemanticFieldV1::Variable(SemanticVariableV1::Free { identity }),
            ) => {
                if identity.is_empty() {
                    return Err(SemanticTermImageError::EmptyFreeVariable {
                        node,
                        field: field_index,
                    });
                }
                self.charge_bytes(identity.len())?;
            },
            (SemanticFieldSchemaV1::Atom { schema }, SemanticFieldV1::Atom(atom))
            | (SemanticFieldSchemaV1::Opaque { schema }, SemanticFieldV1::Opaque(atom)) => {
                if atom.schema != *schema {
                    return Err(SemanticTermImageError::AtomSchema {
                        node,
                        field: Some(field_index),
                        expected: *schema,
                        actual: atom.schema,
                    });
                }
                self.validate_atom(signature, atom, node, Some(field_index))?;
            },
            (SemanticFieldSchemaV1::TokenText, SemanticFieldV1::TokenText(text)) => {
                self.charge_bytes(text.len())?;
            },
            (
                SemanticFieldSchemaV1::OptionalTokenText,
                SemanticFieldV1::OptionalTokenText(text),
            ) => {
                if let Some(text) = text {
                    self.charge_bytes(text.len())?;
                }
            },
            (SemanticFieldSchemaV1::Bytes, SemanticFieldV1::Bytes(bytes)) => {
                self.charge_bytes(bytes.len())?;
            },
            (SemanticFieldSchemaV1::Unit, SemanticFieldV1::Unit) => {},
            _ => {
                return Err(SemanticTermImageError::FieldKind { node, field: field_index });
            },
        }
        Ok(())
    }

    fn charge_bytes(&mut self, bytes: usize) -> Result<(), SemanticTermImageError> {
        charge_bytes(bytes, &mut self.counts, self.limits)
    }

    fn validate_reference(
        &mut self,
        signature: &SemanticSignatureV1,
        nodes: &[SemanticNodeV1],
        location: FieldLocation,
        target: u32,
        expected: CategoryId,
    ) -> Result<(), SemanticTermImageError> {
        let FieldLocation { node, field } = location;
        if target >= node {
            return Err(SemanticTermImageError::Reference { node, field, target });
        }
        self.counts.references = self
            .counts
            .references
            .checked_add(1)
            .ok_or(SemanticTermImageError::LengthOverflow)?;
        enforce_limit(self.counts.references, self.limits.max_references, "references")?;
        let target_node = nodes
            .get(target as usize)
            .ok_or(SemanticTermImageError::Reference { node, field, target })?;
        let actual = signature
            .operators
            .get(target_node.operator.0 as usize)
            .filter(|operator| operator.id == target_node.operator)
            .ok_or(SemanticTermImageError::UnknownOperator {
                node: target,
                operator: target_node.operator,
            })?
            .category;
        if actual != expected {
            return Err(SemanticTermImageError::Category { node, field, expected, actual });
        }
        Ok(())
    }
}

fn charge_bytes(
    bytes: usize,
    counts: &mut AdmissionCounts,
    limits: SemanticTermAdmissionLimits,
) -> Result<(), SemanticTermImageError> {
    enforce_limit(bytes, limits.max_atom_bytes, "atom bytes")?;
    counts.atom_bytes = counts
        .atom_bytes
        .checked_add(bytes)
        .ok_or(SemanticTermImageError::LengthOverflow)?;
    enforce_limit(counts.atom_bytes, limits.max_total_atom_bytes, "total atom bytes")
}

fn field_references(field: &SemanticFieldV1, output: &mut Vec<u32>) {
    match field {
        SemanticFieldV1::Child(target) => output.push(*target),
        SemanticFieldV1::Sequence(targets) => output.extend(targets.iter().copied()),
        SemanticFieldV1::Collection { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticCollectionEntryV1::Value(target) => output.push(*target),
                    SemanticCollectionEntryV1::KeyValue { key, value } => {
                        output.push(*key);
                        output.push(*value);
                    },
                }
            }
        },
        SemanticFieldV1::PathMap { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticPathMapEntryV1::Key(target) => output.push(*target),
                    SemanticPathMapEntryV1::KeyValue { key, value } => {
                        output.push(*key);
                        output.push(*value);
                    },
                }
            }
        },
        SemanticFieldV1::Optional(Some(target)) => output.push(*target),
        SemanticFieldV1::OptionalSequence(Some(targets)) => {
            output.extend(targets.iter().copied());
        },
        SemanticFieldV1::Scope { body, .. } => output.push(*body),
        SemanticFieldV1::Optional(None)
        | SemanticFieldV1::OptionalSequence(None)
        | SemanticFieldV1::OptionalTokenText(_)
        | SemanticFieldV1::Variable(_)
        | SemanticFieldV1::Atom(_)
        | SemanticFieldV1::TokenText(_)
        | SemanticFieldV1::Bytes(_)
        | SemanticFieldV1::Opaque(_)
        | SemanticFieldV1::Unit => {},
    }
}

fn validate_reachability(image: &SemanticTermImageV1) -> Result<(), SemanticTermImageError> {
    let mut reachable = vec![false; image.nodes.len()];
    let mut pending = image.roots.clone();
    let mut references = Vec::new();
    while let Some(node) = pending.pop() {
        let slot = &mut reachable[node as usize];
        if *slot {
            continue;
        }
        *slot = true;
        references.clear();
        for field in &image.nodes[node as usize].fields {
            field_references(field, &mut references);
        }
        pending.extend(references.iter().copied());
    }
    if let Some((index, _)) = reachable.iter().enumerate().find(|(_, seen)| !**seen) {
        return Err(SemanticTermImageError::UnreachableNode(
            u32::try_from(index).unwrap_or(u32::MAX),
        ));
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct ScopeFrame {
    parent: Option<usize>,
    domain: CategoryId,
    arity: u32,
    depth: usize,
}

fn validate_scope_uses(
    image: &SemanticTermImageV1,
    signature: &SemanticSignatureV1,
    limits: SemanticTermAdmissionLimits,
) -> Result<(), SemanticTermImageError> {
    let mut frames = Vec::<ScopeFrame>::new();
    let mut pending: Vec<_> = image.roots.iter().map(|root| (*root, None)).collect();
    let mut visited = BTreeSet::new();
    let mut states = 0usize;
    while let Some((node_index, environment)) = pending.pop() {
        if !visited.insert((node_index, environment)) {
            continue;
        }
        states = states
            .checked_add(1)
            .ok_or(SemanticTermImageError::LengthOverflow)?;
        enforce_limit(states, limits.max_scope_states, "scope states")?;
        let node = &image.nodes[node_index as usize];
        let operator = &signature.operators[node.operator.0 as usize];
        for (field_index, (schema, field)) in operator.fields.iter().zip(&node.fields).enumerate() {
            let field_index = u32::try_from(field_index).unwrap_or(u32::MAX);
            match (schema, field) {
                (
                    SemanticFieldSchemaV1::Variable { category },
                    SemanticFieldV1::Variable(SemanticVariableV1::Bound { scope_depth, slot }),
                ) => {
                    let mut frame: Option<usize> = environment;
                    for _ in 0..*scope_depth {
                        frame = frame.and_then(|index: usize| frames[index].parent);
                    }
                    let valid = frame
                        .map(|index| frames[index])
                        .is_some_and(|frame| frame.domain == *category && *slot < frame.arity);
                    if !valid {
                        return Err(SemanticTermImageError::UnboundVariable {
                            node: node_index,
                            field: field_index,
                        });
                    }
                },
                (
                    SemanticFieldSchemaV1::Scope { .. },
                    SemanticFieldV1::Scope { domain, arity, body },
                ) => {
                    let depth = environment.map_or(1, |index| frames[index].depth + 1);
                    enforce_limit(depth, limits.max_scope_depth, "scope depth")?;
                    let frame = frames.len();
                    frames.push(ScopeFrame {
                        parent: environment,
                        domain: *domain,
                        arity: *arity,
                        depth,
                    });
                    pending.push((*body, Some(frame)));
                },
                _ => push_non_scope_references(field, environment, &mut pending),
            }
        }
    }
    Ok(())
}

fn push_non_scope_references(
    field: &SemanticFieldV1,
    environment: Option<usize>,
    pending: &mut Vec<(u32, Option<usize>)>,
) {
    match field {
        SemanticFieldV1::Child(target) => pending.push((*target, environment)),
        SemanticFieldV1::Sequence(targets) => {
            pending.extend(targets.iter().map(|target| (*target, environment)));
        },
        SemanticFieldV1::Collection { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticCollectionEntryV1::Value(target) => {
                        pending.push((*target, environment));
                    },
                    SemanticCollectionEntryV1::KeyValue { key, value } => {
                        pending.push((*key, environment));
                        pending.push((*value, environment));
                    },
                }
            }
        },
        SemanticFieldV1::PathMap { entries, .. } => {
            for entry in entries {
                match entry {
                    SemanticPathMapEntryV1::Key(target) => {
                        pending.push((*target, environment));
                    },
                    SemanticPathMapEntryV1::KeyValue { key, value } => {
                        pending.push((*key, environment));
                        pending.push((*value, environment));
                    },
                }
            }
        },
        SemanticFieldV1::Optional(Some(target)) => pending.push((*target, environment)),
        SemanticFieldV1::OptionalSequence(Some(targets)) => {
            pending.extend(targets.iter().map(|target| (*target, environment)));
        },
        SemanticFieldV1::Scope { .. }
        | SemanticFieldV1::Optional(None)
        | SemanticFieldV1::OptionalSequence(None)
        | SemanticFieldV1::OptionalTokenText(_)
        | SemanticFieldV1::Variable(_)
        | SemanticFieldV1::Atom(_)
        | SemanticFieldV1::TokenText(_)
        | SemanticFieldV1::Bytes(_)
        | SemanticFieldV1::Opaque(_)
        | SemanticFieldV1::Unit => {},
    }
}

impl SemanticTermImageV1 {
    /// Encode after complete admission. The format is flat and length-prefixed;
    /// no source representation or recursive serializer is involved.
    pub fn encode(
        &self,
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<Vec<u8>, SemanticTermImageError> {
        self.verify(signature, grammar, bindings, limits)?;
        let encoded_len = encoded_image_len(self)?;
        enforce_limit(encoded_len, limits.max_encoded_bytes, "encoded bytes")?;
        let mut output = Vec::new();
        output
            .try_reserve_exact(encoded_len)
            .map_err(|_| SemanticTermImageError::Allocation)?;
        output.extend_from_slice(SEMANTIC_TERM_IMAGE_MAGIC);
        write_u16(&mut output, self.abi);
        output.extend_from_slice(&self.signature_fingerprint);
        write_u32(&mut output, checked_u32(self.nodes.len())?);
        write_u32(&mut output, checked_u32(self.roots.len())?);
        for node in &self.nodes {
            write_u32(&mut output, node.operator.0);
            match &node.payload {
                None => output.push(0),
                Some(atom) => {
                    output.push(1);
                    encode_atom(atom, &mut output)?;
                },
            }
            write_u32(&mut output, checked_u32(node.fields.len())?);
            for field in &node.fields {
                encode_field(field, &mut output)?;
            }
        }
        for root in &self.roots {
            write_u32(&mut output, *root);
        }
        debug_assert_eq!(output.len(), encoded_len);
        Ok(output)
    }

    /// Decode untrusted bytes under allocation bounds, then re-run the full
    /// signature, category, scope, reachability, and authority admission gate.
    pub fn decode(
        bytes: &[u8],
        signature: &SemanticSignatureV1,
        grammar: &GrammarCoreV1,
        bindings: &RuntimeCapabilityBindings,
        limits: SemanticTermAdmissionLimits,
    ) -> Result<Self, SemanticTermImageError> {
        enforce_limit(bytes.len(), limits.max_encoded_bytes, "encoded bytes")?;
        let mut input = ImageReader::new(bytes);
        if input.read_exact(SEMANTIC_TERM_IMAGE_MAGIC.len())? != SEMANTIC_TERM_IMAGE_MAGIC {
            return Err(SemanticTermImageError::InvalidMagic);
        }
        let abi = input.read_u16()?;
        if abi != SEMANTIC_TERM_IMAGE_ABI_V1 {
            return Err(SemanticTermImageError::UnsupportedAbi(abi));
        }
        let signature_fingerprint = input.read_array::<32>()?;
        let expected_fingerprint = signature
            .fingerprint()
            .map_err(SemanticTermImageError::Signature)?;
        if signature_fingerprint != expected_fingerprint {
            return Err(SemanticTermImageError::SignatureFingerprintMismatch);
        }
        let node_count = input.read_count(limits.max_nodes, "nodes")?;
        let root_count = input.read_count(limits.max_roots, "roots")?;
        let mut nodes = empty_vec(node_count)?;
        let mut counts = AdmissionCounts {
            references: root_count,
            ..AdmissionCounts::default()
        };
        enforce_limit(counts.references, limits.max_references, "references")?;
        for node_index in 0..node_count {
            let node_index = u32::try_from(node_index)
                .map_err(|_| SemanticTermImageError::LimitExceeded("nodes"))?;
            let operator = SemanticOperatorId(input.read_u32()?);
            let payload = match input.read_u8()? {
                0 => None,
                1 => Some(decode_atom(&mut input, node_index, None, &mut counts, limits)?),
                tag => return Err(SemanticTermImageError::InvalidTag(tag)),
            };
            let field_count = input.read_count(limits.max_fields_per_node, "fields per node")?;
            counts.fields = counts
                .fields
                .checked_add(field_count)
                .ok_or(SemanticTermImageError::LengthOverflow)?;
            enforce_limit(counts.fields, limits.max_total_fields, "total fields")?;
            let mut fields = empty_vec(field_count)?;
            for field_index in 0..field_count {
                fields.push(decode_field(
                    &mut input,
                    node_index,
                    u32::try_from(field_index)
                        .map_err(|_| SemanticTermImageError::LimitExceeded("fields per node"))?,
                    &mut counts,
                    limits,
                )?);
            }
            nodes.push(SemanticNodeV1 { operator, payload, fields });
        }
        let mut roots = empty_vec(root_count)?;
        for _ in 0..root_count {
            roots.push(input.read_u32()?);
        }
        if !input.is_empty() {
            return Err(SemanticTermImageError::TrailingBytes);
        }
        let image = Self { abi, signature_fingerprint, nodes, roots };
        image.verify(signature, grammar, bindings, limits)?;
        Ok(image)
    }
}

pub(crate) fn checked_u32(value: usize) -> Result<u32, SemanticTermImageError> {
    u32::try_from(value).map_err(|_| SemanticTermImageError::LengthOverflow)
}

pub(crate) fn checked_add(
    total: &mut usize,
    additional: usize,
) -> Result<(), SemanticTermImageError> {
    *total = total
        .checked_add(additional)
        .ok_or(SemanticTermImageError::LengthOverflow)?;
    Ok(())
}

fn encoded_image_len(image: &SemanticTermImageV1) -> Result<usize, SemanticTermImageError> {
    let mut total = SEMANTIC_TERM_IMAGE_MAGIC.len() + 2 + 32 + 4 + 4;
    for node in &image.nodes {
        checked_add(&mut total, 4 + 1 + 4)?;
        if let Some(payload) = &node.payload {
            checked_add(&mut total, encoded_atom_len(payload)?)?;
        }
        for field in &node.fields {
            checked_add(&mut total, encoded_field_len(field)?)?;
        }
    }
    checked_add(
        &mut total,
        image
            .roots
            .len()
            .checked_mul(4)
            .ok_or(SemanticTermImageError::LengthOverflow)?,
    )?;
    Ok(total)
}

fn encoded_atom_len(atom: &SemanticAtomV1) -> Result<usize, SemanticTermImageError> {
    8usize
        .checked_add(atom.bytes.len())
        .ok_or(SemanticTermImageError::LengthOverflow)
}

fn encoded_field_len(field: &SemanticFieldV1) -> Result<usize, SemanticTermImageError> {
    match field {
        SemanticFieldV1::Child(_) => Ok(1 + 4),
        SemanticFieldV1::Sequence(targets) => 5usize
            .checked_add(
                targets
                    .len()
                    .checked_mul(4)
                    .ok_or(SemanticTermImageError::LengthOverflow)?,
            )
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::Collection { entries, .. } => {
            let mut total = 1 + 1 + 4;
            for entry in entries {
                checked_add(
                    &mut total,
                    match entry {
                        SemanticCollectionEntryV1::Value(_) => 1 + 4,
                        SemanticCollectionEntryV1::KeyValue { .. } => 1 + 4 + 4,
                    },
                )?;
            }
            Ok(total)
        },
        SemanticFieldV1::PathMap { entries, .. } => {
            let mut total = 1 + 1 + 4;
            for entry in entries {
                checked_add(
                    &mut total,
                    match entry {
                        SemanticPathMapEntryV1::Key(_) => 4,
                        SemanticPathMapEntryV1::KeyValue { .. } => 4 + 4,
                    },
                )?;
            }
            Ok(total)
        },
        SemanticFieldV1::Optional(None) => Ok(1 + 1),
        SemanticFieldV1::Optional(Some(_)) => Ok(1 + 1 + 4),
        SemanticFieldV1::OptionalSequence(None) => Ok(1 + 1),
        SemanticFieldV1::OptionalSequence(Some(targets)) => 6usize
            .checked_add(
                targets
                    .len()
                    .checked_mul(4)
                    .ok_or(SemanticTermImageError::LengthOverflow)?,
            )
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::OptionalTokenText(None) => Ok(1 + 1),
        SemanticFieldV1::OptionalTokenText(Some(text)) => 6usize
            .checked_add(text.len())
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::Scope { .. } => Ok(1 + 4 + 4 + 4),
        SemanticFieldV1::Variable(SemanticVariableV1::Bound { .. }) => Ok(1 + 1 + 4 + 4),
        SemanticFieldV1::Variable(SemanticVariableV1::Free { identity }) => 6usize
            .checked_add(identity.len())
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::Atom(atom) | SemanticFieldV1::Opaque(atom) => 1usize
            .checked_add(encoded_atom_len(atom)?)
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::TokenText(text) => 5usize
            .checked_add(text.len())
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::Bytes(bytes) => 5usize
            .checked_add(bytes.len())
            .ok_or(SemanticTermImageError::LengthOverflow),
        SemanticFieldV1::Unit => Ok(1),
    }
}

pub(crate) fn write_u16(output: &mut Vec<u8>, value: u16) {
    output.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_u32(output: &mut Vec<u8>, value: u32) {
    output.extend_from_slice(&value.to_le_bytes());
}

fn encode_atom(atom: &SemanticAtomV1, output: &mut Vec<u8>) -> Result<(), SemanticTermImageError> {
    write_u32(output, atom.schema);
    write_u32(output, checked_u32(atom.bytes.len())?);
    output.extend_from_slice(&atom.bytes);
    Ok(())
}

fn encode_field(
    field: &SemanticFieldV1,
    output: &mut Vec<u8>,
) -> Result<(), SemanticTermImageError> {
    match field {
        SemanticFieldV1::Child(target) => {
            output.push(0);
            write_u32(output, *target);
        },
        SemanticFieldV1::Sequence(targets) => {
            output.push(1);
            write_u32(output, checked_u32(targets.len())?);
            for target in targets {
                write_u32(output, *target);
            }
        },
        SemanticFieldV1::Collection { kind, entries } => {
            output.push(2);
            output.push(encode_collection_kind(*kind));
            write_u32(output, checked_u32(entries.len())?);
            for entry in entries {
                match entry {
                    SemanticCollectionEntryV1::Value(target) => {
                        output.push(0);
                        write_u32(output, *target);
                    },
                    SemanticCollectionEntryV1::KeyValue { key, value } => {
                        output.push(1);
                        write_u32(output, *key);
                        write_u32(output, *value);
                    },
                }
            }
        },
        SemanticFieldV1::Optional(target) => {
            output.push(3);
            match target {
                None => output.push(0),
                Some(target) => {
                    output.push(1);
                    write_u32(output, *target);
                },
            }
        },
        SemanticFieldV1::Scope { domain, arity, body } => {
            output.push(4);
            write_u32(output, domain.0);
            write_u32(output, *arity);
            write_u32(output, *body);
        },
        SemanticFieldV1::Variable(SemanticVariableV1::Bound { scope_depth, slot }) => {
            output.push(5);
            output.push(0);
            write_u32(output, *scope_depth);
            write_u32(output, *slot);
        },
        SemanticFieldV1::Variable(SemanticVariableV1::Free { identity }) => {
            output.push(5);
            output.push(1);
            write_u32(output, checked_u32(identity.len())?);
            output.extend_from_slice(identity);
        },
        SemanticFieldV1::Atom(atom) => {
            output.push(6);
            encode_atom(atom, output)?;
        },
        SemanticFieldV1::TokenText(text) => {
            output.push(7);
            write_u32(output, checked_u32(text.len())?);
            output.extend_from_slice(text.as_bytes());
        },
        SemanticFieldV1::Opaque(atom) => {
            output.push(8);
            encode_atom(atom, output)?;
        },
        SemanticFieldV1::Unit => output.push(9),
        SemanticFieldV1::OptionalSequence(targets) => {
            output.push(10);
            match targets {
                None => output.push(0),
                Some(targets) => {
                    output.push(1);
                    write_u32(output, checked_u32(targets.len())?);
                    for target in targets {
                        write_u32(output, *target);
                    }
                },
            }
        },
        SemanticFieldV1::OptionalTokenText(text) => {
            output.push(11);
            match text {
                None => output.push(0),
                Some(text) => {
                    output.push(1);
                    write_u32(output, checked_u32(text.len())?);
                    output.extend_from_slice(text.as_bytes());
                },
            }
        },
        SemanticFieldV1::PathMap { mode, entries } => {
            output.push(12);
            output.push(encode_pathmap_mode(*mode));
            write_u32(output, checked_u32(entries.len())?);
            match mode {
                PathMapModeV1::NeutralEmpty if entries.is_empty() => {},
                PathMapModeV1::NeutralEmpty => {
                    return Err(SemanticTermImageError::PathMapEncoding);
                },
                PathMapModeV1::Set => {
                    for entry in entries {
                        let SemanticPathMapEntryV1::Key(target) = entry else {
                            return Err(SemanticTermImageError::PathMapEncoding);
                        };
                        write_u32(output, *target);
                    }
                },
                PathMapModeV1::Map => {
                    for entry in entries {
                        let SemanticPathMapEntryV1::KeyValue { key, value } = entry else {
                            return Err(SemanticTermImageError::PathMapEncoding);
                        };
                        write_u32(output, *key);
                        write_u32(output, *value);
                    }
                },
            }
        },
        SemanticFieldV1::Bytes(bytes) => {
            output.push(13);
            write_u32(output, checked_u32(bytes.len())?);
            output.extend_from_slice(bytes);
        },
    }
    Ok(())
}

fn encode_pathmap_mode(mode: PathMapModeV1) -> u8 {
    match mode {
        PathMapModeV1::NeutralEmpty => 0,
        PathMapModeV1::Set => 1,
        PathMapModeV1::Map => 2,
    }
}

fn decode_pathmap_mode(tag: u8) -> Result<PathMapModeV1, SemanticTermImageError> {
    match tag {
        0 => Ok(PathMapModeV1::NeutralEmpty),
        1 => Ok(PathMapModeV1::Set),
        2 => Ok(PathMapModeV1::Map),
        tag => Err(SemanticTermImageError::InvalidTag(tag)),
    }
}

pub(crate) fn encode_collection_kind(kind: CollectionKind) -> u8 {
    match kind {
        CollectionKind::Bag => 0,
        CollectionKind::Set => 1,
        CollectionKind::List => 2,
        CollectionKind::Map => 3,
        CollectionKind::PathMap => 4,
    }
}

pub(crate) fn decode_collection_kind(tag: u8) -> Result<CollectionKind, SemanticTermImageError> {
    match tag {
        0 => Ok(CollectionKind::Bag),
        1 => Ok(CollectionKind::Set),
        2 => Ok(CollectionKind::List),
        3 => Ok(CollectionKind::Map),
        4 => Ok(CollectionKind::PathMap),
        tag => Err(SemanticTermImageError::InvalidTag(tag)),
    }
}

pub(crate) fn empty_vec<T>(capacity: usize) -> Result<Vec<T>, SemanticTermImageError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| SemanticTermImageError::Allocation)?;
    Ok(values)
}

pub(crate) fn copy_bytes(bytes: &[u8]) -> Result<Vec<u8>, SemanticTermImageError> {
    let mut output = empty_vec(bytes.len())?;
    output.extend_from_slice(bytes);
    Ok(output)
}

pub(crate) struct ImageReader<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> ImageReader<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, cursor: 0 }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.cursor == self.bytes.len()
    }

    pub(crate) fn read_exact(&mut self, length: usize) -> Result<&'a [u8], SemanticTermImageError> {
        let end = self
            .cursor
            .checked_add(length)
            .ok_or(SemanticTermImageError::LengthOverflow)?;
        let bytes = self
            .bytes
            .get(self.cursor..end)
            .ok_or(SemanticTermImageError::Truncated)?;
        self.cursor = end;
        Ok(bytes)
    }

    pub(crate) fn read_array<const N: usize>(&mut self) -> Result<[u8; N], SemanticTermImageError> {
        self.read_exact(N)?
            .try_into()
            .map_err(|_| SemanticTermImageError::Truncated)
    }

    pub(crate) fn read_u8(&mut self) -> Result<u8, SemanticTermImageError> {
        Ok(self.read_exact(1)?[0])
    }

    pub(crate) fn read_u16(&mut self) -> Result<u16, SemanticTermImageError> {
        Ok(u16::from_le_bytes(self.read_array()?))
    }

    pub(crate) fn read_u32(&mut self) -> Result<u32, SemanticTermImageError> {
        Ok(u32::from_le_bytes(self.read_array()?))
    }

    pub(crate) fn read_count(
        &mut self,
        limit: usize,
        name: &'static str,
    ) -> Result<usize, SemanticTermImageError> {
        let value = usize::try_from(self.read_u32()?)
            .map_err(|_| SemanticTermImageError::LengthOverflow)?;
        enforce_limit(value, limit, name)?;
        Ok(value)
    }
}

fn decode_atom(
    input: &mut ImageReader<'_>,
    node: u32,
    field: Option<u32>,
    counts: &mut AdmissionCounts,
    limits: SemanticTermAdmissionLimits,
) -> Result<SemanticAtomV1, SemanticTermImageError> {
    let schema = input.read_u32()?;
    let length = input.read_count(limits.max_atom_bytes, "atom bytes")?;
    charge_bytes(length, counts, limits)?;
    let bytes = copy_bytes(input.read_exact(length)?)?;
    let _ = (node, field);
    Ok(SemanticAtomV1 { schema, bytes })
}

fn decode_reference(
    input: &mut ImageReader<'_>,
    node: u32,
    field: u32,
    counts: &mut AdmissionCounts,
    limits: SemanticTermAdmissionLimits,
) -> Result<u32, SemanticTermImageError> {
    let target = input.read_u32()?;
    if target >= node {
        return Err(SemanticTermImageError::Reference { node, field, target });
    }
    counts.references = counts
        .references
        .checked_add(1)
        .ok_or(SemanticTermImageError::LengthOverflow)?;
    enforce_limit(counts.references, limits.max_references, "references")?;
    Ok(target)
}

fn decode_field(
    input: &mut ImageReader<'_>,
    node: u32,
    field: u32,
    counts: &mut AdmissionCounts,
    limits: SemanticTermAdmissionLimits,
) -> Result<SemanticFieldV1, SemanticTermImageError> {
    match input.read_u8()? {
        0 => Ok(SemanticFieldV1::Child(decode_reference(input, node, field, counts, limits)?)),
        1 => {
            let count = input.read_count(limits.max_sequence_length, "sequence length")?;
            let mut targets = empty_vec(count)?;
            for _ in 0..count {
                targets.push(decode_reference(input, node, field, counts, limits)?);
            }
            Ok(SemanticFieldV1::Sequence(targets))
        },
        2 => {
            let kind = decode_collection_kind(input.read_u8()?)?;
            let count = input.read_count(limits.max_collection_entries, "collection entries")?;
            let mut entries = empty_vec(count)?;
            for _ in 0..count {
                entries.push(match input.read_u8()? {
                    0 => SemanticCollectionEntryV1::Value(decode_reference(
                        input, node, field, counts, limits,
                    )?),
                    1 => SemanticCollectionEntryV1::KeyValue {
                        key: decode_reference(input, node, field, counts, limits)?,
                        value: decode_reference(input, node, field, counts, limits)?,
                    },
                    tag => return Err(SemanticTermImageError::InvalidTag(tag)),
                });
            }
            Ok(SemanticFieldV1::Collection { kind, entries })
        },
        3 => match input.read_u8()? {
            0 => Ok(SemanticFieldV1::Optional(None)),
            1 => Ok(SemanticFieldV1::Optional(Some(decode_reference(
                input, node, field, counts, limits,
            )?))),
            tag => Err(SemanticTermImageError::InvalidTag(tag)),
        },
        4 => {
            let domain = CategoryId(input.read_u32()?);
            let arity = input.read_u32()?;
            if arity > limits.max_scope_arity {
                return Err(SemanticTermImageError::ScopeArity { node, field });
            }
            let body = decode_reference(input, node, field, counts, limits)?;
            Ok(SemanticFieldV1::Scope { domain, arity, body })
        },
        5 => match input.read_u8()? {
            0 => {
                let scope_depth = input.read_u32()?;
                enforce_limit(scope_depth as usize, limits.max_scope_depth, "scope depth")?;
                Ok(SemanticFieldV1::Variable(SemanticVariableV1::Bound {
                    scope_depth,
                    slot: input.read_u32()?,
                }))
            },
            1 => {
                let length = input.read_count(limits.max_atom_bytes, "atom bytes")?;
                charge_bytes(length, counts, limits)?;
                let identity = copy_bytes(input.read_exact(length)?)?;
                if identity.is_empty() {
                    return Err(SemanticTermImageError::EmptyFreeVariable { node, field });
                }
                Ok(SemanticFieldV1::Variable(SemanticVariableV1::Free { identity }))
            },
            tag => Err(SemanticTermImageError::InvalidTag(tag)),
        },
        6 => Ok(SemanticFieldV1::Atom(decode_atom(input, node, Some(field), counts, limits)?)),
        7 => {
            let length = input.read_count(limits.max_atom_bytes, "atom bytes")?;
            charge_bytes(length, counts, limits)?;
            let bytes = copy_bytes(input.read_exact(length)?)?;
            let text = String::from_utf8(bytes).map_err(|_| SemanticTermImageError::InvalidUtf8)?;
            Ok(SemanticFieldV1::TokenText(text))
        },
        8 => Ok(SemanticFieldV1::Opaque(decode_atom(input, node, Some(field), counts, limits)?)),
        9 => Ok(SemanticFieldV1::Unit),
        10 => match input.read_u8()? {
            0 => Ok(SemanticFieldV1::OptionalSequence(None)),
            1 => {
                let count = input.read_count(limits.max_sequence_length, "sequence length")?;
                let mut targets = empty_vec(count)?;
                for _ in 0..count {
                    targets.push(decode_reference(input, node, field, counts, limits)?);
                }
                Ok(SemanticFieldV1::OptionalSequence(Some(targets)))
            },
            tag => Err(SemanticTermImageError::InvalidTag(tag)),
        },
        11 => match input.read_u8()? {
            0 => Ok(SemanticFieldV1::OptionalTokenText(None)),
            1 => {
                let length = input.read_count(limits.max_atom_bytes, "atom bytes")?;
                charge_bytes(length, counts, limits)?;
                let bytes = copy_bytes(input.read_exact(length)?)?;
                let text =
                    String::from_utf8(bytes).map_err(|_| SemanticTermImageError::InvalidUtf8)?;
                Ok(SemanticFieldV1::OptionalTokenText(Some(text)))
            },
            tag => Err(SemanticTermImageError::InvalidTag(tag)),
        },
        12 => {
            let mode = decode_pathmap_mode(input.read_u8()?)?;
            let count = input.read_count(limits.max_collection_entries, "collection entries")?;
            let mut entries = empty_vec(count)?;
            match mode {
                PathMapModeV1::NeutralEmpty => {
                    if count != 0 {
                        return Err(SemanticTermImageError::PathMapMode { node, field });
                    }
                },
                PathMapModeV1::Set => {
                    for _ in 0..count {
                        entries.push(SemanticPathMapEntryV1::Key(decode_reference(
                            input, node, field, counts, limits,
                        )?));
                    }
                },
                PathMapModeV1::Map => {
                    for _ in 0..count {
                        entries.push(SemanticPathMapEntryV1::KeyValue {
                            key: decode_reference(input, node, field, counts, limits)?,
                            value: decode_reference(input, node, field, counts, limits)?,
                        });
                    }
                },
            }
            Ok(SemanticFieldV1::PathMap { mode, entries })
        },
        13 => {
            let length = input.read_count(limits.max_atom_bytes, "byte-string bytes")?;
            charge_bytes(length, counts, limits)?;
            Ok(SemanticFieldV1::Bytes(copy_bytes(input.read_exact(length)?)?))
        },
        tag => Err(SemanticTermImageError::InvalidTag(tag)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Carrier, Category, FieldSource, Precedence, Production, ProductionClass, ReductionPlan,
        SyntaxItem,
    };

    fn add_production(
        grammar: &mut GrammarCoreV1,
        constructor: u32,
        label: &str,
        syntax: Vec<SyntaxItem>,
        input_arity: u16,
        fields: Vec<FieldSource>,
    ) {
        let production = u32::try_from(grammar.productions.len()).expect("test production ID");
        let reduction = u32::try_from(grammar.reductions.len()).expect("test reduction ID");
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

    fn fixture() -> (GrammarCoreV1, SemanticSignatureV1) {
        let mut grammar = GrammarCoreV1::new("SemanticImageFixture");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: true,
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
        add_production(&mut grammar, 2, "Variable", Vec::new(), 0, vec![FieldSource::Unit]);
        add_production(&mut grammar, 3, "Lambda", Vec::new(), 0, vec![FieldSource::Unit]);
        add_production(&mut grammar, 4, "AllFields", Vec::new(), 0, vec![FieldSource::Unit; 13]);
        grammar.validate().expect("valid fixture grammar");
        let grammar_fingerprint = grammar.fingerprint().expect("fixture fingerprint");
        let signature = SemanticSignatureV1 {
            abi: SEMANTIC_SIGNATURE_ABI_V1,
            grammar_fingerprint,
            category_count: 1,
            constructor_count: 5,
            atom_schemas: vec![SemanticAtomSchemaV1::Builtin(
                SemanticBuiltinAtomV1::SignedInteger { bits: Some(128) },
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
                    label: "Term::Variable".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(2)),
                    payload: None,
                    fields: vec![SemanticFieldSchemaV1::Variable { category: CategoryId(0) }],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(3),
                    category: CategoryId(0),
                    constructor: ConstructorId(3),
                    stable_discriminant: 17,
                    label: "Term::Lambda".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(3)),
                    payload: None,
                    fields: vec![SemanticFieldSchemaV1::Scope {
                        domain: CategoryId(0),
                        body: CategoryId(0),
                        minimum_arity: 1,
                        maximum_arity: Some(8),
                    }],
                },
                SemanticOperatorDeclV1 {
                    id: SemanticOperatorId(4),
                    category: CategoryId(0),
                    constructor: ConstructorId(4),
                    stable_discriminant: 19,
                    label: "Term::AllFields".into(),
                    origin: SemanticOperatorOriginV1::GrammarProduction(ProductionId(4)),
                    payload: None,
                    fields: vec![
                        SemanticFieldSchemaV1::Child { category: CategoryId(0) },
                        SemanticFieldSchemaV1::Sequence { element: CategoryId(0) },
                        SemanticFieldSchemaV1::Collection {
                            kind: CollectionKind::List,
                            key: None,
                            value: CategoryId(0),
                        },
                        SemanticFieldSchemaV1::Collection {
                            kind: CollectionKind::Map,
                            key: Some(CategoryId(0)),
                            value: CategoryId(0),
                        },
                        SemanticFieldSchemaV1::Optional { category: CategoryId(0) },
                        SemanticFieldSchemaV1::OptionalSequence { element: CategoryId(0) },
                        SemanticFieldSchemaV1::OptionalTokenText,
                        SemanticFieldSchemaV1::Scope {
                            domain: CategoryId(0),
                            body: CategoryId(0),
                            minimum_arity: 1,
                            maximum_arity: Some(8),
                        },
                        SemanticFieldSchemaV1::Variable { category: CategoryId(0) },
                        SemanticFieldSchemaV1::Atom { schema: 0 },
                        SemanticFieldSchemaV1::TokenText,
                        SemanticFieldSchemaV1::Bytes,
                        SemanticFieldSchemaV1::Unit,
                    ],
                },
            ],
        };
        signature
            .validate(&grammar, &RuntimeCapabilityBindings::default())
            .expect("valid fixture signature");
        (grammar, signature)
    }

    fn integer_atom(value: i128) -> SemanticAtomV1 {
        SemanticAtomV1 {
            schema: 0,
            bytes: value.to_le_bytes().to_vec(),
        }
    }

    fn leaf(value: i128) -> SemanticNodeV1 {
        SemanticNodeV1 {
            operator: SemanticOperatorId(0),
            payload: Some(integer_atom(value)),
            fields: vec![SemanticFieldV1::Unit],
        }
    }

    fn image(
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

    fn all_fields_node(
        optional_sequence: Option<Vec<u32>>,
        optional_token: Option<&str>,
    ) -> SemanticNodeV1 {
        SemanticNodeV1 {
            operator: SemanticOperatorId(4),
            payload: None,
            fields: vec![
                SemanticFieldV1::Child(0),
                SemanticFieldV1::Sequence(vec![0]),
                SemanticFieldV1::Collection {
                    kind: CollectionKind::List,
                    entries: vec![SemanticCollectionEntryV1::Value(0)],
                },
                SemanticFieldV1::Collection {
                    kind: CollectionKind::Map,
                    entries: vec![SemanticCollectionEntryV1::KeyValue { key: 0, value: 0 }],
                },
                SemanticFieldV1::Optional(Some(0)),
                SemanticFieldV1::OptionalSequence(optional_sequence),
                SemanticFieldV1::OptionalTokenText(optional_token.map(str::to_string)),
                SemanticFieldV1::Scope { domain: CategoryId(0), arity: 1, body: 1 },
                SemanticFieldV1::Variable(SemanticVariableV1::Free {
                    identity: b"free-variable".to_vec(),
                }),
                SemanticFieldV1::Atom(integer_atom(-9)),
                SemanticFieldV1::TokenText("literal token text".into()),
                SemanticFieldV1::Bytes(vec![0x00, 0x7f, 0x80, 0xff]),
                SemanticFieldV1::Unit,
            ],
        }
    }

    #[test]
    fn all_builtin_field_shapes_round_trip_without_source_text() {
        let (grammar, signature) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let nodes = vec![
            leaf(7),
            SemanticNodeV1 {
                operator: SemanticOperatorId(2),
                payload: None,
                fields: vec![SemanticFieldV1::Variable(SemanticVariableV1::Bound {
                    scope_depth: 0,
                    slot: 0,
                })],
            },
            all_fields_node(Some(vec![0]), Some("optional token text")),
        ];
        let image = image(&signature, nodes, vec![2])
            .canonicalize(&signature, &grammar, &bindings, SemanticTermAdmissionLimits::default())
            .expect("canonical all-fields image");
        let encoded = image
            .encode(&signature, &grammar, &bindings, SemanticTermAdmissionLimits::default())
            .expect("encode admitted image");
        let decoded = SemanticTermImageV1::decode(
            &encoded,
            &signature,
            &grammar,
            &bindings,
            SemanticTermAdmissionLimits::default(),
        )
        .expect("decode admitted image");
        assert_eq!(decoded, image);
    }

    #[test]
    fn exact_bytes_are_distinct_from_token_text() {
        let (grammar, signature) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let mut node = all_fields_node(Some(Vec::new()), None);
        node.fields[11] = SemanticFieldV1::TokenText("text is not bytes".into());
        let bound = SemanticNodeV1 {
            operator: SemanticOperatorId(2),
            payload: None,
            fields: vec![SemanticFieldV1::Variable(SemanticVariableV1::Bound {
                scope_depth: 0,
                slot: 0,
            })],
        };
        let image = image(&signature, vec![leaf(7), bound, node], vec![2]);

        assert!(matches!(
            image.verify(&signature, &grammar, &bindings, limits),
            Err(SemanticTermImageError::FieldKind { node: 2, field: 11 })
        ));
    }

    #[test]
    fn optional_sequence_and_token_absence_round_trip_canonically() {
        let (grammar, signature) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let image = image(
            &signature,
            vec![
                leaf(7),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(2),
                    payload: None,
                    fields: vec![SemanticFieldV1::Variable(SemanticVariableV1::Bound {
                        scope_depth: 0,
                        slot: 0,
                    })],
                },
                all_fields_node(None, None),
            ],
            vec![2],
        )
        .canonicalize(&signature, &grammar, &bindings, limits)
        .expect("canonical absent optional fields");
        let bytes = image
            .encode(&signature, &grammar, &bindings, limits)
            .expect("encode absent optional fields");
        assert_eq!(
            SemanticTermImageV1::decode(&bytes, &signature, &grammar, &bindings, limits)
                .expect("decode absent optional fields"),
            image,
        );
    }

    #[test]
    fn twenty_thousand_deep_arena_is_stack_safe() {
        let (grammar, signature) = fixture();
        let mut nodes = Vec::with_capacity(20_001);
        nodes.push(leaf(0));
        for target in 0..20_000u32 {
            nodes.push(SemanticNodeV1 {
                operator: SemanticOperatorId(1),
                payload: None,
                fields: vec![SemanticFieldV1::Child(target)],
            });
        }
        let image = image(&signature, nodes, vec![20_000]);
        let encoded = image
            .encode(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            )
            .expect("deep iterative encode");
        let decoded = SemanticTermImageV1::decode(
            &encoded,
            &signature,
            &grammar,
            &RuntimeCapabilityBindings::default(),
            SemanticTermAdmissionLimits::default(),
        )
        .expect("deep iterative decode");
        assert_eq!(decoded.nodes.len(), 20_001);
        assert_eq!(decoded.roots, vec![20_000]);
    }

    #[test]
    fn forward_references_fail_closed() {
        let (grammar, signature) = fixture();
        let invalid = image(
            &signature,
            vec![SemanticNodeV1 {
                operator: SemanticOperatorId(1),
                payload: None,
                fields: vec![SemanticFieldV1::Child(0)],
            }],
            vec![0],
        );
        assert!(matches!(
            invalid.verify(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            ),
            Err(SemanticTermImageError::Reference { node: 0, target: 0, .. })
        ));
    }

    #[test]
    fn bound_variables_require_the_exact_enclosing_domain_and_slot() {
        let (grammar, signature) = fixture();
        let valid = image(
            &signature,
            vec![
                SemanticNodeV1 {
                    operator: SemanticOperatorId(2),
                    payload: None,
                    fields: vec![SemanticFieldV1::Variable(SemanticVariableV1::Bound {
                        scope_depth: 0,
                        slot: 1,
                    })],
                },
                SemanticNodeV1 {
                    operator: SemanticOperatorId(3),
                    payload: None,
                    fields: vec![SemanticFieldV1::Scope {
                        domain: CategoryId(0),
                        arity: 2,
                        body: 0,
                    }],
                },
            ],
            vec![1],
        );
        valid
            .verify(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            )
            .expect("bound variable is in scope");

        let mut invalid = valid;
        invalid.nodes[0].fields[0] =
            SemanticFieldV1::Variable(SemanticVariableV1::Bound { scope_depth: 0, slot: 2 });
        assert!(matches!(
            invalid.verify(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            ),
            Err(SemanticTermImageError::UnboundVariable { .. })
        ));
    }

    #[test]
    fn decoder_rejects_claimed_counts_before_allocating() {
        let (grammar, signature) = fixture();
        let mut bytes = Vec::new();
        bytes.extend_from_slice(SEMANTIC_TERM_IMAGE_MAGIC);
        write_u16(&mut bytes, SEMANTIC_TERM_IMAGE_ABI_V1);
        bytes.extend_from_slice(&signature.fingerprint().expect("signature fingerprint"));
        write_u32(&mut bytes, 5);
        write_u32(&mut bytes, 0);
        let limits = SemanticTermAdmissionLimits {
            max_nodes: 4,
            ..SemanticTermAdmissionLimits::default()
        };
        assert_eq!(
            SemanticTermImageV1::decode(
                &bytes,
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                limits,
            ),
            Err(SemanticTermImageError::LimitExceeded("nodes"))
        );
    }

    #[test]
    fn decoder_rejects_trailing_bytes() {
        let (grammar, signature) = fixture();
        let image = image(&signature, vec![leaf(1)], vec![0]);
        let mut bytes = image
            .encode(
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            )
            .expect("encode");
        bytes.push(0);
        assert_eq!(
            SemanticTermImageV1::decode(
                &bytes,
                &signature,
                &grammar,
                &RuntimeCapabilityBindings::default(),
                SemanticTermAdmissionLimits::default(),
            ),
            Err(SemanticTermImageError::TrailingBytes)
        );
    }

    #[test]
    fn free_variable_identity_is_charged_to_the_atom_budget() {
        let (grammar, signature) = fixture();
        let image = image(
            &signature,
            vec![SemanticNodeV1 {
                operator: SemanticOperatorId(2),
                payload: None,
                fields: vec![SemanticFieldV1::Variable(SemanticVariableV1::Free {
                    identity: vec![1; 5],
                })],
            }],
            vec![0],
        );
        let limits = SemanticTermAdmissionLimits {
            max_atom_bytes: 4,
            ..SemanticTermAdmissionLimits::default()
        };
        assert_eq!(
            image.verify(&signature, &grammar, &RuntimeCapabilityBindings::default(), limits,),
            Err(SemanticTermImageError::LimitExceeded("atom bytes"))
        );
    }

    #[test]
    fn opaque_atoms_require_an_exact_installed_structural_codec() {
        let (grammar, mut signature) = fixture();
        let key = RuntimeCapabilityKey::structural_codec(
            signature.grammar_fingerprint,
            "example/rational/1",
        );
        signature
            .atom_schemas
            .push(SemanticAtomSchemaV1::External { codec: key.clone() });
        signature.operators[0].fields = vec![SemanticFieldSchemaV1::Opaque { schema: 1 }];
        assert_eq!(
            signature.validate(&grammar, &RuntimeCapabilityBindings::default()),
            Err(SemanticSignatureError::MissingCodec(key.clone()))
        );

        let requirement = RuntimeCapabilityRequirement {
            key: key.clone(),
            effect: RuntimeEffect::Reflect,
        };
        let manifest = crate::RuntimeCapabilityManifest {
            key: key.clone(),
            code_commitment: [23; 32],
            abi: "semantic-structural-codec/1".into(),
            effects: [RuntimeEffect::Reflect].into_iter().collect(),
            cost: crate::RuntimeLogicalCost {
                base: 1,
                per_input_byte: 1,
                per_value: 1,
                maximum: 1024,
            },
        };
        let bindings = RuntimeCapabilityBindings::bind(&[requirement], |_| Some(manifest.clone()))
            .expect("stable exact codec binding");
        signature
            .validate(&grammar, &bindings)
            .expect("installed structural codec admits signature");
        let image = image(
            &signature,
            vec![SemanticNodeV1 {
                operator: SemanticOperatorId(0),
                payload: Some(integer_atom(5)),
                fields: vec![SemanticFieldV1::Opaque(SemanticAtomV1 {
                    schema: 1,
                    bytes: b"canonical-external-value".to_vec(),
                })],
            }],
            vec![0],
        );
        image
            .verify(&signature, &grammar, &bindings, SemanticTermAdmissionLimits::default())
            .expect("opaque value admitted through exact codec");
    }

    fn collection_fixture(kind: CollectionKind) -> (GrammarCoreV1, SemanticSignatureV1) {
        let (grammar, mut signature) = fixture();
        signature.operators[4].fields = vec![SemanticFieldSchemaV1::Collection {
            kind,
            key: matches!(kind, CollectionKind::Map | CollectionKind::PathMap)
                .then_some(CategoryId(0)),
            value: CategoryId(0),
        }];
        signature
            .validate(&grammar, &RuntimeCapabilityBindings::default())
            .expect("valid collection fixture signature");
        (grammar, signature)
    }

    fn collection_node(
        kind: CollectionKind,
        entries: Vec<SemanticCollectionEntryV1>,
    ) -> SemanticNodeV1 {
        SemanticNodeV1 {
            operator: SemanticOperatorId(4),
            payload: None,
            fields: vec![SemanticFieldV1::Collection { kind, entries }],
        }
    }

    fn pathmap_fixture() -> (GrammarCoreV1, SemanticSignatureV1) {
        let (grammar, mut signature) = fixture();
        signature.operators[4].fields =
            vec![SemanticFieldSchemaV1::PathMap { key: CategoryId(0), value: CategoryId(0) }];
        signature
            .validate(&grammar, &RuntimeCapabilityBindings::default())
            .expect("valid path-map fixture signature");
        (grammar, signature)
    }

    fn pathmap_node(mode: PathMapModeV1, entries: Vec<SemanticPathMapEntryV1>) -> SemanticNodeV1 {
        SemanticNodeV1 {
            operator: SemanticOperatorId(4),
            payload: None,
            fields: vec![SemanticFieldV1::PathMap { mode, entries }],
        }
    }

    #[test]
    fn canonical_arena_ignores_allocation_order_and_optional_sharing() {
        let (grammar, signature) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let left = image(
            &signature,
            vec![
                leaf(1),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(1),
                    payload: None,
                    fields: vec![SemanticFieldV1::Child(0)],
                },
                leaf(2),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(1),
                    payload: None,
                    fields: vec![SemanticFieldV1::Child(2)],
                },
            ],
            vec![1, 3],
        );
        let right = image(
            &signature,
            vec![
                leaf(2),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(1),
                    payload: None,
                    fields: vec![SemanticFieldV1::Child(0)],
                },
                leaf(1),
                SemanticNodeV1 {
                    operator: SemanticOperatorId(1),
                    payload: None,
                    fields: vec![SemanticFieldV1::Child(2)],
                },
            ],
            vec![3, 1],
        );
        let canonical_left = left
            .canonicalize(&signature, &grammar, &bindings, limits)
            .expect("canonical left layout");
        let canonical_right = right
            .canonicalize(&signature, &grammar, &bindings, limits)
            .expect("canonical right layout");
        assert_eq!(canonical_left, canonical_right);

        let shared = image(&signature, vec![leaf(7)], vec![0, 0]);
        let duplicated = image(&signature, vec![leaf(7), leaf(7)], vec![0, 1]);
        assert_eq!(
            shared
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical shared roots"),
            duplicated
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical duplicated roots")
        );
    }

    #[test]
    fn canonical_arena_is_invariant_over_all_small_allocation_and_bag_permutations() {
        const PERMUTATIONS: [[usize; 3]; 6] =
            [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
        let (grammar, signature) = collection_fixture(CollectionKind::Bag);
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let values = [3i128, -5, 11];
        let mut expected = None;

        for allocation in PERMUTATIONS {
            let mut leaf_ids = [0u32; 3];
            let mut leaves = Vec::with_capacity(values.len() + 1);
            for (node_id, value_index) in allocation.into_iter().enumerate() {
                leaf_ids[value_index] = u32::try_from(node_id).expect("small node ID");
                leaves.push(leaf(values[value_index]));
            }
            for entry_order in PERMUTATIONS {
                let mut nodes = leaves.clone();
                nodes.push(collection_node(
                    CollectionKind::Bag,
                    entry_order
                        .into_iter()
                        .map(|value_index| SemanticCollectionEntryV1::Value(leaf_ids[value_index]))
                        .collect(),
                ));
                let canonical = image(&signature, nodes, vec![3])
                    .canonicalize(&signature, &grammar, &bindings, limits)
                    .expect("canonical permutation");
                if let Some(expected) = &expected {
                    assert_eq!(&canonical, expected);
                } else {
                    expected = Some(canonical);
                }
            }
        }
    }

    #[test]
    fn canonical_fingerprint_is_representation_independent_and_encode_is_strict() {
        let (grammar, signature) = fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let raw = image(&signature, vec![leaf(9), leaf(9)], vec![0, 1]);
        let canonical = raw
            .canonicalize(&signature, &grammar, &bindings, limits)
            .expect("canonical duplicate nodes");
        assert_eq!(canonical.nodes.len(), 1);
        assert_eq!(canonical.roots, vec![0, 0]);
        assert_eq!(
            raw.verify(&signature, &grammar, &bindings, limits),
            Err(SemanticTermImageError::NonCanonicalArena)
        );
        assert_eq!(
            raw.encode(&signature, &grammar, &bindings, limits),
            Err(SemanticTermImageError::NonCanonicalArena)
        );
        assert_eq!(
            raw.canonical_fingerprint(&signature, &grammar, &bindings, limits),
            canonical.canonical_fingerprint(&signature, &grammar, &bindings, limits)
        );
        canonical
            .verify(&signature, &grammar, &bindings, limits)
            .expect("canonical result is admitted");
    }

    #[test]
    fn bag_set_and_list_obey_their_distinct_canonical_laws() {
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        for kind in [CollectionKind::Bag, CollectionKind::Set] {
            let (grammar, signature) = collection_fixture(kind);
            let left = image(
                &signature,
                vec![
                    leaf(1),
                    leaf(2),
                    collection_node(
                        kind,
                        vec![
                            SemanticCollectionEntryV1::Value(1),
                            SemanticCollectionEntryV1::Value(0),
                            SemanticCollectionEntryV1::Value(0),
                        ],
                    ),
                ],
                vec![2],
            );
            let right = image(
                &signature,
                vec![
                    leaf(2),
                    leaf(1),
                    collection_node(
                        kind,
                        vec![
                            SemanticCollectionEntryV1::Value(0),
                            SemanticCollectionEntryV1::Value(1),
                            SemanticCollectionEntryV1::Value(1),
                        ],
                    ),
                ],
                vec![2],
            );
            let left = left
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical unordered collection");
            let right = right
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical permuted collection");
            assert_eq!(left, right);
            let SemanticFieldV1::Collection { entries, .. } =
                &left.nodes[left.roots[0] as usize].fields[0]
            else {
                panic!("collection root field");
            };
            assert_eq!(entries.len(), if kind == CollectionKind::Bag { 3 } else { 2 });
        }

        let (grammar, signature) = collection_fixture(CollectionKind::List);
        let ascending = image(
            &signature,
            vec![
                leaf(1),
                leaf(2),
                collection_node(
                    CollectionKind::List,
                    vec![SemanticCollectionEntryV1::Value(0), SemanticCollectionEntryV1::Value(1)],
                ),
            ],
            vec![2],
        );
        let descending = image(
            &signature,
            vec![
                leaf(1),
                leaf(2),
                collection_node(
                    CollectionKind::List,
                    vec![SemanticCollectionEntryV1::Value(1), SemanticCollectionEntryV1::Value(0)],
                ),
            ],
            vec![2],
        );
        assert_ne!(
            ascending
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical ascending list"),
            descending
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical descending list")
        );
    }

    #[test]
    fn map_and_pathmap_sort_exact_keys_and_reject_duplicates() {
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        for kind in [CollectionKind::Map, CollectionKind::PathMap] {
            let (grammar, signature) = collection_fixture(kind);
            let left = image(
                &signature,
                vec![
                    leaf(1),
                    leaf(10),
                    leaf(2),
                    leaf(20),
                    collection_node(
                        kind,
                        vec![
                            SemanticCollectionEntryV1::KeyValue { key: 2, value: 3 },
                            SemanticCollectionEntryV1::KeyValue { key: 0, value: 1 },
                        ],
                    ),
                ],
                vec![4],
            );
            let right = image(
                &signature,
                vec![
                    leaf(20),
                    leaf(2),
                    leaf(10),
                    leaf(1),
                    collection_node(
                        kind,
                        vec![
                            SemanticCollectionEntryV1::KeyValue { key: 3, value: 2 },
                            SemanticCollectionEntryV1::KeyValue { key: 1, value: 0 },
                        ],
                    ),
                ],
                vec![4],
            );
            assert_eq!(
                left.canonicalize(&signature, &grammar, &bindings, limits)
                    .expect("canonical map"),
                right
                    .canonicalize(&signature, &grammar, &bindings, limits)
                    .expect("canonical permuted map")
            );

            let duplicate = image(
                &signature,
                vec![
                    leaf(1),
                    leaf(11),
                    leaf(1),
                    leaf(12),
                    collection_node(
                        kind,
                        vec![
                            SemanticCollectionEntryV1::KeyValue { key: 0, value: 1 },
                            SemanticCollectionEntryV1::KeyValue { key: 2, value: 3 },
                        ],
                    ),
                ],
                vec![4],
            );
            assert!(matches!(
                duplicate.canonicalize(&signature, &grammar, &bindings, limits),
                Err(SemanticTermImageError::DuplicateCollectionKey { .. })
            ));
        }
    }

    #[test]
    fn pathmap_empty_modes_remain_distinct_and_round_trip_exactly() {
        let (grammar, signature) = pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let mut encodings = Vec::new();

        for mode in [PathMapModeV1::NeutralEmpty, PathMapModeV1::Set, PathMapModeV1::Map] {
            let canonical = image(&signature, vec![pathmap_node(mode, Vec::new())], vec![0])
                .canonicalize(&signature, &grammar, &bindings, limits)
                .expect("canonical empty path-map mode");
            let bytes = canonical
                .encode(&signature, &grammar, &bindings, limits)
                .expect("encode empty path-map mode");
            let decoded =
                SemanticTermImageV1::decode(&bytes, &signature, &grammar, &bindings, limits)
                    .expect("decode empty path-map mode");
            assert_eq!(decoded, canonical);
            assert!(matches!(
                &decoded.nodes[0].fields[0],
                SemanticFieldV1::PathMap { mode: decoded_mode, entries }
                    if *decoded_mode == mode && entries.is_empty()
            ));
            encodings.push(bytes);
        }

        assert_ne!(encodings[0], encodings[1]);
        assert_ne!(encodings[0], encodings[2]);
        assert_ne!(encodings[1], encodings[2]);
    }

    #[test]
    fn pathmap_set_and_map_canonicalize_by_exact_key_and_reject_duplicates() {
        let (grammar, signature) = pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();

        let set = image(
            &signature,
            vec![
                leaf(2),
                leaf(1),
                pathmap_node(
                    PathMapModeV1::Set,
                    vec![SemanticPathMapEntryV1::Key(0), SemanticPathMapEntryV1::Key(1)],
                ),
            ],
            vec![2],
        )
        .canonicalize(&signature, &grammar, &bindings, limits)
        .expect("canonical path-map set");
        let SemanticFieldV1::PathMap { mode, entries } =
            &set.nodes[set.roots[0] as usize].fields[0]
        else {
            panic!("path-map set field");
        };
        assert_eq!(*mode, PathMapModeV1::Set);
        assert_eq!(entries, &[SemanticPathMapEntryV1::Key(0), SemanticPathMapEntryV1::Key(1)]);
        let set_bytes = set
            .encode(&signature, &grammar, &bindings, limits)
            .expect("encode canonical path-map set");
        assert_eq!(
            SemanticTermImageV1::decode(&set_bytes, &signature, &grammar, &bindings, limits,)
                .expect("decode canonical path-map set"),
            set,
        );

        let map = image(
            &signature,
            vec![
                leaf(20),
                leaf(2),
                leaf(10),
                leaf(1),
                pathmap_node(
                    PathMapModeV1::Map,
                    vec![
                        SemanticPathMapEntryV1::KeyValue { key: 1, value: 0 },
                        SemanticPathMapEntryV1::KeyValue { key: 3, value: 2 },
                    ],
                ),
            ],
            vec![4],
        )
        .canonicalize(&signature, &grammar, &bindings, limits)
        .expect("canonical path-map map");
        let SemanticFieldV1::PathMap { mode, entries } =
            &map.nodes[map.roots[0] as usize].fields[0]
        else {
            panic!("path-map map field");
        };
        assert_eq!(*mode, PathMapModeV1::Map);
        assert!(matches!(
            entries.as_slice(),
            [
                SemanticPathMapEntryV1::KeyValue { key: 0, value: 2 },
                SemanticPathMapEntryV1::KeyValue { key: 1, value: 3 }
            ]
        ));
        let map_bytes = map
            .encode(&signature, &grammar, &bindings, limits)
            .expect("encode canonical path-map map");
        assert_eq!(
            SemanticTermImageV1::decode(&map_bytes, &signature, &grammar, &bindings, limits,)
                .expect("decode canonical path-map map"),
            map,
        );

        let duplicate_set = image(
            &signature,
            vec![
                leaf(1),
                leaf(1),
                pathmap_node(
                    PathMapModeV1::Set,
                    vec![SemanticPathMapEntryV1::Key(0), SemanticPathMapEntryV1::Key(1)],
                ),
            ],
            vec![2],
        );
        assert!(matches!(
            duplicate_set.canonicalize(&signature, &grammar, &bindings, limits),
            Err(SemanticTermImageError::DuplicateCollectionKey { .. })
        ));

        let duplicate = image(
            &signature,
            vec![
                leaf(1),
                leaf(10),
                leaf(1),
                leaf(20),
                pathmap_node(
                    PathMapModeV1::Map,
                    vec![
                        SemanticPathMapEntryV1::KeyValue { key: 0, value: 1 },
                        SemanticPathMapEntryV1::KeyValue { key: 2, value: 3 },
                    ],
                ),
            ],
            vec![4],
        );
        assert!(matches!(
            duplicate.canonicalize(&signature, &grammar, &bindings, limits),
            Err(SemanticTermImageError::DuplicateCollectionKey { .. })
        ));
    }

    #[test]
    fn pathmap_mode_and_entry_shape_mismatches_fail_closed() {
        let (grammar, signature) = pathmap_fixture();
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        for field in [
            SemanticFieldV1::PathMap {
                mode: PathMapModeV1::NeutralEmpty,
                entries: vec![SemanticPathMapEntryV1::Key(0)],
            },
            SemanticFieldV1::PathMap {
                mode: PathMapModeV1::Set,
                entries: vec![SemanticPathMapEntryV1::KeyValue { key: 0, value: 0 }],
            },
            SemanticFieldV1::PathMap {
                mode: PathMapModeV1::Map,
                entries: vec![SemanticPathMapEntryV1::Key(0)],
            },
        ] {
            let invalid = image(
                &signature,
                vec![
                    leaf(1),
                    SemanticNodeV1 {
                        operator: SemanticOperatorId(4),
                        payload: None,
                        fields: vec![field],
                    },
                ],
                vec![1],
            );
            let result = invalid.canonicalize(&signature, &grammar, &bindings, limits);
            assert!(
                matches!(result, Err(SemanticTermImageError::PathMapMode { .. })),
                "mode/entry-shape mismatch must be the first rejection, got {result:?}"
            );
        }
    }

    #[test]
    fn wide_shared_dag_is_bounded_and_preserves_bag_multiplicity() {
        const WIDTH: usize = 20_000;
        let (grammar, signature) = collection_fixture(CollectionKind::Bag);
        let bindings = RuntimeCapabilityBindings::default();
        let limits = SemanticTermAdmissionLimits::default();
        let entries = (0..WIDTH)
            .map(|_| SemanticCollectionEntryV1::Value(0))
            .collect();
        let wide = image(
            &signature,
            vec![leaf(7), collection_node(CollectionKind::Bag, entries)],
            vec![1],
        );
        let canonical = wide
            .canonicalize(&signature, &grammar, &bindings, limits)
            .expect("wide shared DAG canonicalizes iteratively");
        let SemanticFieldV1::Collection { entries, .. } = &canonical.nodes[1].fields[0] else {
            panic!("wide root is a collection");
        };
        assert_eq!(entries.len(), WIDTH);
        assert!(entries
            .iter()
            .all(|entry| *entry == SemanticCollectionEntryV1::Value(0)));

        let too_few_references = SemanticTermAdmissionLimits { max_references: WIDTH, ..limits };
        assert_eq!(
            wide.canonicalize(&signature, &grammar, &bindings, too_few_references),
            Err(SemanticTermImageError::LimitExceeded("references"))
        );
    }
}
