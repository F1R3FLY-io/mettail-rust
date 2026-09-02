//! One generator-time semantic layout shared by typed Dovetail emitters.
//!
//! The generated abstract-syntax tree, the canonical semantic term image, and
//! Dovetail are three representations of one checked language signature.  This
//! module performs the representation analysis once.  The operator emitter,
//! lowering PDA, inverse PDA, signature emitter, and machine-image emitter must
//! consume this layout instead of independently rediscovering constructor or
//! field shape.
//!
//! Two distinctions are load-bearing:
//!
//! - [`SemanticFieldProjection`] describes whether a field is a child edge, a
//!   structural sequence, an exact leaf, or a fail-closed opaque coefficient.
//! - [`SemanticCollectionProjection`] separates associative-commutative bags
//!   from ordered sequences and from containers for which no exact installed
//!   structural codec exists.
//!
//! Stable discriminants are assigned only to accepted operators.  A refused
//! constructor retains its category-local tag so reconstruction tags never
//! move merely because invertibility changes, but it cannot acquire an
//! operator ID or semantic authority.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use mettail_ast::grammar::NonTerminalKind;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use mettail_grammar_core as core;
use syn::Ident;

use super::withholding::{self, WithholdingSet};
use super::{collection_carrier, CollectionCarrier};
use crate::gen::term_ops::subst::{
    collect_category_variants, rule_to_variant_kind, FieldInfo, OpaqueLeafKind, VariantKind,
};

/// A checked field projection in the generated typed-AST adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticFieldProjection {
    /// A normal category field lowered as a child e-class.
    Child,
    /// An optional category child; absence is an indexed `FieldNone` leaf.
    OptionalChild,
    /// A position deliberately severed by a withholding declaration.
    Withheld,
    /// Captured token text carried verbatim in a typed leaf.
    TokenText,
    /// Optional token text; presence and indexed absence are both exact.
    OptionalTokenText,
    /// A non-optional ordered `Vec` carried verbatim in a category-labelled leaf.
    OrderedSequence,
    /// An optional ordered `Vec`; presence uses the exact sequence leaf and
    /// absence uses the indexed `FieldNone` leaf.
    OptionalOrderedSequence,
    /// A coefficient for which this generated backend has no exact inverse.
    Opaque,
    /// An optional opaque coefficient represented by a present leaf or an
    /// indexed absence leaf.
    OptionalOpaque,
}

impl SemanticFieldProjection {
    /// Whether the current generated inverse can reconstruct this projection
    /// without parsing display text or fabricating an unavailable codec.
    pub(crate) fn is_invertible(self) -> bool {
        matches!(
            self,
            Self::Child
                | Self::OptionalChild
                | Self::Withheld
                | Self::TokenText
                | Self::OptionalTokenText
                | Self::OrderedSequence
                | Self::OptionalOrderedSequence
        )
    }
}

/// Projection selected for a whole-constructor collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticCollectionProjection {
    /// An n-ary multiset node whose children may be exactly canonicalized.
    AcBag,
    /// A constructor node over one ordered-sequence leaf.
    OrderedSequence,
    /// A fail-closed coefficient leaf with no structural inverse.
    Opaque,
}

/// One constructor field and its single checked projection.
#[derive(Debug, Clone)]
pub(crate) struct SemanticFieldLayout {
    index: usize,
    field: FieldInfo,
    projection: SemanticFieldProjection,
}

impl SemanticFieldLayout {
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    pub(crate) fn field(&self) -> &FieldInfo {
        &self.field
    }

    pub(crate) fn projection(&self) -> SemanticFieldProjection {
        self.projection
    }
}

/// One typed constructor in the shared semantic census.
#[derive(Debug, Clone)]
pub(crate) struct SemanticVariantLayout {
    kind: VariantKind,
    constructor_tag: u32,
    operator_discriminant: Option<u32>,
    fields: Vec<SemanticFieldLayout>,
    collection: Option<SemanticCollectionProjection>,
}

impl SemanticVariantLayout {
    pub(crate) fn kind(&self) -> &VariantKind {
        &self.kind
    }

    pub(crate) fn label(&self) -> &Ident {
        self.kind.label()
    }

    pub(crate) fn constructor_tag(&self) -> u32 {
        self.constructor_tag
    }

    /// `None` only for a refusing classification, which emits a diagnostic but
    /// cannot be installed as a semantic operator.
    pub(crate) fn operator_discriminant(&self) -> Option<u32> {
        self.operator_discriminant
    }

    pub(crate) fn fields(&self) -> &[SemanticFieldLayout] {
        &self.fields
    }

    pub(crate) fn collection_projection(&self) -> Option<SemanticCollectionProjection> {
        self.collection
    }

    pub(crate) fn all_fields_invertible(&self) -> bool {
        self.fields
            .iter()
            .all(|field| field.projection.is_invertible())
    }
}

/// One semantic category and its complete constructor census.
#[derive(Debug, Clone)]
pub(crate) struct SemanticCategoryLayout {
    category: Ident,
    category_tag: u32,
    variants: Vec<SemanticVariantLayout>,
}

impl SemanticCategoryLayout {
    pub(crate) fn category(&self) -> &Ident {
        &self.category
    }

    /// Dense ordinal in the checked semantic category census.
    pub(crate) fn category_tag(&self) -> u32 {
        self.category_tag
    }

    pub(crate) fn variants(&self) -> &[SemanticVariantLayout] {
        &self.variants
    }

    #[cfg(test)]
    pub(crate) fn variant(&self, label: &Ident) -> Option<&SemanticVariantLayout> {
        self.variants
            .iter()
            .find(|variant| variant.label() == label)
    }
}

/// Identity of a backend-only structural leaf in the one checked sentinel
/// suffix.  Payload-bearing identities retain the category that fixes their
/// exact typed carrier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SemanticSentinelIdentity {
    BinderArity,
    FieldNone,
    FieldOpaque,
    FieldTokenText,
    FieldBytes,
    OrderedSequence {
        element_category: Ident,
    },
    Withheld {
        category: Ident,
    },
    Variable {
        category: Ident,
    },
    CollectionPair {
        kind: core::CollectionKind,
        element_category: Ident,
    },
    PathMapMode {
        element_category: Ident,
    },
    PathMapPair {
        element_category: Ident,
    },
    NativePathMapMode {
        key_category: Ident,
        value_category: Ident,
    },
    NativePathMapPair {
        key_category: Ident,
        value_category: Ident,
    },
}

/// One sentinel identity paired with its stable legacy operator discriminant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemanticSentinel {
    identity: SemanticSentinelIdentity,
    operator_discriminant: u32,
}

impl SemanticSentinel {
    pub(crate) fn identity(&self) -> &SemanticSentinelIdentity {
        &self.identity
    }

    pub(crate) fn operator_discriminant(&self) -> u32 {
        self.operator_discriminant
    }
}

/// The exact dense suffix occupied by generated structural sentinels.
///
/// Identity and discriminant are assigned together once.  Operator emission,
/// lowering, reconstruction, and canonical machine-image generation only
/// project this table; none may reconstruct its order independently.
#[derive(Debug, Clone)]
pub(crate) struct SemanticSentinelLayout {
    first_operator_discriminant: u32,
    end_operator_discriminant: u32,
    entries: Vec<SemanticSentinel>,
}

impl SemanticSentinelLayout {
    fn derive(
        first_operator_discriminant: u32,
        token_text: bool,
        ordered_sequence_elements: Vec<Ident>,
        withheld_categories: Vec<Ident>,
        variable_categories: Vec<Ident>,
        collection_pairs: Vec<(core::CollectionKind, Ident)>,
        pathmap_elements: Vec<Ident>,
        native_pathmaps: Vec<(Ident, Ident)>,
        byte_string: bool,
    ) -> Result<Self, SemanticAdapterLayoutError> {
        let mut identities = vec![
            SemanticSentinelIdentity::BinderArity,
            SemanticSentinelIdentity::FieldNone,
            SemanticSentinelIdentity::FieldOpaque,
        ];
        if token_text {
            identities.push(SemanticSentinelIdentity::FieldTokenText);
        }
        identities.extend(
            ordered_sequence_elements
                .into_iter()
                .map(|element_category| SemanticSentinelIdentity::OrderedSequence {
                    element_category,
                }),
        );
        identities.extend(
            withheld_categories
                .into_iter()
                .map(|category| SemanticSentinelIdentity::Withheld { category }),
        );
        identities.extend(
            variable_categories
                .into_iter()
                .map(|category| SemanticSentinelIdentity::Variable { category }),
        );
        // Append new identity families after every existing sentinel family so
        // extending the structural machine cannot renumber an established
        // typed-Dovetail operator discriminant.
        identities.extend(
            collection_pairs
                .into_iter()
                .map(|(kind, element_category)| SemanticSentinelIdentity::CollectionPair {
                    kind,
                    element_category,
                }),
        );
        identities.extend(pathmap_elements.into_iter().flat_map(|element_category| {
            [
                SemanticSentinelIdentity::PathMapMode {
                    element_category: element_category.clone(),
                },
                SemanticSentinelIdentity::PathMapPair { element_category },
            ]
        }));
        identities.extend(native_pathmaps.into_iter().flat_map(
            |(key_category, value_category)| {
                [
                    SemanticSentinelIdentity::NativePathMapMode {
                        key_category: key_category.clone(),
                        value_category: value_category.clone(),
                    },
                    SemanticSentinelIdentity::NativePathMapPair { key_category, value_category },
                ]
            },
        ));
        if byte_string {
            identities.push(SemanticSentinelIdentity::FieldBytes);
        }

        let mut next = first_operator_discriminant;
        let mut entries = Vec::with_capacity(identities.len());
        for identity in identities {
            entries.push(SemanticSentinel { identity, operator_discriminant: next });
            next = next
                .checked_add(1)
                .ok_or(SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
        }
        Ok(Self {
            first_operator_discriminant,
            end_operator_discriminant: next,
            entries,
        })
    }

    pub(crate) fn entries(&self) -> &[SemanticSentinel] {
        &self.entries
    }

    pub(crate) fn first_operator_discriminant(&self) -> u32 {
        self.first_operator_discriminant
    }

    pub(crate) fn end_operator_discriminant(&self) -> u32 {
        self.end_operator_discriminant
    }

    pub(crate) fn ordered_sequence_elements(&self) -> impl Iterator<Item = &Ident> {
        self.entries
            .iter()
            .filter_map(|entry| match entry.identity() {
                SemanticSentinelIdentity::OrderedSequence { element_category } => {
                    Some(element_category)
                },
                SemanticSentinelIdentity::BinderArity
                | SemanticSentinelIdentity::FieldNone
                | SemanticSentinelIdentity::FieldOpaque
                | SemanticSentinelIdentity::FieldTokenText
                | SemanticSentinelIdentity::FieldBytes
                | SemanticSentinelIdentity::Withheld { .. }
                | SemanticSentinelIdentity::Variable { .. }
                | SemanticSentinelIdentity::CollectionPair { .. }
                | SemanticSentinelIdentity::PathMapMode { .. }
                | SemanticSentinelIdentity::PathMapPair { .. }
                | SemanticSentinelIdentity::NativePathMapMode { .. }
                | SemanticSentinelIdentity::NativePathMapPair { .. } => None,
            })
    }

    pub(crate) fn withheld_categories(&self) -> impl Iterator<Item = &Ident> {
        self.entries
            .iter()
            .filter_map(|entry| match entry.identity() {
                SemanticSentinelIdentity::Withheld { category } => Some(category),
                SemanticSentinelIdentity::BinderArity
                | SemanticSentinelIdentity::FieldNone
                | SemanticSentinelIdentity::FieldOpaque
                | SemanticSentinelIdentity::FieldTokenText
                | SemanticSentinelIdentity::FieldBytes
                | SemanticSentinelIdentity::OrderedSequence { .. }
                | SemanticSentinelIdentity::Variable { .. }
                | SemanticSentinelIdentity::CollectionPair { .. }
                | SemanticSentinelIdentity::PathMapMode { .. }
                | SemanticSentinelIdentity::PathMapPair { .. }
                | SemanticSentinelIdentity::NativePathMapMode { .. }
                | SemanticSentinelIdentity::NativePathMapPair { .. } => None,
            })
    }

    pub(crate) fn has_token_text(&self) -> bool {
        self.entries
            .iter()
            .any(|entry| matches!(entry.identity(), SemanticSentinelIdentity::FieldTokenText))
    }

    pub(crate) fn has_byte_string(&self) -> bool {
        self.entries
            .iter()
            .any(|entry| matches!(entry.identity(), SemanticSentinelIdentity::FieldBytes))
    }

    pub(crate) fn variable(&self, category: &Ident) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::Variable { category: candidate }
                    if candidate == category
            )
        })
    }

    pub(crate) fn collection_pair(
        &self,
        kind: core::CollectionKind,
        element_category: &Ident,
    ) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::CollectionPair {
                    kind: candidate_kind,
                    element_category: candidate_category,
                } if *candidate_kind == kind && candidate_category == element_category
            )
        })
    }

    pub(crate) fn pathmap_mode(&self, element_category: &Ident) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::PathMapMode {
                    element_category: candidate,
                } if candidate == element_category
            )
        })
    }

    pub(crate) fn pathmap_pair(&self, element_category: &Ident) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::PathMapPair {
                    element_category: candidate,
                } if candidate == element_category
            )
        })
    }

    pub(crate) fn native_pathmap_mode(
        &self,
        key_category: &Ident,
        value_category: &Ident,
    ) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::NativePathMapMode {
                    key_category: candidate_key,
                    value_category: candidate_value,
                } if candidate_key == key_category && candidate_value == value_category
            )
        })
    }

    pub(crate) fn native_pathmap_pair(
        &self,
        key_category: &Ident,
        value_category: &Ident,
    ) -> Option<&SemanticSentinel> {
        self.entries.iter().find(|entry| {
            matches!(
                entry.identity(),
                SemanticSentinelIdentity::NativePathMapPair {
                    key_category: candidate_key,
                    value_category: candidate_value,
                } if candidate_key == key_category && candidate_value == value_category
            )
        })
    }
}

/// Canonical checked artifacts derived from the same generator layout as the
/// typed Dovetail backend.  These values contain no Rust source and grant no
/// runtime capability.
#[derive(Debug, Clone)]
pub(crate) struct GeneratedSemanticArtifacts {
    grammar: core::GrammarCoreV1,
    signature: core::SemanticSignatureV1,
    machine: core::SemanticMachineImageV1,
}

impl GeneratedSemanticArtifacts {
    pub(crate) fn grammar(&self) -> &core::GrammarCoreV1 {
        &self.grammar
    }

    pub(crate) fn signature(&self) -> &core::SemanticSignatureV1 {
        &self.signature
    }

    pub(crate) fn machine(&self) -> &core::SemanticMachineImageV1 {
        &self.machine
    }
}

/// Complete generator-time adapter layout for one checked language.
#[derive(Debug, Clone)]
pub(crate) struct SemanticAdapterLayout {
    categories: Vec<SemanticCategoryLayout>,
    sentinels: SemanticSentinelLayout,
}

impl SemanticAdapterLayout {
    pub(crate) fn derive(language: &LanguageDef) -> Result<Self, SemanticAdapterLayoutError> {
        let ordered_sequence_elements = derive_ordered_sequence_elements(language);
        let withholding = withholding::classify_withholdings(language);
        let withheld_categories = withholding
            .earned_categories()
            .into_iter()
            .filter(|category| !is_closed_data_category(language, category))
            .collect::<Vec<_>>();
        let token_text = derive_token_text(language);
        let byte_string = derive_byte_string(language);
        let mut next_operator_discriminant = 0u32;
        let mut categories = Vec::new();

        for (category_ordinal, lang_type) in
            crate::gen::semantic_transit_types(language).enumerate()
        {
            let category = lang_type.name.clone();
            let category_tag = u32::try_from(category_ordinal).map_err(|_| {
                SemanticAdapterLayoutError::CategoryTagOverflow { category: category.to_string() }
            })?;
            let mut variants = Vec::new();
            for (constructor_ordinal, kind) in collect_category_variants(&category, language)
                .into_iter()
                .enumerate()
            {
                let constructor_tag = u32::try_from(constructor_ordinal).map_err(|_| {
                    SemanticAdapterLayoutError::CategoryTagOverflow {
                        category: category.to_string(),
                    }
                })?;
                let operator_discriminant = if matches!(kind, VariantKind::Refused { .. }) {
                    None
                } else {
                    let current = next_operator_discriminant;
                    next_operator_discriminant = next_operator_discriminant
                        .checked_add(1)
                        .ok_or(SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
                    Some(current)
                };
                let fields = variant_fields(&kind)
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(index, field)| SemanticFieldLayout {
                        projection: derive_field_projection(
                            language,
                            kind.label(),
                            index,
                            &field,
                            &ordered_sequence_elements,
                            &withholding,
                        ),
                        index,
                        field,
                    })
                    .collect();
                let collection =
                    derive_collection_projection(language, &kind, &ordered_sequence_elements);
                variants.push(SemanticVariantLayout {
                    kind,
                    constructor_tag,
                    operator_discriminant,
                    fields,
                    collection,
                });
            }
            categories.push(SemanticCategoryLayout { category, category_tag, variants });
        }

        // Binder codomains are scheduled through typed raw-pointer tasks in
        // both lowering and reconstruction.  Validate their category against
        // the one shared census before any emitter can construct such a task.
        for category in &categories {
            for variant in &category.variants {
                let body_category = match variant.kind() {
                    VariantKind::Binder { body_cat, .. }
                    | VariantKind::MultiBinder { body_cat, .. } => body_cat,
                    _ => continue,
                };
                if !categories
                    .iter()
                    .any(|candidate| candidate.category() == body_category)
                {
                    return Err(SemanticAdapterLayoutError::UnknownCategory(
                        body_category.to_string(),
                    ));
                }
            }
        }

        let variable_categories = categories
            .iter()
            .filter(|category| {
                category
                    .variants
                    .iter()
                    .any(|variant| matches!(variant.kind(), VariantKind::Var { .. }))
            })
            .map(|category| category.category.clone())
            .collect();
        let collection_pairs = derive_collection_pairs(&categories);
        let pathmap_elements = derive_pathmap_elements(&categories);
        let native_pathmaps = derive_native_pathmaps(&categories);

        let sentinels = SemanticSentinelLayout::derive(
            next_operator_discriminant,
            token_text,
            ordered_sequence_elements,
            withheld_categories,
            variable_categories,
            collection_pairs,
            pathmap_elements,
            native_pathmaps,
            byte_string,
        )?;

        Ok(Self { categories, sentinels })
    }

    pub(crate) fn categories(&self) -> &[SemanticCategoryLayout] {
        &self.categories
    }

    pub(crate) fn category(&self, category: &Ident) -> Option<&SemanticCategoryLayout> {
        self.categories
            .iter()
            .find(|candidate| candidate.category == *category)
    }

    pub(crate) fn sentinels(&self) -> &SemanticSentinelLayout {
        &self.sentinels
    }

    pub(crate) fn ordered_sequence_elements(&self) -> impl Iterator<Item = &Ident> {
        self.sentinels.ordered_sequence_elements()
    }

    pub(crate) fn withheld_categories(&self) -> impl Iterator<Item = &Ident> {
        self.sentinels.withheld_categories()
    }

    pub(crate) fn has_token_text(&self) -> bool {
        self.sentinels.has_token_text()
    }

    pub(crate) fn has_byte_string(&self) -> bool {
        self.sentinels.has_byte_string()
    }

    #[cfg(test)]
    pub(crate) fn has_exact_optional_fields(&self) -> bool {
        self.categories.iter().any(|category| {
            category.variants.iter().any(|variant| {
                variant.fields.iter().any(|field| {
                    matches!(
                        field.projection,
                        SemanticFieldProjection::OptionalChild
                            | SemanticFieldProjection::OptionalTokenText
                            | SemanticFieldProjection::OptionalOrderedSequence
                    )
                })
            })
        })
    }
}

fn derive_collection_pairs(
    categories: &[SemanticCategoryLayout],
) -> Vec<(core::CollectionKind, Ident)> {
    let mut pairs = Vec::new();
    for category in categories {
        for variant in category.variants() {
            let VariantKind::CollectionLiteral {
                element_cat,
                coll_type: CollectionType::HashMap,
                ..
            } = variant.kind()
            else {
                continue;
            };
            let identity = (core::CollectionKind::Map, element_cat.clone());
            if !pairs.iter().any(|candidate| candidate == &identity) {
                pairs.push(identity);
            }
        }
    }
    pairs
}

fn derive_pathmap_elements(categories: &[SemanticCategoryLayout]) -> Vec<Ident> {
    let mut elements = Vec::new();
    for category in categories {
        for variant in category.variants() {
            let VariantKind::CollectionLiteral {
                element_cat,
                coll_type: CollectionType::PathMap,
                ..
            } = variant.kind()
            else {
                continue;
            };
            if !elements.iter().any(|candidate| candidate == element_cat) {
                elements.push(element_cat.clone());
            }
        }
    }
    elements
}

fn derive_native_pathmaps(categories: &[SemanticCategoryLayout]) -> Vec<(Ident, Ident)> {
    let mut pathmaps = Vec::new();
    for category in categories {
        for variant in category.variants() {
            let VariantKind::RecursiveNativeLiteral { carrier, .. } = variant.kind() else {
                continue;
            };
            let identity = (carrier.key_category().clone(), carrier.value_category().clone());
            if !pathmaps.iter().any(|candidate| candidate == &identity) {
                pathmaps.push(identity);
            }
        }
    }
    pathmaps
}

/// Derive and fully validate the source-neutral grammar/signature/machine
/// triple for a generated language.  Unsupported exact codecs or structural
/// carriers are explicit errors; the generator never substitutes debug text.
pub(crate) fn derive_semantic_artifacts(
    language: &LanguageDef,
    layout: &SemanticAdapterLayout,
) -> Result<GeneratedSemanticArtifacts, SemanticAdapterLayoutError> {
    let spec = crate::gen::syntax::parser::prattail_bridge::language_def_to_spec(language)
        .map_err(SemanticAdapterLayoutError::GrammarBridge)?;
    let grammar = spec
        .to_grammar_core()
        .map_err(SemanticAdapterLayoutError::GrammarBridge)?;
    let grammar_fingerprint = grammar
        .fingerprint()
        .map_err(|error| SemanticAdapterLayoutError::ArtifactValidation(format!("{error:?}")))?;

    let categories: BTreeMap<String, core::CategoryId> = grammar
        .categories
        .iter()
        .map(|category| (category.name.clone(), category.id))
        .collect();
    let mut productions = BTreeMap::new();
    for production in &grammar.productions {
        let category = grammar
            .categories
            .get(production.result.0 as usize)
            .filter(|category| category.id == production.result)
            .ok_or_else(|| {
                SemanticAdapterLayoutError::ArtifactValidation(format!(
                    "production {:?} references a non-dense category {:?}",
                    production.id, production.result
                ))
            })?;
        let key = (category.name.clone(), production.label.clone());
        if productions.insert(key.clone(), production).is_some() {
            return Err(SemanticAdapterLayoutError::DuplicateProduction {
                category: key.0,
                label: key.1,
            });
        }
    }

    let grammar_constructor_count = u32::try_from(grammar.productions.len())
        .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
    let mut next_generated_constructor = grammar_constructor_count;
    let mut covered_productions = BTreeSet::new();
    let mut atom_schemas = Vec::new();
    let mut operators = Vec::new();
    let mut machine_operators = Vec::new();

    for category_layout in layout.categories() {
        let category_name = category_layout.category().to_string();
        let category = categories
            .get(&category_name)
            .copied()
            .ok_or_else(|| SemanticAdapterLayoutError::UnknownCategory(category_name.clone()))?;
        for variant in category_layout.variants() {
            let Some(stable_discriminant) = variant.operator_discriminant() else {
                continue;
            };
            let label = variant.label().to_string();
            let key = (category_name.clone(), label.clone());
            let (constructor, origin) = match productions.get(&key) {
                Some(production) => {
                    covered_productions.insert(production.id);
                    (
                        production.constructor,
                        core::SemanticOperatorOriginV1::GrammarProduction(production.id),
                    )
                },
                None => {
                    let constructor = core::ConstructorId(next_generated_constructor);
                    next_generated_constructor = next_generated_constructor
                        .checked_add(1)
                        .ok_or(SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
                    (
                        constructor,
                        core::SemanticOperatorOriginV1::Generated {
                            family: generated_variant_family(variant.kind()).to_string(),
                            ordinal: variant.constructor_tag(),
                        },
                    )
                },
            };
            let payload = match variant.kind() {
                VariantKind::Literal { .. } => {
                    let schema = literal_atom_schema(language, category_layout.category())?;
                    Some(intern_atom_schema(&mut atom_schemas, schema)?)
                },
                VariantKind::CollectionLiteral { .. }
                | VariantKind::RecursiveNativeLiteral { .. } => None,
                VariantKind::Refused { .. }
                | VariantKind::Var { .. }
                | VariantKind::Nullary { .. }
                | VariantKind::Regular { .. }
                | VariantKind::Collection { .. }
                | VariantKind::Binder { .. }
                | VariantKind::MultiBinder { .. } => None,
            };
            let (fields, field_projections) = derive_variant_artifact_fields(
                layout,
                &categories,
                category,
                category_layout.category(),
                variant,
            )?;
            let operator = core::SemanticOperatorId(
                u32::try_from(operators.len())
                    .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?,
            );
            let qualified_label = format!("{}::{category_name}::{label}", language.name);
            operators.push(core::SemanticOperatorDeclV1 {
                id: operator,
                category,
                constructor,
                stable_discriminant,
                label: qualified_label.clone(),
                origin,
                payload,
                fields,
            });
            machine_operators.push(core::MachineOperatorProjectionV1 {
                operator,
                main: core::MachineOperatorTemplateV1 {
                    stable_discriminant,
                    fixed_payload_segments: Vec::new(),
                    label: qualified_label,
                },
                fields: field_projections,
            });
        }
    }

    for production in &grammar.productions {
        if !covered_productions.contains(&production.id) {
            let category = grammar
                .categories
                .get(production.result.0 as usize)
                .map(|category| category.name.clone())
                .unwrap_or_else(|| format!("#{:?}", production.result));
            return Err(SemanticAdapterLayoutError::MissingProduction {
                category,
                label: production.label.clone(),
            });
        }
    }

    let signature = core::SemanticSignatureV1 {
        abi: core::SEMANTIC_SIGNATURE_ABI_V1,
        grammar_fingerprint,
        category_count: u32::try_from(grammar.categories.len())
            .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?,
        constructor_count: next_generated_constructor,
        atom_schemas,
        operators,
    };
    let bindings = core::RuntimeCapabilityBindings::default();
    signature
        .validate(&grammar, &bindings)
        .map_err(|error| SemanticAdapterLayoutError::ArtifactValidation(format!("{error:?}")))?;
    let signature_fingerprint = signature
        .fingerprint()
        .map_err(|error| SemanticAdapterLayoutError::ArtifactValidation(format!("{error:?}")))?;
    let machine = core::SemanticMachineImageV1 {
        abi: core::SEMANTIC_MACHINE_IMAGE_ABI_V1,
        signature_fingerprint,
        operators: machine_operators,
    };
    machine
        .validate(&signature, &grammar, &bindings, core::SemanticMachineAdmissionLimits::default())
        .map_err(|error| SemanticAdapterLayoutError::ArtifactValidation(format!("{error:?}")))?;

    Ok(GeneratedSemanticArtifacts { grammar, signature, machine })
}

fn generated_variant_family(kind: &VariantKind) -> &'static str {
    match kind {
        VariantKind::Var { .. } => "implicit-variable",
        VariantKind::Literal { .. } => "implicit-literal",
        VariantKind::CollectionLiteral { .. } => "implicit-collection-literal",
        VariantKind::RecursiveNativeLiteral { .. } => "implicit-recursive-native-literal",
        VariantKind::Refused { .. }
        | VariantKind::Nullary { .. }
        | VariantKind::Regular { .. }
        | VariantKind::Collection { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => "generated-constructor",
    }
}

fn intern_atom_schema(
    schemas: &mut Vec<core::SemanticAtomSchemaV1>,
    schema: core::SemanticAtomSchemaV1,
) -> Result<u32, SemanticAdapterLayoutError> {
    if let Some(index) = schemas.iter().position(|existing| existing == &schema) {
        return u32::try_from(index)
            .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow);
    }
    let index = u32::try_from(schemas.len())
        .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
    schemas.push(schema);
    Ok(index)
}

fn literal_atom_schema(
    language: &LanguageDef,
    category: &Ident,
) -> Result<core::SemanticAtomSchemaV1, SemanticAdapterLayoutError> {
    let native = language
        .get_type(category)
        .and_then(|lang_type| lang_type.native_type.as_ref())
        .map(crate::gen::native::native_type_to_full_string)
        .ok_or_else(|| SemanticAdapterLayoutError::UnsupportedCodec {
            category: category.to_string(),
            carrier: "missing native literal carrier".to_string(),
        })?;
    let compact: String = native
        .chars()
        .filter(|character| !character.is_whitespace())
        .collect();
    let terminal = compact.rsplit("::").next().unwrap_or(&compact);
    let builtin = match terminal {
        "bool" => core::SemanticBuiltinAtomV1::Boolean,
        "i8" => core::SemanticBuiltinAtomV1::SignedInteger { bits: Some(8) },
        "i16" => core::SemanticBuiltinAtomV1::SignedInteger { bits: Some(16) },
        "i32" => core::SemanticBuiltinAtomV1::SignedInteger { bits: Some(32) },
        "i64" => core::SemanticBuiltinAtomV1::SignedInteger { bits: Some(64) },
        "i128" => core::SemanticBuiltinAtomV1::SignedInteger { bits: Some(128) },
        "u8" => core::SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(8) },
        "u16" => core::SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(16) },
        "u32" => core::SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(32) },
        "u64" => core::SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(64) },
        "u128" => core::SemanticBuiltinAtomV1::UnsignedInteger { bits: Some(128) },
        "BigInt" | "CanonicalBigInt" => core::SemanticBuiltinAtomV1::SignedInteger { bits: None },
        "f32" => core::SemanticBuiltinAtomV1::Float { bits: 32 },
        "f64" | "CanonicalFloat64" => core::SemanticBuiltinAtomV1::Float { bits: 64 },
        "String" | "str" => core::SemanticBuiltinAtomV1::Utf8,
        "()" => core::SemanticBuiltinAtomV1::Unit,
        "isize" | "usize" => {
            return Err(SemanticAdapterLayoutError::UnsupportedCodec {
                category: category.to_string(),
                carrier: format!("platform-width carrier `{native}`"),
            });
        },
        _ => {
            return Err(SemanticAdapterLayoutError::UnsupportedCodec {
                category: category.to_string(),
                carrier: native,
            });
        },
    };
    Ok(core::SemanticAtomSchemaV1::Builtin(builtin))
}

fn derive_variant_artifact_fields(
    layout: &SemanticAdapterLayout,
    categories: &BTreeMap<String, core::CategoryId>,
    owner_category: core::CategoryId,
    owner_category_name: &Ident,
    variant: &SemanticVariantLayout,
) -> Result<
    (Vec<core::SemanticFieldSchemaV1>, Vec<core::MachineFieldProjectionV1>),
    SemanticAdapterLayoutError,
> {
    let mut schemas = Vec::new();
    let mut projections = Vec::new();
    match variant.kind() {
        VariantKind::Refused { .. } => {
            return Err(SemanticAdapterLayoutError::UnsupportedVariant {
                category: owner_category_name.to_string(),
                label: variant.label().to_string(),
                reason: "refused variants have no semantic operator",
            });
        },
        VariantKind::Var { .. } => {
            let sentinel = layout
                .sentinels()
                .variable(owner_category_name)
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::MissingSentinel(format!(
                        "variable/{owner_category_name}"
                    ))
                })?;
            schemas.push(core::SemanticFieldSchemaV1::Variable { category: owner_category });
            projections.push(core::MachineFieldProjectionV1::Variable {
                leaf: sentinel_template(sentinel, Vec::new()),
            });
        },
        VariantKind::Literal { .. } | VariantKind::Nullary { .. } => {},
        VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            let element = categories
                .get(&element_cat.to_string())
                .copied()
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::UnknownCategory(element_cat.to_string())
                })?;
            let (kind, key, projection) = match coll_type {
                CollectionType::Vec => (
                    core::CollectionKind::List,
                    None,
                    core::MachineFieldProjectionV1::InlineValueCollection {
                        kind: core::CollectionKind::List,
                        child_order: core::MachineChildOrderV1::Ordered,
                    },
                ),
                CollectionType::HashBag => (
                    core::CollectionKind::Bag,
                    None,
                    core::MachineFieldProjectionV1::InlineValueCollection {
                        kind: core::CollectionKind::Bag,
                        child_order: core::MachineChildOrderV1::CanonicalExactKey,
                    },
                ),
                CollectionType::HashSet => (
                    core::CollectionKind::Set,
                    None,
                    core::MachineFieldProjectionV1::InlineValueCollection {
                        kind: core::CollectionKind::Set,
                        child_order: core::MachineChildOrderV1::CanonicalExactKey,
                    },
                ),
                CollectionType::HashMap => {
                    let pair = layout
                        .sentinels()
                        .collection_pair(core::CollectionKind::Map, element_cat)
                        .ok_or_else(|| {
                            SemanticAdapterLayoutError::MissingSentinel(format!(
                                "collection-pair/Map/{element_cat}"
                            ))
                        })?;
                    (
                        core::CollectionKind::Map,
                        Some(element),
                        core::MachineFieldProjectionV1::InlinePairCollection {
                            kind: core::CollectionKind::Map,
                            pair: sentinel_template(pair, Vec::new()),
                            child_order: core::MachineChildOrderV1::Ordered,
                        },
                    )
                },
                CollectionType::PathMap => {
                    let mode = layout
                        .sentinels()
                        .pathmap_mode(element_cat)
                        .ok_or_else(|| {
                            SemanticAdapterLayoutError::MissingSentinel(format!(
                                "pathmap-mode/{element_cat}"
                            ))
                        })?;
                    let pair = layout
                        .sentinels()
                        .pathmap_pair(element_cat)
                        .ok_or_else(|| {
                            SemanticAdapterLayoutError::MissingSentinel(format!(
                                "pathmap-pair/{element_cat}"
                            ))
                        })?;
                    schemas.push(core::SemanticFieldSchemaV1::PathMap {
                        key: element,
                        value: element,
                    });
                    projections.push(core::MachineFieldProjectionV1::InlinePathMap {
                        empty: sentinel_template(mode, vec![vec![0]]),
                        set: sentinel_template(mode, vec![vec![1]]),
                        map: sentinel_template(mode, vec![vec![2]]),
                        pair: sentinel_template(pair, Vec::new()),
                    });
                    return Ok((schemas, projections));
                },
            };
            schemas.push(core::SemanticFieldSchemaV1::Collection { kind, key, value: element });
            projections.push(projection);
        },
        VariantKind::RecursiveNativeLiteral { carrier, .. } => {
            let key_category = carrier.key_category();
            let value_category = carrier.value_category();
            let key = categories
                .get(&key_category.to_string())
                .copied()
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::UnknownCategory(key_category.to_string())
                })?;
            let value = categories
                .get(&value_category.to_string())
                .copied()
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::UnknownCategory(value_category.to_string())
                })?;
            let mode = layout
                .sentinels()
                .native_pathmap_mode(key_category, value_category)
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::MissingSentinel(format!(
                        "native-pathmap-mode/{key_category}/{value_category}"
                    ))
                })?;
            let pair = layout
                .sentinels()
                .native_pathmap_pair(key_category, value_category)
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::MissingSentinel(format!(
                        "native-pathmap-pair/{key_category}/{value_category}"
                    ))
                })?;
            schemas.push(core::SemanticFieldSchemaV1::PathMap { key, value });
            projections.push(core::MachineFieldProjectionV1::InlinePathMap {
                empty: sentinel_template(mode, vec![vec![0]]),
                set: sentinel_template(mode, vec![vec![1]]),
                map: sentinel_template(mode, vec![vec![2]]),
                pair: sentinel_template(pair, Vec::new()),
            });
            schemas.push(core::SemanticFieldSchemaV1::Bytes);
            projections.push(core::MachineFieldProjectionV1::Bytes {
                leaf: byte_string_template(layout)?,
            });
        },
        VariantKind::Collection { label, element_cat, .. } => {
            let element = categories
                .get(&element_cat.to_string())
                .copied()
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::UnknownCategory(element_cat.to_string())
                })?;
            match variant.collection_projection().ok_or_else(|| {
                SemanticAdapterLayoutError::UnsupportedVariant {
                    category: owner_category_name.to_string(),
                    label: label.to_string(),
                    reason: "collection variant is missing its shared carrier projection",
                }
            })? {
                SemanticCollectionProjection::AcBag => {
                    schemas.push(core::SemanticFieldSchemaV1::Collection {
                        kind: core::CollectionKind::Bag,
                        key: None,
                        value: element,
                    });
                    projections.push(core::MachineFieldProjectionV1::InlineValueCollection {
                        kind: core::CollectionKind::Bag,
                        child_order: core::MachineChildOrderV1::CanonicalExactKey,
                    });
                },
                SemanticCollectionProjection::OrderedSequence => {
                    schemas.push(core::SemanticFieldSchemaV1::Sequence { element });
                    projections.push(core::MachineFieldProjectionV1::Sequence {
                        spine: sequence_template(layout, element_cat)?,
                        child_order: core::MachineChildOrderV1::Ordered,
                    });
                },
                SemanticCollectionProjection::Opaque => {
                    return Err(SemanticAdapterLayoutError::UnsupportedVariant {
                        category: owner_category_name.to_string(),
                        label: label.to_string(),
                        reason: "whole-constructor collection requires an exact structural carrier",
                    });
                },
            }
        },
        VariantKind::Regular { .. } => {
            append_regular_artifact_fields(
                layout,
                categories,
                variant,
                &mut schemas,
                &mut projections,
            )?;
        },
        VariantKind::Binder { binder_cat, body_cat, .. } => {
            append_regular_artifact_fields(
                layout,
                categories,
                variant,
                &mut schemas,
                &mut projections,
            )?;
            append_scope_artifact_field(
                layout,
                categories,
                binder_cat,
                body_cat,
                1,
                Some(1),
                &mut schemas,
                &mut projections,
            )?;
        },
        VariantKind::MultiBinder { binder_cat, body_cat, .. } => {
            append_regular_artifact_fields(
                layout,
                categories,
                variant,
                &mut schemas,
                &mut projections,
            )?;
            append_scope_artifact_field(
                layout,
                categories,
                binder_cat,
                body_cat,
                0,
                None,
                &mut schemas,
                &mut projections,
            )?;
        },
    }
    Ok((schemas, projections))
}

fn append_regular_artifact_fields(
    layout: &SemanticAdapterLayout,
    categories: &BTreeMap<String, core::CategoryId>,
    variant: &SemanticVariantLayout,
    schemas: &mut Vec<core::SemanticFieldSchemaV1>,
    projections: &mut Vec<core::MachineFieldProjectionV1>,
) -> Result<(), SemanticAdapterLayoutError> {
    for field in variant.fields() {
        let category = || {
            categories
                .get(&field.field().category.to_string())
                .copied()
                .ok_or_else(|| {
                    SemanticAdapterLayoutError::UnknownCategory(field.field().category.to_string())
                })
        };
        let field_index = u32::try_from(field.index())
            .map_err(|_| SemanticAdapterLayoutError::OperatorDiscriminantOverflow)?;
        match field.projection() {
            SemanticFieldProjection::Child => {
                schemas.push(core::SemanticFieldSchemaV1::Child { category: category()? });
                projections.push(core::MachineFieldProjectionV1::Child);
            },
            SemanticFieldProjection::OptionalChild => {
                schemas.push(core::SemanticFieldSchemaV1::Optional { category: category()? });
                projections.push(core::MachineFieldProjectionV1::Optional {
                    none: field_none_template(layout, field_index)?,
                });
            },
            SemanticFieldProjection::TokenText => {
                schemas.push(core::SemanticFieldSchemaV1::TokenText);
                projections.push(core::MachineFieldProjectionV1::TokenText {
                    leaf: token_text_template(layout)?,
                });
            },
            SemanticFieldProjection::OptionalTokenText => {
                schemas.push(core::SemanticFieldSchemaV1::OptionalTokenText);
                projections.push(core::MachineFieldProjectionV1::OptionalTokenText {
                    none: field_none_template(layout, field_index)?,
                    leaf: token_text_template(layout)?,
                });
            },
            SemanticFieldProjection::OrderedSequence => {
                let element = category()?;
                schemas.push(core::SemanticFieldSchemaV1::Sequence { element });
                projections.push(core::MachineFieldProjectionV1::Sequence {
                    spine: sequence_template(layout, &field.field().category)?,
                    child_order: core::MachineChildOrderV1::Ordered,
                });
            },
            SemanticFieldProjection::OptionalOrderedSequence => {
                let element = category()?;
                schemas.push(core::SemanticFieldSchemaV1::OptionalSequence { element });
                projections.push(core::MachineFieldProjectionV1::OptionalSequence {
                    none: field_none_template(layout, field_index)?,
                    spine: sequence_template(layout, &field.field().category)?,
                    child_order: core::MachineChildOrderV1::Ordered,
                });
            },
            SemanticFieldProjection::Withheld => {
                return Err(SemanticAdapterLayoutError::UnsupportedField {
                    field: field.index(),
                    reason: "withholding requires a structural-child coefficient projection",
                });
            },
            SemanticFieldProjection::Opaque | SemanticFieldProjection::OptionalOpaque => {
                return Err(SemanticAdapterLayoutError::UnsupportedField {
                    field: field.index(),
                    reason: "an exact installed structural codec is required",
                });
            },
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn append_scope_artifact_field(
    layout: &SemanticAdapterLayout,
    categories: &BTreeMap<String, core::CategoryId>,
    domain: &Ident,
    body: &Ident,
    minimum_arity: u32,
    maximum_arity: Option<u32>,
    schemas: &mut Vec<core::SemanticFieldSchemaV1>,
    projections: &mut Vec<core::MachineFieldProjectionV1>,
) -> Result<(), SemanticAdapterLayoutError> {
    let category = |name: &Ident| {
        categories
            .get(&name.to_string())
            .copied()
            .ok_or_else(|| SemanticAdapterLayoutError::UnknownCategory(name.to_string()))
    };
    let sentinel = find_sentinel(
        layout,
        |identity| matches!(identity, SemanticSentinelIdentity::BinderArity),
        "binder-arity",
    )?;
    schemas.push(core::SemanticFieldSchemaV1::Scope {
        domain: category(domain)?,
        body: category(body)?,
        minimum_arity,
        maximum_arity,
    });
    projections.push(core::MachineFieldProjectionV1::Scope {
        arity: sentinel_template(sentinel, Vec::new()),
    });
    Ok(())
}

fn field_none_template(
    layout: &SemanticAdapterLayout,
    field_index: u32,
) -> Result<core::MachineOperatorTemplateV1, SemanticAdapterLayoutError> {
    let sentinel = find_sentinel(
        layout,
        |identity| matches!(identity, SemanticSentinelIdentity::FieldNone),
        "field-none",
    )?;
    Ok(sentinel_template(sentinel, vec![field_index.to_le_bytes().to_vec()]))
}

fn token_text_template(
    layout: &SemanticAdapterLayout,
) -> Result<core::MachineOperatorTemplateV1, SemanticAdapterLayoutError> {
    let sentinel = find_sentinel(
        layout,
        |identity| matches!(identity, SemanticSentinelIdentity::FieldTokenText),
        "field-token-text",
    )?;
    Ok(sentinel_template(sentinel, Vec::new()))
}

fn byte_string_template(
    layout: &SemanticAdapterLayout,
) -> Result<core::MachineOperatorTemplateV1, SemanticAdapterLayoutError> {
    let sentinel = find_sentinel(
        layout,
        |identity| matches!(identity, SemanticSentinelIdentity::FieldBytes),
        "field-bytes",
    )?;
    Ok(sentinel_template(sentinel, Vec::new()))
}

fn sequence_template(
    layout: &SemanticAdapterLayout,
    category: &Ident,
) -> Result<core::MachineOperatorTemplateV1, SemanticAdapterLayoutError> {
    let sentinel = find_sentinel(
        layout,
        |identity| {
            matches!(
                identity,
                SemanticSentinelIdentity::OrderedSequence { element_category }
                    if element_category == category
            )
        },
        &format!("field-sequence/{category}"),
    )?;
    Ok(sentinel_template(sentinel, Vec::new()))
}

fn find_sentinel<'a>(
    layout: &'a SemanticAdapterLayout,
    predicate: impl Fn(&SemanticSentinelIdentity) -> bool,
    label: &str,
) -> Result<&'a SemanticSentinel, SemanticAdapterLayoutError> {
    layout
        .sentinels()
        .entries()
        .iter()
        .find(|sentinel| predicate(sentinel.identity()))
        .ok_or_else(|| SemanticAdapterLayoutError::MissingSentinel(label.to_string()))
}

fn sentinel_template(
    sentinel: &SemanticSentinel,
    fixed_payload_segments: Vec<Vec<u8>>,
) -> core::MachineOperatorTemplateV1 {
    core::MachineOperatorTemplateV1 {
        stable_discriminant: sentinel.operator_discriminant(),
        fixed_payload_segments,
        label: sentinel_label(sentinel.identity()),
    }
}

fn sentinel_label(identity: &SemanticSentinelIdentity) -> String {
    match identity {
        SemanticSentinelIdentity::BinderArity => "<binder-arity>".to_string(),
        SemanticSentinelIdentity::FieldNone => "<field-none>".to_string(),
        SemanticSentinelIdentity::FieldOpaque => "<field-opaque>".to_string(),
        SemanticSentinelIdentity::FieldTokenText => "<field-token-text>".to_string(),
        SemanticSentinelIdentity::FieldBytes => "<field-bytes>".to_string(),
        SemanticSentinelIdentity::OrderedSequence { element_category } => {
            format!("<field-seq-{element_category}>")
        },
        SemanticSentinelIdentity::Withheld { category } => {
            format!("<field-withheld-{category}>")
        },
        SemanticSentinelIdentity::Variable { category } => {
            format!("<field-variable-{category}>")
        },
        SemanticSentinelIdentity::CollectionPair { kind, element_category } => {
            format!("<collection-pair-{kind:?}-{element_category}>")
        },
        SemanticSentinelIdentity::PathMapMode { element_category } => {
            format!("<pathmap-mode-{element_category}>")
        },
        SemanticSentinelIdentity::PathMapPair { element_category } => {
            format!("<pathmap-pair-{element_category}>")
        },
        SemanticSentinelIdentity::NativePathMapMode { key_category, value_category } => {
            format!("<native-pathmap-mode-{key_category}-{value_category}>")
        },
        SemanticSentinelIdentity::NativePathMapPair { key_category, value_category } => {
            format!("<native-pathmap-pair-{key_category}-{value_category}>")
        },
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SemanticAdapterLayoutError {
    CategoryTagOverflow {
        category: String,
    },
    OperatorDiscriminantOverflow,
    GrammarBridge(String),
    ArtifactValidation(String),
    DuplicateProduction {
        category: String,
        label: String,
    },
    MissingProduction {
        category: String,
        label: String,
    },
    UnknownCategory(String),
    MissingSentinel(String),
    UnsupportedCodec {
        category: String,
        carrier: String,
    },
    UnsupportedVariant {
        category: String,
        label: String,
        reason: &'static str,
    },
    UnsupportedField {
        field: usize,
        reason: &'static str,
    },
}

impl fmt::Display for SemanticAdapterLayoutError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CategoryTagOverflow { category } => write!(
                formatter,
                "semantic adapter category `{category}` has more than u32::MAX constructors"
            ),
            Self::OperatorDiscriminantOverflow => formatter.write_str(
                "semantic adapter operators and structural sentinel leaves exhaust the u32 discriminant space",
            ),
            Self::GrammarBridge(message) => {
                write!(formatter, "semantic artifact GrammarCore bridge failed: {message}")
            },
            Self::ArtifactValidation(message) => {
                write!(formatter, "semantic artifact validation failed: {message}")
            },
            Self::DuplicateProduction { category, label } => write!(
                formatter,
                "semantic artifact has duplicate production key `{category}::{label}`"
            ),
            Self::MissingProduction { category, label } => write!(
                formatter,
                "semantic adapter has no exact variant for production `{category}::{label}`"
            ),
            Self::UnknownCategory(category) => {
                write!(formatter, "semantic artifact references unknown category `{category}`")
            },
            Self::MissingSentinel(sentinel) => {
                write!(formatter, "semantic artifact is missing sentinel `{sentinel}`")
            },
            Self::UnsupportedCodec { category, carrier } => write!(
                formatter,
                "semantic category `{category}` requires an exact codec for `{carrier}`"
            ),
            Self::UnsupportedVariant { category, label, reason } => write!(
                formatter,
                "semantic variant `{category}::{label}` is not exactly representable: {reason}"
            ),
            Self::UnsupportedField { field, reason } => write!(
                formatter,
                "semantic field {field} is not exactly representable: {reason}"
            ),
        }
    }
}

pub(crate) fn is_closed_data_category(language: &LanguageDef, category: &Ident) -> bool {
    language
        .get_type(category)
        .is_some_and(mettail_ast::language::LangType::is_data)
}

fn variant_fields(kind: &VariantKind) -> &[FieldInfo] {
    match kind {
        VariantKind::Regular { fields, .. } => fields,
        VariantKind::Binder { pre_scope_fields, .. }
        | VariantKind::MultiBinder { pre_scope_fields, .. } => pre_scope_fields,
        VariantKind::Refused { .. }
        | VariantKind::Var { .. }
        | VariantKind::Literal { .. }
        | VariantKind::CollectionLiteral { .. }
        | VariantKind::RecursiveNativeLiteral { .. }
        | VariantKind::Nullary { .. }
        | VariantKind::Collection { .. } => &[],
    }
}

fn derive_field_projection(
    language: &LanguageDef,
    owner_label: &Ident,
    field_index: usize,
    field: &FieldInfo,
    ordered_sequence_elements: &[Ident],
    withholding: &WithholdingSet,
) -> SemanticFieldProjection {
    if field.is_semantic_boundary(language) {
        return SemanticFieldProjection::Opaque;
    }
    if withholding.is_severed(owner_label, field_index) {
        return SemanticFieldProjection::Withheld;
    }
    if NonTerminalKind::classify(&field.category.to_string()).is_builtin() {
        return SemanticFieldProjection::Opaque;
    }
    if field.is_optional {
        if field.is_predicate || field.is_opaque_leaf() {
            return if field.opaque_leaf == Some(OpaqueLeafKind::TokenText) {
                SemanticFieldProjection::OptionalTokenText
            } else {
                SemanticFieldProjection::OptionalOpaque
            };
        }
        return if field.is_collection {
            match collection_carrier(field.coll_type.as_ref()) {
                CollectionCarrier::OrderedSeq
                    if ordered_sequence_elements
                        .iter()
                        .any(|element| *element == field.category) =>
                {
                    SemanticFieldProjection::OptionalOrderedSequence
                },
                CollectionCarrier::OrderedSeq
                | CollectionCarrier::AcBag
                | CollectionCarrier::Opaque => SemanticFieldProjection::OptionalOpaque,
            }
        } else {
            SemanticFieldProjection::OptionalChild
        };
    }
    if field.is_predicate || field.is_opaque_leaf() {
        return if field.opaque_leaf == Some(OpaqueLeafKind::TokenText) {
            SemanticFieldProjection::TokenText
        } else {
            SemanticFieldProjection::Opaque
        };
    }
    if field.is_collection {
        return match collection_carrier(field.coll_type.as_ref()) {
            CollectionCarrier::OrderedSeq
                if ordered_sequence_elements
                    .iter()
                    .any(|element| *element == field.category) =>
            {
                SemanticFieldProjection::OrderedSequence
            },
            CollectionCarrier::OrderedSeq
            | CollectionCarrier::AcBag
            | CollectionCarrier::Opaque => SemanticFieldProjection::Opaque,
        };
    }
    SemanticFieldProjection::Child
}

fn derive_collection_projection(
    language: &LanguageDef,
    kind: &VariantKind,
    ordered_sequence_elements: &[Ident],
) -> Option<SemanticCollectionProjection> {
    let VariantKind::Collection { element_cat, coll_type, .. } = kind else {
        return None;
    };
    if is_closed_data_category(language, element_cat) {
        return Some(SemanticCollectionProjection::Opaque);
    }
    Some(match collection_carrier(Some(coll_type)) {
        CollectionCarrier::AcBag => SemanticCollectionProjection::AcBag,
        CollectionCarrier::OrderedSeq
            if ordered_sequence_elements
                .iter()
                .any(|element| element == element_cat) =>
        {
            SemanticCollectionProjection::OrderedSequence
        },
        CollectionCarrier::OrderedSeq | CollectionCarrier::Opaque => {
            SemanticCollectionProjection::Opaque
        },
    })
}

pub(crate) fn derive_ordered_sequence_elements(language: &LanguageDef) -> Vec<Ident> {
    fn ordered_field_element(language: &LanguageDef, field: &FieldInfo) -> Option<Ident> {
        if !field.is_collection || field.is_semantic_boundary(language) {
            return None;
        }
        match collection_carrier(field.coll_type.as_ref()) {
            CollectionCarrier::OrderedSeq => Some(field.category.clone()),
            CollectionCarrier::AcBag | CollectionCarrier::Opaque => None,
        }
    }

    let mut output = Vec::new();
    let mut push_unique = |category: Ident| {
        if !output.iter().any(|seen| *seen == category) {
            output.push(category);
        }
    };
    for rule in &language.terms {
        match rule_to_variant_kind(rule, language) {
            VariantKind::Regular { fields, .. } => {
                for category in fields
                    .iter()
                    .filter_map(|field| ordered_field_element(language, field))
                {
                    push_unique(category);
                }
            },
            VariantKind::Binder { pre_scope_fields, .. }
            | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                for category in pre_scope_fields
                    .iter()
                    .filter_map(|field| ordered_field_element(language, field))
                {
                    push_unique(category);
                }
            },
            VariantKind::Collection { element_cat, coll_type, .. }
                if collection_carrier(Some(&coll_type)) == CollectionCarrier::OrderedSeq
                    && !is_closed_data_category(language, &element_cat) =>
            {
                push_unique(element_cat);
            },
            VariantKind::Refused { .. }
            | VariantKind::Var { .. }
            | VariantKind::Literal { .. }
            | VariantKind::CollectionLiteral { .. }
            | VariantKind::RecursiveNativeLiteral { .. }
            | VariantKind::Nullary { .. }
            | VariantKind::Collection { .. } => {},
        }
    }
    output
}

pub(crate) fn derive_token_text(language: &LanguageDef) -> bool {
    fn carries_token_text(field: &FieldInfo) -> bool {
        field.opaque_leaf == Some(OpaqueLeafKind::TokenText)
    }

    crate::gen::semantic_transit_types(language).any(|lang_type| {
        collect_category_variants(&lang_type.name, language)
            .iter()
            .any(|variant| match variant {
                VariantKind::Regular { fields, .. } => fields.iter().any(carries_token_text),
                VariantKind::Binder { pre_scope_fields, .. }
                | VariantKind::MultiBinder { pre_scope_fields, .. } => {
                    pre_scope_fields.iter().any(carries_token_text)
                },
                VariantKind::Refused { .. }
                | VariantKind::Var { .. }
                | VariantKind::Literal { .. }
                | VariantKind::CollectionLiteral { .. }
                | VariantKind::RecursiveNativeLiteral { .. }
                | VariantKind::Nullary { .. }
                | VariantKind::Collection { .. } => false,
            })
    })
}

pub(crate) fn derive_byte_string(language: &LanguageDef) -> bool {
    crate::gen::semantic_transit_types(language).any(|lang_type| {
        collect_category_variants(&lang_type.name, language)
            .iter()
            .any(|variant| matches!(variant, VariantKind::RecursiveNativeLiteral { .. }))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> LanguageDef {
        syn::parse_str(
            r#"
                name: AdapterLayout,
                types {
                    Proc
                    ![i64] as Int
                    ![mettail_runtime::HashBag<Proc>] as Bag
                    ![mettail_runtime::HashMapLit<Proc, Proc>] as Map
                },
                terms {
                    PZero . |- "0" : Proc;
                    Pair . left:Proc, right:Proc |- "(" left "," right ")" : Proc;
                    Maybe . *opt(value:Proc) |- "maybe" *opt(value) : Proc;
                    PBag . values:HashBag(Proc) |- "{" values.*sep("|") "}" : Proc;
                    AddInt . left:Int, right:Int |- left "+" right : Int ![left + right] fold;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("semantic-adapter fixture must parse")
    }

    #[test]
    fn one_layout_owns_dense_operator_and_category_tags() {
        let language = fixture();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let mut expected_discriminant = 0u32;
        for (expected_category_tag, category) in layout.categories().iter().enumerate() {
            assert_eq!(category.category_tag(), expected_category_tag as u32);
            for (expected_tag, variant) in category.variants().iter().enumerate() {
                assert_eq!(variant.constructor_tag(), expected_tag as u32);
                if let Some(discriminant) = variant.operator_discriminant() {
                    assert_eq!(discriminant, expected_discriminant);
                    expected_discriminant += 1;
                }
                assert_eq!(
                    category
                        .variant(variant.label())
                        .map(|v| v.constructor_tag()),
                    Some(variant.constructor_tag())
                );
            }
        }
        assert_eq!(layout.sentinels().first_operator_discriminant(), expected_discriminant);
        for (index, sentinel) in layout.sentinels().entries().iter().enumerate() {
            assert_eq!(sentinel.operator_discriminant(), expected_discriminant + index as u32);
        }
        assert_eq!(
            layout.sentinels().end_operator_discriminant(),
            expected_discriminant + layout.sentinels().entries().len() as u32
        );
    }

    #[test]
    fn constructor_fields_have_one_shared_projection() {
        let language = fixture();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let category = layout
            .category(&syn::parse_str("Proc").expect("identifier"))
            .expect("Proc layout");
        let pair = category
            .variant(&syn::parse_str("Pair").expect("identifier"))
            .expect("Pair layout");
        assert_eq!(pair.fields().len(), 2);
        assert!(pair
            .fields()
            .iter()
            .all(|field| field.projection() == SemanticFieldProjection::Child));
        assert!(pair.all_fields_invertible());

        let maybe = category
            .variant(&syn::parse_str("Maybe").expect("identifier"))
            .expect("Maybe layout");
        assert_eq!(maybe.fields().len(), 1);
        assert_eq!(maybe.fields()[0].projection(), SemanticFieldProjection::OptionalChild,);
        assert!(maybe.all_fields_invertible());
        assert!(layout.has_exact_optional_fields());
    }

    #[test]
    fn sentinel_identity_and_discriminant_share_one_exact_table() {
        let sequence_category: Ident = syn::parse_str("Proc").expect("identifier");
        let withheld_category: Ident = syn::parse_str("Name").expect("identifier");
        let sentinels = SemanticSentinelLayout::derive(
            17,
            true,
            vec![sequence_category.clone()],
            vec![withheld_category.clone()],
            vec![sequence_category.clone()],
            vec![(core::CollectionKind::Map, sequence_category.clone())],
            Vec::new(),
            Vec::new(),
            false,
        )
        .expect("sentinel layout must derive");

        assert_eq!(sentinels.first_operator_discriminant(), 17);
        assert_eq!(sentinels.end_operator_discriminant(), 25);
        assert_eq!(sentinels.entries().len(), 8);
        assert!(matches!(
            sentinels.entries()[0].identity(),
            SemanticSentinelIdentity::BinderArity
        ));
        assert!(matches!(sentinels.entries()[1].identity(), SemanticSentinelIdentity::FieldNone));
        assert!(matches!(
            sentinels.entries()[2].identity(),
            SemanticSentinelIdentity::FieldOpaque
        ));
        assert!(matches!(
            sentinels.entries()[3].identity(),
            SemanticSentinelIdentity::FieldTokenText
        ));
        assert_eq!(
            sentinels.entries()[4].identity(),
            &SemanticSentinelIdentity::OrderedSequence {
                element_category: sequence_category.clone(),
            }
        );
        assert_eq!(
            sentinels.entries()[5].identity(),
            &SemanticSentinelIdentity::Withheld { category: withheld_category }
        );
        assert_eq!(
            sentinels.entries()[6].identity(),
            &SemanticSentinelIdentity::Variable { category: sequence_category.clone() }
        );
        assert_eq!(
            sentinels
                .variable(&sequence_category)
                .map(SemanticSentinel::operator_discriminant),
            Some(23)
        );
        assert_eq!(
            sentinels.entries()[7].identity(),
            &SemanticSentinelIdentity::CollectionPair {
                kind: core::CollectionKind::Map,
                element_category: sequence_category.clone(),
            }
        );
        assert_eq!(
            sentinels
                .collection_pair(core::CollectionKind::Map, &sequence_category)
                .map(SemanticSentinel::operator_discriminant),
            Some(24)
        );
        for (index, sentinel) in sentinels.entries().iter().enumerate() {
            assert_eq!(sentinel.operator_discriminant(), 17 + index as u32);
        }
    }

    #[test]
    fn canonical_signature_and_machine_share_the_generated_layout() {
        let language = fixture();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let artifacts =
            derive_semantic_artifacts(&language, &layout).expect("artifacts must derive");
        let bindings = core::RuntimeCapabilityBindings::default();
        artifacts
            .signature()
            .validate(artifacts.grammar(), &bindings)
            .expect("signature must validate");
        artifacts
            .machine()
            .validate(
                artifacts.signature(),
                artifacts.grammar(),
                &bindings,
                core::SemanticMachineAdmissionLimits::default(),
            )
            .expect("machine must validate");

        assert_eq!(
            artifacts.signature().operators.len(),
            layout
                .categories()
                .iter()
                .flat_map(SemanticCategoryLayout::variants)
                .filter(|variant| variant.operator_discriminant().is_some())
                .count()
        );
        let maybe_index = artifacts
            .signature()
            .operators
            .iter()
            .position(|operator| operator.label.ends_with("::Proc::Maybe"))
            .expect("Maybe operator");
        assert!(matches!(
            artifacts.signature().operators[maybe_index]
                .fields
                .as_slice(),
            [core::SemanticFieldSchemaV1::Optional { .. }]
        ));
        let core::MachineFieldProjectionV1::Optional { none } =
            &artifacts.machine().operators[maybe_index].fields[0]
        else {
            panic!("Maybe must use an exact optional projection")
        };
        assert_eq!(none.fixed_payload_segments, vec![0u32.to_le_bytes().to_vec()]);
        assert!(artifacts.signature().operators.iter().any(|operator| {
            matches!(
                operator.origin,
                core::SemanticOperatorOriginV1::Generated { ref family, .. }
                    if family == "implicit-variable"
            ) && matches!(
                operator.fields.as_slice(),
                [core::SemanticFieldSchemaV1::Variable { .. }]
            )
        }));
        let bag_literal_index = artifacts
            .signature()
            .operators
            .iter()
            .position(|operator| operator.label.ends_with("::Bag::BagLit"))
            .expect("generated BagLit operator");
        assert_eq!(artifacts.signature().operators[bag_literal_index].payload, None);
        assert!(matches!(
            artifacts.signature().operators[bag_literal_index]
                .fields
                .as_slice(),
            [core::SemanticFieldSchemaV1::Collection {
                kind: core::CollectionKind::Bag,
                key: None,
                ..
            }]
        ));
        assert!(matches!(
            artifacts.machine().operators[bag_literal_index]
                .fields
                .as_slice(),
            [core::MachineFieldProjectionV1::InlineValueCollection {
                kind: core::CollectionKind::Bag,
                child_order: core::MachineChildOrderV1::CanonicalExactKey,
            }]
        ));
        let map_literal_index = artifacts
            .signature()
            .operators
            .iter()
            .position(|operator| operator.label.ends_with("::Map::MapLit"))
            .expect("generated MapLit operator");
        assert_eq!(artifacts.signature().operators[map_literal_index].payload, None);
        assert!(matches!(
            artifacts.signature().operators[map_literal_index]
                .fields
                .as_slice(),
            [core::SemanticFieldSchemaV1::Collection {
                kind: core::CollectionKind::Map,
                key: Some(_),
                ..
            }]
        ));
        let [core::MachineFieldProjectionV1::InlinePairCollection {
            kind: core::CollectionKind::Map,
            pair,
            child_order: core::MachineChildOrderV1::Ordered,
        }] = artifacts.machine().operators[map_literal_index]
            .fields
            .as_slice()
        else {
            panic!("MapLit must use the checked inline-pair projection")
        };
        assert_eq!(
            Some(pair.stable_discriminant),
            layout
                .sentinels()
                .collection_pair(
                    core::CollectionKind::Map,
                    &syn::parse_str("Proc").expect("identifier"),
                )
                .map(SemanticSentinel::operator_discriminant)
        );
        let bag_index = artifacts
            .signature()
            .operators
            .iter()
            .position(|operator| operator.label.ends_with("::Proc::PBag"))
            .expect("PBag operator");
        assert!(matches!(
            artifacts.signature().operators[bag_index].fields.as_slice(),
            [core::SemanticFieldSchemaV1::Collection {
                kind: core::CollectionKind::Bag,
                key: None,
                ..
            }]
        ));
        assert!(matches!(
            artifacts.machine().operators[bag_index].fields.as_slice(),
            [core::MachineFieldProjectionV1::InlineValueCollection {
                kind: core::CollectionKind::Bag,
                child_order: core::MachineChildOrderV1::CanonicalExactKey,
            }]
        ));
    }

    #[test]
    fn pathmap_artifact_preserves_mode_and_pair_roles_from_one_collection_census() {
        let language = crate::gen::collection_literal_language_for_tests();
        let layout = SemanticAdapterLayout::derive(&language).expect("layout must derive");
        let artifacts =
            derive_semantic_artifacts(&language, &layout).expect("PathMap artifacts must derive");
        let index = artifacts
            .signature()
            .operators
            .iter()
            .position(|operator| operator.label.ends_with("::Pathmap::PathmapLit"))
            .expect("PathmapLit operator");
        assert!(matches!(
            artifacts.signature().operators[index].fields.as_slice(),
            [core::SemanticFieldSchemaV1::PathMap {
                key: core::CategoryId(0),
                value: core::CategoryId(0),
            }]
        ));
        let [core::MachineFieldProjectionV1::InlinePathMap { empty, set, map, pair }] =
            artifacts.machine().operators[index].fields.as_slice()
        else {
            panic!("PathmapLit must use the exact mode-preserving inline projection")
        };
        let proc_category: Ident = syn::parse_str("Proc").expect("identifier");
        let mode_sentinel = layout
            .sentinels()
            .pathmap_mode(&proc_category)
            .expect("PathMap mode sentinel");
        let pair_sentinel = layout
            .sentinels()
            .pathmap_pair(&proc_category)
            .expect("PathMap pair sentinel");
        assert_eq!(empty.stable_discriminant, mode_sentinel.operator_discriminant());
        assert_eq!(set.stable_discriminant, mode_sentinel.operator_discriminant());
        assert_eq!(map.stable_discriminant, mode_sentinel.operator_discriminant());
        assert_eq!(empty.fixed_payload_segments, vec![vec![0]]);
        assert_eq!(set.fixed_payload_segments, vec![vec![1]]);
        assert_eq!(map.fixed_payload_segments, vec![vec![2]]);
        assert_eq!(pair.stable_discriminant, pair_sentinel.operator_discriminant());
        assert!(pair.fixed_payload_segments.is_empty());
    }
}
