//! Verified, authority-free execution images for runtime-defined GSLTs.
//!
//! [`TheoryCoreV1`](crate::TheoryCoreV1) is authoritative.  A
//! [`TheorySemanticImageV1`] is a replaceable cache artifact that resolves
//! source names to dense identifiers, normalizes rule terms to a closed
//! polynomial operator language, and carries an independently checkable
//! set-automaton quotient for positional left-hand sides.  The complete rule
//! programs remain present, so collection remainders and other generalized
//! patterns do not disappear when they are outside the positional quotient.
//!
//! All arenas are flat and backward-referencing.  Validation and automaton
//! correspondence checks use explicit worklists, keeping admission independent
//! of the native call stack.  The image contains rights *requirements* only;
//! authority is supplied separately by an installed language handle.

use crate::{
    CategoryId, CollectionKind, ConstructorId, JudgmentAtomV1, JudgmentDecisionV1, JudgmentRuleV1,
    LanguageCoreV1, LanguageRights, PathMapModeV1, SemanticActionExecutionV1,
    SemanticEffectClassV1, SemanticNormalizationBranchingV1, TheoryCoreV1, TheoryIntrinsicV1,
    TheoryLiteralCarrierV1, TheoryLiteralV1, TheoryPremiseFormV1, TheoryRuleArenaV1,
    TheoryRuleReferenceV1, TheorySortKindV1, TheoryTermFormV1, TheoryTermId, TheoryVariableId,
    TheoryVariableRoleV1,
};
use mettail_semantic_key::{write_framed, SemanticHash};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub const THEORY_SEMANTIC_IMAGE_ABI_V1: u16 = 1;
pub const THEORY_SEMANTIC_IMAGE_ABI_V2: u16 = 2;
pub const THEORY_SEMANTIC_IMAGE_ABI_V3: u16 = 3;
pub const THEORY_SEMANTIC_IMAGE_ABI_V4: u16 = 4;
pub const THEORY_SEMANTIC_IMAGE_ABI_CURRENT: u16 = THEORY_SEMANTIC_IMAGE_ABI_V4;
pub const THEORY_IMAGE_COMPILER_ABI_V1: u16 = 1;
pub const THEORY_IMAGE_COMPILER_ABI_V2: u16 = 2;
pub const THEORY_IMAGE_COMPILER_ABI_V3: u16 = 3;
pub const THEORY_IMAGE_COMPILER_ABI_V4: u16 = 4;
pub const THEORY_IMAGE_COMPILER_ABI_CURRENT: u16 = THEORY_IMAGE_COMPILER_ABI_V4;

macro_rules! image_id {
    ($name:ident) => {
        #[derive(
            Clone,
            Copy,
            Debug,
            Default,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            Hash,
            Serialize,
            Deserialize,
        )]
        pub struct $name(pub u32);
    };
}

image_id!(TheorySortId);
image_id!(TheoryConstructorId);
image_id!(TheoryJudgmentId);
image_id!(TheoryEffectId);
image_id!(TheoryActionId);
image_id!(TheoryRuleProgramId);
image_id!(TheoryJudgmentRuleProgramId);
image_id!(TheoryPatternStateId);
image_id!(TheoryPatternEntryId);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheorySortImageV1 {
    pub id: TheorySortId,
    pub kind: TheorySortKindImageV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheorySortKindImageV1 {
    Syntax {
        literal: Option<TheoryLiteralCarrierV1>,
    },
    Collection {
        kind: CollectionKind,
        key: Option<TheorySortId>,
        element: TheorySortId,
    },
    Function {
        domain: TheorySortId,
        codomain: TheorySortId,
        multiple: bool,
    },
    Product {
        factors: Vec<TheorySortId>,
    },
    Opaque {
        abi: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryConstructorImageV1 {
    pub id: TheoryConstructorId,
    pub domain: Vec<TheorySortId>,
    pub codomain: TheorySortId,
    /// The parsed semantic constructor when this theory constructor is part of
    /// the concrete grammar.  Internal semantic constructors may leave it
    /// absent, but the compiler must never invent a grammar binding.
    pub grammar: Option<TheoryGrammarConstructorV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryGrammarConstructorV1 {
    pub category: CategoryId,
    pub constructor: ConstructorId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TheoryImageOperatorV1 {
    Constructor(TheoryConstructorId),
    Abstraction {
        sort: TheorySortId,
    },
    Substitution {
        sort: TheorySortId,
        function: TheorySortId,
    },
    Collection {
        sort: TheorySortId,
        element: TheorySortId,
        kind: CollectionKind,
    },
    Product {
        sort: TheorySortId,
    },
    Literal {
        sort: TheorySortId,
        value: TheoryLiteralV1,
    },
    /// Synthetic root used only to match a relational judgment conclusion.
    /// It is never a language term and carries no authority or executable
    /// callback; the exact child arity is checked against the declaration.
    Judgment {
        judgment: TheoryJudgmentId,
    },
    /// Derived structural marker used by the generalized collection matcher
    /// to preserve a PathMap's explicit mode in residual rows.
    PathMapMode {
        sort: TheorySortId,
        mode: PathMapModeV1,
    },
}

// SAFETY: the leading variant tag is injective; every fixed-width identifier
// uses its complete little-endian representation; and every variable-width
// literal payload is length-framed.  This stream therefore agrees exactly
// with the derived `Eq`/`Hash` implementation, including literal spelling.
unsafe impl SemanticHash for TheoryImageOperatorV1 {
    fn write_content(&self, output: &mut Vec<u8>) {
        match self {
            Self::Constructor(constructor) => {
                output.push(0);
                output.extend_from_slice(&constructor.0.to_le_bytes());
            },
            Self::Abstraction { sort } => {
                output.push(1);
                output.extend_from_slice(&sort.0.to_le_bytes());
            },
            Self::Substitution { sort, function } => {
                output.push(2);
                output.extend_from_slice(&sort.0.to_le_bytes());
                output.extend_from_slice(&function.0.to_le_bytes());
            },
            Self::Collection { sort, element, kind } => {
                output.push(3);
                output.extend_from_slice(&sort.0.to_le_bytes());
                output.extend_from_slice(&element.0.to_le_bytes());
                output.push(match kind {
                    CollectionKind::Bag => 0,
                    CollectionKind::Set => 1,
                    CollectionKind::List => 2,
                    CollectionKind::Map => 3,
                    CollectionKind::PathMap => 4,
                });
            },
            Self::Product { sort } => {
                output.push(4);
                output.extend_from_slice(&sort.0.to_le_bytes());
            },
            Self::Literal { sort, value } => {
                output.push(5);
                output.extend_from_slice(&sort.0.to_le_bytes());
                match value {
                    TheoryLiteralV1::String(value) => {
                        output.push(0);
                        write_framed(output, value.as_bytes());
                    },
                    TheoryLiteralV1::Bytes(value) => {
                        output.push(1);
                        write_framed(output, value);
                    },
                    TheoryLiteralV1::Integer(value) => {
                        output.push(2);
                        output.extend_from_slice(&value.to_le_bytes());
                    },
                    TheoryLiteralV1::FloatBits(value) => {
                        output.push(3);
                        output.extend_from_slice(&value.to_le_bytes());
                    },
                    TheoryLiteralV1::Boolean(value) => {
                        output.push(4);
                        output.push(u8::from(*value));
                    },
                    TheoryLiteralV1::Unit => output.push(5),
                }
            },
            Self::Judgment { judgment } => {
                output.push(6);
                output.extend_from_slice(&judgment.0.to_le_bytes());
            },
            Self::PathMapMode { sort, mode } => {
                output.push(7);
                output.extend_from_slice(&sort.0.to_le_bytes());
                output.push(match mode {
                    PathMapModeV1::NeutralEmpty => 0,
                    PathMapModeV1::Set => 1,
                    PathMapModeV1::Map => 2,
                });
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryImageVariableV1 {
    pub id: TheoryVariableId,
    pub sort: TheorySortId,
    pub role: TheoryVariableRoleV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryImageTermNodeV1 {
    pub sort: TheorySortId,
    pub form: TheoryImageTermFormV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryImageTermFormV1 {
    Slot(TheoryVariableId),
    Apply {
        operator: TheoryImageOperatorV1,
        arguments: Vec<TheoryTermId>,
        /// Variable-valued structural children.  The canonical order is slots
        /// first, followed by `arguments`.
        slots: Vec<TheoryVariableId>,
        /// A collection-tail binding.  Its matching law depends on the
        /// collection kind, so it is not disguised as a positional child.
        remainder: Option<TheoryVariableId>,
        /// Exact PathMap mode evidence. `None` is mode-polymorphic and must
        /// acquire a canonical marker from a remainder during construction.
        #[serde(default)]
        pathmap_mode: Option<PathMapModeV1>,
    },
    /// Rule-only collection comprehension. `sources.len() == 1` is map;
    /// `sources.len() >= 2` is exact zip followed by map. It never has a
    /// runtime operator encoding and cannot enter the semantic e-graph.
    Map {
        sources: Vec<TheoryTermId>,
        parameters: Vec<TheoryVariableId>,
        body: TheoryTermId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryImagePremiseNodeV1 {
    pub form: TheoryImagePremiseFormV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryImagePremiseFormV1 {
    Freshness {
        variable: TheoryVariableId,
        target: TheoryVariableId,
        remainder: bool,
    },
    Transition {
        source: TheoryVariableId,
        target: TheoryVariableId,
    },
    Judgment {
        judgment: TheoryJudgmentId,
        terms: Vec<TheoryTermId>,
    },
    ForAll {
        collection: TheoryVariableId,
        parameter: TheoryVariableId,
        body: u32,
    },
    Intrinsic(TheoryImageIntrinsicV1),
    /// The guard value remains in the authoritative TheoryCore.  This exact
    /// commitment prevents substitution while keeping the executable image
    /// flat and allocation-bounded.
    Guard {
        commitment: [u8; 32],
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryImageIntrinsicV1 {
    ExactTermEq {
        left: TheoryVariableId,
        right: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8AtEnd {
        text: TheoryVariableId,
        cursor: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8ScalarAt {
        text: TheoryVariableId,
        cursor: TheoryVariableId,
        scalar: TheoryVariableId,
        next_cursor: TheoryVariableId,
    },
    Utf8Slice {
        text: TheoryVariableId,
        start: TheoryVariableId,
        end: TheoryVariableId,
        output: TheoryVariableId,
    },
    CheckedNatAdd {
        left: TheoryVariableId,
        right: TheoryVariableId,
        output: TheoryVariableId,
    },
    Utf8ConcatMany {
        pieces: TheoryVariableId,
        output: TheoryVariableId,
    },
}

impl TheoryImageIntrinsicV1 {
    pub fn for_each_variable(&self, mut visit: impl FnMut(TheoryVariableId)) {
        match self {
            Self::ExactTermEq { left, right, output }
            | Self::CheckedNatAdd { left, right, output } => {
                visit(*left);
                visit(*right);
                visit(*output);
            },
            Self::Utf8AtEnd { text, cursor, output } => {
                visit(*text);
                visit(*cursor);
                visit(*output);
            },
            Self::Utf8ScalarAt { text, cursor, scalar, next_cursor } => {
                visit(*text);
                visit(*cursor);
                visit(*scalar);
                visit(*next_cursor);
            },
            Self::Utf8Slice { text, start, end, output } => {
                visit(*text);
                visit(*start);
                visit(*end);
                visit(*output);
            },
            Self::Utf8ConcatMany { pieces, output } => {
                visit(*pieces);
                visit(*output);
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryRuleDirectionV1 {
    Forward,
    Reverse,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryRuleOriginV1 {
    Equation {
        source: u32,
        direction: TheoryRuleDirectionV1,
    },
    Rewrite {
        source: u32,
    },
}

/// The executable disposition of one declared rule orientation.
///
/// Every source orientation remains visible in the image.  An unsafe
/// match-everything orientation or an orientation whose premises/template are
/// not closed under its left-hand side is recorded, never silently discarded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryRuleDispositionV1 {
    Executable,
    Suppressed(TheoryRuleSuppressionV1),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryRuleSuppressionV1 {
    MatchAllRoot,
    PremiseDependency { variable: TheoryVariableId },
    UnboundTemplate { variable: TheoryVariableId },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryWorkChargeV1 {
    pub pattern_nodes: u32,
    pub template_nodes: u32,
    pub premise_nodes: u32,
    pub variable_slots: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryRuleProgramV1 {
    pub id: TheoryRuleProgramId,
    pub origin: TheoryRuleOriginV1,
    pub disposition: TheoryRuleDispositionV1,
    pub name: String,
    pub variables: Vec<TheoryImageVariableV1>,
    pub terms: Vec<TheoryImageTermNodeV1>,
    pub premises: Vec<TheoryImagePremiseNodeV1>,
    pub premise_roots: Vec<u32>,
    pub left: TheoryTermId,
    pub right: TheoryTermId,
    pub charge: TheoryWorkChargeV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryImageJudgmentAtomV1 {
    pub judgment: TheoryJudgmentId,
    pub terms: Vec<TheoryTermId>,
}

/// One source-exact Horn clause. Terms are kept in a flat, backward-pointing
/// arena and premise order is semantic order. Runtime proof search owns the
/// substitution and explores these programs with the same bounded FIFO
/// frontier used for rewrite premises.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryJudgmentRuleProgramV1 {
    pub id: TheoryJudgmentRuleProgramId,
    pub owner: TheoryJudgmentId,
    pub name: String,
    pub variables: Vec<TheoryImageVariableV1>,
    pub terms: Vec<TheoryImageTermNodeV1>,
    pub premises: Vec<TheoryImageJudgmentAtomV1>,
    pub conclusion: TheoryImageJudgmentAtomV1,
    pub charge: TheoryWorkChargeV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryJudgmentImageV1 {
    pub id: TheoryJudgmentId,
    pub arguments: Vec<TheorySortId>,
    pub decision: JudgmentDecisionV1,
    pub rules: Vec<TheoryJudgmentRuleProgramId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryPatternInvocationV1 {
    pub state: TheoryPatternStateId,
    /// Child-local slot -> parent-local slot.
    pub parent_slots: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryPatternStateV1 {
    pub id: TheoryPatternStateId,
    pub slot_count: u32,
    pub form: TheoryPatternStateFormV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryPatternStateFormV1 {
    Bind,
    Apply {
        operator: TheoryImageOperatorV1,
        arguments: Vec<TheoryPatternInvocationV1>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryPatternEntryV1 {
    pub id: TheoryPatternEntryId,
    pub rule: TheoryRuleProgramId,
    pub root: TheoryPatternStateId,
    /// Root-local slot -> rule variable.
    pub slot_variables: Vec<TheoryVariableId>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryPatternAutomatonV1 {
    pub states: Vec<TheoryPatternStateV1>,
    pub entries: Vec<TheoryPatternEntryV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryJudgmentPatternEntryV1 {
    pub id: TheoryPatternEntryId,
    pub rule: TheoryJudgmentRuleProgramId,
    pub root: TheoryPatternStateId,
    /// Root-local slot -> judgment-clause variable.
    pub slot_variables: Vec<TheoryVariableId>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryJudgmentPatternAutomatonV1 {
    pub states: Vec<TheoryPatternStateV1>,
    pub entries: Vec<TheoryJudgmentPatternEntryV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryActionImageV1 {
    pub id: TheoryActionId,
    pub domain: Vec<TheorySortId>,
    pub codomain: TheorySortId,
    pub transitions: Vec<TheoryRuleProgramId>,
    pub effect: TheoryEffectId,
    pub effect_class: SemanticEffectClassV1,
    /// Declarative demand only.  It is intersected with an independently
    /// supplied handle grant before the kernel can run.
    pub required_rights: LanguageRights,
    pub grade: TheorySortId,
    pub execution: TheoryActionExecutionImageV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryActionExecutionImageV1 {
    OneStep,
    Normalize {
        relation_sort: TheorySortId,
        terminal_constructors: Vec<TheoryConstructorId>,
        branching: SemanticNormalizationBranchingV1,
    },
}

/// Whether the authoritative theory carries the checked additional structure
/// required by `Cost(G)`.  This is independent of [`SemanticEffectClassV1`]:
/// purity constrains observable effects, not semantic resource consumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TheoryResourceProfileV1 {
    /// The base theory has no semantic resource grade. Host execution may
    /// still consume and be charged for ordinary machine resources.
    Uncosted,
    /// The theory is a checked `Cost(G)` presentation. Every successful
    /// transition requires grade evidence in this exact sort from a separately
    /// verified cost image.
    Costed { grade_sort: TheorySortId },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheorySemanticImageV1 {
    pub abi: u16,
    pub compiler_abi: u16,
    pub language_fingerprint: [u8; 32],
    pub grammar_fingerprint: [u8; 32],
    pub theory_fingerprint: [u8; 32],
    pub resource_profile: TheoryResourceProfileV1,
    pub sorts: Vec<TheorySortImageV1>,
    pub constructors: Vec<TheoryConstructorImageV1>,
    pub rules: Vec<TheoryRuleProgramV1>,
    pub patterns: TheoryPatternAutomatonV1,
    pub judgments: Vec<TheoryJudgmentImageV1>,
    pub judgment_rules: Vec<TheoryJudgmentRuleProgramV1>,
    pub judgment_patterns: TheoryJudgmentPatternAutomatonV1,
    pub actions: Vec<TheoryActionImageV1>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TheoryImageAdmissionLimits {
    pub max_encoded_bytes: usize,
    pub max_sorts: usize,
    pub max_constructors: usize,
    pub max_judgments: usize,
    pub max_effects: usize,
    pub max_rules: usize,
    pub max_actions: usize,
    pub max_total_sort_references: usize,
    pub max_total_sort_metadata_bytes: usize,
    pub max_total_constructor_arguments: usize,
    pub max_total_action_arguments: usize,
    pub max_total_action_terminal_constructors: usize,
    pub max_total_rule_variables: usize,
    pub max_total_term_nodes: usize,
    pub max_total_term_references: usize,
    pub max_total_premise_nodes: usize,
    pub max_total_premise_roots: usize,
    pub max_total_name_bytes: usize,
    pub max_total_literal_bytes: usize,
    pub max_total_guard_nodes: usize,
    pub max_total_guard_bytes: usize,
    pub max_total_action_transitions: usize,
    pub max_automaton_states: usize,
    pub max_automaton_entries: usize,
    pub max_automaton_edges: usize,
    pub max_automaton_slot_references: usize,
    pub max_automaton_checks: usize,
}

impl Default for TheoryImageAdmissionLimits {
    fn default() -> Self {
        Self {
            max_encoded_bytes: 64 * 1024 * 1024,
            max_sorts: 1_000_000,
            max_constructors: 1_000_000,
            max_judgments: 1_000_000,
            max_effects: 1_000_000,
            max_rules: 1_000_000,
            max_actions: 1_000_000,
            max_total_sort_references: 10_000_000,
            max_total_sort_metadata_bytes: 64 * 1024 * 1024,
            max_total_constructor_arguments: 10_000_000,
            max_total_action_arguments: 10_000_000,
            max_total_action_terminal_constructors: 10_000_000,
            max_total_rule_variables: 10_000_000,
            max_total_term_nodes: 10_000_000,
            max_total_term_references: 20_000_000,
            max_total_premise_nodes: 10_000_000,
            max_total_premise_roots: 10_000_000,
            max_total_name_bytes: 64 * 1024 * 1024,
            max_total_literal_bytes: 64 * 1024 * 1024,
            max_total_guard_nodes: 10_000_000,
            max_total_guard_bytes: 64 * 1024 * 1024,
            max_total_action_transitions: 10_000_000,
            max_automaton_states: 10_000_000,
            max_automaton_entries: 1_000_000,
            max_automaton_edges: 20_000_000,
            max_automaton_slot_references: 20_000_000,
            max_automaton_checks: 50_000_000,
        }
    }
}

impl TheoryImageAdmissionLimits {
    /// Preflight the complete source expansion before an image compiler clones
    /// any rule arena or allocates automaton state.  Equation orientations are
    /// counted separately because both remain auditable image programs even
    /// when one is explicitly suppressed.
    pub fn validate_source(self, language: &LanguageCoreV1) -> Result<(), TheoryImageError> {
        language
            .validate()
            .map_err(|errors| TheoryImageError::InvalidLanguage(format!("{errors:?}")))?;
        enforce(language.theory.sorts.len(), self.max_sorts, "sorts")?;
        enforce(language.theory.constructors.len(), self.max_constructors, "constructors")?;
        enforce(language.theory.judgments.len(), self.max_judgments, "judgments")?;
        enforce(language.theory.effects.len(), self.max_effects, "effects")?;
        enforce(language.theory.actions.len(), self.max_actions, "actions")?;
        let mut sort_references = 0usize;
        let mut sort_metadata_bytes = 0usize;
        for sort in &language.theory.sorts {
            match &sort.kind {
                TheorySortKindV1::Syntax {
                    literal:
                        Some(
                            TheoryLiteralCarrierV1::External(value)
                            | TheoryLiteralCarrierV1::HostOpaque(value),
                        ),
                } => {
                    sort_metadata_bytes = checked_total(
                        sort_metadata_bytes,
                        value.len(),
                        self.max_total_sort_metadata_bytes,
                        "sort metadata bytes",
                    )?;
                },
                TheorySortKindV1::Syntax { .. } => {},
                TheorySortKindV1::Collection { key, .. } => {
                    sort_references = checked_total(
                        sort_references,
                        1usize
                            .checked_add(usize::from(key.is_some()))
                            .ok_or(TheoryImageError::LengthOverflow)?,
                        self.max_total_sort_references,
                        "sort references",
                    )?;
                },
                TheorySortKindV1::Function { .. } => {
                    sort_references = checked_total(
                        sort_references,
                        2,
                        self.max_total_sort_references,
                        "sort references",
                    )?;
                },
                TheorySortKindV1::Product { factors } => {
                    sort_references = checked_total(
                        sort_references,
                        factors.len(),
                        self.max_total_sort_references,
                        "sort references",
                    )?;
                },
                TheorySortKindV1::Opaque { abi } => {
                    sort_metadata_bytes = checked_total(
                        sort_metadata_bytes,
                        abi.len(),
                        self.max_total_sort_metadata_bytes,
                        "sort metadata bytes",
                    )?;
                },
            }
        }
        let rule_count = language
            .theory
            .equations
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(language.theory.rewrites.len()))
            .ok_or(TheoryImageError::LengthOverflow)?;
        let judgment_rule_count =
            language
                .theory
                .judgments
                .iter()
                .try_fold(0usize, |count, judgment| {
                    count
                        .checked_add(judgment.rules.len())
                        .ok_or(TheoryImageError::LengthOverflow)
                })?;
        let total_rule_count = rule_count
            .checked_add(judgment_rule_count)
            .ok_or(TheoryImageError::LengthOverflow)?;
        enforce(total_rule_count, self.max_rules, "rules")?;
        enforce(total_rule_count, self.max_automaton_entries, "automaton entries")?;

        let mut totals = SourceImageTotals::default();
        for constructor in &language.theory.constructors {
            totals.constructor_arguments = checked_total(
                totals.constructor_arguments,
                constructor.domain.len(),
                self.max_total_constructor_arguments,
                "constructor arguments",
            )?;
        }
        for equation in &language.theory.equations {
            account_source_arena(&equation.arena, equation.name.len(), 2, self, &mut totals)?;
        }
        for rewrite in &language.theory.rewrites {
            account_source_arena(&rewrite.arena, rewrite.name.len(), 1, self, &mut totals)?;
        }
        for judgment in &language.theory.judgments {
            for rule in &judgment.rules {
                account_source_judgment_rule(rule, self, &mut totals)?;
            }
        }
        for action in &language.theory.actions {
            totals.action_arguments = checked_total(
                totals.action_arguments,
                action.domain.len(),
                self.max_total_action_arguments,
                "action arguments",
            )?;
            if let SemanticActionExecutionV1::Normalize { terminal_constructors, .. } =
                &action.execution
            {
                totals.action_terminal_constructors = checked_total(
                    totals.action_terminal_constructors,
                    terminal_constructors.len(),
                    self.max_total_action_terminal_constructors,
                    "action terminal constructors",
                )?;
            }
            let count = match &action.transition {
                TheoryRuleReferenceV1::Equation(name) => language
                    .theory
                    .equations
                    .iter()
                    .filter(|rule| rule.name == *name)
                    .count()
                    .checked_mul(2)
                    .ok_or(TheoryImageError::LengthOverflow)?,
                TheoryRuleReferenceV1::Rewrite(name) => language
                    .theory
                    .rewrites
                    .iter()
                    .filter(|rule| rule.name == *name)
                    .count(),
                TheoryRuleReferenceV1::Handler(_) => {
                    return Err(TheoryImageError::SourceMismatch {
                        kind: "runtime handler",
                        index: u32::MAX,
                    });
                },
            };
            totals.action_transitions = checked_total(
                totals.action_transitions,
                count,
                self.max_total_action_transitions,
                "action transitions",
            )?;
        }
        Ok(())
    }
}

#[derive(Default)]
struct SourceImageTotals {
    constructor_arguments: usize,
    action_arguments: usize,
    action_terminal_constructors: usize,
    variables: usize,
    terms: usize,
    term_references: usize,
    premises: usize,
    premise_roots: usize,
    names: usize,
    literals: usize,
    guard_nodes: usize,
    guard_bytes: usize,
    automaton_states: usize,
    automaton_edges: usize,
    automaton_slot_references: usize,
    action_transitions: usize,
}

fn account_source_arena(
    arena: &TheoryRuleArenaV1,
    name_bytes: usize,
    orientations: usize,
    limits: TheoryImageAdmissionLimits,
    totals: &mut SourceImageTotals,
) -> Result<(), TheoryImageError> {
    let scaled = |value: usize| {
        value
            .checked_mul(orientations)
            .ok_or(TheoryImageError::LengthOverflow)
    };
    totals.variables = checked_total(
        totals.variables,
        scaled(arena.variables.len())?,
        limits.max_total_rule_variables,
        "rule variables",
    )?;
    totals.terms = checked_total(
        totals.terms,
        scaled(arena.terms.len())?,
        limits.max_total_term_nodes,
        "term nodes",
    )?;
    totals.premises = checked_total(
        totals.premises,
        scaled(arena.premises.len())?,
        limits.max_total_premise_nodes,
        "premise nodes",
    )?;
    totals.premise_roots = checked_total(
        totals.premise_roots,
        scaled(arena.premise_roots.len())?,
        limits.max_total_premise_roots,
        "premise roots",
    )?;
    totals.names = checked_total(
        totals.names,
        scaled(name_bytes)?,
        limits.max_total_name_bytes,
        "name bytes",
    )?;

    let mut slot_occurrences = 0usize;
    let mut child_edges = 0usize;
    for term in &arena.terms {
        let (children, slots) = match &term.form {
            TheoryTermFormV1::Variable(_) => (0, 0),
            TheoryTermFormV1::Constructor { arguments, .. } => (arguments.len(), 0),
            TheoryTermFormV1::Abstraction { .. } => (1, 1),
            TheoryTermFormV1::Substitution { .. } => (2, 0),
            TheoryTermFormV1::Collection { elements, remainder, .. } => {
                (elements.len(), usize::from(remainder.is_some()))
            },
            TheoryTermFormV1::Map { sources, parameters, .. } => {
                (sources.len().saturating_add(1), parameters.len())
            },
            TheoryTermFormV1::Product { factors } => (factors.len(), 0),
            TheoryTermFormV1::Literal(value) => {
                totals.literals = checked_total(
                    totals.literals,
                    scaled(literal_bytes(value))?,
                    limits.max_total_literal_bytes,
                    "literal bytes",
                )?;
                (0, 0)
            },
        };
        child_edges = child_edges
            .checked_add(children)
            .and_then(|total| total.checked_add(slots))
            .ok_or(TheoryImageError::LengthOverflow)?;
        slot_occurrences = slot_occurrences
            .checked_add(slots)
            .ok_or(TheoryImageError::LengthOverflow)?;
    }
    totals.automaton_states = checked_total(
        totals.automaton_states,
        scaled(
            arena
                .terms
                .len()
                .checked_add(slot_occurrences)
                .ok_or(TheoryImageError::LengthOverflow)?,
        )?,
        limits.max_automaton_states,
        "automaton states",
    )?;
    totals.automaton_edges = checked_total(
        totals.automaton_edges,
        scaled(child_edges)?,
        limits.max_automaton_edges,
        "automaton edges",
    )?;
    let slot_reference_upper = arena
        .terms
        .len()
        .checked_add(slot_occurrences)
        .and_then(|states| states.checked_mul(arena.variables.len()))
        .and_then(|references| references.checked_add(arena.variables.len()))
        .ok_or(TheoryImageError::LengthOverflow)?;
    totals.automaton_slot_references = checked_total(
        totals.automaton_slot_references,
        scaled(slot_reference_upper)?,
        limits.max_automaton_slot_references,
        "automaton slot references",
    )?;

    let mut term_references = child_edges;
    for premise in &arena.premises {
        match &premise.form {
            TheoryPremiseFormV1::Judgment(atom) => {
                term_references = term_references
                    .checked_add(atom.terms.len())
                    .ok_or(TheoryImageError::LengthOverflow)?;
            },
            TheoryPremiseFormV1::Guard(value) => {
                let (nodes, bytes) = canonical_guard_footprint(value, limits)?;
                totals.guard_nodes = checked_total(
                    totals.guard_nodes,
                    scaled(nodes)?,
                    limits.max_total_guard_nodes,
                    "guard nodes",
                )?;
                totals.guard_bytes = checked_total(
                    totals.guard_bytes,
                    scaled(bytes)?,
                    limits.max_total_guard_bytes,
                    "guard bytes",
                )?;
            },
            TheoryPremiseFormV1::Freshness { .. }
            | TheoryPremiseFormV1::Transition { .. }
            | TheoryPremiseFormV1::ForAll { .. }
            | TheoryPremiseFormV1::Intrinsic(_) => {},
        }
    }
    totals.term_references = checked_total(
        totals.term_references,
        scaled(term_references)?,
        limits.max_total_term_references,
        "term references",
    )?;
    Ok(())
}

fn account_source_judgment_rule(
    rule: &JudgmentRuleV1,
    limits: TheoryImageAdmissionLimits,
    totals: &mut SourceImageTotals,
) -> Result<(), TheoryImageError> {
    totals.variables = checked_total(
        totals.variables,
        rule.variables.len(),
        limits.max_total_rule_variables,
        "rule variables",
    )?;
    totals.terms =
        checked_total(totals.terms, rule.terms.len(), limits.max_total_term_nodes, "term nodes")?;
    totals.premises = checked_total(
        totals.premises,
        rule.premises.len(),
        limits.max_total_premise_nodes,
        "premise nodes",
    )?;
    totals.names =
        checked_total(totals.names, rule.name.len(), limits.max_total_name_bytes, "name bytes")?;

    let mut child_edges = 0usize;
    let mut slot_occurrences = 0usize;
    for term in &rule.terms {
        let (children, slots) = match &term.form {
            TheoryTermFormV1::Variable(_) => (0, 0),
            TheoryTermFormV1::Constructor { arguments, .. } => (arguments.len(), 0),
            TheoryTermFormV1::Abstraction { .. } => (1, 1),
            TheoryTermFormV1::Substitution { .. } => (2, 0),
            TheoryTermFormV1::Collection { elements, remainder, .. } => {
                (elements.len(), usize::from(remainder.is_some()))
            },
            TheoryTermFormV1::Map { sources, parameters, .. } => {
                (sources.len().saturating_add(1), parameters.len())
            },
            TheoryTermFormV1::Product { factors } => (factors.len(), 0),
            TheoryTermFormV1::Literal(value) => {
                totals.literals = checked_total(
                    totals.literals,
                    literal_bytes(value),
                    limits.max_total_literal_bytes,
                    "literal bytes",
                )?;
                (0, 0)
            },
        };
        child_edges = child_edges
            .checked_add(children)
            .and_then(|count| count.checked_add(slots))
            .ok_or(TheoryImageError::LengthOverflow)?;
        slot_occurrences = slot_occurrences
            .checked_add(slots)
            .ok_or(TheoryImageError::LengthOverflow)?;
    }
    let atom_references = rule
        .premises
        .iter()
        .chain(std::iter::once(&rule.conclusion))
        .try_fold(0usize, |count, atom| {
            count
                .checked_add(atom.terms.len())
                .ok_or(TheoryImageError::LengthOverflow)
        })?;
    totals.term_references = checked_total(
        totals.term_references,
        child_edges
            .checked_add(atom_references)
            .ok_or(TheoryImageError::LengthOverflow)?,
        limits.max_total_term_references,
        "term references",
    )?;
    totals.automaton_states = checked_total(
        totals.automaton_states,
        rule.terms
            .len()
            .checked_add(slot_occurrences)
            .and_then(|count| count.checked_add(1))
            .ok_or(TheoryImageError::LengthOverflow)?,
        limits.max_automaton_states,
        "automaton states",
    )?;
    totals.automaton_edges = checked_total(
        totals.automaton_edges,
        child_edges
            .checked_add(rule.conclusion.terms.len())
            .ok_or(TheoryImageError::LengthOverflow)?,
        limits.max_automaton_edges,
        "automaton edges",
    )?;
    let slot_reference_upper = rule
        .terms
        .len()
        .checked_add(slot_occurrences)
        .and_then(|states| states.checked_mul(rule.variables.len()))
        .and_then(|references| references.checked_add(rule.variables.len()))
        .ok_or(TheoryImageError::LengthOverflow)?;
    totals.automaton_slot_references = checked_total(
        totals.automaton_slot_references,
        slot_reference_upper,
        limits.max_automaton_slot_references,
        "automaton slot references",
    )?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryImageError {
    InvalidLanguage(String),
    UnsupportedAbi(u16),
    UnsupportedCompilerAbi(u16),
    Fingerprint(String),
    FingerprintMismatch(&'static str),
    LimitExceeded(&'static str),
    LengthOverflow,
    NonDenseId {
        kind: &'static str,
        expected: u32,
        actual: u32,
    },
    SourceMismatch {
        kind: &'static str,
        index: u32,
    },
    UnknownReference {
        kind: &'static str,
        owner: u32,
        target: u32,
    },
    ForwardReference {
        kind: &'static str,
        owner: u32,
        target: u32,
    },
    DuplicateReference {
        kind: &'static str,
        owner: u32,
        target: u32,
    },
    AutomatonCoverage {
        rule: u32,
        actual: usize,
    },
    AutomatonShape {
        entry: u32,
    },
    Allocation,
    InvalidMagic,
    InvalidTag(u8),
    InvalidUtf8,
    Truncated,
    TrailingBytes,
}

impl TheorySemanticImageV1 {
    pub fn validate(
        &self,
        language: &LanguageCoreV1,
        limits: TheoryImageAdmissionLimits,
    ) -> Result<(), TheoryImageError> {
        limits.validate_source(language)?;
        if self.abi != THEORY_SEMANTIC_IMAGE_ABI_CURRENT {
            return Err(TheoryImageError::UnsupportedAbi(self.abi));
        }
        if self.compiler_abi != THEORY_IMAGE_COMPILER_ABI_CURRENT {
            return Err(TheoryImageError::UnsupportedCompilerAbi(self.compiler_abi));
        }
        check_fingerprint(
            self.language_fingerprint,
            language
                .fingerprint()
                .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
            "language",
        )?;
        check_fingerprint(
            self.grammar_fingerprint,
            language
                .grammar_fingerprint()
                .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
            "grammar",
        )?;
        check_fingerprint(
            self.theory_fingerprint,
            language
                .theory_fingerprint()
                .map_err(|error| TheoryImageError::Fingerprint(error.to_string()))?,
            "theory",
        )?;

        enforce(self.sorts.len(), limits.max_sorts, "sorts")?;
        enforce(self.constructors.len(), limits.max_constructors, "constructors")?;
        enforce(self.judgments.len(), limits.max_judgments, "judgments")?;
        enforce(
            self.rules
                .len()
                .checked_add(self.judgment_rules.len())
                .ok_or(TheoryImageError::LengthOverflow)?,
            limits.max_rules,
            "rules",
        )?;
        enforce(self.actions.len(), limits.max_actions, "actions")?;
        validate_image_totals(self, limits)?;
        enforce(
            crate::theory_image_codec::encoded_theory_image_len(self)?,
            limits.max_encoded_bytes,
            "encoded bytes",
        )?;
        enforce(
            self.patterns
                .states
                .len()
                .checked_add(self.judgment_patterns.states.len())
                .ok_or(TheoryImageError::LengthOverflow)?,
            limits.max_automaton_states,
            "automaton states",
        )?;
        enforce(
            self.patterns
                .entries
                .len()
                .checked_add(self.judgment_patterns.entries.len())
                .ok_or(TheoryImageError::LengthOverflow)?,
            limits.max_automaton_entries,
            "automaton entries",
        )?;

        let context = ImageSourceContext::new(&language.theory)?;
        let expected_resource_profile = match &language.theory.cost {
            None => TheoryResourceProfileV1::Uncosted,
            Some(cost) => TheoryResourceProfileV1::Costed {
                grade_sort: context.sort(&cost.signature_sort)?,
            },
        };
        if self.resource_profile != expected_resource_profile {
            return Err(TheoryImageError::SourceMismatch { kind: "resource profile", index: 0 });
        }
        validate_sorts(self, language, &context)?;
        validate_constructors(self, language, &context)?;
        validate_rules(self, language, &context)?;
        validate_judgments(self, language, &context)?;
        validate_actions(self, language, &context)?;
        validate_pattern_automaton(self, limits)?;
        validate_judgment_pattern_automaton(self, limits)?;
        Ok(())
    }
}

struct ImageSourceContext<'a> {
    theory: &'a TheoryCoreV1,
    sorts: BTreeMap<&'a str, TheorySortId>,
    constructors: BTreeMap<&'a str, TheoryConstructorId>,
    judgments: BTreeMap<&'a str, TheoryJudgmentId>,
    effects: BTreeMap<&'a str, TheoryEffectId>,
}

impl<'a> ImageSourceContext<'a> {
    fn new(theory: &'a TheoryCoreV1) -> Result<Self, TheoryImageError> {
        Ok(Self {
            theory,
            sorts: index_names(theory.sorts.iter().map(|sort| sort.name.as_str()), "sort")?,
            constructors: index_names(
                theory
                    .constructors
                    .iter()
                    .map(|constructor| constructor.name.as_str()),
                "constructor",
            )?,
            judgments: index_names(
                theory
                    .judgments
                    .iter()
                    .map(|judgment| judgment.name.as_str()),
                "judgment",
            )?,
            effects: index_names(
                theory.effects.iter().map(|effect| effect.name.as_str()),
                "effect",
            )?,
        })
    }

    fn sort(&self, name: &str) -> Result<TheorySortId, TheoryImageError> {
        self.sorts
            .get(name)
            .copied()
            .ok_or(TheoryImageError::SourceMismatch { kind: "sort", index: u32::MAX })
    }
}

fn index_names<'a, I, Id>(
    names: I,
    kind: &'static str,
) -> Result<BTreeMap<&'a str, Id>, TheoryImageError>
where
    I: IntoIterator<Item = &'a str>,
    Id: From<u32>,
{
    let mut output = BTreeMap::new();
    for (index, name) in names.into_iter().enumerate() {
        let index = u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded(kind))?;
        if output.insert(name, Id::from(index)).is_some() {
            return Err(TheoryImageError::SourceMismatch { kind, index });
        }
    }
    Ok(output)
}

macro_rules! impl_from_u32 {
    ($($name:ident),+ $(,)?) => {
        $(
            impl From<u32> for $name {
                fn from(value: u32) -> Self { Self(value) }
            }
        )+
    };
}

impl_from_u32!(TheorySortId, TheoryConstructorId, TheoryJudgmentId, TheoryEffectId);

fn validate_sorts(
    image: &TheorySemanticImageV1,
    language: &LanguageCoreV1,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    if image.sorts.len() != language.theory.sorts.len() {
        return Err(TheoryImageError::SourceMismatch { kind: "sort count", index: 0 });
    }
    for (index, (actual, source)) in image.sorts.iter().zip(&language.theory.sorts).enumerate() {
        let index = u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("sorts"))?;
        dense("sort", index, actual.id.0)?;
        let matches = match (&actual.kind, &source.kind) {
            (
                TheorySortKindImageV1::Syntax { literal: actual },
                TheorySortKindV1::Syntax { literal: source },
            ) => actual == source,
            (
                TheorySortKindImageV1::Collection {
                    kind: actual_kind,
                    key: actual_key,
                    element: actual_element,
                },
                TheorySortKindV1::Collection { kind, key, element },
            ) => {
                *actual_kind == *kind
                    && *actual_key == key.as_deref().map(|name| context.sort(name)).transpose()?
                    && *actual_element == context.sort(element)?
            },
            (
                TheorySortKindImageV1::Function {
                    domain: actual_domain,
                    codomain: actual_codomain,
                    multiple: actual_multiple,
                },
                TheorySortKindV1::Function { domain, codomain, multiple },
            ) => {
                *actual_domain == context.sort(domain)?
                    && *actual_codomain == context.sort(codomain)?
                    && *actual_multiple == *multiple
            },
            (
                TheorySortKindImageV1::Product { factors: actual },
                TheorySortKindV1::Product { factors: source },
            ) => {
                if actual.len() != source.len() {
                    false
                } else {
                    let mut equal = true;
                    for (actual, source) in actual.iter().zip(source) {
                        if *actual != context.sort(source)? {
                            equal = false;
                            break;
                        }
                    }
                    equal
                }
            },
            (
                TheorySortKindImageV1::Opaque { abi: actual },
                TheorySortKindV1::Opaque { abi: source },
            ) => actual == source,
            _ => false,
        };
        if !matches {
            return Err(TheoryImageError::SourceMismatch { kind: "sort", index });
        }
    }
    Ok(())
}

fn validate_constructors(
    image: &TheorySemanticImageV1,
    language: &LanguageCoreV1,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    if image.constructors.len() != language.theory.constructors.len() {
        return Err(TheoryImageError::SourceMismatch { kind: "constructor count", index: 0 });
    }
    for (index, (actual, source)) in image
        .constructors
        .iter()
        .zip(&language.theory.constructors)
        .enumerate()
    {
        let index =
            u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("constructors"))?;
        dense("constructor", index, actual.id.0)?;
        let expected_domain = source
            .domain
            .iter()
            .map(|sort| context.sort(sort))
            .collect::<Result<Vec<_>, _>>()?;
        if actual.domain != expected_domain || actual.codomain != context.sort(&source.codomain)? {
            return Err(TheoryImageError::SourceMismatch { kind: "constructor", index });
        }
        let expected_binding = unique_grammar_binding(language, &source.name, index)?;
        if actual.grammar != Some(expected_binding) {
            return Err(TheoryImageError::SourceMismatch { kind: "grammar constructor", index });
        }
        let category = language
            .grammar
            .categories
            .get(expected_binding.category.0 as usize)
            .ok_or(TheoryImageError::SourceMismatch { kind: "grammar category", index })?;
        if category.name != source.codomain {
            return Err(TheoryImageError::SourceMismatch { kind: "constructor codomain", index });
        }
    }
    Ok(())
}

fn unique_grammar_binding(
    language: &LanguageCoreV1,
    label: &str,
    index: u32,
) -> Result<TheoryGrammarConstructorV1, TheoryImageError> {
    let mut binding = None;
    for production in &language.grammar.productions {
        if production.label != label {
            continue;
        }
        let candidate = TheoryGrammarConstructorV1 {
            category: production.result,
            constructor: production.constructor,
        };
        if binding.is_some_and(|current| current != candidate) {
            return Err(TheoryImageError::SourceMismatch {
                kind: "ambiguous grammar constructor",
                index,
            });
        }
        binding = Some(candidate);
    }
    binding.ok_or(TheoryImageError::SourceMismatch { kind: "grammar constructor", index })
}

fn validate_image_totals(
    image: &TheorySemanticImageV1,
    limits: TheoryImageAdmissionLimits,
) -> Result<(), TheoryImageError> {
    let mut sort_references = 0usize;
    let mut sort_metadata_bytes = 0usize;
    for sort in &image.sorts {
        match &sort.kind {
            TheorySortKindImageV1::Syntax {
                literal:
                    Some(
                        TheoryLiteralCarrierV1::External(value)
                        | TheoryLiteralCarrierV1::HostOpaque(value),
                    ),
            } => {
                sort_metadata_bytes = checked_total(
                    sort_metadata_bytes,
                    value.len(),
                    limits.max_total_sort_metadata_bytes,
                    "sort metadata bytes",
                )?;
            },
            TheorySortKindImageV1::Syntax { .. } => {},
            TheorySortKindImageV1::Collection { key, .. } => {
                sort_references = checked_total(
                    sort_references,
                    1usize
                        .checked_add(usize::from(key.is_some()))
                        .ok_or(TheoryImageError::LengthOverflow)?,
                    limits.max_total_sort_references,
                    "sort references",
                )?;
            },
            TheorySortKindImageV1::Function { .. } => {
                sort_references = checked_total(
                    sort_references,
                    2,
                    limits.max_total_sort_references,
                    "sort references",
                )?;
            },
            TheorySortKindImageV1::Product { factors } => {
                sort_references = checked_total(
                    sort_references,
                    factors.len(),
                    limits.max_total_sort_references,
                    "sort references",
                )?;
            },
            TheorySortKindImageV1::Opaque { abi } => {
                sort_metadata_bytes = checked_total(
                    sort_metadata_bytes,
                    abi.len(),
                    limits.max_total_sort_metadata_bytes,
                    "sort metadata bytes",
                )?;
            },
        }
    }
    let mut constructor_arguments = 0usize;
    for constructor in &image.constructors {
        constructor_arguments = checked_total(
            constructor_arguments,
            constructor.domain.len(),
            limits.max_total_constructor_arguments,
            "constructor arguments",
        )?;
    }
    let mut variables = 0usize;
    let mut terms = 0usize;
    let mut term_references = 0usize;
    let mut premises = 0usize;
    let mut premise_roots = 0usize;
    let mut names = 0usize;
    let mut literals = 0usize;
    let mut action_arguments = 0usize;
    let mut action_terminal_constructors = 0usize;
    let mut transitions = 0usize;
    for rule in &image.rules {
        variables = checked_total(
            variables,
            rule.variables.len(),
            limits.max_total_rule_variables,
            "rule variables",
        )?;
        terms = checked_total(terms, rule.terms.len(), limits.max_total_term_nodes, "term nodes")?;
        premises = checked_total(
            premises,
            rule.premises.len(),
            limits.max_total_premise_nodes,
            "premise nodes",
        )?;
        names = checked_total(names, rule.name.len(), limits.max_total_name_bytes, "name bytes")?;
        for term in &rule.terms {
            match &term.form {
                TheoryImageTermFormV1::Apply {
                    operator, arguments, slots, remainder, ..
                } => {
                    term_references = checked_total(
                        term_references,
                        arguments
                            .len()
                            .checked_add(slots.len())
                            .and_then(|count| count.checked_add(usize::from(remainder.is_some())))
                            .ok_or(TheoryImageError::LengthOverflow)?,
                        limits.max_total_term_references,
                        "term references",
                    )?;
                    sort_references = checked_total(
                        sort_references,
                        operator_sort_reference_count(operator)?,
                        limits.max_total_sort_references,
                        "sort references",
                    )?;
                },
                TheoryImageTermFormV1::Map { sources, parameters, .. } => {
                    term_references = checked_total(
                        term_references,
                        sources
                            .len()
                            .checked_add(parameters.len())
                            .and_then(|count| count.checked_add(1))
                            .ok_or(TheoryImageError::LengthOverflow)?,
                        limits.max_total_term_references,
                        "term references",
                    )?;
                },
                TheoryImageTermFormV1::Slot(_) => {},
            }
            if let TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Literal { value, .. },
                ..
            } = &term.form
            {
                literals = checked_total(
                    literals,
                    literal_bytes(value),
                    limits.max_total_literal_bytes,
                    "literal bytes",
                )?;
            }
        }
        for premise in &rule.premises {
            if let TheoryImagePremiseFormV1::Judgment { terms, .. } = &premise.form {
                term_references = checked_total(
                    term_references,
                    terms.len(),
                    limits.max_total_term_references,
                    "term references",
                )?;
            }
        }
        premise_roots = checked_total(
            premise_roots,
            rule.premise_roots.len(),
            limits.max_total_premise_roots,
            "premise roots",
        )?;
    }
    for rule in &image.judgment_rules {
        variables = checked_total(
            variables,
            rule.variables.len(),
            limits.max_total_rule_variables,
            "rule variables",
        )?;
        terms = checked_total(terms, rule.terms.len(), limits.max_total_term_nodes, "term nodes")?;
        premises = checked_total(
            premises,
            rule.premises.len(),
            limits.max_total_premise_nodes,
            "premise nodes",
        )?;
        names = checked_total(names, rule.name.len(), limits.max_total_name_bytes, "name bytes")?;
        for term in &rule.terms {
            match &term.form {
                TheoryImageTermFormV1::Apply {
                    operator, arguments, slots, remainder, ..
                } => {
                    term_references = checked_total(
                        term_references,
                        arguments
                            .len()
                            .checked_add(slots.len())
                            .and_then(|count| count.checked_add(usize::from(remainder.is_some())))
                            .ok_or(TheoryImageError::LengthOverflow)?,
                        limits.max_total_term_references,
                        "term references",
                    )?;
                    sort_references = checked_total(
                        sort_references,
                        operator_sort_reference_count(operator)?,
                        limits.max_total_sort_references,
                        "sort references",
                    )?;
                },
                TheoryImageTermFormV1::Map { sources, parameters, .. } => {
                    term_references = checked_total(
                        term_references,
                        sources
                            .len()
                            .checked_add(parameters.len())
                            .and_then(|count| count.checked_add(1))
                            .ok_or(TheoryImageError::LengthOverflow)?,
                        limits.max_total_term_references,
                        "term references",
                    )?;
                },
                TheoryImageTermFormV1::Slot(_) => {},
            }
            if let TheoryImageTermFormV1::Apply {
                operator: TheoryImageOperatorV1::Literal { value, .. },
                ..
            } = &term.form
            {
                literals = checked_total(
                    literals,
                    literal_bytes(value),
                    limits.max_total_literal_bytes,
                    "literal bytes",
                )?;
            }
        }
        for atom in rule
            .premises
            .iter()
            .chain(std::iter::once(&rule.conclusion))
        {
            term_references = checked_total(
                term_references,
                atom.terms.len(),
                limits.max_total_term_references,
                "term references",
            )?;
        }
    }
    for action in &image.actions {
        action_arguments = checked_total(
            action_arguments,
            action.domain.len(),
            limits.max_total_action_arguments,
            "action arguments",
        )?;
        transitions = checked_total(
            transitions,
            action.transitions.len(),
            limits.max_total_action_transitions,
            "action transitions",
        )?;
        if let TheoryActionExecutionImageV1::Normalize { terminal_constructors, .. } =
            &action.execution
        {
            action_terminal_constructors = checked_total(
                action_terminal_constructors,
                terminal_constructors.len(),
                limits.max_total_action_terminal_constructors,
                "action terminal constructors",
            )?;
        }
    }
    for state in image
        .patterns
        .states
        .iter()
        .chain(&image.judgment_patterns.states)
    {
        if let TheoryPatternStateFormV1::Apply { operator, .. } = &state.form {
            sort_references = checked_total(
                sort_references,
                operator_sort_reference_count(operator)?,
                limits.max_total_sort_references,
                "sort references",
            )?;
        }
    }
    Ok(())
}

fn operator_sort_reference_count(
    operator: &TheoryImageOperatorV1,
) -> Result<usize, TheoryImageError> {
    match operator {
        TheoryImageOperatorV1::Constructor(_) | TheoryImageOperatorV1::Judgment { .. } => Ok(0),
        TheoryImageOperatorV1::Abstraction { .. }
        | TheoryImageOperatorV1::Product { .. }
        | TheoryImageOperatorV1::Literal { .. }
        | TheoryImageOperatorV1::PathMapMode { .. } => Ok(1),
        TheoryImageOperatorV1::Substitution { .. } | TheoryImageOperatorV1::Collection { .. } => {
            Ok(2)
        },
    }
}

fn canonical_guard_footprint(
    value: &crate::CanonicalValue,
    limits: TheoryImageAdmissionLimits,
) -> Result<(usize, usize), TheoryImageError> {
    let mut pending = vec![value];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    while let Some(value) = pending.pop() {
        nodes = checked_total(nodes, 1, limits.max_total_guard_nodes, "guard nodes")?;
        match value {
            crate::CanonicalValue::Map(values) => {
                pending
                    .try_reserve(values.len())
                    .map_err(|_| TheoryImageError::Allocation)?;
                for (key, value) in values.iter().rev() {
                    bytes = checked_total(
                        bytes,
                        key.len(),
                        limits.max_total_guard_bytes,
                        "guard bytes",
                    )?;
                    pending.push(value);
                }
            },
            crate::CanonicalValue::List(values) => {
                pending
                    .try_reserve(values.len())
                    .map_err(|_| TheoryImageError::Allocation)?;
                pending.extend(values.iter().rev());
            },
            crate::CanonicalValue::String(value) => {
                bytes =
                    checked_total(bytes, value.len(), limits.max_total_guard_bytes, "guard bytes")?;
            },
            crate::CanonicalValue::Bytes(value) => {
                bytes =
                    checked_total(bytes, value.len(), limits.max_total_guard_bytes, "guard bytes")?;
            },
            crate::CanonicalValue::Integer(_)
            | crate::CanonicalValue::FloatBits(_)
            | crate::CanonicalValue::Boolean(_)
            | crate::CanonicalValue::Nil => {},
        }
    }
    Ok((nodes, bytes))
}

fn literal_bytes(literal: &TheoryLiteralV1) -> usize {
    match literal {
        TheoryLiteralV1::String(value) => value.len(),
        TheoryLiteralV1::Bytes(value) => value.len(),
        TheoryLiteralV1::Integer(_)
        | TheoryLiteralV1::FloatBits(_)
        | TheoryLiteralV1::Boolean(_)
        | TheoryLiteralV1::Unit => 0,
    }
}

fn checked_total(
    current: usize,
    additional: usize,
    limit: usize,
    kind: &'static str,
) -> Result<usize, TheoryImageError> {
    let total = current
        .checked_add(additional)
        .ok_or(TheoryImageError::LengthOverflow)?;
    enforce(total, limit, kind)?;
    Ok(total)
}

fn validate_rules(
    image: &TheorySemanticImageV1,
    language: &LanguageCoreV1,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    let expected_count = language
        .theory
        .equations
        .len()
        .checked_mul(2)
        .and_then(|count| count.checked_add(language.theory.rewrites.len()))
        .ok_or(TheoryImageError::LengthOverflow)?;
    if image.rules.len() != expected_count {
        return Err(TheoryImageError::SourceMismatch { kind: "rule count", index: 0 });
    }
    for (index, program) in image.rules.iter().enumerate() {
        let index = u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("rules"))?;
        dense("rule", index, program.id.0)?;
        let (name, arena, left, right) = source_rule(&language.theory, program.origin)?;
        if program.name != name || program.left != left || program.right != right {
            return Err(TheoryImageError::SourceMismatch { kind: "rule header", index });
        }
        validate_program(program, arena, context, index)?;
        if structurally_equal(&program.terms, program.left, program.right)? {
            return Err(TheoryImageError::SourceMismatch { kind: "non-progressing rule", index });
        }
        let allow_transition = matches!(program.origin, TheoryRuleOriginV1::Rewrite { .. });
        if program.disposition != rule_disposition(arena, left, right, allow_transition)? {
            return Err(TheoryImageError::SourceMismatch { kind: "rule disposition", index });
        }
    }
    Ok(())
}

fn validate_judgments(
    image: &TheorySemanticImageV1,
    language: &LanguageCoreV1,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    if image.judgments.len() != language.theory.judgments.len() {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment count", index: 0 });
    }
    let expected_rule_count =
        language
            .theory
            .judgments
            .iter()
            .try_fold(0usize, |count, judgment| {
                count
                    .checked_add(judgment.rules.len())
                    .ok_or(TheoryImageError::LengthOverflow)
            })?;
    if image.judgment_rules.len() != expected_rule_count {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment rule count", index: 0 });
    }

    let mut next_rule = 0usize;
    for (judgment_index, (actual, source)) in image
        .judgments
        .iter()
        .zip(&language.theory.judgments)
        .enumerate()
    {
        let judgment_index = u32::try_from(judgment_index)
            .map_err(|_| TheoryImageError::LimitExceeded("judgments"))?;
        dense("judgment", judgment_index, actual.id.0)?;
        let expected_arguments = source
            .arguments
            .iter()
            .map(|sort| context.sort(sort))
            .collect::<Result<Vec<_>, _>>()?;
        let next_rule_end = next_rule
            .checked_add(source.rules.len())
            .ok_or(TheoryImageError::LengthOverflow)?;
        let expected_rules = (next_rule..next_rule_end)
            .map(|index| {
                u32::try_from(index)
                    .map(TheoryJudgmentRuleProgramId)
                    .map_err(|_| TheoryImageError::LimitExceeded("judgment rules"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if actual.arguments != expected_arguments
            || actual.decision != source.decision
            || actual.rules != expected_rules
        {
            return Err(TheoryImageError::SourceMismatch {
                kind: "judgment",
                index: judgment_index,
            });
        }
        for source_rule in &source.rules {
            let program =
                image
                    .judgment_rules
                    .get(next_rule)
                    .ok_or(TheoryImageError::UnknownReference {
                        kind: "judgment rule",
                        owner: judgment_index,
                        target: u32::try_from(next_rule).unwrap_or(u32::MAX),
                    })?;
            let expected_id = u32::try_from(next_rule)
                .map_err(|_| TheoryImageError::LimitExceeded("judgment rules"))?;
            dense("judgment rule", expected_id, program.id.0)?;
            validate_judgment_program(program, source_rule, actual.id, context)?;
            next_rule += 1;
        }
    }
    Ok(())
}

fn validate_judgment_program(
    program: &TheoryJudgmentRuleProgramV1,
    source: &JudgmentRuleV1,
    owner: TheoryJudgmentId,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    let index = program.id.0;
    if program.owner != owner
        || program.name != source.name
        || program.variables.len() != source.variables.len()
        || program.terms.len() != source.terms.len()
        || program.premises.len() != source.premises.len()
    {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment rule", index });
    }
    for (variable_index, (actual, expected)) in
        program.variables.iter().zip(&source.variables).enumerate()
    {
        let variable_index = u32::try_from(variable_index)
            .map_err(|_| TheoryImageError::LimitExceeded("rule variables"))?;
        dense("judgment rule variable", variable_index, actual.id.0)?;
        if actual.sort != context.sort(&expected.sort)? || actual.role != expected.role {
            return Err(TheoryImageError::SourceMismatch { kind: "judgment rule variable", index });
        }
    }
    for (term_index, (actual, expected)) in program.terms.iter().zip(&source.terms).enumerate() {
        let term_index =
            u32::try_from(term_index).map_err(|_| TheoryImageError::LimitExceeded("rule terms"))?;
        if actual.sort != context.sort(&expected.sort)?
            || actual.form
                != expected_term_form(expected, &source.terms, &source.variables, context)?
        {
            return Err(TheoryImageError::SourceMismatch { kind: "judgment rule term", index });
        }
        validate_term_references(actual, term_index, program.variables.len())?;
    }
    for (actual, expected) in program.premises.iter().zip(&source.premises) {
        if actual != &expected_judgment_atom(expected, context)? {
            return Err(TheoryImageError::SourceMismatch { kind: "judgment rule premise", index });
        }
        validate_judgment_atom_references(actual, index, program.terms.len())?;
    }
    if program.conclusion != expected_judgment_atom(&source.conclusion, context)? {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment rule conclusion", index });
    }
    validate_judgment_atom_references(&program.conclusion, index, program.terms.len())?;
    if program.conclusion.judgment != owner {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment rule owner", index });
    }
    let expected_charge = TheoryWorkChargeV1 {
        pattern_nodes: u32::try_from(source.terms.len())
            .map_err(|_| TheoryImageError::LimitExceeded("judgment rule terms"))?,
        template_nodes: 0,
        premise_nodes: u32::try_from(source.premises.len())
            .map_err(|_| TheoryImageError::LimitExceeded("judgment rule premises"))?,
        variable_slots: u32::try_from(source.variables.len())
            .map_err(|_| TheoryImageError::LimitExceeded("judgment rule variables"))?,
    };
    if program.charge != expected_charge {
        return Err(TheoryImageError::SourceMismatch { kind: "judgment resource charge", index });
    }
    Ok(())
}

fn expected_judgment_atom(
    source: &JudgmentAtomV1,
    context: &ImageSourceContext<'_>,
) -> Result<TheoryImageJudgmentAtomV1, TheoryImageError> {
    Ok(TheoryImageJudgmentAtomV1 {
        judgment: context
            .judgments
            .get(source.judgment.as_str())
            .copied()
            .ok_or(TheoryImageError::SourceMismatch { kind: "judgment atom", index: u32::MAX })?,
        terms: source.terms.clone(),
    })
}

fn validate_judgment_atom_references(
    atom: &TheoryImageJudgmentAtomV1,
    owner: u32,
    term_count: usize,
) -> Result<(), TheoryImageError> {
    for term in &atom.terms {
        if term.0 as usize >= term_count {
            return Err(TheoryImageError::UnknownReference {
                kind: "judgment term",
                owner,
                target: term.0,
            });
        }
    }
    Ok(())
}

fn source_rule(
    theory: &TheoryCoreV1,
    origin: TheoryRuleOriginV1,
) -> Result<(&str, &TheoryRuleArenaV1, TheoryTermId, TheoryTermId), TheoryImageError> {
    match origin {
        TheoryRuleOriginV1::Equation { source, direction } => {
            let equation = theory.equations.get(source as usize).ok_or(
                TheoryImageError::UnknownReference {
                    kind: "equation",
                    owner: source,
                    target: source,
                },
            )?;
            Ok(match direction {
                TheoryRuleDirectionV1::Forward => {
                    (&equation.name, &equation.arena, equation.left, equation.right)
                },
                TheoryRuleDirectionV1::Reverse => {
                    (&equation.name, &equation.arena, equation.right, equation.left)
                },
            })
        },
        TheoryRuleOriginV1::Rewrite { source } => {
            let rewrite =
                theory
                    .rewrites
                    .get(source as usize)
                    .ok_or(TheoryImageError::UnknownReference {
                        kind: "rewrite",
                        owner: source,
                        target: source,
                    })?;
            Ok((&rewrite.name, &rewrite.arena, rewrite.left, rewrite.right))
        },
    }
}

fn validate_program(
    program: &TheoryRuleProgramV1,
    source: &TheoryRuleArenaV1,
    context: &ImageSourceContext<'_>,
    owner: u32,
) -> Result<(), TheoryImageError> {
    if program.variables.len() != source.variables.len()
        || program.terms.len() != source.terms.len()
        || program.premises.len() != source.premises.len()
        || program
            .premise_roots
            .iter()
            .copied()
            .ne(source.premise_roots.iter().map(|id| id.0))
    {
        return Err(TheoryImageError::SourceMismatch { kind: "rule arena", index: owner });
    }
    for (index, (actual, expected)) in program.variables.iter().zip(&source.variables).enumerate() {
        let index =
            u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("rule variables"))?;
        dense("rule variable", index, actual.id.0)?;
        if actual.sort != context.sort(&expected.sort)? || actual.role != expected.role {
            return Err(TheoryImageError::SourceMismatch { kind: "rule variable", index: owner });
        }
    }
    for (index, (actual, expected)) in program.terms.iter().zip(&source.terms).enumerate() {
        let index =
            u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("rule terms"))?;
        if actual.sort != context.sort(&expected.sort)?
            || actual.form
                != expected_term_form(expected, &source.terms, &source.variables, context)?
        {
            return Err(TheoryImageError::SourceMismatch { kind: "rule term", index: owner });
        }
        validate_term_references(actual, index, program.variables.len())?;
    }
    for (index, (actual, expected)) in program.premises.iter().zip(&source.premises).enumerate() {
        let index =
            u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("premises"))?;
        if actual.form != expected_premise_form(&expected.form, context)? {
            return Err(TheoryImageError::SourceMismatch { kind: "premise", index: owner });
        }
        validate_premise_references(actual, index, program)?;
    }
    let count = |value: usize| u32::try_from(value).unwrap_or(u32::MAX);
    let expected_charge = TheoryWorkChargeV1 {
        pattern_nodes: count(source.terms.len()),
        template_nodes: count(source.terms.len()),
        premise_nodes: count(source.premises.len()),
        variable_slots: count(source.variables.len()),
    };
    if program.charge != expected_charge {
        return Err(TheoryImageError::SourceMismatch { kind: "resource charge", index: owner });
    }
    Ok(())
}

fn expected_term_form(
    node: &crate::TheoryTermNodeV1,
    terms: &[crate::TheoryTermNodeV1],
    variables: &[crate::TheoryVariableV1],
    context: &ImageSourceContext<'_>,
) -> Result<TheoryImageTermFormV1, TheoryImageError> {
    let sort = context.sort(&node.sort)?;
    Ok(match &node.form {
        TheoryTermFormV1::Variable(variable) => TheoryImageTermFormV1::Slot(*variable),
        TheoryTermFormV1::Constructor { constructor, arguments } => TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Constructor(
                context
                    .constructors
                    .get(constructor.as_str())
                    .copied()
                    .ok_or(TheoryImageError::SourceMismatch {
                        kind: "constructor",
                        index: u32::MAX,
                    })?,
            ),
            arguments: arguments.clone(),
            slots: Vec::new(),
            remainder: None,
            pathmap_mode: None,
        },
        TheoryTermFormV1::Abstraction { binder, body } => TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Abstraction { sort },
            arguments: vec![*body],
            slots: vec![*binder],
            remainder: None,
            pathmap_mode: None,
        },
        TheoryTermFormV1::Substitution { abstraction, argument } => TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Substitution {
                sort,
                function: context.sort(
                    &terms
                        .get(abstraction.0 as usize)
                        .ok_or(TheoryImageError::UnknownReference {
                            kind: "substitution abstraction",
                            owner: u32::MAX,
                            target: abstraction.0,
                        })?
                        .sort,
                )?,
            },
            arguments: vec![*abstraction, *argument],
            slots: Vec::new(),
            remainder: None,
            pathmap_mode: None,
        },
        TheoryTermFormV1::Collection { elements, remainder, pathmap_mode } => {
            return expected_collection_form(sort, elements, *remainder, *pathmap_mode, context);
        },
        TheoryTermFormV1::Map { sources, parameters, body } => {
            // Resolve every binder and source sort here as part of the
            // source/image correspondence check, even though the compact
            // metainstruction stores stable dense term/variable identifiers.
            for parameter in parameters {
                let variable = variables.get(parameter.0 as usize).ok_or(
                    TheoryImageError::UnknownReference {
                        kind: "map parameter",
                        owner: u32::MAX,
                        target: parameter.0,
                    },
                )?;
                context.sort(&variable.sort)?;
            }
            for source in sources {
                let source =
                    terms
                        .get(source.0 as usize)
                        .ok_or(TheoryImageError::UnknownReference {
                            kind: "map source",
                            owner: u32::MAX,
                            target: source.0,
                        })?;
                context.sort(&source.sort)?;
            }
            TheoryImageTermFormV1::Map {
                sources: sources.clone(),
                parameters: parameters.clone(),
                body: *body,
            }
        },
        TheoryTermFormV1::Product { factors } => TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Product { sort },
            arguments: factors.clone(),
            slots: Vec::new(),
            remainder: None,
            pathmap_mode: None,
        },
        TheoryTermFormV1::Literal(value) => TheoryImageTermFormV1::Apply {
            operator: TheoryImageOperatorV1::Literal { sort, value: value.clone() },
            arguments: Vec::new(),
            slots: Vec::new(),
            remainder: None,
            pathmap_mode: None,
        },
    })
}

fn expected_collection_form(
    sort: TheorySortId,
    elements: &[TheoryTermId],
    remainder: Option<TheoryVariableId>,
    pathmap_mode: Option<PathMapModeV1>,
    context: &ImageSourceContext<'_>,
) -> Result<TheoryImageTermFormV1, TheoryImageError> {
    let declaration = context
        .theory
        .sorts
        .get(sort.0 as usize)
        .ok_or(TheoryImageError::SourceMismatch { kind: "collection sort", index: sort.0 })?;
    let TheorySortKindV1::Collection { kind, element, .. } = &declaration.kind else {
        return Err(TheoryImageError::SourceMismatch {
            kind: "collection signature",
            index: sort.0,
        });
    };
    Ok(TheoryImageTermFormV1::Apply {
        operator: TheoryImageOperatorV1::Collection {
            sort,
            element: context.sort(element)?,
            kind: *kind,
        },
        arguments: elements.to_vec(),
        slots: Vec::new(),
        remainder,
        pathmap_mode,
    })
}

fn expected_premise_form(
    form: &TheoryPremiseFormV1,
    context: &ImageSourceContext<'_>,
) -> Result<TheoryImagePremiseFormV1, TheoryImageError> {
    Ok(match form {
        TheoryPremiseFormV1::Freshness { variable, target, remainder } => {
            TheoryImagePremiseFormV1::Freshness {
                variable: *variable,
                target: *target,
                remainder: *remainder,
            }
        },
        TheoryPremiseFormV1::Transition { source, target } => {
            TheoryImagePremiseFormV1::Transition { source: *source, target: *target }
        },
        TheoryPremiseFormV1::Judgment(JudgmentAtomV1 { judgment, terms }) => {
            TheoryImagePremiseFormV1::Judgment {
                judgment: context.judgments.get(judgment.as_str()).copied().ok_or(
                    TheoryImageError::SourceMismatch { kind: "judgment", index: u32::MAX },
                )?,
                terms: terms.clone(),
            }
        },
        TheoryPremiseFormV1::ForAll { collection, parameter, body } => {
            TheoryImagePremiseFormV1::ForAll {
                collection: *collection,
                parameter: *parameter,
                body: body.0,
            }
        },
        TheoryPremiseFormV1::Intrinsic(intrinsic) => {
            TheoryImagePremiseFormV1::Intrinsic(expected_intrinsic(intrinsic))
        },
        TheoryPremiseFormV1::Guard(value) => TheoryImagePremiseFormV1::Guard {
            commitment: theory_guard_commitment_v1(value)?,
        },
    })
}

fn expected_intrinsic(intrinsic: &TheoryIntrinsicV1) -> TheoryImageIntrinsicV1 {
    match intrinsic {
        TheoryIntrinsicV1::ExactTermEq { left, right, output } => {
            TheoryImageIntrinsicV1::ExactTermEq {
                left: *left,
                right: *right,
                output: *output,
            }
        },
        TheoryIntrinsicV1::Utf8AtEnd { text, cursor, output } => {
            TheoryImageIntrinsicV1::Utf8AtEnd {
                text: *text,
                cursor: *cursor,
                output: *output,
            }
        },
        TheoryIntrinsicV1::Utf8ScalarAt { text, cursor, scalar, next_cursor } => {
            TheoryImageIntrinsicV1::Utf8ScalarAt {
                text: *text,
                cursor: *cursor,
                scalar: *scalar,
                next_cursor: *next_cursor,
            }
        },
        TheoryIntrinsicV1::Utf8Slice { text, start, end, output } => {
            TheoryImageIntrinsicV1::Utf8Slice {
                text: *text,
                start: *start,
                end: *end,
                output: *output,
            }
        },
        TheoryIntrinsicV1::CheckedNatAdd { left, right, output } => {
            TheoryImageIntrinsicV1::CheckedNatAdd {
                left: *left,
                right: *right,
                output: *output,
            }
        },
        TheoryIntrinsicV1::Utf8ConcatMany { pieces, output } => {
            TheoryImageIntrinsicV1::Utf8ConcatMany { pieces: *pieces, output: *output }
        },
    }
}

/// Domain-separated, representation-independent commitment to a guard value.
/// The traversal is iterative and streams directly into BLAKE3, so deeply
/// nested guards neither recurse nor require a second full-size byte buffer.
pub fn theory_guard_commitment_v1(
    value: &crate::CanonicalValue,
) -> Result<[u8; 32], TheoryImageError> {
    enum Task<'a> {
        Value(&'a crate::CanonicalValue),
        Key(&'a str),
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"mettail-theory-guard/1\0");
    let mut pending = vec![Task::Value(value)];
    while let Some(task) = pending.pop() {
        match task {
            Task::Key(key) => hash_guard_bytes(&mut hasher, key.as_bytes()),
            Task::Value(crate::CanonicalValue::Map(values)) => {
                hasher.update(b"m");
                hash_guard_len(&mut hasher, values.len());
                pending
                    .try_reserve(values.len().saturating_mul(2))
                    .map_err(|_| TheoryImageError::Allocation)?;
                for (key, value) in values.iter().rev() {
                    pending.push(Task::Value(value));
                    pending.push(Task::Key(key));
                }
            },
            Task::Value(crate::CanonicalValue::List(values)) => {
                hasher.update(b"l");
                hash_guard_len(&mut hasher, values.len());
                pending
                    .try_reserve(values.len())
                    .map_err(|_| TheoryImageError::Allocation)?;
                pending.extend(values.iter().rev().map(Task::Value));
            },
            Task::Value(crate::CanonicalValue::String(value)) => {
                hasher.update(b"s");
                hash_guard_bytes(&mut hasher, value.as_bytes());
            },
            Task::Value(crate::CanonicalValue::Bytes(value)) => {
                hasher.update(b"b");
                hash_guard_bytes(&mut hasher, value);
            },
            Task::Value(crate::CanonicalValue::Integer(value)) => {
                hasher.update(b"i");
                hasher.update(&value.to_be_bytes());
            },
            Task::Value(crate::CanonicalValue::FloatBits(value)) => {
                hasher.update(b"d");
                hasher.update(&value.to_be_bytes());
            },
            Task::Value(crate::CanonicalValue::Boolean(value)) => {
                hasher.update(if *value { b"t" } else { b"f" });
            },
            Task::Value(crate::CanonicalValue::Nil) => {
                hasher.update(b"n");
            },
        }
    }
    Ok(*hasher.finalize().as_bytes())
}

fn hash_guard_len(hasher: &mut blake3::Hasher, length: usize) {
    hasher.update(&u64::try_from(length).unwrap_or(u64::MAX).to_be_bytes());
}

fn hash_guard_bytes(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hash_guard_len(hasher, bytes.len());
    hasher.update(bytes);
}

fn validate_term_references(
    node: &TheoryImageTermNodeV1,
    owner: u32,
    variable_count: usize,
) -> Result<(), TheoryImageError> {
    match &node.form {
        TheoryImageTermFormV1::Slot(variable) => {
            variable_reference(*variable, owner, variable_count)
        },
        TheoryImageTermFormV1::Apply { arguments, slots, remainder, .. } => {
            for target in arguments {
                if target.0 >= owner {
                    return Err(TheoryImageError::ForwardReference {
                        kind: "term",
                        owner,
                        target: target.0,
                    });
                }
            }
            for variable in slots {
                variable_reference(*variable, owner, variable_count)?;
            }
            if let Some(variable) = remainder {
                variable_reference(*variable, owner, variable_count)?;
            }
            Ok(())
        },
        TheoryImageTermFormV1::Map { sources, parameters, body } => {
            if sources.is_empty() {
                return Err(TheoryImageError::SourceMismatch {
                    kind: "empty map sources",
                    index: owner,
                });
            }
            for target in sources.iter().chain(std::iter::once(body)) {
                if target.0 >= owner {
                    return Err(TheoryImageError::ForwardReference {
                        kind: "term",
                        owner,
                        target: target.0,
                    });
                }
            }
            for variable in parameters {
                variable_reference(*variable, owner, variable_count)?;
            }
            Ok(())
        },
    }
}

fn validate_premise_references(
    node: &TheoryImagePremiseNodeV1,
    owner: u32,
    program: &TheoryRuleProgramV1,
) -> Result<(), TheoryImageError> {
    let variables = program.variables.len();
    let terms = program.terms.len();
    match &node.form {
        TheoryImagePremiseFormV1::Freshness { variable, target, .. } => {
            variable_reference(*variable, owner, variables)?;
            variable_reference(*target, owner, variables)
        },
        TheoryImagePremiseFormV1::Transition { source, target } => {
            variable_reference(*source, owner, variables)?;
            variable_reference(*target, owner, variables)
        },
        TheoryImagePremiseFormV1::Judgment { terms: arguments, .. } => {
            for target in arguments {
                if target.0 as usize >= terms {
                    return Err(TheoryImageError::UnknownReference {
                        kind: "premise term",
                        owner,
                        target: target.0,
                    });
                }
            }
            Ok(())
        },
        TheoryImagePremiseFormV1::ForAll { collection, parameter, body } => {
            variable_reference(*collection, owner, variables)?;
            variable_reference(*parameter, owner, variables)?;
            if *body >= owner {
                return Err(TheoryImageError::ForwardReference {
                    kind: "premise",
                    owner,
                    target: *body,
                });
            }
            Ok(())
        },
        TheoryImagePremiseFormV1::Intrinsic(intrinsic) => {
            let mut result = Ok(());
            intrinsic.for_each_variable(|variable| {
                if result.is_ok() {
                    result = variable_reference(variable, owner, variables);
                }
            });
            result
        },
        TheoryImagePremiseFormV1::Guard { .. } => Ok(()),
    }
}

fn variable_reference(
    variable: TheoryVariableId,
    owner: u32,
    count: usize,
) -> Result<(), TheoryImageError> {
    if variable.0 as usize >= count {
        return Err(TheoryImageError::UnknownReference {
            kind: "variable",
            owner,
            target: variable.0,
        });
    }
    Ok(())
}

fn structurally_equal(
    terms: &[TheoryImageTermNodeV1],
    left: TheoryTermId,
    right: TheoryTermId,
) -> Result<bool, TheoryImageError> {
    let mut pending = vec![(left, right)];
    let mut seen = BTreeSet::new();
    while let Some((left, right)) = pending.pop() {
        if !seen.insert((left, right)) {
            continue;
        }
        let left_node = terms
            .get(left.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "term root",
                owner: left.0,
                target: left.0,
            })?;
        let right_node = terms
            .get(right.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "term root",
                owner: right.0,
                target: right.0,
            })?;
        if left_node.sort != right_node.sort {
            return Ok(false);
        }
        match (&left_node.form, &right_node.form) {
            (TheoryImageTermFormV1::Slot(left), TheoryImageTermFormV1::Slot(right)) => {
                if left != right {
                    return Ok(false);
                }
            },
            (
                TheoryImageTermFormV1::Apply {
                    operator: left_operator,
                    arguments: left_arguments,
                    slots: left_slots,
                    remainder: left_remainder,
                    pathmap_mode: left_pathmap_mode,
                },
                TheoryImageTermFormV1::Apply {
                    operator: right_operator,
                    arguments: right_arguments,
                    slots: right_slots,
                    remainder: right_remainder,
                    pathmap_mode: right_pathmap_mode,
                },
            ) => {
                if left_operator != right_operator
                    || left_slots != right_slots
                    || left_remainder != right_remainder
                    || left_pathmap_mode != right_pathmap_mode
                    || left_arguments.len() != right_arguments.len()
                {
                    return Ok(false);
                }
                pending.extend(
                    left_arguments
                        .iter()
                        .copied()
                        .zip(right_arguments.iter().copied()),
                );
            },
            (
                TheoryImageTermFormV1::Map {
                    sources: left_sources,
                    parameters: left_parameters,
                    body: left_body,
                },
                TheoryImageTermFormV1::Map {
                    sources: right_sources,
                    parameters: right_parameters,
                    body: right_body,
                },
            ) => {
                if left_parameters != right_parameters || left_sources.len() != right_sources.len()
                {
                    return Ok(false);
                }
                pending.extend(
                    left_sources
                        .iter()
                        .copied()
                        .zip(right_sources.iter().copied()),
                );
                pending.push((*left_body, *right_body));
            },
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn rule_disposition(
    arena: &TheoryRuleArenaV1,
    left: TheoryTermId,
    right: TheoryTermId,
    allow_transition: bool,
) -> Result<TheoryRuleDispositionV1, TheoryImageError> {
    let left_node = arena
        .terms
        .get(left.0 as usize)
        .ok_or(TheoryImageError::UnknownReference {
            kind: "left root",
            owner: left.0,
            target: left.0,
        })?;
    if matches!(left_node.form, TheoryTermFormV1::Variable(_)) {
        return Ok(TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::MatchAllRoot));
    }

    let mut available = term_variables(arena, left)?;
    if let Some(variable) = unavailable_premise_variable(arena, &mut available, allow_transition)? {
        return Ok(TheoryRuleDispositionV1::Suppressed(
            TheoryRuleSuppressionV1::PremiseDependency { variable },
        ));
    }
    if let Some(variable) = term_variables(arena, right)?
        .into_iter()
        .find(|variable| !available.contains(variable))
    {
        return Ok(TheoryRuleDispositionV1::Suppressed(TheoryRuleSuppressionV1::UnboundTemplate {
            variable,
        }));
    }
    Ok(TheoryRuleDispositionV1::Executable)
}

fn term_variables(
    arena: &TheoryRuleArenaV1,
    root: TheoryTermId,
) -> Result<BTreeSet<TheoryVariableId>, TheoryImageError> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if !reachable.insert(term) {
            continue;
        }
        let node = arena
            .terms
            .get(term.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "term",
                owner: root.0,
                target: term.0,
            })?;
        match &node.form {
            TheoryTermFormV1::Variable(_) | TheoryTermFormV1::Literal(_) => {},
            TheoryTermFormV1::Constructor { arguments, .. } => {
                pending.extend(arguments.iter().copied());
            },
            TheoryTermFormV1::Abstraction { body, .. } => {
                pending.push(*body);
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                pending.push(*abstraction);
                pending.push(*argument);
            },
            TheoryTermFormV1::Collection { elements, .. } => {
                pending.extend(elements.iter().copied());
            },
            TheoryTermFormV1::Map { sources, body, .. } => {
                pending.extend(sources.iter().copied());
                pending.push(*body);
            },
            TheoryTermFormV1::Product { factors } => {
                pending.extend(factors.iter().copied());
            },
        }
    }

    let mut free = vec![BTreeSet::new(); arena.terms.len()];
    for (index, node) in arena.terms.iter().enumerate() {
        let term = TheoryTermId(index as u32);
        if !reachable.contains(&term) {
            continue;
        }
        let mut variables = BTreeSet::new();
        macro_rules! inherit {
            ($child:expr) => {{
                let child = $child;
                let child_index = child.0 as usize;
                if child_index >= index {
                    return Err(TheoryImageError::UnknownReference {
                        kind: "non-prior term",
                        owner: term.0,
                        target: child.0,
                    });
                }
                variables.extend(free[child_index].iter().copied());
            }};
        }
        match &node.form {
            TheoryTermFormV1::Variable(variable) => {
                variables.insert(*variable);
            },
            TheoryTermFormV1::Constructor { arguments, .. } => {
                for child in arguments {
                    inherit!(*child);
                }
            },
            TheoryTermFormV1::Abstraction { binder, body } => {
                variables.insert(*binder);
                inherit!(*body);
            },
            TheoryTermFormV1::Substitution { abstraction, argument } => {
                inherit!(*abstraction);
                inherit!(*argument);
            },
            TheoryTermFormV1::Collection { elements, remainder, .. } => {
                for child in elements {
                    inherit!(*child);
                }
                variables.extend(remainder.iter().copied());
            },
            TheoryTermFormV1::Map { sources, parameters, body } => {
                for source in sources {
                    inherit!(*source);
                }
                let mut body_variables = free
                    .get(body.0 as usize)
                    .filter(|_| (body.0 as usize) < index)
                    .cloned()
                    .ok_or(TheoryImageError::UnknownReference {
                        kind: "non-prior term",
                        owner: term.0,
                        target: body.0,
                    })?;
                for parameter in parameters {
                    body_variables.remove(parameter);
                }
                variables.extend(body_variables);
            },
            TheoryTermFormV1::Product { factors } => {
                for child in factors {
                    inherit!(*child);
                }
            },
            TheoryTermFormV1::Literal(_) => {},
        }
        free[index] = variables;
    }
    free.get(root.0 as usize)
        .cloned()
        .ok_or(TheoryImageError::UnknownReference {
            kind: "term",
            owner: root.0,
            target: root.0,
        })
}

fn unavailable_premise_variable(
    arena: &TheoryRuleArenaV1,
    available: &mut BTreeSet<TheoryVariableId>,
    allow_transition: bool,
) -> Result<Option<TheoryVariableId>, TheoryImageError> {
    for root in &arena.premise_roots {
        let mut pending = vec![(root.0, available.clone(), true)];
        while let Some((index, mut scope, is_root)) = pending.pop() {
            let premise =
                arena
                    .premises
                    .get(index as usize)
                    .ok_or(TheoryImageError::UnknownReference {
                        kind: "premise",
                        owner: root.0,
                        target: index,
                    })?;
            let require =
                |variable, scope: &BTreeSet<_>| (!scope.contains(&variable)).then_some(variable);
            match &premise.form {
                TheoryPremiseFormV1::Freshness { variable, target, .. } => {
                    if let Some(missing) =
                        require(*variable, &scope).or_else(|| require(*target, &scope))
                    {
                        return Ok(Some(missing));
                    }
                },
                TheoryPremiseFormV1::Transition { source, target } => {
                    if !allow_transition {
                        return Ok(Some(*source));
                    }
                    if let Some(missing) = require(*source, &scope) {
                        return Ok(Some(missing));
                    }
                    if is_root {
                        available.insert(*target);
                    }
                },
                TheoryPremiseFormV1::Judgment(atom) => {
                    for term in &atom.terms {
                        if let Some(missing) = term_variables(arena, *term)?
                            .into_iter()
                            .find(|variable| !scope.contains(variable))
                        {
                            return Ok(Some(missing));
                        }
                    }
                },
                TheoryPremiseFormV1::ForAll { collection, parameter, body } => {
                    if let Some(missing) = require(*collection, &scope) {
                        return Ok(Some(missing));
                    }
                    scope.insert(*parameter);
                    pending.push((body.0, scope, false));
                },
                TheoryPremiseFormV1::Intrinsic(intrinsic) => {
                    let mut missing = None;
                    intrinsic.for_each_input(|variable| {
                        if missing.is_none() {
                            missing = require(variable, &scope);
                        }
                    });
                    if missing.is_some() {
                        return Ok(missing);
                    }
                    if is_root {
                        intrinsic.for_each_output(|variable| {
                            available.insert(variable);
                        });
                    }
                },
                TheoryPremiseFormV1::Guard(_) => {},
            }
        }
    }
    Ok(None)
}

fn validate_actions(
    image: &TheorySemanticImageV1,
    language: &LanguageCoreV1,
    context: &ImageSourceContext<'_>,
) -> Result<(), TheoryImageError> {
    if image.actions.len() != language.theory.actions.len() {
        return Err(TheoryImageError::SourceMismatch { kind: "action count", index: 0 });
    }
    for (index, (actual, source)) in image
        .actions
        .iter()
        .zip(&language.theory.actions)
        .enumerate()
    {
        let index = u32::try_from(index).map_err(|_| TheoryImageError::LimitExceeded("actions"))?;
        dense("action", index, actual.id.0)?;
        let expected_transitions = resolve_action_rules(&image.rules, &source.transition)?;
        let expected = TheoryActionImageV1 {
            id: TheoryActionId(index),
            domain: source
                .domain
                .iter()
                .map(|sort| context.sort(sort))
                .collect::<Result<Vec<_>, _>>()?,
            codomain: context.sort(&source.codomain)?,
            transitions: expected_transitions,
            effect: context
                .effects
                .get(source.effect.as_str())
                .copied()
                .ok_or(TheoryImageError::SourceMismatch { kind: "effect", index })?,
            effect_class: source.effect_class,
            required_rights: source.required_rights.clone(),
            grade: context.sort(&source.grade)?,
            execution: expected_action_execution(&source.execution, context)?,
        };
        if actual != &expected {
            return Err(TheoryImageError::SourceMismatch { kind: "action", index });
        }
        if actual
            .required_rights
            .iter()
            .any(|right| !source.required_rights.contains(right))
        {
            return Err(TheoryImageError::SourceMismatch { kind: "action rights", index });
        }
    }
    Ok(())
}

fn expected_action_execution(
    execution: &SemanticActionExecutionV1,
    context: &ImageSourceContext<'_>,
) -> Result<TheoryActionExecutionImageV1, TheoryImageError> {
    Ok(match execution {
        SemanticActionExecutionV1::OneStep => TheoryActionExecutionImageV1::OneStep,
        SemanticActionExecutionV1::Normalize {
            relation_sort,
            terminal_constructors,
            branching,
        } => {
            let mut terminals = Vec::new();
            terminals
                .try_reserve_exact(terminal_constructors.len())
                .map_err(|_| TheoryImageError::Allocation)?;
            for constructor in terminal_constructors {
                terminals.push(*context.constructors.get(constructor.as_str()).ok_or(
                    TheoryImageError::SourceMismatch {
                        kind: "action terminal constructor",
                        index: u32::MAX,
                    },
                )?);
            }
            TheoryActionExecutionImageV1::Normalize {
                relation_sort: context.sort(relation_sort)?,
                terminal_constructors: terminals,
                branching: *branching,
            }
        },
    })
}

fn resolve_action_rules(
    rules: &[TheoryRuleProgramV1],
    reference: &TheoryRuleReferenceV1,
) -> Result<Vec<TheoryRuleProgramId>, TheoryImageError> {
    let matches = rules
        .iter()
        .filter(|rule| match (reference, rule.origin) {
            (TheoryRuleReferenceV1::Equation(name), TheoryRuleOriginV1::Equation { .. })
            | (TheoryRuleReferenceV1::Rewrite(name), TheoryRuleOriginV1::Rewrite { .. }) => {
                rule.name == *name && rule.disposition == TheoryRuleDispositionV1::Executable
            },
            _ => false,
        })
        .map(|rule| rule.id)
        .collect::<Vec<_>>();
    match reference {
        TheoryRuleReferenceV1::Handler(_) => {
            Err(TheoryImageError::SourceMismatch { kind: "runtime handler", index: u32::MAX })
        },
        TheoryRuleReferenceV1::Equation(_) | TheoryRuleReferenceV1::Rewrite(_)
            if matches.is_empty() =>
        {
            Err(TheoryImageError::SourceMismatch {
                kind: "action transition",
                index: u32::MAX,
            })
        },
        TheoryRuleReferenceV1::Equation(_) | TheoryRuleReferenceV1::Rewrite(_) => Ok(matches),
    }
}

fn validate_pattern_automaton(
    image: &TheorySemanticImageV1,
    limits: TheoryImageAdmissionLimits,
) -> Result<(), TheoryImageError> {
    let mut edges = 0usize;
    let mut slot_references = 0usize;
    for (index, state) in image.patterns.states.iter().enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| TheoryImageError::LimitExceeded("automaton states"))?;
        dense("pattern state", index, state.id.0)?;
        match &state.form {
            TheoryPatternStateFormV1::Bind => {
                if state.slot_count != 1 {
                    return Err(TheoryImageError::SourceMismatch {
                        kind: "bind slot count",
                        index,
                    });
                }
            },
            TheoryPatternStateFormV1::Apply { arguments, .. } => {
                let mut used = BTreeSet::new();
                for invocation in arguments {
                    edges = edges
                        .checked_add(1)
                        .ok_or(TheoryImageError::LengthOverflow)?;
                    enforce(edges, limits.max_automaton_edges, "automaton edges")?;
                    if invocation.state.0 >= index {
                        return Err(TheoryImageError::ForwardReference {
                            kind: "pattern state",
                            owner: index,
                            target: invocation.state.0,
                        });
                    }
                    let child = &image.patterns.states[invocation.state.0 as usize];
                    if invocation.parent_slots.len() != child.slot_count as usize {
                        return Err(TheoryImageError::SourceMismatch {
                            kind: "pattern slot map",
                            index,
                        });
                    }
                    slot_references = checked_total(
                        slot_references,
                        invocation.parent_slots.len(),
                        limits.max_automaton_slot_references,
                        "automaton slot references",
                    )?;
                    for slot in &invocation.parent_slots {
                        if *slot >= state.slot_count {
                            return Err(TheoryImageError::UnknownReference {
                                kind: "pattern slot",
                                owner: index,
                                target: *slot,
                            });
                        }
                        used.insert(*slot);
                    }
                }
                if used.iter().copied().ne(0..state.slot_count) {
                    return Err(TheoryImageError::SourceMismatch {
                        kind: "pattern slot density",
                        index,
                    });
                }
            },
        }
    }

    let mut coverage = vec![0usize; image.rules.len()];
    let mut checks = 0usize;
    for (index, entry) in image.patterns.entries.iter().enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| TheoryImageError::LimitExceeded("automaton entries"))?;
        dense("pattern entry", index, entry.id.0)?;
        let rule =
            image
                .rules
                .get(entry.rule.0 as usize)
                .ok_or(TheoryImageError::UnknownReference {
                    kind: "pattern rule",
                    owner: index,
                    target: entry.rule.0,
                })?;
        let root = image.patterns.states.get(entry.root.0 as usize).ok_or(
            TheoryImageError::UnknownReference {
                kind: "pattern root",
                owner: index,
                target: entry.root.0,
            },
        )?;
        if entry.slot_variables.len() != root.slot_count as usize {
            return Err(TheoryImageError::AutomatonShape { entry: index });
        }
        slot_references = checked_total(
            slot_references,
            entry.slot_variables.len(),
            limits.max_automaton_slot_references,
            "automaton slot references",
        )?;
        let mut unique = BTreeSet::new();
        for variable in &entry.slot_variables {
            variable_reference(*variable, index, rule.variables.len())?;
            if !unique.insert(*variable) {
                return Err(TheoryImageError::DuplicateReference {
                    kind: "entry variable",
                    owner: index,
                    target: variable.0,
                });
            }
        }
        check_entry_matches_program(image, entry, rule, &mut checks, limits.max_automaton_checks)?;
        coverage[entry.rule.0 as usize] += 1;
    }
    for (index, rule) in image.rules.iter().enumerate() {
        let expected = usize::from(rule_is_positional(rule)?);
        if coverage[index] != expected {
            return Err(TheoryImageError::AutomatonCoverage {
                rule: rule.id.0,
                actual: coverage[index],
            });
        }
    }
    Ok(())
}

fn validate_judgment_pattern_automaton(
    image: &TheorySemanticImageV1,
    limits: TheoryImageAdmissionLimits,
) -> Result<(), TheoryImageError> {
    let states = &image.judgment_patterns.states;
    let mut edges = 0usize;
    let mut slot_references = 0usize;
    for (index, state) in states.iter().enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| TheoryImageError::LimitExceeded("judgment automaton states"))?;
        dense("judgment pattern state", index, state.id.0)?;
        match &state.form {
            TheoryPatternStateFormV1::Bind => {
                if state.slot_count != 1 {
                    return Err(TheoryImageError::SourceMismatch {
                        kind: "judgment bind slot count",
                        index,
                    });
                }
            },
            TheoryPatternStateFormV1::Apply { arguments, .. } => {
                let mut used = BTreeSet::new();
                for invocation in arguments {
                    edges = checked_total(edges, 1, limits.max_automaton_edges, "automaton edges")?;
                    if invocation.state.0 >= index {
                        return Err(TheoryImageError::ForwardReference {
                            kind: "judgment pattern state",
                            owner: index,
                            target: invocation.state.0,
                        });
                    }
                    let child = &states[invocation.state.0 as usize];
                    if invocation.parent_slots.len() != child.slot_count as usize {
                        return Err(TheoryImageError::SourceMismatch {
                            kind: "judgment pattern slot map",
                            index,
                        });
                    }
                    slot_references = checked_total(
                        slot_references,
                        invocation.parent_slots.len(),
                        limits.max_automaton_slot_references,
                        "automaton slot references",
                    )?;
                    for slot in &invocation.parent_slots {
                        if *slot >= state.slot_count {
                            return Err(TheoryImageError::UnknownReference {
                                kind: "judgment pattern slot",
                                owner: index,
                                target: *slot,
                            });
                        }
                        used.insert(*slot);
                    }
                }
                if used.iter().copied().ne(0..state.slot_count) {
                    return Err(TheoryImageError::SourceMismatch {
                        kind: "judgment pattern slot density",
                        index,
                    });
                }
            },
        }
    }

    let mut coverage = vec![0usize; image.judgment_rules.len()];
    let mut checks = 0usize;
    for (index, entry) in image.judgment_patterns.entries.iter().enumerate() {
        let index = u32::try_from(index)
            .map_err(|_| TheoryImageError::LimitExceeded("judgment automaton entries"))?;
        dense("judgment pattern entry", index, entry.id.0)?;
        let rule = image.judgment_rules.get(entry.rule.0 as usize).ok_or(
            TheoryImageError::UnknownReference {
                kind: "judgment pattern rule",
                owner: index,
                target: entry.rule.0,
            },
        )?;
        let root = states
            .get(entry.root.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "judgment pattern root",
                owner: index,
                target: entry.root.0,
            })?;
        if entry.slot_variables.len() != root.slot_count as usize {
            return Err(TheoryImageError::AutomatonShape { entry: index });
        }
        slot_references = checked_total(
            slot_references,
            entry.slot_variables.len(),
            limits.max_automaton_slot_references,
            "automaton slot references",
        )?;
        let mut unique = BTreeSet::new();
        for variable in &entry.slot_variables {
            variable_reference(*variable, index, rule.variables.len())?;
            if !unique.insert(*variable) {
                return Err(TheoryImageError::DuplicateReference {
                    kind: "judgment entry variable",
                    owner: index,
                    target: variable.0,
                });
            }
        }
        check_judgment_entry_matches_program(
            image,
            entry,
            rule,
            &mut checks,
            limits.max_automaton_checks,
        )?;
        coverage[entry.rule.0 as usize] += 1;
    }
    for (index, rule) in image.judgment_rules.iter().enumerate() {
        let expected = usize::from(term_roots_are_positional_image(
            &rule.terms,
            &rule.conclusion.terms,
            rule.id.0,
        )?);
        if coverage[index] != expected {
            return Err(TheoryImageError::AutomatonCoverage {
                rule: rule.id.0,
                actual: coverage[index],
            });
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum PatternSubject {
    Term(TheoryTermId),
    Slot(TheoryVariableId),
}

fn check_entry_matches_program(
    image: &TheorySemanticImageV1,
    entry: &TheoryPatternEntryV1,
    rule: &TheoryRuleProgramV1,
    checks: &mut usize,
    limit: usize,
) -> Result<(), TheoryImageError> {
    let root_state = &image.patterns.states[entry.root.0 as usize];
    let root_slots = (0..root_state.slot_count).collect::<Vec<_>>();
    check_pattern_subjects(
        &image.patterns.states,
        &rule.terms,
        entry.id.0,
        &entry.slot_variables,
        vec![(PatternSubject::Term(rule.left), entry.root, root_slots)],
        checks,
        limit,
    )
}

fn check_judgment_entry_matches_program(
    image: &TheorySemanticImageV1,
    entry: &TheoryJudgmentPatternEntryV1,
    rule: &TheoryJudgmentRuleProgramV1,
    checks: &mut usize,
    limit: usize,
) -> Result<(), TheoryImageError> {
    let states = &image.judgment_patterns.states;
    let root = states
        .get(entry.root.0 as usize)
        .ok_or(TheoryImageError::UnknownReference {
            kind: "judgment pattern root",
            owner: entry.id.0,
            target: entry.root.0,
        })?;
    charge_pattern_check(checks, limit)?;
    let TheoryPatternStateFormV1::Apply { operator, arguments } = &root.form else {
        return Err(TheoryImageError::AutomatonShape { entry: entry.id.0 });
    };
    if operator != &(TheoryImageOperatorV1::Judgment { judgment: rule.conclusion.judgment })
        || arguments.len() != rule.conclusion.terms.len()
    {
        return Err(TheoryImageError::AutomatonShape { entry: entry.id.0 });
    }

    let root_slots = (0..root.slot_count).collect::<Vec<_>>();
    let mut pending = Vec::new();
    pending
        .try_reserve(arguments.len())
        .map_err(|_| TheoryImageError::Allocation)?;
    for (term, invocation) in rule.conclusion.terms.iter().zip(arguments).rev() {
        let child_slots = invocation
            .parent_slots
            .iter()
            .map(|parent| {
                root_slots
                    .get(*parent as usize)
                    .copied()
                    .ok_or(TheoryImageError::AutomatonShape { entry: entry.id.0 })
            })
            .collect::<Result<Vec<_>, _>>()?;
        pending.push((PatternSubject::Term(*term), invocation.state, child_slots));
    }
    check_pattern_subjects(
        states,
        &rule.terms,
        entry.id.0,
        &entry.slot_variables,
        pending,
        checks,
        limit,
    )
}

fn check_pattern_subjects(
    states: &[TheoryPatternStateV1],
    terms: &[TheoryImageTermNodeV1],
    entry: u32,
    slot_variables: &[TheoryVariableId],
    mut pending: Vec<(PatternSubject, TheoryPatternStateId, Vec<u32>)>,
    checks: &mut usize,
    limit: usize,
) -> Result<(), TheoryImageError> {
    while let Some((subject, state_id, slots_to_root)) = pending.pop() {
        charge_pattern_check(checks, limit)?;
        let state = states
            .get(state_id.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "pattern state",
                owner: entry,
                target: state_id.0,
            })?;
        if slots_to_root.len() != state.slot_count as usize {
            return Err(TheoryImageError::AutomatonShape { entry });
        }
        match (subject, &state.form) {
            (PatternSubject::Slot(variable), TheoryPatternStateFormV1::Bind) => {
                let root_slot = *slots_to_root
                    .first()
                    .ok_or(TheoryImageError::AutomatonShape { entry })?;
                if slot_variables.get(root_slot as usize) != Some(&variable) {
                    return Err(TheoryImageError::AutomatonShape { entry });
                }
            },
            (PatternSubject::Term(term), TheoryPatternStateFormV1::Bind) => {
                let node =
                    terms
                        .get(term.0 as usize)
                        .ok_or(TheoryImageError::UnknownReference {
                            kind: "pattern term",
                            owner: entry,
                            target: term.0,
                        })?;
                let TheoryImageTermFormV1::Slot(variable) = node.form else {
                    return Err(TheoryImageError::AutomatonShape { entry });
                };
                pending.push((PatternSubject::Slot(variable), state_id, slots_to_root));
            },
            (
                PatternSubject::Term(term),
                TheoryPatternStateFormV1::Apply { operator, arguments },
            ) => {
                let node =
                    terms
                        .get(term.0 as usize)
                        .ok_or(TheoryImageError::UnknownReference {
                            kind: "pattern term",
                            owner: entry,
                            target: term.0,
                        })?;
                let TheoryImageTermFormV1::Apply {
                    operator: expected_operator,
                    arguments: term_arguments,
                    slots,
                    remainder,
                    pathmap_mode,
                } = &node.form
                else {
                    return Err(TheoryImageError::AutomatonShape { entry });
                };
                if expected_operator != operator
                    || remainder.is_some()
                    || !slots.is_empty()
                    || pathmap_mode.is_some()
                {
                    return Err(TheoryImageError::AutomatonShape { entry });
                }
                let subjects = slots
                    .iter()
                    .copied()
                    .map(PatternSubject::Slot)
                    .chain(term_arguments.iter().copied().map(PatternSubject::Term))
                    .collect::<Vec<_>>();
                if subjects.len() != arguments.len() {
                    return Err(TheoryImageError::AutomatonShape { entry });
                }
                for (subject, invocation) in subjects.into_iter().zip(arguments).rev() {
                    let child_slots = invocation
                        .parent_slots
                        .iter()
                        .map(|parent| {
                            slots_to_root
                                .get(*parent as usize)
                                .copied()
                                .ok_or(TheoryImageError::AutomatonShape { entry })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    pending.push((subject, invocation.state, child_slots));
                }
            },
            (PatternSubject::Slot(_), TheoryPatternStateFormV1::Apply { .. }) => {
                return Err(TheoryImageError::AutomatonShape { entry });
            },
        }
    }
    Ok(())
}

fn charge_pattern_check(checks: &mut usize, limit: usize) -> Result<(), TheoryImageError> {
    *checks = checks
        .checked_add(1)
        .ok_or(TheoryImageError::LengthOverflow)?;
    enforce(*checks, limit, "automaton correspondence checks")
}

fn rule_is_positional(rule: &TheoryRuleProgramV1) -> Result<bool, TheoryImageError> {
    if rule.disposition != TheoryRuleDispositionV1::Executable {
        return Ok(false);
    }
    term_roots_are_positional_image(&rule.terms, &[rule.left], rule.id.0)
}

fn term_roots_are_positional_image(
    terms: &[TheoryImageTermNodeV1],
    roots: &[TheoryTermId],
    owner: u32,
) -> Result<bool, TheoryImageError> {
    let mut pending = roots.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        let node = terms
            .get(term.0 as usize)
            .ok_or(TheoryImageError::UnknownReference {
                kind: "pattern term",
                owner,
                target: term.0,
            })?;
        match &node.form {
            TheoryImageTermFormV1::Map { .. } => return Ok(false),
            TheoryImageTermFormV1::Apply {
                operator, arguments, slots, remainder, ..
            } => {
                if remainder.is_some() || !slots.is_empty() {
                    return Ok(false);
                }
                if matches!(
                    operator,
                    TheoryImageOperatorV1::Abstraction { .. }
                        | TheoryImageOperatorV1::Judgment { .. }
                        | TheoryImageOperatorV1::Collection {
                            kind: CollectionKind::Bag
                                | CollectionKind::Set
                                | CollectionKind::Map
                                | CollectionKind::PathMap,
                            ..
                        }
                ) {
                    return Ok(false);
                }
                pending.extend(arguments.iter().copied());
            },
            TheoryImageTermFormV1::Slot(_) => {},
        }
    }
    Ok(true)
}

fn check_fingerprint(
    actual: [u8; 32],
    expected: [u8; 32],
    kind: &'static str,
) -> Result<(), TheoryImageError> {
    if actual != expected {
        return Err(TheoryImageError::FingerprintMismatch(kind));
    }
    Ok(())
}

fn dense(kind: &'static str, expected: u32, actual: u32) -> Result<(), TheoryImageError> {
    if expected != actual {
        return Err(TheoryImageError::NonDenseId { kind, expected, actual });
    }
    Ok(())
}

fn enforce(actual: usize, limit: usize, kind: &'static str) -> Result<(), TheoryImageError> {
    if actual > limit {
        return Err(TheoryImageError::LimitExceeded(kind));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_semantic_key::SemanticHash;

    #[test]
    fn image_fingerprint_domain_is_not_the_language_domain() {
        let language_bytes = b"same bytes";
        let mut language = blake3::Hasher::new();
        language.update(b"mettail-language-core/2\0");
        language.update(language_bytes);
        let mut image = blake3::Hasher::new();
        image.update(b"mettail-theory-semantic-image/1\0");
        image.update(language_bytes);
        assert_ne!(language.finalize(), image.finalize());
    }

    #[test]
    fn image_rights_are_demands_not_handle_authority() {
        let demand = LanguageRights::from_rights([crate::LanguageRight::Reduce]);
        let grant = LanguageRights::none();
        assert!(grant.attenuate(&demand).iter().next().is_none());
    }

    #[test]
    fn theory_operator_exact_keys_are_injective_over_every_variant() {
        let operators = vec![
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(0) },
            TheoryImageOperatorV1::Substitution {
                sort: TheorySortId(0),
                function: TheorySortId(1),
            },
            TheoryImageOperatorV1::Substitution {
                sort: TheorySortId(0),
                function: TheorySortId(2),
            },
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(0),
                element: TheorySortId(1),
                kind: CollectionKind::List,
            },
            TheoryImageOperatorV1::Product { sort: TheorySortId(0) },
            TheoryImageOperatorV1::Product { sort: TheorySortId(1) },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::String("a".into()),
            },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Bytes(vec![b'a']),
            },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Integer(97),
            },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::FloatBits(97),
            },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Boolean(true),
            },
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Unit,
            },
        ];
        let keys = operators
            .iter()
            .map(SemanticHash::content_key)
            .collect::<Vec<_>>();
        assert!(keys
            .iter()
            .enumerate()
            .all(|(index, key)| keys[..index].iter().all(|prior| prior != key)));
        assert_eq!(operators[0].content_key(), operators[0].clone().content_key());
    }
}
