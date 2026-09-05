//! Runtime execution boundary for verified GSLT semantic images.
//!
//! This module restores the compiler-produced positional pattern quotient and
//! source-exact generalized rules into one bounded Horn/WPDA evaluator. It
//! does not rebuild source syntax, parse text, or introduce a second semantic
//! evaluator.

use dovetail::hash::HashMap;
use dovetail::key::{ContentKey, FramedSemanticOperator, SemanticHash};
use dovetail::rules::Subst;
use dovetail::set_automaton::{
    FlatAutomatonEntryImage, FlatAutomatonImage, FlatAutomatonInvocationImage,
    FlatAutomatonNodeImage, FlatAutomatonRestoreError, FlatAutomatonStateImage, PatternId,
    SetAutomaton, SetAutomatonSearchStop, SetAutomatonStats,
};
use dovetail::{egraph::EClassId, egraph::EGraph, egraph::EGraphConfig, egraph::ENode};
use mettail_grammar_core::{
    CollectionKind, LanguageRight, LanguageRights, PathMapModeV1, SemanticEffectClassV1,
    TheoryActionId, TheoryEffectId, TheoryImageOperatorV1, TheoryImageTermFormV1, TheoryJudgmentId,
    TheoryJudgmentPatternAutomatonV1, TheoryJudgmentRuleProgramId, TheoryLimitsV1,
    TheoryLiteralCarrierV1, TheoryPatternAutomatonV1, TheoryPatternStateFormV1,
    TheoryPatternStateId, TheoryPatternStateV1, TheoryResourceProfileV1, TheoryRuleDispositionV1,
    TheoryRuleOriginV1, TheoryRuleProgramId, TheoryRuleProgramV1, TheorySemanticImageV1,
    TheorySortId, TheorySortKindImageV1, TheoryVariableId,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

const THEORY_OPERATOR_DISCRIMINANT: u32 = u32::MAX;
const THEORY_OPERATOR_DOMAIN: &[u8] = b"mettail-theory-machine-operator/1";
const THEORY_PATHMAP_MODE_DOMAIN: &[u8] = b"mettail-theory-pathmap-mode/1";

/// Inject one closed theory-image operator into the shared semantic-machine
/// carrier.  The stable discriminant selects the theory namespace and the two
/// framed payload segments retain the domain and the operator's complete exact
/// content, so no finite digest becomes semantic identity.
pub fn theory_operator_to_machine(operator: &TheoryImageOperatorV1) -> FramedSemanticOperator {
    if let TheoryImageOperatorV1::PathMapMode { sort, mode } = operator {
        return theory_pathmap_mode_to_machine(*sort, *mode);
    }
    let mut exact = Vec::new();
    operator.write_content(&mut exact);
    FramedSemanticOperator::new(
        THEORY_OPERATOR_DISCRIMINANT,
        vec![THEORY_OPERATOR_DOMAIN.to_vec(), exact],
    )
}

fn theory_pathmap_mode_to_machine(
    sort: TheorySortId,
    mode: PathMapModeV1,
) -> FramedSemanticOperator {
    FramedSemanticOperator::new(
        THEORY_OPERATOR_DISCRIMINANT,
        vec![
            THEORY_PATHMAP_MODE_DOMAIN.to_vec(),
            sort.0.to_le_bytes().to_vec(),
            vec![match mode {
                PathMapModeV1::NeutralEmpty => 0,
                PathMapModeV1::Set => 1,
                PathMapModeV1::Map => 2,
            }],
        ],
    )
}

/// Failure restoring an admitted theory's reusable matchers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryPatternRestoreError {
    /// A dense image identifier cannot be represented on this target.
    IdentifierOverflow,
    /// The image violated Dovetail's canonical flat-automaton contract.
    Automaton(FlatAutomatonRestoreError),
    /// A checked allocation failed while restoring reusable matcher state.
    Allocation,
}

impl From<FlatAutomatonRestoreError> for TheoryPatternRestoreError {
    fn from(error: FlatAutomatonRestoreError) -> Self {
        Self::Automaton(error)
    }
}

/// Restore the exact positional quotient stored in a verified theory image.
///
/// `TheoryPatternEntryV1::rule` is the semantic dispatch identity; the entry's
/// dense `id` is only its serialized position.  Slot names are reconstructed
/// from dense variable identifiers using the same injective encoding as the
/// compiler.  [`SetAutomaton::restore_flat_image`] independently rechecks
/// backward references, the canonical state quotient, slot interfaces, and
/// entry uniqueness before any matcher can escape.
pub fn restore_theory_pattern_automaton(
    image: &TheoryPatternAutomatonV1,
) -> Result<SetAutomaton<FramedSemanticOperator>, TheoryPatternRestoreError> {
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(image.entries.len())
        .map_err(|_| TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation))?;
    for entry in &image.entries {
        entries.push(TheoryPatternEntryRef {
            pattern: PatternId(
                usize::try_from(entry.rule.0)
                    .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
            ),
            root: entry.root,
            slot_variables: &entry.slot_variables,
        });
    }
    restore_theory_pattern_parts(&image.states, &entries)
}

/// Restore the exact positional quotient for Horn-clause conclusions.
/// Judgment roots use the same closed operator carrier and set-automaton
/// implementation as transition rules; only their dispatch identifier type
/// differs in the serialized image.
pub fn restore_theory_judgment_pattern_automaton(
    image: &TheoryJudgmentPatternAutomatonV1,
) -> Result<SetAutomaton<FramedSemanticOperator>, TheoryPatternRestoreError> {
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(image.entries.len())
        .map_err(|_| TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation))?;
    for entry in &image.entries {
        entries.push(TheoryPatternEntryRef {
            pattern: PatternId(
                usize::try_from(entry.rule.0)
                    .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
            ),
            root: entry.root,
            slot_variables: &entry.slot_variables,
        });
    }
    restore_theory_pattern_parts(&image.states, &entries)
}

struct TheoryPatternEntryRef<'a> {
    pattern: PatternId,
    root: TheoryPatternStateId,
    slot_variables: &'a [TheoryVariableId],
}

fn restore_theory_pattern_parts(
    image_states: &[TheoryPatternStateV1],
    image_entries: &[TheoryPatternEntryRef<'_>],
) -> Result<SetAutomaton<FramedSemanticOperator>, TheoryPatternRestoreError> {
    let mut states = Vec::new();
    states
        .try_reserve_exact(image_states.len())
        .map_err(|_| TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation))?;
    for state in image_states {
        let node = match &state.form {
            TheoryPatternStateFormV1::Bind => FlatAutomatonNodeImage::Var,
            TheoryPatternStateFormV1::Apply { operator, arguments } => {
                let mut invocations = Vec::new();
                invocations
                    .try_reserve_exact(arguments.len())
                    .map_err(|_| {
                        TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation)
                    })?;
                for invocation in arguments {
                    let mut parent_slots = Vec::new();
                    parent_slots
                        .try_reserve_exact(invocation.parent_slots.len())
                        .map_err(|_| {
                            TheoryPatternRestoreError::Automaton(
                                FlatAutomatonRestoreError::Allocation,
                            )
                        })?;
                    for slot in &invocation.parent_slots {
                        parent_slots.push(
                            usize::try_from(*slot)
                                .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
                        );
                    }
                    invocations.push(FlatAutomatonInvocationImage {
                        state: usize::try_from(invocation.state.0)
                            .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
                        parent_slots,
                    });
                }
                FlatAutomatonNodeImage::App {
                    op: theory_operator_to_machine(operator),
                    args: invocations,
                }
            },
        };
        states.push(FlatAutomatonStateImage {
            slot_count: usize::try_from(state.slot_count)
                .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
            node,
        });
    }

    let mut entries = Vec::new();
    entries
        .try_reserve_exact(image_entries.len())
        .map_err(|_| TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation))?;
    for entry in image_entries {
        let mut slot_names = Vec::new();
        slot_names
            .try_reserve_exact(entry.slot_variables.len())
            .map_err(|_| {
                TheoryPatternRestoreError::Automaton(FlatAutomatonRestoreError::Allocation)
            })?;
        for variable in entry.slot_variables {
            slot_names.push(format!("v{}", variable.0));
        }
        entries.push(FlatAutomatonEntryImage {
            id: entry.pattern,
            root_state: usize::try_from(entry.root.0)
                .map_err(|_| TheoryPatternRestoreError::IdentifierOverflow)?,
            slot_names,
        });
    }

    SetAutomaton::restore_flat_image(FlatAutomatonImage { states, entries }).map_err(Into::into)
}

/// Why bounded semantic matching could not establish a complete answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticMatchUndetermined {
    WorkBudgetExhausted,
    Cancelled,
    InvalidImageEvidence,
    PremiseEvaluationUnavailable,
    ResourceGradeUnavailable,
    InputLimitExceeded,
    OutputLimitExceeded,
    EGraphNodeBudgetExhausted,
    AllocationFailed,
    FrontierLimitExceeded,
    ProofLimitExceeded,
}

/// A complete negative semantic-matching result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticMatchRefutation {
    RequestRejected,
    NoTransition,
    PremiseRefuted,
}

/// One matcher-owned substitution for an action-selected rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticRuleMatch {
    pub rule: TheoryRuleProgramId,
    pub root: EClassId,
    pub substitution: BTreeMap<TheoryVariableId, EClassId>,
}

/// Complete result of the private action-match phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenSemanticMatches {
    pub matches: Vec<SemanticRuleMatch>,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

/// Three-valued result used by every bounded semantic stage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticMatchDecision {
    Proven(ProvenSemanticMatches),
    Refuted(SemanticMatchRefutation),
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
        stats: SetAutomatonStats,
    },
}

/// One conclusion match for a checked Horn-clause activation. Premise
/// discharge owns the activation namespace and may extend this substitution
/// with premise-only existential variables before anything is published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticJudgmentHeadMatch {
    pub rule: TheoryJudgmentRuleProgramId,
    pub substitution: BTreeMap<TheoryVariableId, EClassId>,
}

/// Complete private head-match set for one ground judgment query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenSemanticJudgmentHeads {
    pub matches: Vec<SemanticJudgmentHeadMatch>,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

/// Three-valued result of conclusion dispatch. This is deliberately named a
/// head decision: a successful head match is not a proof until every premise
/// in that fresh clause activation has succeeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticJudgmentHeadDecision {
    Proven(ProvenSemanticJudgmentHeads),
    Refuted(SemanticMatchRefutation),
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
        stats: SetAutomatonStats,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SemanticJudgmentProofStep {
    pub activation: u64,
    pub rule: TheoryJudgmentRuleProgramId,
    pub parent_activation: Option<u64>,
    pub premise_index: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticJudgmentProofReceipt {
    pub language_fingerprint: [u8; 32],
    pub theory_fingerprint: [u8; 32],
    pub image_fingerprint: [u8; 32],
    pub judgment: TheoryJudgmentId,
    pub arguments: Vec<Vec<u8>>,
    pub steps: Vec<SemanticJudgmentProofStep>,
    pub work: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenSemanticJudgmentProofs {
    pub proofs: Vec<SemanticJudgmentProofReceipt>,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticJudgmentDecision {
    Proven(ProvenSemanticJudgmentProofs),
    Refuted(SemanticMatchRefutation),
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
        stats: SetAutomatonStats,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticJudgmentLimits {
    pub work: u64,
    pub frontier: usize,
    pub proofs: usize,
    pub proof_nodes: usize,
    pub term_nodes: usize,
    pub term_bytes: usize,
}

impl From<TheoryLimitsV1> for SemanticJudgmentLimits {
    fn from(limits: TheoryLimitsV1) -> Self {
        Self {
            work: u64::from(limits.max_steps),
            frontier: limits.max_frontier as usize,
            proofs: limits.max_frontier as usize,
            proof_nodes: limits.max_proof_nodes as usize,
            term_nodes: limits.max_term_nodes as usize,
            term_bytes: limits.max_output_bytes as usize,
        }
    }
}

/// Bounds used to admit one canonical semantic input before action execution.
/// They are deliberately separate from successor/output limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticInputLimits {
    pub work: u64,
    pub nodes: usize,
    pub bytes: usize,
}

#[derive(Clone, Copy)]
struct GroundKeyLimits {
    work: u64,
    nodes: usize,
    bytes: usize,
    limit_reason: SemanticMatchUndetermined,
}

#[derive(Clone, Copy)]
struct TermConstructionLimits {
    work: u64,
    nodes: usize,
    bytes: usize,
}

struct TermInstantiation<'image, 'rule, 'substitution> {
    image: &'image TheorySemanticImageV1,
    rule: &'rule mettail_grammar_core::TheoryRuleProgramV1,
    substitution: &'substitution ActionSubstitution,
    root: mettail_grammar_core::TheoryTermId,
    limits: TermConstructionLimits,
}

struct ConstructionLookupContext<'substitution, 'graph, 'work, 'cancel, C> {
    substitution: &'substitution ActionSubstitution,
    egraph: &'graph mut EGraph<FramedSemanticOperator>,
    work: &'work mut u64,
    work_limit: u64,
    is_cancelled: &'cancel mut C,
}

struct CollectionCanonicalization<'image, 'operator> {
    image: &'image TheorySemanticImageV1,
    operator: &'operator TheoryImageOperatorV1,
    pathmap_mode: Option<PathMapModeV1>,
    limits: TermConstructionLimits,
}

#[derive(Clone, Copy)]
struct ProjectionLimits {
    work: u64,
    nodes: usize,
    bytes: usize,
    limit_reason: SemanticMatchUndetermined,
}

struct TermConstructionEnvironment {
    parent: Option<usize>,
    bindings: Vec<(TheoryVariableId, EClassId)>,
}

enum TermConstructionTask {
    Evaluate {
        term: mettail_grammar_core::TheoryTermId,
        environment: Option<usize>,
    },
    FinishApply {
        operator: TheoryImageOperatorV1,
        arguments: Vec<mettail_grammar_core::TheoryTermId>,
        slots: Vec<TheoryVariableId>,
        remainder: Option<TheoryVariableId>,
        pathmap_mode: Option<PathMapModeV1>,
        environment: Option<usize>,
        value_base: usize,
    },
    FinishMapSources {
        target_sort: TheorySortId,
        sources: Vec<mettail_grammar_core::TheoryTermId>,
        parameters: Vec<TheoryVariableId>,
        body: mettail_grammar_core::TheoryTermId,
        environment: Option<usize>,
        value_base: usize,
    },
    FinishMapBodies {
        target_sort: TheorySortId,
        row_count: usize,
        value_base: usize,
    },
}

/// An exact, acyclic, single-representative semantic input. Fields are private
/// so action execution cannot be invoked with a forged structural key.
pub struct SemanticTransitionInput {
    egraph: EGraph<FramedSemanticOperator>,
    root: EClassId,
    exact_key: ContentKey,
    admission_work: u64,
}

impl SemanticTransitionInput {
    pub fn admit<C>(
        egraph: EGraph<FramedSemanticOperator>,
        root: EClassId,
        limits: SemanticInputLimits,
        mut is_cancelled: C,
    ) -> SemanticInputDecision
    where
        C: FnMut() -> bool,
    {
        let Some(source_root) = egraph.try_find(root) else {
            return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        };
        if egraph.nodes(source_root).is_empty() {
            return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }
        let mut work = 0;
        let exact_key = match exact_ground_key(
            &egraph,
            source_root,
            &mut work,
            GroundKeyLimits {
                work: limits.work,
                nodes: limits.nodes,
                bytes: limits.bytes,
                limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            },
            &mut is_cancelled,
        ) {
            Ok(exact_key) => exact_key,
            Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
            },
            Err(reason) => return SemanticInputDecision::Undetermined { reason, work },
        };
        let (projected, remap) = match project_reachable_egraph(
            &egraph,
            &[source_root],
            &mut work,
            ProjectionLimits {
                work: limits.work,
                nodes: limits.nodes,
                bytes: limits.bytes,
                limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            },
            &mut is_cancelled,
        ) {
            Ok(projected) => projected,
            Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
            },
            Err(reason) => return SemanticInputDecision::Undetermined { reason, work },
        };
        let projected_root = match remapped_eclass(&remap, source_root) {
            Ok(root) => root,
            Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
            },
            Err(reason) => return SemanticInputDecision::Undetermined { reason, work },
        };
        SemanticInputDecision::Proven(Self {
            root: projected_root,
            egraph: projected,
            exact_key,
            admission_work: work,
        })
    }

    pub fn egraph(&self) -> &EGraph<FramedSemanticOperator> {
        &self.egraph
    }

    pub fn root(&self) -> EClassId {
        self.root
    }

    pub fn exact_key(&self) -> &ContentKey {
        &self.exact_key
    }

    pub fn admission_work(&self) -> u64 {
        self.admission_work
    }
}

pub enum SemanticInputDecision {
    Proven(SemanticTransitionInput),
    Refuted(SemanticMatchRefutation),
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
    },
}

pub(crate) struct SemanticActionMatchRequest<'a> {
    pub image: &'a TheorySemanticImageV1,
    pub granted_rights: &'a LanguageRights,
    pub egraph: &'a mut EGraph<FramedSemanticOperator>,
    pub root: EClassId,
    pub limits: SemanticTransitionLimits,
}

pub struct SemanticJudgmentHeadRequest<'a> {
    pub image: &'a TheorySemanticImageV1,
    pub judgment: TheoryJudgmentId,
    pub granted_rights: &'a LanguageRights,
    pub egraph: &'a EGraph<FramedSemanticOperator>,
    pub arguments: &'a [EClassId],
    pub work_limit: u64,
}

pub struct SemanticJudgmentProofRequest<'a> {
    pub image: &'a TheorySemanticImageV1,
    pub judgment: TheoryJudgmentId,
    pub granted_rights: &'a LanguageRights,
    pub egraph: &'a EGraph<FramedSemanticOperator>,
    pub arguments: &'a [EClassId],
    pub limits: SemanticJudgmentLimits,
}

pub struct SemanticActionExecutionRequest<'a> {
    pub image: &'a TheorySemanticImageV1,
    pub action: TheoryActionId,
    pub granted_rights: &'a LanguageRights,
    pub input: SemanticTransitionInput,
    pub limits: SemanticTransitionLimits,
}

/// Verified matcher shared by action execution and OSLF checking.
///
/// Construction restores the exact positional quotient. Non-positional rules
/// execute from their canonical image through the bounded Horn/WPDA path.
/// Calls never mutate the matcher; all per-request substitutions and
/// diagnostics remain private until a complete bounded scan and action filter
/// have succeeded.
pub struct SemanticTransitionMatcher {
    transition_automaton: SetAutomaton<FramedSemanticOperator>,
    judgment_automaton: SetAutomaton<FramedSemanticOperator>,
}

#[derive(Clone, Copy)]
enum TransitionRuleSelection<'a> {
    ActionRules(&'a [TheoryRuleProgramId]),
    RewriteRelation(TheorySortId),
}

struct TransitionRuleMatchRequest<'a> {
    image: &'a TheorySemanticImageV1,
    egraph: &'a mut EGraph<FramedSemanticOperator>,
    root: EClassId,
    limits: SemanticTransitionLimits,
    input_sort: TheorySortId,
}

impl TransitionRuleSelection<'_> {
    fn includes(self, rule: &TheoryRuleProgramV1) -> Result<bool, SemanticMatchUndetermined> {
        if rule.disposition != TheoryRuleDispositionV1::Executable {
            return Ok(false);
        }
        match self {
            Self::ActionRules(rules) => Ok(rules.contains(&rule.id)),
            Self::RewriteRelation(sort) => {
                if !matches!(rule.origin, TheoryRuleOriginV1::Rewrite { .. }) {
                    return Ok(false);
                }
                let source = rule
                    .terms
                    .get(rule.left.0 as usize)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                Ok(source.sort == sort)
            },
        }
    }
}

impl SemanticTransitionMatcher {
    pub fn restore(image: &TheorySemanticImageV1) -> Result<Self, TheoryPatternRestoreError> {
        Ok(Self {
            transition_automaton: restore_theory_pattern_automaton(&image.patterns)?,
            judgment_automaton: restore_theory_judgment_pattern_automaton(
                &image.judgment_patterns,
            )?,
        })
    }

    /// Match one action at one canonical root under explicit authority and
    /// work bounds. Nested redexes found by the shared e-graph scan are not
    /// action successors of `root` and are discarded before publication.
    pub(crate) fn match_action<C>(
        &self,
        action_id: TheoryActionId,
        request: SemanticActionMatchRequest<'_>,
        is_cancelled: C,
    ) -> SemanticMatchDecision
    where
        C: FnMut() -> bool,
    {
        let SemanticActionMatchRequest {
            image,
            granted_rights,
            egraph,
            root,
            limits,
        } = request;
        let Some(action) = image
            .actions
            .get(action_id.0 as usize)
            .filter(|candidate| candidate.id == action_id)
        else {
            return SemanticMatchDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        };
        if !action.required_rights.is_subset_of(granted_rights) || egraph.nodes(root).is_empty() {
            return SemanticMatchDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }

        let [input_sort] = action.domain.as_slice() else {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work: 0,
                stats: SetAutomatonStats::default(),
            };
        };
        if action.transitions.is_empty() {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work: 0,
                stats: SetAutomatonStats::default(),
            };
        }
        for (index, rule_id) in action.transitions.iter().enumerate() {
            if action.transitions[..index].contains(rule_id) {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            }
            let Some(rule) = image.rules.get(rule_id.0 as usize).filter(|candidate| {
                candidate.id == *rule_id
                    && candidate.disposition == TheoryRuleDispositionV1::Executable
            }) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            };
            let Some(source) = rule.terms.get(rule.left.0 as usize) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            };
            let Some(target) = rule.terms.get(rule.right.0 as usize) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            };
            if source.sort != *input_sort || target.sort != action.codomain {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            }
        }
        self.match_transition_rules(
            TransitionRuleSelection::ActionRules(&action.transitions),
            TransitionRuleMatchRequest {
                image,
                egraph,
                root,
                limits,
                input_sort: *input_sort,
            },
            is_cancelled,
        )
    }

    fn match_rewrite_relation<C>(
        &self,
        sort: TheorySortId,
        request: SemanticActionMatchRequest<'_>,
        is_cancelled: C,
    ) -> SemanticMatchDecision
    where
        C: FnMut() -> bool,
    {
        let SemanticActionMatchRequest {
            image,
            granted_rights,
            egraph,
            root,
            limits,
        } = request;
        if !granted_rights.contains(LanguageRight::Reduce) || egraph.nodes(root).is_empty() {
            return SemanticMatchDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }
        self.match_transition_rules(
            TransitionRuleSelection::RewriteRelation(sort),
            TransitionRuleMatchRequest {
                image,
                egraph,
                root,
                limits,
                input_sort: sort,
            },
            is_cancelled,
        )
    }

    fn match_transition_rules<C>(
        &self,
        selection: TransitionRuleSelection<'_>,
        request: TransitionRuleMatchRequest<'_>,
        mut is_cancelled: C,
    ) -> SemanticMatchDecision
    where
        C: FnMut() -> bool,
    {
        let TransitionRuleMatchRequest { image, egraph, root, limits, input_sort } = request;
        let mut validator = HornEvaluator {
            image,
            egraph,
            work: 0,
            work_limit: limits.work,
            ground_key_nodes: limits.term_nodes,
            ground_key_bytes: limits.term_bytes,
            ground_key_limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            is_cancelled: &mut is_cancelled,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 0,
        };
        if let Err(reason) = validator.validate_ground_term(root, input_sort) {
            return match reason {
                SemanticMatchUndetermined::InvalidImageEvidence => {
                    SemanticMatchDecision::Refuted(SemanticMatchRefutation::RequestRejected)
                },
                reason => SemanticMatchDecision::Undetermined {
                    reason,
                    work: validator.work,
                    stats: SetAutomatonStats::default(),
                },
            };
        }
        let validation_work = validator.work;
        drop(validator);
        let Some(remaining_work) = limits.work.checked_sub(validation_work) else {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work: validation_work,
                stats: SetAutomatonStats::default(),
            };
        };

        let scan = match self.transition_automaton.search_eclass_bounded(
            egraph,
            root,
            remaining_work,
            &mut is_cancelled,
        ) {
            Ok(scan) => scan,
            Err(failure) => {
                let Some(work) = validation_work.checked_add(failure.work) else {
                    return SemanticMatchDecision::Undetermined {
                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                        work: validation_work,
                        stats: failure.stats,
                    };
                };
                return SemanticMatchDecision::Undetermined {
                    reason: semantic_stop_reason(failure.reason),
                    work,
                    stats: failure.stats,
                };
            },
        };

        let mut selected_count = 0usize;
        for rule in &image.rules {
            match selection.includes(rule) {
                Ok(true) => {
                    let Some(next) = selected_count.checked_add(1) else {
                        return SemanticMatchDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work: validation_work,
                            stats: scan.run.stats,
                        };
                    };
                    selected_count = next;
                },
                Ok(false) => {},
                Err(reason) => {
                    return SemanticMatchDecision::Undetermined {
                        reason,
                        work: validation_work,
                        stats: scan.run.stats,
                    };
                },
            }
        }
        let mut entries_by_rule = Vec::new();
        if entries_by_rule
            .try_reserve_exact(image.rules.len())
            .is_err()
        {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work: validation_work,
                stats: scan.run.stats,
            };
        }
        entries_by_rule.extend((0..image.rules.len()).map(|_| None));
        for entry in &image.patterns.entries {
            let Some(slot) = entries_by_rule.get_mut(entry.rule.0 as usize) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: validation_work,
                    stats: scan.run.stats,
                };
            };
            if slot.replace(entry).is_some() {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: validation_work,
                    stats: scan.run.stats,
                };
            }
        }
        let stats = scan.run.stats;
        let Some(mut work) = validation_work.checked_add(scan.work) else {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work: validation_work,
                stats,
            };
        };
        let mut matches = Vec::new();
        if matches
            .try_reserve(selected_count.min(limits.outputs))
            .is_err()
        {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work,
                stats,
            };
        }
        for matched in scan.run.matches {
            if is_cancelled() {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::Cancelled,
                    work,
                    stats,
                };
            }
            if work == limits.work {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::WorkBudgetExhausted,
                    work,
                    stats,
                };
            }
            work += 1;
            let Ok(rule_id) = u32::try_from(matched.pattern.0).map(TheoryRuleProgramId) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(rule) = image
                .rules
                .get(rule_id.0 as usize)
                .filter(|candidate| candidate.id == rule_id)
            else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let selected = match selection.includes(rule) {
                Ok(selected) => selected,
                Err(reason) => {
                    return SemanticMatchDecision::Undetermined { reason, work, stats };
                },
            };
            if !selected || !egraph.equiv(matched.root, root) {
                continue;
            }
            let Some(entry) = entries_by_rule
                .get(rule_id.0 as usize)
                .and_then(|entry| *entry)
            else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let substitution = match project_automaton_substitution(
                &entry.slot_variables,
                &matched.subst,
                egraph,
                &mut work,
                limits.work,
                &mut is_cancelled,
            ) {
                Ok(substitution) => substitution,
                Err(reason) => {
                    return SemanticMatchDecision::Undetermined { reason, work, stats };
                },
            };
            if matches.len() == limits.outputs {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::OutputLimitExceeded,
                    work,
                    stats,
                };
            }
            if matches.try_reserve(1).is_err() {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::AllocationFailed,
                    work,
                    stats,
                };
            }
            matches.push(SemanticRuleMatch {
                rule: rule_id,
                root: egraph.find(matched.root),
                substitution,
            });
        }

        for rule in &image.rules {
            let selected = match selection.includes(rule) {
                Ok(selected) => selected,
                Err(reason) => {
                    return SemanticMatchDecision::Undetermined { reason, work, stats };
                },
            };
            if !selected {
                continue;
            }
            let rule_id = rule.id;
            let Some(entry) = entries_by_rule.get(rule_id.0 as usize) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            if entry.is_some() {
                continue;
            }
            let mut evaluator = HornEvaluator {
                image,
                egraph,
                work,
                work_limit: limits.work,
                ground_key_nodes: limits.term_nodes,
                ground_key_bytes: limits.term_bytes,
                ground_key_limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
                is_cancelled: &mut is_cancelled,
                synthetic_terms: Vec::new(),
                lexical_scopes: Vec::new(),
                collection_states: Vec::new(),
                comprehension_states: Vec::new(),
                derived_collections: Vec::new(),
                next_activation: 0,
            };
            let activation = match evaluator.fresh_activation() {
                Ok(activation) => activation,
                Err(reason) => {
                    return SemanticMatchDecision::Undetermined { reason, work, stats };
                },
            };
            let equation = [(
                HornTermRef::Clause {
                    activation,
                    rule: HornRuleRef::Transition(rule.id),
                    term: rule.left,
                    scope: None,
                },
                HornTermRef::Ground { class: root, sort: input_sort },
            )];
            let horn_substitutions =
                match evaluator.unify_all(&equation, &Vec::new(), limits.frontier) {
                    Ok(substitutions) => substitutions,
                    Err(reason) => {
                        return SemanticMatchDecision::Undetermined {
                            reason,
                            work: evaluator.work,
                            stats,
                        };
                    },
                };
            if horn_substitutions.len() > limits.outputs.saturating_sub(matches.len()) {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::OutputLimitExceeded,
                    work: evaluator.work,
                    stats,
                };
            }
            let mut projected = Vec::new();
            if projected
                .try_reserve_exact(horn_substitutions.len())
                .is_err()
            {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::AllocationFailed,
                    work: evaluator.work,
                    stats,
                };
            }
            for substitution in &horn_substitutions {
                match evaluator.project_transition_substitution(rule, activation, substitution) {
                    Ok(substitution) => projected.push(substitution),
                    Err(reason) => {
                        return SemanticMatchDecision::Undetermined {
                            reason,
                            work: evaluator.work,
                            stats,
                        };
                    },
                }
            }
            work = evaluator.work;
            let synthetic_terms = std::mem::take(&mut evaluator.synthetic_terms);
            drop(evaluator);
            for projected in projected {
                let substitution = match materialize_horn_substitution(
                    egraph,
                    &synthetic_terms,
                    &projected,
                    &mut work,
                    TermConstructionLimits {
                        work: limits.work,
                        nodes: limits.term_nodes,
                        bytes: limits.term_bytes,
                    },
                    &mut is_cancelled,
                ) {
                    Ok(substitution) => substitution,
                    Err(reason) => {
                        return SemanticMatchDecision::Undetermined { reason, work, stats };
                    },
                };
                if matches.len() == limits.outputs {
                    return SemanticMatchDecision::Undetermined {
                        reason: SemanticMatchUndetermined::OutputLimitExceeded,
                        work,
                        stats,
                    };
                }
                if matches.try_reserve(1).is_err() {
                    return SemanticMatchDecision::Undetermined {
                        reason: SemanticMatchUndetermined::AllocationFailed,
                        work,
                        stats,
                    };
                }
                matches.push(SemanticRuleMatch {
                    rule: rule_id,
                    root: egraph.find(root),
                    substitution: substitution.into_iter().collect(),
                });
            }
        }

        if matches.is_empty() {
            SemanticMatchDecision::Refuted(SemanticMatchRefutation::NoTransition)
        } else {
            SemanticMatchDecision::Proven(ProvenSemanticMatches { matches, work, stats })
        }
    }

    /// Match the conclusions of one ground judgment query without publishing
    /// a proof. The synthetic judgment application is evaluated as a virtual
    /// root, so querying cannot mutate the caller's semantic e-graph.
    ///
    /// `Check` authorizes verification and `SearchProof` authorizes exploring
    /// rule alternatives. Possessing parse, reduce, or reflected grammar data
    /// alone is intentionally insufficient.
    pub fn match_judgment_heads<C>(
        &self,
        request: SemanticJudgmentHeadRequest<'_>,
        mut is_cancelled: C,
    ) -> SemanticJudgmentHeadDecision
    where
        C: FnMut() -> bool,
    {
        let SemanticJudgmentHeadRequest {
            image,
            judgment,
            granted_rights,
            egraph,
            arguments,
            work_limit,
        } = request;
        let Some(judgment_image) = image
            .judgments
            .get(judgment.0 as usize)
            .filter(|candidate| candidate.id == judgment)
        else {
            return SemanticJudgmentHeadDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        };
        if !granted_rights.contains(LanguageRight::Check)
            || !granted_rights.contains(LanguageRight::SearchProof)
            || arguments.len() != judgment_image.arguments.len()
            || arguments
                .iter()
                .any(|argument| egraph.nodes(*argument).is_empty())
        {
            return SemanticJudgmentHeadDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }

        let operator = theory_operator_to_machine(&TheoryImageOperatorV1::Judgment { judgment });
        let scan = match self.judgment_automaton.search_application_bounded(
            egraph,
            &operator,
            arguments,
            work_limit,
            &mut is_cancelled,
        ) {
            Ok(scan) => scan,
            Err(failure) => {
                return SemanticJudgmentHeadDecision::Undetermined {
                    reason: semantic_stop_reason(failure.reason),
                    work: failure.work,
                    stats: failure.stats,
                };
            },
        };

        let selected: BTreeSet<_> = judgment_image.rules.iter().copied().collect();
        let entries: BTreeMap<_, _> = image
            .judgment_patterns
            .entries
            .iter()
            .map(|entry| (entry.rule, entry))
            .collect();
        let stats = scan.run.stats;
        let mut work = scan.work;
        let mut matches = Vec::new();
        for matched in scan.run.matches {
            if let Err(reason) = charge_work(&mut work, work_limit, &mut is_cancelled) {
                return SemanticJudgmentHeadDecision::Undetermined { reason, work, stats };
            }
            let Ok(rule_id) = u32::try_from(matched.pattern.0).map(TheoryJudgmentRuleProgramId)
            else {
                return SemanticJudgmentHeadDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            if !selected.contains(&rule_id) {
                continue;
            }
            let Some(rule) = image
                .judgment_rules
                .get(rule_id.0 as usize)
                .filter(|candidate| candidate.id == rule_id && candidate.owner == judgment)
            else {
                return SemanticJudgmentHeadDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(entry) = entries.get(&rule.id) else {
                return SemanticJudgmentHeadDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let substitution = match project_automaton_substitution(
                &entry.slot_variables,
                &matched.subst,
                egraph,
                &mut work,
                work_limit,
                &mut is_cancelled,
            ) {
                Ok(substitution) => substitution,
                Err(reason) => {
                    return SemanticJudgmentHeadDecision::Undetermined { reason, work, stats };
                },
            };
            if matches.try_reserve(1).is_err() {
                return SemanticJudgmentHeadDecision::Undetermined {
                    reason: SemanticMatchUndetermined::AllocationFailed,
                    work,
                    stats,
                };
            }
            matches.push(SemanticJudgmentHeadMatch { rule: rule.id, substitution });
        }

        if matches.is_empty() {
            SemanticJudgmentHeadDecision::Refuted(SemanticMatchRefutation::NoTransition)
        } else {
            SemanticJudgmentHeadDecision::Proven(ProvenSemanticJudgmentHeads {
                matches,
                work,
                stats,
            })
        }
    }

    /// Search a checked Horn program for proofs of one ground judgment.
    ///
    /// The frontier is FIFO, every clause activation receives a globally fresh
    /// variable namespace, and every branch owns its substitution and proof
    /// trace. Results remain private until the frontier is completely explored;
    /// cancellation, exhaustion, malformed evidence, or a bound failure
    /// discards every proof accumulated so far.
    pub fn prove_ground_judgment<C>(
        &self,
        request: SemanticJudgmentProofRequest<'_>,
        is_cancelled: C,
    ) -> SemanticJudgmentDecision
    where
        C: FnMut() -> bool,
    {
        let SemanticJudgmentProofRequest {
            image,
            judgment,
            granted_rights,
            egraph,
            arguments,
            limits,
        } = request;
        let Some(declaration) = image
            .judgments
            .get(judgment.0 as usize)
            .filter(|candidate| candidate.id == judgment)
        else {
            return SemanticJudgmentDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        };
        if !granted_rights.contains(LanguageRight::Check)
            || !granted_rights.contains(LanguageRight::SearchProof)
            || arguments.len() != declaration.arguments.len()
        {
            return SemanticJudgmentDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }
        let image_fingerprint = match image.fingerprint() {
            Ok(fingerprint) => fingerprint,
            Err(_) => {
                return SemanticJudgmentDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: 0,
                    stats: SetAutomatonStats::default(),
                };
            },
        };
        let mut evaluator = HornEvaluator {
            image,
            egraph,
            work: 0,
            work_limit: limits.work,
            ground_key_nodes: limits.term_nodes,
            ground_key_bytes: limits.term_bytes,
            ground_key_limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            is_cancelled,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 0,
        };
        let mut argument_keys = Vec::new();
        if argument_keys.try_reserve_exact(arguments.len()).is_err() {
            return SemanticJudgmentDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work: evaluator.work,
                stats: SetAutomatonStats::default(),
            };
        }
        for (&argument, &sort) in arguments.iter().zip(&declaration.arguments) {
            match evaluator.validate_ground_term(argument, sort) {
                Ok(()) => {},
                Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                    return SemanticJudgmentDecision::Refuted(
                        SemanticMatchRefutation::RequestRejected,
                    );
                },
                Err(reason) => {
                    return SemanticJudgmentDecision::Undetermined {
                        reason,
                        work: evaluator.work,
                        stats: SetAutomatonStats::default(),
                    };
                },
            }
            match exact_ground_key(
                egraph,
                argument,
                &mut evaluator.work,
                GroundKeyLimits {
                    work: limits.work,
                    nodes: limits.term_nodes,
                    bytes: limits.term_bytes,
                    limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
                },
                &mut evaluator.is_cancelled,
            ) {
                Ok(key) => argument_keys.push(key.as_bytes().to_vec()),
                Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                    return SemanticJudgmentDecision::Refuted(
                        SemanticMatchRefutation::RequestRejected,
                    );
                },
                Err(reason) => {
                    return SemanticJudgmentDecision::Undetermined {
                        reason,
                        work: evaluator.work,
                        stats: SetAutomatonStats::default(),
                    };
                },
            }
        }

        let mut root_terms = Vec::new();
        if root_terms.try_reserve_exact(arguments.len()).is_err() {
            return SemanticJudgmentDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work: evaluator.work,
                stats: SetAutomatonStats::default(),
            };
        }
        for ((&class, &sort), _) in arguments
            .iter()
            .zip(&declaration.arguments)
            .zip(&argument_keys)
        {
            root_terms.push(HornTermRef::Ground { class: egraph.find(class), sort });
        }
        let mut root_goals = VecDeque::new();
        if root_goals.try_reserve_exact(1).is_err() {
            return SemanticJudgmentDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work: evaluator.work,
                stats: SetAutomatonStats::default(),
            };
        }
        root_goals.push_back(HornGoal {
            judgment,
            terms: root_terms,
            parent_activation: None,
            premise_index: None,
        });
        let mut frontier = VecDeque::new();
        if frontier.try_reserve_exact(1).is_err() {
            return SemanticJudgmentDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work: evaluator.work,
                stats: SetAutomatonStats::default(),
            };
        }
        frontier.push_back(HornBranch {
            goals: root_goals,
            substitution: Vec::new(),
            steps: Vec::new(),
        });
        let mut proofs = Vec::new();
        let mut stats = SetAutomatonStats::default();

        while let Some(mut branch) = frontier.pop_front() {
            if let Err(reason) = evaluator.charge() {
                return SemanticJudgmentDecision::Undetermined {
                    reason,
                    work: evaluator.work,
                    stats,
                };
            }
            let Some(goal) = branch.goals.pop_front() else {
                if proofs.len() == limits.proofs {
                    return SemanticJudgmentDecision::Undetermined {
                        reason: SemanticMatchUndetermined::ProofLimitExceeded,
                        work: evaluator.work,
                        stats,
                    };
                }
                let arguments = match clone_byte_vectors(&argument_keys) {
                    Ok(arguments) => arguments,
                    Err(reason) => {
                        return SemanticJudgmentDecision::Undetermined {
                            reason,
                            work: evaluator.work,
                            stats,
                        };
                    },
                };
                proofs.push(SemanticJudgmentProofReceipt {
                    language_fingerprint: image.language_fingerprint,
                    theory_fingerprint: image.theory_fingerprint,
                    image_fingerprint,
                    judgment,
                    arguments,
                    steps: branch.steps,
                    work: 0,
                });
                continue;
            };
            let Some(goal_declaration) = image
                .judgments
                .get(goal.judgment.0 as usize)
                .filter(|candidate| candidate.id == goal.judgment)
            else {
                return SemanticJudgmentDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: evaluator.work,
                    stats,
                };
            };
            if goal.terms.len() != goal_declaration.arguments.len() {
                return SemanticJudgmentDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work: evaluator.work,
                    stats,
                };
            }

            let candidate_rules =
                match evaluator.ground_arguments(&goal, &branch.substitution) {
                    Ok(Some(ground_arguments)) => {
                        let Some(remaining) = limits.work.checked_sub(evaluator.work) else {
                            return SemanticJudgmentDecision::Undetermined {
                                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                work: evaluator.work,
                                stats,
                            };
                        };
                        let decision = self.match_judgment_heads(
                            SemanticJudgmentHeadRequest {
                                image,
                                judgment: goal.judgment,
                                granted_rights,
                                egraph,
                                arguments: &ground_arguments,
                                work_limit: remaining,
                            },
                            &mut evaluator.is_cancelled,
                        );
                        let mut matched = BTreeSet::new();
                        match decision {
                            SemanticJudgmentHeadDecision::Proven(proven) => {
                                if let Err(reason) = absorb_matcher_accounting(
                                    &mut evaluator.work,
                                    limits.work,
                                    &mut stats,
                                    proven.work,
                                    proven.stats,
                                ) {
                                    return SemanticJudgmentDecision::Undetermined {
                                        reason,
                                        work: evaluator.work,
                                        stats,
                                    };
                                }
                                matched.extend(proven.matches.into_iter().map(|item| item.rule));
                            },
                            SemanticJudgmentHeadDecision::Refuted(
                                SemanticMatchRefutation::NoTransition,
                            ) => {},
                            SemanticJudgmentHeadDecision::Refuted(_) => {
                                return SemanticJudgmentDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work: evaluator.work,
                                    stats,
                                };
                            },
                            SemanticJudgmentHeadDecision::Undetermined {
                                reason,
                                work,
                                stats: head_stats,
                            } => {
                                if let Err(accounting_reason) = absorb_matcher_accounting(
                                    &mut evaluator.work,
                                    limits.work,
                                    &mut stats,
                                    work,
                                    head_stats,
                                ) {
                                    return SemanticJudgmentDecision::Undetermined {
                                        reason: accounting_reason,
                                        work: evaluator.work,
                                        stats,
                                    };
                                }
                                return SemanticJudgmentDecision::Undetermined {
                                    reason,
                                    work: evaluator.work,
                                    stats,
                                };
                            },
                        }
                        let positional: BTreeSet<_> = image
                            .judgment_patterns
                            .entries
                            .iter()
                            .map(|entry| entry.rule)
                            .collect();
                        let mut candidates = Vec::new();
                        if candidates
                            .try_reserve_exact(goal_declaration.rules.len())
                            .is_err()
                        {
                            return SemanticJudgmentDecision::Undetermined {
                                reason: SemanticMatchUndetermined::AllocationFailed,
                                work: evaluator.work,
                                stats,
                            };
                        }
                        candidates.extend(
                            goal_declaration.rules.iter().copied().filter(|rule| {
                                !positional.contains(rule) || matched.contains(rule)
                            }),
                        );
                        candidates
                    },
                    Ok(None) => match clone_copy_slice(&goal_declaration.rules) {
                        Ok(rules) => rules,
                        Err(reason) => {
                            return SemanticJudgmentDecision::Undetermined {
                                reason,
                                work: evaluator.work,
                                stats,
                            };
                        },
                    },
                    Err(reason) => {
                        return SemanticJudgmentDecision::Undetermined {
                            reason,
                            work: evaluator.work,
                            stats,
                        };
                    },
                };

            for rule_id in candidate_rules {
                if let Err(reason) = evaluator.charge() {
                    return SemanticJudgmentDecision::Undetermined {
                        reason,
                        work: evaluator.work,
                        stats,
                    };
                }
                let Some(rule) = image
                    .judgment_rules
                    .get(rule_id.0 as usize)
                    .filter(|candidate| {
                        candidate.id == rule_id && candidate.owner == goal.judgment
                    })
                else {
                    return SemanticJudgmentDecision::Undetermined {
                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                        work: evaluator.work,
                        stats,
                    };
                };
                if rule.conclusion.terms.len() != goal.terms.len() {
                    return SemanticJudgmentDecision::Undetermined {
                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                        work: evaluator.work,
                        stats,
                    };
                }
                let activation = match evaluator.fresh_activation() {
                    Ok(activation) => activation,
                    Err(reason) => {
                        return SemanticJudgmentDecision::Undetermined {
                            reason,
                            work: evaluator.work,
                            stats,
                        };
                    },
                };
                let mut equations = Vec::new();
                if equations.try_reserve_exact(goal.terms.len()).is_err() {
                    return SemanticJudgmentDecision::Undetermined {
                        reason: SemanticMatchUndetermined::AllocationFailed,
                        work: evaluator.work,
                        stats,
                    };
                }
                for (&query, &conclusion) in goal.terms.iter().zip(&rule.conclusion.terms) {
                    equations.push((
                        query,
                        HornTermRef::Clause {
                            activation,
                            rule: HornRuleRef::Judgment(rule.id),
                            term: conclusion,
                            scope: None,
                        },
                    ));
                }
                let substitutions =
                    match evaluator.unify_all(&equations, &branch.substitution, limits.frontier) {
                        Ok(substitutions) => substitutions,
                        Err(reason) => {
                            return SemanticJudgmentDecision::Undetermined {
                                reason,
                                work: evaluator.work,
                                stats,
                            };
                        },
                    };
                for substitution in substitutions {
                    let mut child = match clone_horn_branch(&branch) {
                        Ok(child) => child,
                        Err(reason) => {
                            return SemanticJudgmentDecision::Undetermined {
                                reason,
                                work: evaluator.work,
                                stats,
                            };
                        },
                    };
                    child.substitution = substitution;
                    if child.steps.len() == limits.proof_nodes {
                        return SemanticJudgmentDecision::Undetermined {
                            reason: SemanticMatchUndetermined::ProofLimitExceeded,
                            work: evaluator.work,
                            stats,
                        };
                    }
                    child.steps.push(SemanticJudgmentProofStep {
                        activation,
                        rule: rule.id,
                        parent_activation: goal.parent_activation,
                        premise_index: goal.premise_index,
                    });
                    let total_goals = match rule.premises.len().checked_add(child.goals.len()) {
                        Some(total) => total,
                        None => {
                            return SemanticJudgmentDecision::Undetermined {
                                reason: SemanticMatchUndetermined::FrontierLimitExceeded,
                                work: evaluator.work,
                                stats,
                            };
                        },
                    };
                    let mut goals = VecDeque::new();
                    if goals.try_reserve_exact(total_goals).is_err() {
                        return SemanticJudgmentDecision::Undetermined {
                            reason: SemanticMatchUndetermined::AllocationFailed,
                            work: evaluator.work,
                            stats,
                        };
                    }
                    for (premise_index, premise) in rule.premises.iter().enumerate() {
                        let Ok(premise_index) = u32::try_from(premise_index) else {
                            return SemanticJudgmentDecision::Undetermined {
                                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                work: evaluator.work,
                                stats,
                            };
                        };
                        let mut terms = Vec::new();
                        if terms.try_reserve_exact(premise.terms.len()).is_err() {
                            return SemanticJudgmentDecision::Undetermined {
                                reason: SemanticMatchUndetermined::AllocationFailed,
                                work: evaluator.work,
                                stats,
                            };
                        }
                        for term in &premise.terms {
                            terms.push(HornTermRef::Clause {
                                activation,
                                rule: HornRuleRef::Judgment(rule.id),
                                term: *term,
                                scope: None,
                            });
                        }
                        goals.push_back(HornGoal {
                            judgment: premise.judgment,
                            terms,
                            parent_activation: Some(activation),
                            premise_index: Some(premise_index),
                        });
                    }
                    goals.append(&mut child.goals);
                    child.goals = goals;
                    if frontier.len() == limits.frontier {
                        return SemanticJudgmentDecision::Undetermined {
                            reason: SemanticMatchUndetermined::FrontierLimitExceeded,
                            work: evaluator.work,
                            stats,
                        };
                    }
                    if frontier.try_reserve(1).is_err() {
                        return SemanticJudgmentDecision::Undetermined {
                            reason: SemanticMatchUndetermined::AllocationFailed,
                            work: evaluator.work,
                            stats,
                        };
                    }
                    frontier.push_back(child);
                }
            }
        }

        if proofs.is_empty() {
            SemanticJudgmentDecision::Refuted(SemanticMatchRefutation::PremiseRefuted)
        } else {
            proofs.sort_unstable_by(|left, right| left.steps.cmp(&right.steps));
            proofs.dedup_by(|left, right| left.steps == right.steps);
            for proof in &mut proofs {
                proof.work = evaluator.work;
            }
            SemanticJudgmentDecision::Proven(ProvenSemanticJudgmentProofs {
                proofs,
                work: evaluator.work,
                stats,
            })
        }
    }

    /// Execute a complete, one-step action on an owned private e-graph.
    ///
    /// Ownership is the transaction boundary: on every refuted or
    /// undetermined path the graph is dropped, so intermediate RHS nodes can
    /// never escape.  A successful result returns the graph together with all
    /// exact-keyed successors and receipts.
    pub fn execute_action<C>(
        &self,
        request: SemanticActionExecutionRequest<'_>,
        is_cancelled: C,
    ) -> SemanticTransitionDecision
    where
        C: FnMut() -> bool,
    {
        let mut guards = UnavailableGuardEvaluator;
        self.execute_action_with_guards(request, &mut guards, is_cancelled)
    }

    pub fn execute_action_with_guards<C, G>(
        &self,
        request: SemanticActionExecutionRequest<'_>,
        guards: &mut G,
        mut is_cancelled: C,
    ) -> SemanticTransitionDecision
    where
        C: FnMut() -> bool,
        G: SemanticGuardEvaluator,
    {
        let SemanticActionExecutionRequest {
            image,
            action,
            granted_rights,
            input,
            limits,
        } = request;
        let SemanticTransitionInput {
            mut egraph,
            root,
            exact_key: input_key,
            admission_work: prefix_work,
        } = input;
        if prefix_work > limits.work {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::WorkBudgetExhausted,
                work: 0,
                stats: SetAutomatonStats::default(),
            };
        }
        let initial_nodes = egraph.node_count();
        let Some(private_node_limit) = limits.term_nodes.checked_add(limits.output_nodes) else {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::OutputLimitExceeded,
                work: prefix_work,
                stats: SetAutomatonStats::default(),
            };
        };
        if !egraph.set_additional_node_budget(private_node_limit) {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::OutputLimitExceeded,
                work: prefix_work,
                stats: SetAutomatonStats::default(),
            };
        }
        let matches = self.match_action(
            action,
            SemanticActionMatchRequest {
                image,
                granted_rights,
                egraph: &mut egraph,
                root,
                limits: SemanticTransitionLimits {
                    work: limits.work.saturating_sub(prefix_work),
                    outputs: limits.frontier,
                    ..limits
                },
            },
            &mut is_cancelled,
        );
        let ProvenSemanticMatches { matches, work: match_work, mut stats } = match matches {
            SemanticMatchDecision::Proven(matches) => matches,
            SemanticMatchDecision::Refuted(reason) => {
                return SemanticTransitionDecision::Refuted(reason);
            },
            SemanticMatchDecision::Undetermined { reason, work: match_work, stats } => {
                return SemanticTransitionDecision::Undetermined {
                    reason,
                    work: prefix_work.saturating_add(match_work),
                    stats,
                };
            },
        };
        let Some(mut work) = prefix_work.checked_add(match_work) else {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::WorkBudgetExhausted,
                work: limits.work,
                stats,
            };
        };
        if matches.len() > limits.frontier {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::FrontierLimitExceeded,
                work,
                stats,
            };
        }
        let Some(action_image) = image
            .actions
            .get(action.0 as usize)
            .filter(|candidate| candidate.id == action)
        else {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work,
                stats,
            };
        };
        match image.resource_profile {
            TheoryResourceProfileV1::Uncosted => {},
            TheoryResourceProfileV1::Costed { .. } => {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::ResourceGradeUnavailable,
                    work,
                    stats,
                };
            },
        };
        let Ok(image_fingerprint) = image.fingerprint() else {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work,
                stats,
            };
        };
        let input = match clone_copy_slice(input_key.as_bytes()) {
            Ok(input) => input,
            Err(reason) => {
                return SemanticTransitionDecision::Undetermined { reason, work, stats };
            },
        };
        let mut frontier = VecDeque::new();
        for matched in matches {
            let Some(rule) = image
                .rules
                .get(matched.rule.0 as usize)
                .filter(|candidate| candidate.id == matched.rule)
            else {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let substitution = match action_substitution_from_map(matched.substitution) {
                Ok(substitution) => substitution,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            let frame = match action_frame(rule, egraph.find(root), substitution, None) {
                Ok(frame) => frame,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            let mut frames = Vec::new();
            if frames.try_reserve_exact(1).is_err() {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::AllocationFailed,
                    work,
                    stats,
                };
            }
            frames.push(frame);
            if let Err(reason) = push_action_branch(
                &mut frontier,
                ActionBranch { frames, premises: Vec::new() },
                limits.frontier,
            ) {
                return SemanticTransitionDecision::Undetermined { reason, work, stats };
            }
        }
        let mut completed = Vec::new();
        while let Some(mut branch) = frontier.pop_front() {
            if let Err(reason) = charge_work(&mut work, limits.work, &mut is_cancelled) {
                return SemanticTransitionDecision::Undetermined { reason, work, stats };
            }
            let Some(frame) = branch.frames.last_mut() else {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let task = frame.pending.pop_front();
            let frame_rule = frame.rule;
            let Some(rule) = image
                .rules
                .get(frame_rule.0 as usize)
                .filter(|candidate| candidate.id == frame_rule)
            else {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };

            let Some(task) = task else {
                if !frame.saved_forall_scopes.is_empty() {
                    return SemanticTransitionDecision::Undetermined {
                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                        work,
                        stats,
                    };
                }
                let output = match instantiate_rule_term(
                    TermInstantiation {
                        image,
                        rule,
                        substitution: &frame.substitution,
                        root: rule.right,
                        limits: TermConstructionLimits {
                            work: limits.work,
                            nodes: private_node_limit,
                            bytes: limits.output_bytes,
                        },
                    },
                    &mut egraph,
                    &mut work,
                    &mut is_cancelled,
                ) {
                    Ok(output) => output,
                    Err(reason) => {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    },
                };
                if egraph.node_count().saturating_sub(initial_nodes) > private_node_limit {
                    return SemanticTransitionDecision::Undetermined {
                        reason: SemanticMatchUndetermined::EGraphNodeBudgetExhausted,
                        work,
                        stats,
                    };
                }
                let Some(frame) = branch.frames.pop() else {
                    return SemanticTransitionDecision::Undetermined {
                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                        work,
                        stats,
                    };
                };
                if let Some(return_to_parent) = frame.return_to_parent {
                    let Some(parent) = branch.frames.last_mut() else {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work,
                            stats,
                        };
                    };
                    if parent.rule != return_to_parent.parent_rule {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work,
                            stats,
                        };
                    }
                    if let Err(reason) = action_bind_new(
                        &mut parent.substitution,
                        return_to_parent.target,
                        egraph.find(output),
                    ) {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                    if let Err(reason) = push_premise_receipt(
                        &mut branch,
                        SemanticPremiseReceipt::Transition {
                            rule: return_to_parent.parent_rule,
                            premise: return_to_parent.parent_premise,
                            child_rule: frame.rule,
                        },
                        limits.proof_nodes,
                    ) {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                    if let Err(reason) = push_action_branch(&mut frontier, branch, limits.frontier)
                    {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                } else {
                    if completed.len() == limits.frontier {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::FrontierLimitExceeded,
                            work,
                            stats,
                        };
                    }
                    if completed.try_reserve(1).is_err() {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::AllocationFailed,
                            work,
                            stats,
                        };
                    }
                    completed.push(CompletedActionBranch {
                        rule: frame.rule,
                        output: egraph.find(output),
                        substitution: frame.substitution,
                        premises: branch.premises,
                    });
                }
                continue;
            };

            match task {
                ActionPremiseTask::Evaluate { premise } => {
                    let Some(premise_node) = rule.premises.get(premise as usize) else {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work,
                            stats,
                        };
                    };
                    match &premise_node.form {
                        mettail_grammar_core::TheoryImagePremiseFormV1::Freshness {
                            variable,
                            target,
                            remainder,
                        } => {
                            let Some(variable_value) =
                                action_lookup(&frame.substitution, *variable)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            let Some(target_value) = action_lookup(&frame.substitution, *target)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            let target_is_remainder = rule
                                .variables
                                .get(target.0 as usize)
                                .filter(|declaration| declaration.id == *target)
                                .map(|declaration| {
                                    declaration.role
                                        == mettail_grammar_core::TheoryVariableRoleV1::Remainder
                                });
                            if target_is_remainder != Some(*remainder) {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            }
                            match freshness_holds(
                                &egraph,
                                variable_value,
                                target_value,
                                &mut work,
                                limits.work,
                                &mut is_cancelled,
                            ) {
                                Ok(true) => {},
                                Ok(false) => continue,
                                Err(reason) => {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                },
                            }
                            if let Err(reason) = push_premise_receipt(
                                &mut branch,
                                SemanticPremiseReceipt::Freshness { rule: frame_rule, premise },
                                limits.proof_nodes,
                            ) {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                            if let Err(reason) =
                                push_action_branch(&mut frontier, branch, limits.frontier)
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                        },
                        mettail_grammar_core::TheoryImagePremiseFormV1::Transition {
                            source,
                            target,
                        } => {
                            let Some(source_declaration) = rule
                                .variables
                                .get(source.0 as usize)
                                .filter(|declaration| declaration.id == *source)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            let Some(target_declaration) =
                                rule.variables.get(target.0 as usize).filter(|declaration| {
                                    declaration.id == *target
                                        && declaration.role
                                            == mettail_grammar_core::TheoryVariableRoleV1::Derived
                                })
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            if source_declaration.sort != target_declaration.sort {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            }
                            let Some(source_value) = action_lookup(&frame.substitution, *source)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            if action_lookup(&frame.substitution, *target).is_some() {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            }
                            let remaining = limits.work.saturating_sub(work);
                            let decision = self.match_rewrite_relation(
                                source_declaration.sort,
                                SemanticActionMatchRequest {
                                    image,
                                    granted_rights,
                                    egraph: &mut egraph,
                                    root: source_value,
                                    limits: SemanticTransitionLimits {
                                        work: remaining,
                                        outputs: limits.frontier,
                                        ..limits
                                    },
                                },
                                &mut is_cancelled,
                            );
                            let nested_matches = match decision {
                                SemanticMatchDecision::Proven(proven) => {
                                    if let Err(reason) = absorb_matcher_accounting(
                                        &mut work,
                                        limits.work,
                                        &mut stats,
                                        proven.work,
                                        proven.stats,
                                    ) {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    proven.matches
                                },
                                SemanticMatchDecision::Refuted(
                                    SemanticMatchRefutation::NoTransition,
                                ) => continue,
                                SemanticMatchDecision::Refuted(reason) => {
                                    return SemanticTransitionDecision::Refuted(reason);
                                },
                                SemanticMatchDecision::Undetermined {
                                    reason,
                                    work: nested_work,
                                    stats: nested_stats,
                                } => {
                                    if let Err(accounting_reason) = absorb_matcher_accounting(
                                        &mut work,
                                        limits.work,
                                        &mut stats,
                                        nested_work,
                                        nested_stats,
                                    ) {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason: accounting_reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                },
                            };
                            for nested in nested_matches {
                                if nested.root != egraph.find(source_value) {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                        work,
                                        stats,
                                    };
                                }
                                let Some(child_rule) = image
                                    .rules
                                    .get(nested.rule.0 as usize)
                                    .filter(|candidate| candidate.id == nested.rule)
                                else {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                        work,
                                        stats,
                                    };
                                };
                                let mut child = match clone_action_branch(&branch) {
                                    Ok(child) => child,
                                    Err(reason) => {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    },
                                };
                                let substitution =
                                    match action_substitution_from_map(nested.substitution) {
                                        Ok(substitution) => substitution,
                                        Err(reason) => {
                                            return SemanticTransitionDecision::Undetermined {
                                                reason,
                                                work,
                                                stats,
                                            };
                                        },
                                    };
                                let frame = match action_frame(
                                    child_rule,
                                    egraph.find(source_value),
                                    substitution,
                                    Some(ActionReturnFrame {
                                        parent_rule: frame_rule,
                                        parent_premise: premise,
                                        target: *target,
                                    }),
                                ) {
                                    Ok(frame) => frame,
                                    Err(reason) => {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    },
                                };
                                if child.frames.len() == limits.proof_nodes {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason: SemanticMatchUndetermined::ProofLimitExceeded,
                                        work,
                                        stats,
                                    };
                                }
                                if child.frames.try_reserve(1).is_err() {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason: SemanticMatchUndetermined::AllocationFailed,
                                        work,
                                        stats,
                                    };
                                }
                                child.frames.push(frame);
                                if let Err(reason) =
                                    push_action_branch(&mut frontier, child, limits.frontier)
                                {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                }
                            }
                        },
                        mettail_grammar_core::TheoryImagePremiseFormV1::Judgment {
                            judgment,
                            terms,
                        } => {
                            let mut arguments = Vec::new();
                            if arguments.try_reserve_exact(terms.len()).is_err() {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::AllocationFailed,
                                    work,
                                    stats,
                                };
                            }
                            for term in terms {
                                let argument = match instantiate_rule_term(
                                    TermInstantiation {
                                        image,
                                        rule,
                                        substitution: &frame.substitution,
                                        root: *term,
                                        limits: TermConstructionLimits {
                                            work: limits.work,
                                            nodes: private_node_limit,
                                            bytes: limits.term_bytes,
                                        },
                                    },
                                    &mut egraph,
                                    &mut work,
                                    &mut is_cancelled,
                                ) {
                                    Ok(argument) => argument,
                                    Err(reason) => {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    },
                                };
                                arguments.push(argument);
                            }
                            if egraph.node_count().saturating_sub(initial_nodes)
                                > private_node_limit
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::EGraphNodeBudgetExhausted,
                                    work,
                                    stats,
                                };
                            }
                            let remaining = limits.work.saturating_sub(work);
                            let decision = self.prove_ground_judgment(
                                SemanticJudgmentProofRequest {
                                    image,
                                    judgment: *judgment,
                                    granted_rights,
                                    egraph: &egraph,
                                    arguments: &arguments,
                                    limits: SemanticJudgmentLimits {
                                        work: remaining,
                                        frontier: limits.frontier,
                                        proofs: limits.proofs,
                                        proof_nodes: limits.proof_nodes,
                                        term_nodes: limits.term_nodes,
                                        term_bytes: limits.term_bytes,
                                    },
                                },
                                &mut is_cancelled,
                            );
                            match decision {
                                SemanticJudgmentDecision::Proven(proven) => {
                                    if let Err(reason) = absorb_matcher_accounting(
                                        &mut work,
                                        limits.work,
                                        &mut stats,
                                        proven.work,
                                        proven.stats,
                                    ) {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    let Ok(proofs) = u32::try_from(proven.proofs.len()) else {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason: SemanticMatchUndetermined::ProofLimitExceeded,
                                            work,
                                            stats,
                                        };
                                    };
                                    let proof_steps =
                                        proven.proofs.iter().try_fold(0u32, |total, proof| {
                                            u32::try_from(proof.steps.len())
                                                .ok()
                                                .and_then(|steps| total.checked_add(steps))
                                        });
                                    let Some(proof_steps) = proof_steps else {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason: SemanticMatchUndetermined::ProofLimitExceeded,
                                            work,
                                            stats,
                                        };
                                    };
                                    if let Err(reason) = push_premise_receipt(
                                        &mut branch,
                                        SemanticPremiseReceipt::Judgment {
                                            rule: frame_rule,
                                            premise,
                                            judgment: *judgment,
                                            proofs,
                                            proof_steps,
                                        },
                                        limits.proof_nodes,
                                    ) {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    if let Err(reason) =
                                        push_action_branch(&mut frontier, branch, limits.frontier)
                                    {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    }
                                },
                                SemanticJudgmentDecision::Refuted(
                                    SemanticMatchRefutation::PremiseRefuted
                                    | SemanticMatchRefutation::NoTransition,
                                ) => {},
                                SemanticJudgmentDecision::Refuted(reason) => {
                                    return SemanticTransitionDecision::Refuted(reason);
                                },
                                SemanticJudgmentDecision::Undetermined {
                                    reason,
                                    work: judgment_work,
                                    stats: judgment_stats,
                                } => {
                                    if let Err(accounting_reason) = absorb_matcher_accounting(
                                        &mut work,
                                        limits.work,
                                        &mut stats,
                                        judgment_work,
                                        judgment_stats,
                                    ) {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason: accounting_reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                },
                            }
                        },
                        mettail_grammar_core::TheoryImagePremiseFormV1::ForAll {
                            collection,
                            parameter,
                            body,
                        } => {
                            let Some(collection_value) =
                                action_lookup(&frame.substitution, *collection)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            let Some(collection_declaration) = rule
                                .variables
                                .get(collection.0 as usize)
                                .filter(|declaration| declaration.id == *collection)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            let (element_sort, elements) = match concrete_collection_elements(
                                image,
                                &egraph,
                                collection_value,
                                collection_declaration.sort,
                                &mut work,
                                limits.work,
                                &mut is_cancelled,
                            ) {
                                Ok(elements) => elements,
                                Err(reason) => {
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                },
                            };
                            let Some(parameter_declaration) = rule
                                .variables
                                .get(parameter.0 as usize)
                                .filter(|declaration| declaration.id == *parameter)
                            else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            };
                            if parameter_declaration.sort != element_sort
                                || rule.premises.get(*body as usize).is_none()
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                                    work,
                                    stats,
                                };
                            }
                            let Ok(element_count) = u32::try_from(elements.len()) else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::ProofLimitExceeded,
                                    work,
                                    stats,
                                };
                            };
                            let Some(additional) = elements.len().checked_add(1) else {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::FrontierLimitExceeded,
                                    work,
                                    stats,
                                };
                            };
                            if frame.pending.try_reserve(additional).is_err() {
                                return SemanticTransitionDecision::Undetermined {
                                    reason: SemanticMatchUndetermined::AllocationFailed,
                                    work,
                                    stats,
                                };
                            }
                            frame.pending.push_front(ActionPremiseTask::RecordForAll {
                                premise,
                                elements: element_count,
                            });
                            for element in elements.into_iter().rev() {
                                frame.pending.push_front(ActionPremiseTask::ForAllElement {
                                    body: *body,
                                    parameter: *parameter,
                                    element,
                                });
                            }
                            if let Err(reason) =
                                push_action_branch(&mut frontier, branch, limits.frontier)
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                        },
                        mettail_grammar_core::TheoryImagePremiseFormV1::Guard { commitment } => {
                            let remaining = limits.work.saturating_sub(work);
                            let decision = guards.evaluate_guard(SemanticGuardRequest {
                                language_fingerprint: image.language_fingerprint,
                                theory_fingerprint: image.theory_fingerprint,
                                image_fingerprint,
                                rule: frame_rule,
                                premise,
                                guard_commitment: *commitment,
                                redex: frame.redex,
                                substitution: &frame.substitution,
                                egraph: &egraph,
                                work_limit: remaining,
                            });
                            let (evidence_commitment, guard_work) = match decision {
                                SemanticGuardDecision::Proven {
                                    evidence_commitment,
                                    work: guard_work,
                                } => (evidence_commitment, guard_work),
                                SemanticGuardDecision::Refuted { work: guard_work } => {
                                    if let Err(reason) =
                                        absorb_reported_work(&mut work, limits.work, guard_work)
                                    {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    continue;
                                },
                                SemanticGuardDecision::Undetermined {
                                    reason,
                                    work: guard_work,
                                } => {
                                    if let Err(accounting_reason) =
                                        absorb_reported_work(&mut work, limits.work, guard_work)
                                    {
                                        return SemanticTransitionDecision::Undetermined {
                                            reason: accounting_reason,
                                            work,
                                            stats,
                                        };
                                    }
                                    return SemanticTransitionDecision::Undetermined {
                                        reason,
                                        work,
                                        stats,
                                    };
                                },
                            };
                            if let Err(reason) =
                                absorb_reported_work(&mut work, limits.work, guard_work)
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                            if let Err(reason) = push_premise_receipt(
                                &mut branch,
                                SemanticPremiseReceipt::Guard {
                                    rule: frame_rule,
                                    premise,
                                    guard_commitment: *commitment,
                                    evidence_commitment,
                                },
                                limits.proof_nodes,
                            ) {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                            if let Err(reason) =
                                push_action_branch(&mut frontier, branch, limits.frontier)
                            {
                                return SemanticTransitionDecision::Undetermined {
                                    reason,
                                    work,
                                    stats,
                                };
                            }
                        },
                    }
                },
                ActionPremiseTask::ForAllElement { body, parameter, element } => {
                    let scope = match clone_copy_slice(&frame.substitution) {
                        Ok(scope) => scope,
                        Err(reason) => {
                            return SemanticTransitionDecision::Undetermined {
                                reason,
                                work,
                                stats,
                            };
                        },
                    };
                    if frame.saved_forall_scopes.len() == limits.proof_nodes {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::ProofLimitExceeded,
                            work,
                            stats,
                        };
                    }
                    if frame.saved_forall_scopes.try_reserve(1).is_err() {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::AllocationFailed,
                            work,
                            stats,
                        };
                    }
                    frame.saved_forall_scopes.push(scope);
                    if let Err(reason) =
                        action_bind_overlay(&mut frame.substitution, parameter, element)
                    {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                    if frame.pending.try_reserve(2).is_err() {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::AllocationFailed,
                            work,
                            stats,
                        };
                    }
                    frame.pending.push_front(ActionPremiseTask::RestoreForAll);
                    frame
                        .pending
                        .push_front(ActionPremiseTask::Evaluate { premise: body });
                    if let Err(reason) = push_action_branch(&mut frontier, branch, limits.frontier)
                    {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                },
                ActionPremiseTask::RestoreForAll => {
                    let Some(scope) = frame.saved_forall_scopes.pop() else {
                        return SemanticTransitionDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work,
                            stats,
                        };
                    };
                    frame.substitution = scope;
                    if let Err(reason) = push_action_branch(&mut frontier, branch, limits.frontier)
                    {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                },
                ActionPremiseTask::RecordForAll { premise, elements } => {
                    if let Err(reason) = push_premise_receipt(
                        &mut branch,
                        SemanticPremiseReceipt::ForAll { rule: frame_rule, premise, elements },
                        limits.proof_nodes,
                    ) {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                    if let Err(reason) = push_action_branch(&mut frontier, branch, limits.frontier)
                    {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    }
                },
            }
        }

        if completed.is_empty() {
            return SemanticTransitionDecision::Refuted(SemanticMatchRefutation::PremiseRefuted);
        }
        let mut transitions = Vec::new();
        if transitions.try_reserve_exact(completed.len()).is_err() {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work,
                stats,
            };
        }
        for completed in completed {
            let Some(rule) = image
                .rules
                .get(completed.rule.0 as usize)
                .filter(|candidate| candidate.id == completed.rule)
            else {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(output_sort) = rule.terms.get(rule.right.0 as usize).map(|term| term.sort)
            else {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let output_key = match exact_ground_key(
                &egraph,
                completed.output,
                &mut work,
                GroundKeyLimits {
                    work: limits.work,
                    nodes: limits.output_nodes,
                    bytes: limits.output_bytes,
                    limit_reason: SemanticMatchUndetermined::OutputLimitExceeded,
                },
                &mut is_cancelled,
            ) {
                Ok(key) => key,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            let output = match clone_copy_slice(output_key.as_bytes()) {
                Ok(output) => output,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            transitions.push(SemanticTransition {
                output: completed.output,
                output_sort,
                substitution: SemanticActionSubstitution { bindings: completed.substitution },
                receipt: SemanticTransitionReceipt {
                    language_fingerprint: image.language_fingerprint,
                    theory_fingerprint: image.theory_fingerprint,
                    image_fingerprint,
                    action,
                    rule: rule.id,
                    input: match clone_copy_slice(&input) {
                        Ok(input) => input,
                        Err(reason) => {
                            return SemanticTransitionDecision::Undetermined {
                                reason,
                                work,
                                stats,
                            };
                        },
                    },
                    output,
                    effect: action_image.effect,
                    effect_class: action_image.effect_class,
                    resource: SemanticResourceReceipt::NoSemanticGrade,
                    premises: completed.premises,
                    work: 0,
                },
            });
        }
        transitions.sort_unstable_by(|left, right| {
            left.receipt
                .output
                .cmp(&right.receipt.output)
                .then_with(|| left.receipt.rule.cmp(&right.receipt.rule))
                .then_with(|| left.substitution.cmp(&right.substitution))
                .then_with(|| left.receipt.premises.cmp(&right.receipt.premises))
        });
        transitions.dedup_by(|left, right| {
            left.receipt.output == right.receipt.output
                && left.receipt.rule == right.receipt.rule
                && left.substitution == right.substitution
        });
        if transitions.len() > limits.outputs {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::OutputLimitExceeded,
                work,
                stats,
            };
        }
        let root_count = match transitions.iter().try_fold(0usize, |count, transition| {
            count
                .checked_add(1)?
                .checked_add(transition.substitution.bindings.len())
        }) {
            Some(count) => count,
            None => {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::OutputLimitExceeded,
                    work,
                    stats,
                };
            },
        };
        let mut publication_roots = Vec::new();
        if publication_roots.try_reserve_exact(root_count).is_err() {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::AllocationFailed,
                work,
                stats,
            };
        }
        for transition in &transitions {
            publication_roots.push(egraph.find(transition.output));
            publication_roots.extend(
                transition
                    .substitution
                    .bindings
                    .iter()
                    .map(|(_, value)| egraph.find(*value)),
            );
        }
        let (published_egraph, publication_remap) = match project_reachable_egraph(
            &egraph,
            &publication_roots,
            &mut work,
            ProjectionLimits {
                work: limits.work,
                nodes: limits.output_nodes,
                bytes: limits.output_bytes,
                limit_reason: SemanticMatchUndetermined::OutputLimitExceeded,
            },
            &mut is_cancelled,
        ) {
            Ok(projected) => projected,
            Err(reason) => {
                return SemanticTransitionDecision::Undetermined { reason, work, stats };
            },
        };
        for transition in &mut transitions {
            transition.output =
                match remapped_eclass(&publication_remap, egraph.find(transition.output)) {
                    Ok(output) => output,
                    Err(reason) => {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    },
                };
            for (_, value) in &mut transition.substitution.bindings {
                *value = match remapped_eclass(&publication_remap, egraph.find(*value)) {
                    Ok(value) => value,
                    Err(reason) => {
                        return SemanticTransitionDecision::Undetermined { reason, work, stats };
                    },
                };
            }
        }
        for transition in &mut transitions {
            transition.receipt.work = work;
        }
        if transitions.is_empty() {
            SemanticTransitionDecision::Refuted(SemanticMatchRefutation::NoTransition)
        } else {
            SemanticTransitionDecision::Proven(ProvenSemanticTransitions {
                egraph: published_egraph,
                transitions,
                work,
                stats,
            })
        }
    }
}

/// Request bounds are explicit and may only attenuate an installed theory's
/// limits.  No execution entry point has an unbounded default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticTransitionLimits {
    pub work: u64,
    pub outputs: usize,
    pub frontier: usize,
    pub proofs: usize,
    pub proof_nodes: usize,
    pub term_nodes: usize,
    pub term_bytes: usize,
    pub output_nodes: usize,
    pub output_bytes: usize,
}

impl From<TheoryLimitsV1> for SemanticTransitionLimits {
    fn from(limits: TheoryLimitsV1) -> Self {
        Self {
            work: u64::from(limits.max_steps),
            outputs: limits.max_frontier as usize,
            frontier: limits.max_frontier as usize,
            proofs: limits.max_frontier as usize,
            proof_nodes: limits.max_proof_nodes as usize,
            term_nodes: limits.max_term_nodes as usize,
            term_bytes: limits.max_output_bytes as usize,
            output_nodes: limits.max_output_nodes as usize,
            output_bytes: limits.max_output_bytes as usize,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticResourceReceipt {
    /// The authoritative theory is not a `Cost(G)` presentation. This is not a
    /// zero-cost claim: host execution resources remain independently metered.
    NoSemanticGrade,
    /// Exact grade evidence emitted by a verified cost image. The transition
    /// kernel never manufactures a unit from an action's effect class.
    Checked {
        grade_sort: TheorySortId,
        grade: Vec<u8>,
        cost_image_fingerprint: [u8; 32],
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticTransitionReceipt {
    pub language_fingerprint: [u8; 32],
    pub theory_fingerprint: [u8; 32],
    pub image_fingerprint: [u8; 32],
    pub action: TheoryActionId,
    pub rule: TheoryRuleProgramId,
    pub input: Vec<u8>,
    pub output: Vec<u8>,
    pub effect: TheoryEffectId,
    pub effect_class: SemanticEffectClassV1,
    pub resource: SemanticResourceReceipt,
    pub premises: Vec<SemanticPremiseReceipt>,
    pub work: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticActionSubstitution {
    bindings: Vec<(TheoryVariableId, EClassId)>,
}

impl SemanticActionSubstitution {
    pub fn get(&self, variable: TheoryVariableId) -> Option<EClassId> {
        self.bindings
            .binary_search_by_key(&variable, |(candidate, _)| *candidate)
            .ok()
            .map(|index| self.bindings[index].1)
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (TheoryVariableId, EClassId)> + '_ {
        self.bindings.iter().copied()
    }
}

impl PartialOrd for SemanticActionSubstitution {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SemanticActionSubstitution {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bindings.cmp(&other.bindings)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticTransition {
    pub output: EClassId,
    pub output_sort: TheorySortId,
    pub substitution: SemanticActionSubstitution,
    pub receipt: SemanticTransitionReceipt,
}

pub struct ProvenSemanticTransitions {
    egraph: EGraph<FramedSemanticOperator>,
    pub transitions: Vec<SemanticTransition>,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

impl ProvenSemanticTransitions {
    pub fn egraph(&self) -> &EGraph<FramedSemanticOperator> {
        &self.egraph
    }

    pub fn into_parts(self) -> (EGraph<FramedSemanticOperator>, Vec<SemanticTransition>) {
        (self.egraph, self.transitions)
    }
}

pub enum SemanticTransitionDecision {
    Proven(ProvenSemanticTransitions),
    Refuted(SemanticMatchRefutation),
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
        stats: SetAutomatonStats,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SemanticPremiseReceipt {
    Freshness {
        rule: TheoryRuleProgramId,
        premise: u32,
    },
    Transition {
        rule: TheoryRuleProgramId,
        premise: u32,
        child_rule: TheoryRuleProgramId,
    },
    Judgment {
        rule: TheoryRuleProgramId,
        premise: u32,
        judgment: TheoryJudgmentId,
        proofs: u32,
        proof_steps: u32,
    },
    ForAll {
        rule: TheoryRuleProgramId,
        premise: u32,
        elements: u32,
    },
    Guard {
        rule: TheoryRuleProgramId,
        premise: u32,
        guard_commitment: [u8; 32],
        evidence_commitment: [u8; 32],
    },
}

pub struct SemanticGuardRequest<'a> {
    pub language_fingerprint: [u8; 32],
    pub theory_fingerprint: [u8; 32],
    pub image_fingerprint: [u8; 32],
    pub rule: TheoryRuleProgramId,
    pub premise: u32,
    pub guard_commitment: [u8; 32],
    pub redex: EClassId,
    pub substitution: &'a [(TheoryVariableId, EClassId)],
    pub egraph: &'a EGraph<FramedSemanticOperator>,
    pub work_limit: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticGuardDecision {
    Proven {
        evidence_commitment: [u8; 32],
        work: u64,
    },
    Refuted {
        work: u64,
    },
    Undetermined {
        reason: SemanticMatchUndetermined,
        work: u64,
    },
}

/// Capability-injected evaluator for an authoritative guard commitment.
/// Implementations are installed together with the checked theory and receive
/// no ambient authority from grammar data.
pub trait SemanticGuardEvaluator {
    fn evaluate_guard(&mut self, request: SemanticGuardRequest<'_>) -> SemanticGuardDecision;
}

struct UnavailableGuardEvaluator;

impl SemanticGuardEvaluator for UnavailableGuardEvaluator {
    fn evaluate_guard(&mut self, _request: SemanticGuardRequest<'_>) -> SemanticGuardDecision {
        SemanticGuardDecision::Undetermined {
            reason: SemanticMatchUndetermined::PremiseEvaluationUnavailable,
            work: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ScopedClauseVariable {
    activation: u64,
    variable: TheoryVariableId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum HornTermRef {
    Ground {
        class: EClassId,
        sort: TheorySortId,
    },
    Clause {
        activation: u64,
        rule: HornRuleRef,
        term: mettail_grammar_core::TheoryTermId,
        scope: Option<usize>,
    },
    Variable {
        variable: ScopedClauseVariable,
        sort: TheorySortId,
    },
    Synthetic {
        term: usize,
        sort: TheorySortId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum HornRuleRef {
    Transition(TheoryRuleProgramId),
    Judgment(TheoryJudgmentRuleProgramId),
}

type ActionSubstitution = Vec<(TheoryVariableId, EClassId)>;

#[derive(Clone, Copy)]
enum ActionPremiseTask {
    Evaluate {
        premise: u32,
    },
    ForAllElement {
        body: u32,
        parameter: TheoryVariableId,
        element: EClassId,
    },
    RestoreForAll,
    RecordForAll {
        premise: u32,
        elements: u32,
    },
}

#[derive(Clone, Copy)]
struct ActionReturnFrame {
    parent_rule: TheoryRuleProgramId,
    parent_premise: u32,
    target: TheoryVariableId,
}

struct ActionFrame {
    rule: TheoryRuleProgramId,
    redex: EClassId,
    substitution: ActionSubstitution,
    pending: VecDeque<ActionPremiseTask>,
    saved_forall_scopes: Vec<ActionSubstitution>,
    return_to_parent: Option<ActionReturnFrame>,
}

struct ActionBranch {
    frames: Vec<ActionFrame>,
    premises: Vec<SemanticPremiseReceipt>,
}

struct CompletedActionBranch {
    rule: TheoryRuleProgramId,
    output: EClassId,
    substitution: ActionSubstitution,
    premises: Vec<SemanticPremiseReceipt>,
}

type HornSubstitution = Vec<(ScopedClauseVariable, HornTermRef)>;

struct HornGoal {
    judgment: TheoryJudgmentId,
    terms: Vec<HornTermRef>,
    parent_activation: Option<u64>,
    premise_index: Option<u32>,
}

struct HornBranch {
    goals: VecDeque<HornGoal>,
    substitution: HornSubstitution,
    steps: Vec<SemanticJudgmentProofStep>,
}

#[derive(Clone, Copy)]
enum HornConstraint {
    Equation(HornTermRef, HornTermRef),
    Collection(usize),
    ComprehensionRow(usize),
    FinalizeDerived(usize),
}

struct HornUnificationBranch {
    pending: Vec<HornConstraint>,
    substitution: HornSubstitution,
}

struct HornLexicalScope {
    parent: Option<usize>,
    bindings: Vec<(TheoryVariableId, ScopedClauseVariable)>,
}

struct HornCollectionPatternState {
    sort: TheorySortId,
    operator: FramedSemanticOperator,
    collection: CollectionKind,
    patterns: Vec<HornTermRef>,
    target_arguments: Vec<HornTermRef>,
    remainder: Option<HornTermRef>,
    pattern_pathmap_mode: Option<PathMapModeV1>,
    target_pathmap_mode: Option<PathMapModeV1>,
}

struct HornComprehensionRowState {
    collection: HornCollectionPatternState,
    row_bodies: Vec<HornTermRef>,
    row_seeds: Vec<Vec<(HornTermRef, HornTermRef)>>,
    derived: Vec<HornDerivedCollection>,
    next_row: usize,
}

struct HornDerivedCollection {
    variable: ScopedClauseVariable,
    sort: TheorySortId,
    elements: Vec<HornTermRef>,
}

struct HornRowPairingBranch {
    next_left: usize,
    used_right: Vec<bool>,
    equations: Vec<(HornTermRef, HornTermRef)>,
    unmatched_left: Vec<HornTermRef>,
}

struct HornCollectionEquation {
    sort: TheorySortId,
    operator: FramedSemanticOperator,
    collection: CollectionKind,
    left_arguments: Vec<HornTermRef>,
    left_remainder: Option<HornTermRef>,
    left_pathmap_mode: Option<PathMapModeV1>,
    right_arguments: Vec<HornTermRef>,
    right_remainder: Option<HornTermRef>,
    right_pathmap_mode: Option<PathMapModeV1>,
}

enum HornTermForm {
    Variable(ScopedClauseVariable),
    Application {
        operator: FramedSemanticOperator,
        arguments: Vec<HornTermRef>,
        collection: Option<CollectionKind>,
        remainder: Option<HornTermRef>,
        pathmap_mode: Option<PathMapModeV1>,
    },
    Comprehension {
        sources: Vec<HornTermRef>,
        parameters: Vec<TheoryVariableId>,
        body: HornTermRef,
    },
}

struct HornClauseProgram<'a> {
    variables: &'a [mettail_grammar_core::TheoryImageVariableV1],
    terms: &'a [mettail_grammar_core::TheoryImageTermNodeV1],
}

struct HornSyntheticTerm {
    sort: TheorySortId,
    operator: FramedSemanticOperator,
    arguments: Vec<HornTermRef>,
    collection: Option<CollectionKind>,
    remainder: Option<HornTermRef>,
    pathmap_mode: Option<PathMapModeV1>,
}

struct HornTermView {
    term: HornTermRef,
    sort: TheorySortId,
    form: HornTermForm,
}

type ResolvedCollectionTerms = (
    TheorySortId,
    FramedSemanticOperator,
    CollectionKind,
    Option<PathMapModeV1>,
    Vec<HornTermRef>,
);

enum HornVirtualizationTask {
    Visit(HornTermRef),
    Finish {
        sort: TheorySortId,
        operator: FramedSemanticOperator,
        collection: Option<CollectionKind>,
        remainder: bool,
        pathmap_mode: Option<PathMapModeV1>,
        argument_count: usize,
        value_base: usize,
    },
}

enum RuntimeChildSortContract {
    Fixed(Vec<TheorySortId>),
    Homogeneous(TheorySortId),
    RemainderOnly,
}

struct RuntimeOperatorSignature {
    result: TheorySortId,
    children: RuntimeChildSortContract,
}

struct HornEvaluator<'a, C> {
    image: &'a TheorySemanticImageV1,
    egraph: &'a EGraph<FramedSemanticOperator>,
    work: u64,
    work_limit: u64,
    ground_key_nodes: usize,
    ground_key_bytes: usize,
    ground_key_limit_reason: SemanticMatchUndetermined,
    is_cancelled: C,
    synthetic_terms: Vec<HornSyntheticTerm>,
    lexical_scopes: Vec<HornLexicalScope>,
    collection_states: Vec<HornCollectionPatternState>,
    comprehension_states: Vec<HornComprehensionRowState>,
    derived_collections: Vec<HornDerivedCollection>,
    next_activation: u64,
}

impl<'a, C> HornEvaluator<'a, C>
where
    C: FnMut() -> bool,
{
    fn exact_ground_key(
        &mut self,
        root: EClassId,
    ) -> Result<ContentKey, SemanticMatchUndetermined> {
        exact_ground_key(
            self.egraph,
            root,
            &mut self.work,
            GroundKeyLimits {
                work: self.work_limit,
                nodes: self.ground_key_nodes,
                bytes: self.ground_key_bytes,
                limit_reason: self.ground_key_limit_reason,
            },
            &mut self.is_cancelled,
        )
    }

    fn charge(&mut self) -> Result<(), SemanticMatchUndetermined> {
        charge_work(&mut self.work, self.work_limit, &mut self.is_cancelled)
    }

    fn charge_units(&mut self, units: usize) -> Result<(), SemanticMatchUndetermined> {
        if (self.is_cancelled)() {
            return Err(SemanticMatchUndetermined::Cancelled);
        }
        let units =
            u64::try_from(units).map_err(|_| SemanticMatchUndetermined::WorkBudgetExhausted)?;
        self.work = self
            .work
            .checked_add(units)
            .filter(|work| *work <= self.work_limit)
            .ok_or(SemanticMatchUndetermined::WorkBudgetExhausted)?;
        Ok(())
    }

    fn fresh_activation(&mut self) -> Result<u64, SemanticMatchUndetermined> {
        let activation = self.next_activation;
        self.next_activation = self
            .next_activation
            .checked_add(1)
            .ok_or(SemanticMatchUndetermined::ProofLimitExceeded)?;
        Ok(activation)
    }

    fn synthetic_collection(
        &mut self,
        sort: TheorySortId,
        operator: FramedSemanticOperator,
        collection: CollectionKind,
        arguments: Vec<HornTermRef>,
        remainder: Option<HornTermRef>,
        pathmap_mode: Option<PathMapModeV1>,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        self.synthetic_terms
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let term = self.synthetic_terms.len();
        self.synthetic_terms.push(HornSyntheticTerm {
            sort,
            operator,
            arguments,
            collection: Some(collection),
            remainder,
            pathmap_mode,
        });
        Ok(HornTermRef::Synthetic { term, sort })
    }

    fn synthetic_application(
        &mut self,
        sort: TheorySortId,
        operator: FramedSemanticOperator,
        arguments: Vec<HornTermRef>,
        collection: Option<CollectionKind>,
        remainder: Option<HornTermRef>,
        pathmap_mode: Option<PathMapModeV1>,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        self.synthetic_terms
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let term = self.synthetic_terms.len();
        self.synthetic_terms.push(HornSyntheticTerm {
            sort,
            operator,
            arguments,
            collection,
            remainder,
            pathmap_mode,
        });
        Ok(HornTermRef::Synthetic { term, sort })
    }

    fn ground_virtual_term(
        &mut self,
        root: HornTermRef,
        substitution: &HornSubstitution,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        let mut tasks = Vec::new();
        tasks
            .try_reserve_exact(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        tasks.push(HornVirtualizationTask::Visit(root));
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.charge()?;
            match task {
                HornVirtualizationTask::Visit(term) => {
                    let view = self.view(term, substitution)?;
                    match view.form {
                        HornTermForm::Variable(_) | HornTermForm::Comprehension { .. } => {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        },
                        HornTermForm::Application {
                            operator,
                            arguments,
                            collection,
                            remainder,
                            pathmap_mode,
                        } => {
                            if matches!(view.term, HornTermRef::Ground { .. }) {
                                values
                                    .try_reserve(1)
                                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                                values.push(view.term);
                                continue;
                            }
                            let child_count = arguments
                                .len()
                                .checked_add(usize::from(remainder.is_some()))
                                .ok_or(SemanticMatchUndetermined::AllocationFailed)?;
                            tasks
                                .try_reserve(child_count.saturating_add(1))
                                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                            tasks.push(HornVirtualizationTask::Finish {
                                sort: view.sort,
                                operator,
                                collection,
                                remainder: remainder.is_some(),
                                pathmap_mode,
                                argument_count: arguments.len(),
                                value_base: values.len(),
                            });
                            if let Some(remainder) = remainder {
                                tasks.push(HornVirtualizationTask::Visit(remainder));
                            }
                            for argument in arguments.into_iter().rev() {
                                tasks.push(HornVirtualizationTask::Visit(argument));
                            }
                        },
                    }
                },
                HornVirtualizationTask::Finish {
                    sort,
                    operator,
                    collection,
                    remainder,
                    pathmap_mode,
                    argument_count,
                    value_base,
                } => {
                    let expected = argument_count
                        .checked_add(usize::from(remainder))
                        .ok_or(SemanticMatchUndetermined::AllocationFailed)?;
                    if value_base > values.len() || values.len() - value_base != expected {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let mut children = values.split_off(value_base);
                    let remainder = if remainder { children.pop() } else { None };
                    if children.len() != argument_count {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let value = self.synthetic_application(
                        sort,
                        operator,
                        children,
                        collection,
                        remainder,
                        pathmap_mode,
                    )?;
                    values
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    values.push(value);
                },
            }
        }
        match values.as_slice() {
            [value] => Ok(*value),
            _ => Err(SemanticMatchUndetermined::InvalidImageEvidence),
        }
    }

    fn project_transition_substitution(
        &mut self,
        rule: &TheoryRuleProgramV1,
        activation: u64,
        substitution: &HornSubstitution,
    ) -> Result<Vec<(TheoryVariableId, HornTermRef)>, SemanticMatchUndetermined> {
        let mut candidates = Vec::new();
        candidates
            .try_reserve_exact(rule.variables.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for declaration in &rule.variables {
            if declaration.role != mettail_grammar_core::TheoryVariableRoleV1::Binder {
                candidates.push(declaration.id);
            }
        }
        let mut projected = Vec::new();
        projected
            .try_reserve_exact(candidates.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for variable in candidates {
            let scoped = ScopedClauseVariable { activation, variable };
            let Some(term) = Self::lookup_substitution(substitution, scoped) else {
                continue;
            };
            let term = self.ground_virtual_term(term, substitution)?;
            projected.push((variable, term));
        }
        Ok(projected)
    }

    fn lookup_substitution(
        substitution: &[(ScopedClauseVariable, HornTermRef)],
        variable: ScopedClauseVariable,
    ) -> Option<HornTermRef> {
        substitution
            .iter()
            .rev()
            .find_map(|(candidate, term)| (*candidate == variable).then_some(*term))
    }

    fn keyed_entry_key(
        &mut self,
        entry: EClassId,
        pair_sort: TheorySortId,
        key_sort: TheorySortId,
        value_sort: TheorySortId,
    ) -> Result<ContentKey, SemanticMatchUndetermined> {
        self.charge()?;
        let entry = self.egraph.find(entry);
        let [node] = self.egraph.nodes(entry) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let exact = exact_theory_operator_bytes(&node.op)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if exact.len() != 5
            || exact[0] != 4
            || TheorySortId(read_u32(&exact[1..])) != pair_sort
            || node.children.len() != 2
        {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        let TheorySortKindImageV1::Product { factors } = runtime_sort_kind(self.image, pair_sort)?
        else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        if factors.as_slice() != [key_sort, value_sort] {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        let key = self.egraph.find(node.children[0]);
        self.exact_ground_key(key)
    }

    fn pathmap_mode(
        &mut self,
        marker: EClassId,
        sort: TheorySortId,
    ) -> Result<PathMapModeV1, SemanticMatchUndetermined> {
        self.charge()?;
        let marker = self.egraph.find(marker);
        let [node] = self.egraph.nodes(marker) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        if !node.children.is_empty() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        exact_theory_pathmap_mode(&node.op, sort)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
    }

    fn clause_program(
        &self,
        rule: HornRuleRef,
    ) -> Result<HornClauseProgram<'_>, SemanticMatchUndetermined> {
        match rule {
            HornRuleRef::Transition(id) => {
                let program = self
                    .image
                    .rules
                    .get(id.0 as usize)
                    .filter(|candidate| candidate.id == id)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                Ok(HornClauseProgram {
                    variables: &program.variables,
                    terms: &program.terms,
                })
            },
            HornRuleRef::Judgment(id) => {
                let program = self
                    .image
                    .judgment_rules
                    .get(id.0 as usize)
                    .filter(|candidate| candidate.id == id)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                Ok(HornClauseProgram {
                    variables: &program.variables,
                    terms: &program.terms,
                })
            },
        }
    }

    fn scoped_clause_variable(
        &self,
        activation: u64,
        mut scope: Option<usize>,
        variable: TheoryVariableId,
    ) -> Result<ScopedClauseVariable, SemanticMatchUndetermined> {
        while let Some(index) = scope {
            let lexical = self
                .lexical_scopes
                .get(index)
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
            if let Some((_, scoped)) = lexical
                .bindings
                .iter()
                .find(|(candidate, _)| *candidate == variable)
            {
                return Ok(*scoped);
            }
            if lexical.parent.is_some_and(|parent| parent >= index) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            scope = lexical.parent;
        }
        Ok(ScopedClauseVariable { activation, variable })
    }

    fn push_lexical_scope(
        &mut self,
        parent: Option<usize>,
        parameters: &[TheoryVariableId],
    ) -> Result<(usize, Vec<ScopedClauseVariable>), SemanticMatchUndetermined> {
        let activation = self.fresh_activation()?;
        let mut bindings = Vec::new();
        bindings
            .try_reserve_exact(parameters.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let mut scoped = Vec::new();
        scoped
            .try_reserve_exact(parameters.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for parameter in parameters {
            let variable = ScopedClauseVariable { activation, variable: *parameter };
            bindings.push((*parameter, variable));
            scoped.push(variable);
        }
        self.lexical_scopes
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let index = self.lexical_scopes.len();
        if parent.is_some_and(|parent| parent >= index) {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        self.lexical_scopes
            .push(HornLexicalScope { parent, bindings });
        Ok((index, scoped))
    }

    fn with_lexical_scope(
        term: HornTermRef,
        scope: usize,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        match term {
            HornTermRef::Clause { activation, rule, term, .. } => Ok(HornTermRef::Clause {
                activation,
                rule,
                term,
                scope: Some(scope),
            }),
            _ => Err(SemanticMatchUndetermined::InvalidImageEvidence),
        }
    }

    fn view(
        &mut self,
        mut term: HornTermRef,
        substitution: &[(ScopedClauseVariable, HornTermRef)],
    ) -> Result<HornTermView, SemanticMatchUndetermined> {
        let mut visited = BTreeSet::new();
        loop {
            self.charge()?;
            if !visited.insert(term) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            match term {
                HornTermRef::Variable { variable, sort } => {
                    if let Some(bound) = Self::lookup_substitution(substitution, variable) {
                        term = bound;
                    } else {
                        return Ok(HornTermView {
                            term,
                            sort,
                            form: HornTermForm::Variable(variable),
                        });
                    }
                },
                HornTermRef::Clause { activation, rule, term: term_id, scope } => {
                    let program = self.clause_program(rule)?;
                    let node = program
                        .terms
                        .get(term_id.0 as usize)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    match &node.form {
                        TheoryImageTermFormV1::Slot(variable) => {
                            let declaration = program
                                .variables
                                .get(variable.0 as usize)
                                .filter(|candidate| candidate.id == *variable)
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            if declaration.sort != node.sort {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            term = HornTermRef::Variable {
                                variable: self
                                    .scoped_clause_variable(activation, scope, *variable)?,
                                sort: declaration.sort,
                            };
                        },
                        TheoryImageTermFormV1::Apply {
                            operator,
                            arguments,
                            slots,
                            remainder,
                            pathmap_mode,
                        } => {
                            let signature =
                                runtime_operator_signature(self.image, operator, *pathmap_mode)?;
                            if signature.result != node.sort {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            let child_count = slots
                                .len()
                                .checked_add(arguments.len())
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            match &signature.children {
                                RuntimeChildSortContract::Fixed(sorts)
                                    if sorts.len() == child_count && remainder.is_none() => {},
                                RuntimeChildSortContract::Homogeneous(_) => {},
                                RuntimeChildSortContract::RemainderOnly
                                    if child_count == 0 && remainder.is_some() => {},
                                _ => {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                },
                            }
                            let mut children = Vec::new();
                            children
                                .try_reserve_exact(child_count)
                                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                            for (index, variable) in slots.iter().enumerate() {
                                let declaration = program
                                    .variables
                                    .get(variable.0 as usize)
                                    .filter(|candidate| candidate.id == *variable)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                let expected = match &signature.children {
                                    RuntimeChildSortContract::Fixed(sorts) => sorts[index],
                                    RuntimeChildSortContract::Homogeneous(sort) => *sort,
                                    RuntimeChildSortContract::RemainderOnly => {
                                        return Err(
                                            SemanticMatchUndetermined::InvalidImageEvidence,
                                        );
                                    },
                                };
                                if declaration.sort != expected {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                children.push(HornTermRef::Variable {
                                    variable: ScopedClauseVariable {
                                        activation,
                                        variable: *variable,
                                    },
                                    sort: declaration.sort,
                                });
                            }
                            for (offset, argument) in arguments.iter().enumerate() {
                                let argument_node = program
                                    .terms
                                    .get(argument.0 as usize)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                let expected = match &signature.children {
                                    RuntimeChildSortContract::Fixed(sorts) => {
                                        sorts[slots.len() + offset]
                                    },
                                    RuntimeChildSortContract::Homogeneous(sort) => *sort,
                                    RuntimeChildSortContract::RemainderOnly => {
                                        return Err(
                                            SemanticMatchUndetermined::InvalidImageEvidence,
                                        );
                                    },
                                };
                                let collection_splice =
                                    matches!(operator, TheoryImageOperatorV1::Collection { .. })
                                        && matches!(
                                            argument_node.form,
                                            TheoryImageTermFormV1::Map { .. }
                                        )
                                        && argument_node.sort == node.sort;
                                if !collection_splice && argument_node.sort != expected {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                children.push(HornTermRef::Clause {
                                    activation,
                                    rule,
                                    term: *argument,
                                    scope,
                                });
                            }
                            let remainder = match remainder {
                                Some(variable) => {
                                    if !matches!(
                                        &signature.children,
                                        RuntimeChildSortContract::Homogeneous(_)
                                            | RuntimeChildSortContract::RemainderOnly
                                    ) {
                                        return Err(
                                            SemanticMatchUndetermined::InvalidImageEvidence,
                                        );
                                    }
                                    let declaration = program
                                        .variables
                                        .get(variable.0 as usize)
                                        .filter(|candidate| candidate.id == *variable)
                                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                    if declaration.sort != node.sort {
                                        return Err(
                                            SemanticMatchUndetermined::InvalidImageEvidence,
                                        );
                                    }
                                    Some(HornTermRef::Variable {
                                        variable: self
                                            .scoped_clause_variable(activation, scope, *variable)?,
                                        sort: node.sort,
                                    })
                                },
                                None => None,
                            };
                            let collection = match operator {
                                TheoryImageOperatorV1::Collection { kind, .. } => Some(*kind),
                                _ => None,
                            };
                            let view = HornTermView {
                                term,
                                sort: node.sort,
                                form: HornTermForm::Application {
                                    operator: theory_operator_to_machine(operator),
                                    arguments: children,
                                    collection,
                                    remainder,
                                    pathmap_mode: *pathmap_mode,
                                },
                            };
                            self.charge_units(child_count)?;
                            return Ok(view);
                        },
                        TheoryImageTermFormV1::Map { sources, parameters, body } => {
                            let view_work = sources
                                .len()
                                .checked_add(parameters.len())
                                .and_then(|count| count.checked_add(1))
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            let mut source_terms = Vec::new();
                            source_terms
                                .try_reserve_exact(sources.len())
                                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                            for source in sources {
                                let source_node = program
                                    .terms
                                    .get(source.0 as usize)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                source_terms.push(HornTermRef::Clause {
                                    activation,
                                    rule,
                                    term: *source,
                                    scope,
                                });
                                if !matches!(
                                    runtime_sort_kind(self.image, source_node.sort)?,
                                    TheorySortKindImageV1::Collection { .. }
                                ) {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                            }
                            let mut checked_parameters = Vec::new();
                            checked_parameters
                                .try_reserve_exact(parameters.len())
                                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                            for parameter in parameters {
                                let declaration = program
                                    .variables
                                    .get(parameter.0 as usize)
                                    .filter(|candidate| candidate.id == *parameter)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                if declaration.role
                                    != mettail_grammar_core::TheoryVariableRoleV1::Binder
                                {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                checked_parameters.push(*parameter);
                            }
                            let body_node = program
                                .terms
                                .get(body.0 as usize)
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            let TheorySortKindImageV1::Collection { element, .. } =
                                runtime_sort_kind(self.image, node.sort)?
                            else {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            };
                            if body_node.sort != *element || sources.is_empty() {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            let view = HornTermView {
                                term,
                                sort: node.sort,
                                form: HornTermForm::Comprehension {
                                    sources: source_terms,
                                    parameters: checked_parameters,
                                    body: HornTermRef::Clause {
                                        activation,
                                        rule,
                                        term: *body,
                                        scope,
                                    },
                                },
                            };
                            self.charge_units(view_work)?;
                            return Ok(view);
                        },
                    }
                },
                HornTermRef::Ground { class, sort } => {
                    return self.view_ground(class, sort);
                },
                HornTermRef::Synthetic { term: term_id, sort } => {
                    let synthetic = self
                        .synthetic_terms
                        .get(term_id)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    if synthetic.sort != sort {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    return Ok(HornTermView {
                        term,
                        sort,
                        form: HornTermForm::Application {
                            operator: synthetic.operator.clone(),
                            arguments: clone_copy_slice(&synthetic.arguments)?,
                            collection: synthetic.collection,
                            remainder: synthetic.remainder,
                            pathmap_mode: synthetic.pathmap_mode,
                        },
                    });
                },
            }
        }
    }

    fn view_ground(
        &mut self,
        class: EClassId,
        expected_sort: TheorySortId,
    ) -> Result<HornTermView, SemanticMatchUndetermined> {
        self.charge()?;
        let class = self.egraph.find(class);
        let [node] = self.egraph.nodes(class) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let child_count = node.children.len();
        self.charge_units(child_count)?;
        let [node] = self.egraph.nodes(class) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        runtime_sort_kind(self.image, expected_sort)?;
        let exact = exact_theory_operator_bytes(&node.op)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let (&tag, payload) = exact
            .split_first()
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let mut arguments = Vec::new();
        let mut collection = None;
        let mut pathmap_mode = None;
        match tag {
            0 => {
                if payload.len() != 4 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let constructor = mettail_grammar_core::TheoryConstructorId(read_u32(payload));
                let signature = self
                    .image
                    .constructors
                    .get(constructor.0 as usize)
                    .filter(|candidate| candidate.id == constructor)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                if signature.codomain != expected_sort
                    || signature.domain.len() != node.children.len()
                {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                arguments
                    .try_reserve_exact(node.children.len())
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for (&child, &sort) in node.children.iter().zip(&signature.domain) {
                    arguments.push(HornTermRef::Ground { class: self.egraph.find(child), sort });
                }
            },
            1 => {
                if payload.len() != 4 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let function = TheorySortId(read_u32(payload));
                let TheorySortKindImageV1::Function { domain, codomain, .. } =
                    runtime_sort_kind(self.image, function)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if function != expected_sort || node.children.len() != 2 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                arguments
                    .try_reserve_exact(2)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[0]),
                    sort: *domain,
                });
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[1]),
                    sort: *codomain,
                });
            },
            2 => {
                if payload.len() != 8 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let result = TheorySortId(read_u32(&payload[..4]));
                let function = TheorySortId(read_u32(&payload[4..]));
                let TheorySortKindImageV1::Function { domain, codomain, .. } =
                    runtime_sort_kind(self.image, function)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if result != expected_sort || *codomain != result || node.children.len() != 2 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                arguments
                    .try_reserve_exact(2)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[0]),
                    sort: function,
                });
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[1]),
                    sort: *domain,
                });
            },
            3 => {
                if payload.len() != 9 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let sort = TheorySortId(read_u32(&payload[..4]));
                let element = TheorySortId(read_u32(&payload[4..8]));
                let kind = decode_runtime_collection_kind(payload[8])?;
                let TheorySortKindImageV1::Collection {
                    kind: declared_kind,
                    key: declared_key,
                    element: declared_element,
                } = runtime_sort_kind(self.image, sort)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if sort != expected_sort || kind != *declared_kind || element != *declared_element {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                collection = Some(kind);
                let mut children = Vec::new();
                children
                    .try_reserve_exact(node.children.len())
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                children.extend(node.children.iter().map(|child| self.egraph.find(*child)));
                match kind {
                    CollectionKind::List => {
                        if declared_key.is_some() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        arguments
                            .try_reserve_exact(children.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        arguments.extend(
                            children
                                .into_iter()
                                .map(|class| HornTermRef::Ground { class, sort: element }),
                        );
                    },
                    CollectionKind::Bag | CollectionKind::Set => {
                        if declared_key.is_some() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        let mut keys = Vec::new();
                        keys.try_reserve_exact(children.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        arguments
                            .try_reserve_exact(children.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        for class in children {
                            keys.push(self.exact_ground_key(class)?);
                            arguments.push(HornTermRef::Ground { class, sort: element });
                        }
                        let canonical = if kind == CollectionKind::Bag {
                            keys_are_nondecreasing(&keys)
                        } else {
                            keys_are_strictly_increasing(&keys)
                        };
                        if !canonical {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                    },
                    CollectionKind::Map => {
                        let sorts =
                            runtime_keyed_collection_sorts(self.image, sort, kind, element)?;
                        let mut keys = Vec::new();
                        keys.try_reserve_exact(children.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        arguments
                            .try_reserve_exact(children.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        for class in children {
                            keys.push(self.keyed_entry_key(
                                class,
                                sorts.pair,
                                sorts.key,
                                sorts.value,
                            )?);
                            arguments.push(HornTermRef::Ground { class, sort: element });
                        }
                        if !keys_are_strictly_increasing(&keys) {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                    },
                    CollectionKind::PathMap => {
                        let sorts =
                            runtime_keyed_collection_sorts(self.image, sort, kind, element)?;
                        let Some((&marker, entries)) = children.split_first() else {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        };
                        let mode = self.pathmap_mode(marker, sort)?;
                        pathmap_mode = Some(mode);
                        let mut keys = Vec::new();
                        keys.try_reserve_exact(entries.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        arguments
                            .try_reserve_exact(entries.len())
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        match mode {
                            PathMapModeV1::NeutralEmpty => {
                                if !entries.is_empty() {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                            },
                            PathMapModeV1::Set => {
                                for &class in entries {
                                    keys.push(self.exact_ground_key(class)?);
                                    arguments.push(HornTermRef::Ground { class, sort: sorts.key });
                                }
                            },
                            PathMapModeV1::Map => {
                                for &class in entries {
                                    keys.push(self.keyed_entry_key(
                                        class,
                                        sorts.pair,
                                        sorts.key,
                                        sorts.value,
                                    )?);
                                    arguments.push(HornTermRef::Ground { class, sort: element });
                                }
                            },
                        }
                        if !keys_are_strictly_increasing(&keys) {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                    },
                }
            },
            4 => {
                if payload.len() != 4 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let product = TheorySortId(read_u32(payload));
                let TheorySortKindImageV1::Product { factors } =
                    runtime_sort_kind(self.image, product)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if product != expected_sort || factors.len() != node.children.len() {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                arguments
                    .try_reserve_exact(factors.len())
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for (&child, &sort) in node.children.iter().zip(factors) {
                    arguments.push(HornTermRef::Ground { class: self.egraph.find(child), sort });
                }
            },
            5 => {
                if !node.children.is_empty()
                    || payload.len() < 5
                    || TheorySortId(read_u32(&payload[..4])) != expected_sort
                {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let TheorySortKindImageV1::Syntax { literal: Some(carrier) } =
                    runtime_sort_kind(self.image, expected_sort)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if !literal_payload_matches_carrier(&payload[4..], carrier) {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
            },
            _ => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
        }
        Ok(HornTermView {
            term: HornTermRef::Ground { class, sort: expected_sort },
            sort: expected_sort,
            form: HornTermForm::Application {
                operator: node.op.clone(),
                arguments,
                collection,
                remainder: None,
                pathmap_mode,
            },
        })
    }

    fn ground_arguments(
        &mut self,
        goal: &HornGoal,
        substitution: &[(ScopedClauseVariable, HornTermRef)],
    ) -> Result<Option<Vec<EClassId>>, SemanticMatchUndetermined> {
        let mut arguments = Vec::new();
        arguments
            .try_reserve_exact(goal.terms.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for term in &goal.terms {
            let view = self.view(*term, substitution)?;
            let HornTermRef::Ground { class, .. } = view.term else {
                return Ok(None);
            };
            arguments.push(class);
        }
        Ok(Some(arguments))
    }

    fn validate_ground_term(
        &mut self,
        root: EClassId,
        sort: TheorySortId,
    ) -> Result<(), SemanticMatchUndetermined> {
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.push(HornTermRef::Ground { class: root, sort });
        let mut visited = BTreeSet::new();
        while let Some(term) = pending.pop() {
            self.charge()?;
            if !visited.insert(term) {
                continue;
            }
            let view = self.view(term, &[])?;
            match view.form {
                HornTermForm::Variable(_) => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
                HornTermForm::Application { arguments, .. } => {
                    pending
                        .try_reserve(arguments.len())
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    pending.extend(arguments.into_iter().rev());
                },
                HornTermForm::Comprehension { .. } => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
            }
        }
        Ok(())
    }

    fn occurs(
        &mut self,
        needle: ScopedClauseVariable,
        term: HornTermRef,
        substitution: &[(ScopedClauseVariable, HornTermRef)],
    ) -> Result<bool, SemanticMatchUndetermined> {
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.push(term);
        let mut visited = BTreeSet::new();
        while let Some(term) = pending.pop() {
            self.charge()?;
            if !visited.insert(term) {
                continue;
            }
            match self.view(term, substitution)? {
                HornTermView {
                    form: HornTermForm::Variable(variable), ..
                } if variable == needle => return Ok(true),
                HornTermView { form: HornTermForm::Variable(_), .. } => {},
                HornTermView {
                    form: HornTermForm::Application { arguments, .. },
                    ..
                } => {
                    pending
                        .try_reserve(arguments.len())
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    pending.extend(arguments.into_iter().rev());
                },
                HornTermView {
                    form: HornTermForm::Comprehension { mut sources, body, .. },
                    ..
                } => {
                    sources.push(body);
                    pending
                        .try_reserve(sources.len())
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    pending.extend(sources.into_iter().rev());
                },
            }
        }
        Ok(false)
    }

    fn push_unification_branch(
        frontier: &mut VecDeque<HornUnificationBranch>,
        branch: HornUnificationBranch,
        frontier_limit: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        if frontier.len() == frontier_limit {
            return Err(SemanticMatchUndetermined::FrontierLimitExceeded);
        }
        frontier
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        frontier.push_back(branch);
        Ok(())
    }

    fn extend_unification_equations(
        pending: &mut Vec<HornConstraint>,
        equations: &[(HornTermRef, HornTermRef)],
    ) -> Result<(), SemanticMatchUndetermined> {
        pending
            .try_reserve(equations.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.extend(
            equations
                .iter()
                .rev()
                .map(|&(left, right)| HornConstraint::Equation(left, right)),
        );
        Ok(())
    }

    fn clone_unification_branch(
        branch: &HornUnificationBranch,
    ) -> Result<HornUnificationBranch, SemanticMatchUndetermined> {
        Ok(HornUnificationBranch {
            pending: clone_copy_slice(&branch.pending)?,
            substitution: clone_copy_slice(&branch.substitution)?,
        })
    }

    fn store_collection_state(
        &mut self,
        state: HornCollectionPatternState,
    ) -> Result<usize, SemanticMatchUndetermined> {
        self.collection_states
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let index = self.collection_states.len();
        self.collection_states.push(state);
        Ok(index)
    }

    fn store_comprehension_state(
        &mut self,
        state: HornComprehensionRowState,
    ) -> Result<usize, SemanticMatchUndetermined> {
        self.comprehension_states
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let index = self.comprehension_states.len();
        self.comprehension_states.push(state);
        Ok(index)
    }

    fn store_derived_collection(
        &mut self,
        state: HornDerivedCollection,
    ) -> Result<usize, SemanticMatchUndetermined> {
        self.derived_collections
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let index = self.derived_collections.len();
        self.derived_collections.push(state);
        Ok(index)
    }

    fn collection_state_copy(
        &self,
        index: usize,
    ) -> Result<HornCollectionPatternState, SemanticMatchUndetermined> {
        let state = self
            .collection_states
            .get(index)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        Ok(HornCollectionPatternState {
            sort: state.sort,
            operator: state.operator.clone(),
            collection: state.collection,
            patterns: clone_copy_slice(&state.patterns)?,
            target_arguments: clone_copy_slice(&state.target_arguments)?,
            remainder: state.remainder,
            pattern_pathmap_mode: state.pattern_pathmap_mode,
            target_pathmap_mode: state.target_pathmap_mode,
        })
    }

    fn resolved_collection_mode(
        state: &HornCollectionPatternState,
    ) -> Result<Option<PathMapModeV1>, SemanticMatchUndetermined> {
        match state.collection {
            CollectionKind::PathMap => {
                match (state.pattern_pathmap_mode, state.target_pathmap_mode) {
                    (Some(left), Some(right)) if left != right => Ok(None),
                    (Some(mode), _) | (_, Some(mode)) => Ok(Some(mode)),
                    (None, None) => Err(SemanticMatchUndetermined::InvalidImageEvidence),
                }
            },
            _ if state.pattern_pathmap_mode.is_some() || state.target_pathmap_mode.is_some() => {
                Err(SemanticMatchUndetermined::InvalidImageEvidence)
            },
            _ => Ok(None),
        }
    }

    fn remove_copy_at<T: Copy>(
        values: &[T],
        index: usize,
    ) -> Result<Vec<T>, SemanticMatchUndetermined> {
        if index >= values.len() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        let mut output = Vec::new();
        output
            .try_reserve_exact(values.len() - 1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        output.extend(values[..index].iter().copied());
        output.extend(values[index + 1..].iter().copied());
        Ok(output)
    }

    fn push_collection_continuation(
        &mut self,
        branch: &mut HornUnificationBranch,
        state: HornCollectionPatternState,
    ) -> Result<(), SemanticMatchUndetermined> {
        let index = self.store_collection_state(state)?;
        branch
            .pending
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        branch.pending.push(HornConstraint::Collection(index));
        Ok(())
    }

    fn arguments_contain_comprehension(
        &mut self,
        arguments: &[HornTermRef],
        substitution: &HornSubstitution,
    ) -> Result<bool, SemanticMatchUndetermined> {
        for argument in arguments {
            if matches!(
                self.view(*argument, substitution)?.form,
                HornTermForm::Comprehension { .. }
            ) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn expand_collection_constraint(
        &mut self,
        mut branch: HornUnificationBranch,
        state_index: usize,
        frontier: &mut VecDeque<HornUnificationBranch>,
        frontier_limit: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        let mut state = self.collection_state_copy(state_index)?;
        let resolved_mode = Self::resolved_collection_mode(&state)?;
        if state.collection == CollectionKind::PathMap
            && state.pattern_pathmap_mode.is_some()
            && state.target_pathmap_mode.is_some()
            && resolved_mode.is_none()
        {
            return Ok(());
        }
        if state.patterns.is_empty() {
            if let Some(remainder) = state.remainder {
                let fragment = self.collection_fragment(
                    state.sort,
                    &state.operator,
                    state.collection,
                    state.target_arguments,
                    None,
                    resolved_mode,
                )?;
                branch
                    .pending
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                branch
                    .pending
                    .push(HornConstraint::Equation(remainder, fragment));
                Self::push_unification_branch(frontier, branch, frontier_limit)?;
            } else if state.target_arguments.is_empty() {
                Self::push_unification_branch(frontier, branch, frontier_limit)?;
            }
            return Ok(());
        }

        let pattern = state.patterns[0];
        if matches!(
            self.view(pattern, &branch.substitution)?.form,
            HornTermForm::Comprehension { .. }
        ) {
            if state.collection == CollectionKind::PathMap
                && state.target_pathmap_mode != Some(PathMapModeV1::Map)
            {
                return Ok(());
            }
            state.patterns.remove(0);
            let comprehension =
                self.prepare_comprehension_state(pattern, state, &branch.substitution)?;
            let index = self.store_comprehension_state(comprehension)?;
            branch
                .pending
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            branch.pending.push(HornConstraint::ComprehensionRow(index));
            Self::push_unification_branch(frontier, branch, frontier_limit)?;
            return Ok(());
        }

        if state.target_arguments.is_empty() {
            return Ok(());
        }
        let candidate_indices: std::ops::Range<usize> = match state.collection {
            CollectionKind::List => 0..1,
            _ => 0..state.target_arguments.len(),
        };
        for candidate_index in candidate_indices {
            self.charge()?;
            let mut candidate = Self::clone_unification_branch(&branch)?;
            let target = state.target_arguments[candidate_index];
            let continuation = HornCollectionPatternState {
                sort: state.sort,
                operator: state.operator.clone(),
                collection: state.collection,
                patterns: clone_copy_slice(&state.patterns[1..])?,
                target_arguments: Self::remove_copy_at(&state.target_arguments, candidate_index)?,
                remainder: state.remainder,
                pattern_pathmap_mode: state.pattern_pathmap_mode,
                target_pathmap_mode: state.target_pathmap_mode,
            };
            self.push_collection_continuation(&mut candidate, continuation)?;
            candidate
                .pending
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            candidate
                .pending
                .push(HornConstraint::Equation(pattern, target));
            Self::push_unification_branch(frontier, candidate, frontier_limit)?;
        }
        Ok(())
    }

    fn resolved_collection_terms(
        &mut self,
        root: HornTermRef,
        substitution: &HornSubstitution,
    ) -> Result<ResolvedCollectionTerms, SemanticMatchUndetermined> {
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.push(root);
        let mut visited = BTreeSet::new();
        let mut expected = None;
        let mut arguments = Vec::new();
        while let Some(term) = pending.pop() {
            self.charge()?;
            let view = self.view(term, substitution)?;
            if !visited.insert(view.term) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let HornTermForm::Application {
                operator,
                arguments: segment,
                collection: Some(collection),
                remainder,
                pathmap_mode,
            } = view.form
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            match &expected {
                None => expected = Some((view.sort, operator.clone(), collection, pathmap_mode)),
                Some((sort, expected_operator, expected_collection, expected_mode))
                    if *sort == view.sort
                        && *expected_operator == operator
                        && *expected_collection == collection
                        && (*expected_mode == pathmap_mode
                            || expected_mode.is_none()
                            || pathmap_mode.is_none()) => {},
                Some(_) => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
            }
            arguments
                .try_reserve(segment.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            arguments.extend(segment);
            if let Some(remainder) = remainder {
                pending
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                pending.push(remainder);
            }
        }
        let (sort, operator, collection, mode) =
            expected.ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        Ok((sort, operator, collection, mode, arguments))
    }

    fn prepare_comprehension_state(
        &mut self,
        comprehension: HornTermRef,
        collection: HornCollectionPatternState,
        substitution: &HornSubstitution,
    ) -> Result<HornComprehensionRowState, SemanticMatchUndetermined> {
        let HornTermView {
            form: HornTermForm::Comprehension { sources, parameters, body },
            ..
        } = self.view(comprehension, substitution)?
        else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let (activation, rule, parent_scope) = match body {
            HornTermRef::Clause { activation, rule, scope, .. } => (activation, rule, scope),
            _ => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
        };
        let parameter_sorts = {
            let program = self.clause_program(rule)?;
            let mut sorts = Vec::new();
            sorts
                .try_reserve_exact(parameters.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            for parameter in &parameters {
                let declaration = program
                    .variables
                    .get(parameter.0 as usize)
                    .filter(|candidate| candidate.id == *parameter)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                if declaration.role != mettail_grammar_core::TheoryVariableRoleV1::Binder {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                sorts.push(declaration.sort);
            }
            sorts
        };
        if sources.is_empty() || parameters.is_empty() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }

        let mut resolved_sources = Vec::new();
        resolved_sources
            .try_reserve_exact(sources.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        let mut derived_sources = Vec::new();
        for (index, source) in sources.iter().copied().enumerate() {
            let source_view = self.view(source, substitution)?;
            match source_view.form {
                HornTermForm::Variable(variable) if index > 0 && sources.len() > 1 => {
                    derived_sources.push((index, variable, source_view.sort));
                    resolved_sources.push(None);
                },
                HornTermForm::Variable(_) => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
                HornTermForm::Application { .. } => {
                    let (sort, _, kind, _, rows) =
                        self.resolved_collection_terms(source, substitution)?;
                    if sort != source_view.sort
                        || (sources.len() > 1 && kind != CollectionKind::List)
                    {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let TheorySortKindImageV1::Collection { element, .. } =
                        runtime_sort_kind(self.image, sort)?
                    else {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    };
                    resolved_sources.push(Some((*element, rows)));
                },
                HornTermForm::Comprehension { .. } => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
            }
        }
        let row_count = resolved_sources
            .first()
            .and_then(Option::as_ref)
            .map(|(_, rows)| rows.len())
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if resolved_sources
            .iter()
            .flatten()
            .any(|(_, rows)| rows.len() != row_count)
        {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }

        let mut row_bodies = Vec::new();
        let mut row_scoped_parameters = Vec::new();
        let mut row_seeds = Vec::new();
        row_bodies
            .try_reserve_exact(row_count)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        row_scoped_parameters
            .try_reserve_exact(row_count)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        row_seeds
            .try_reserve_exact(row_count)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for row in 0..row_count {
            let (scope, scoped_parameters) = self.push_lexical_scope(parent_scope, &parameters)?;
            row_bodies.push(Self::with_lexical_scope(body, scope)?);
            let mut seeds = Vec::new();
            seeds
                .try_reserve_exact(parameters.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            if sources.len() == 1 {
                let Some((element_sort, rows)) = &resolved_sources[0] else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                match runtime_sort_kind(self.image, *element_sort)? {
                    TheorySortKindImageV1::Product { factors } => {
                        if factors.as_slice() != parameter_sorts.as_slice() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        let row_view = self.view(rows[row], substitution)?;
                        let HornTermForm::Application {
                            operator,
                            arguments,
                            collection: None,
                            remainder: None,
                            pathmap_mode: None,
                        } = row_view.form
                        else {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        };
                        if operator
                            != theory_operator_to_machine(&TheoryImageOperatorV1::Product {
                                sort: *element_sort,
                            })
                            || arguments.len() != scoped_parameters.len()
                        {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        for ((variable, sort), value) in scoped_parameters
                            .iter()
                            .copied()
                            .zip(parameter_sorts.iter().copied())
                            .zip(arguments)
                        {
                            seeds.push((HornTermRef::Variable { variable, sort }, value));
                        }
                    },
                    _ => {
                        if scoped_parameters.len() != 1
                            || parameter_sorts.first() != Some(element_sort)
                        {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        seeds.push((
                            HornTermRef::Variable {
                                variable: scoped_parameters[0],
                                sort: parameter_sorts[0],
                            },
                            rows[row],
                        ));
                    },
                }
            } else {
                if sources.len() != parameters.len() {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                for (index, source) in resolved_sources.iter().enumerate() {
                    if let Some((element_sort, rows)) = source {
                        if parameter_sorts[index] != *element_sort {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        seeds.push((
                            HornTermRef::Variable {
                                variable: scoped_parameters[index],
                                sort: parameter_sorts[index],
                            },
                            rows[row],
                        ));
                    }
                }
            }
            row_scoped_parameters.push(scoped_parameters);
            row_seeds.push(seeds);
        }

        let mut derived = Vec::new();
        derived
            .try_reserve_exact(derived_sources.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for (parameter_index, variable, sort) in derived_sources {
            let TheorySortKindImageV1::Collection { kind: CollectionKind::List, element, .. } =
                runtime_sort_kind(self.image, sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if *element != parameter_sorts[parameter_index] {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let mut elements = Vec::new();
            elements
                .try_reserve_exact(row_count)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            for row in &row_scoped_parameters {
                elements.push(HornTermRef::Variable {
                    variable: row[parameter_index],
                    sort: *element,
                });
            }
            derived.push(HornDerivedCollection { variable, sort, elements });
        }
        let _ = activation;
        Ok(HornComprehensionRowState {
            collection,
            row_bodies,
            row_seeds,
            derived,
            next_row: 0,
        })
    }

    fn comprehension_state_copy(
        &self,
        index: usize,
    ) -> Result<HornComprehensionRowState, SemanticMatchUndetermined> {
        let state = self
            .comprehension_states
            .get(index)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let mut row_seeds = Vec::new();
        row_seeds
            .try_reserve_exact(state.row_seeds.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for seeds in &state.row_seeds {
            row_seeds.push(clone_copy_slice(seeds)?);
        }
        let mut derived = Vec::new();
        derived
            .try_reserve_exact(state.derived.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for item in &state.derived {
            derived.push(HornDerivedCollection {
                variable: item.variable,
                sort: item.sort,
                elements: clone_copy_slice(&item.elements)?,
            });
        }
        Ok(HornComprehensionRowState {
            collection: HornCollectionPatternState {
                sort: state.collection.sort,
                operator: state.collection.operator.clone(),
                collection: state.collection.collection,
                patterns: clone_copy_slice(&state.collection.patterns)?,
                target_arguments: clone_copy_slice(&state.collection.target_arguments)?,
                remainder: state.collection.remainder,
                pattern_pathmap_mode: state.collection.pattern_pathmap_mode,
                target_pathmap_mode: state.collection.target_pathmap_mode,
            },
            row_bodies: clone_copy_slice(&state.row_bodies)?,
            row_seeds,
            derived,
            next_row: state.next_row,
        })
    }

    fn expand_comprehension_row_constraint(
        &mut self,
        mut branch: HornUnificationBranch,
        state_index: usize,
        frontier: &mut VecDeque<HornUnificationBranch>,
        frontier_limit: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        let state = self.comprehension_state_copy(state_index)?;
        if state.next_row == state.row_bodies.len() {
            self.push_collection_continuation(&mut branch, state.collection)?;
            for derived in state.derived.into_iter().rev() {
                let index = self.store_derived_collection(derived)?;
                branch
                    .pending
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                branch.pending.push(HornConstraint::FinalizeDerived(index));
            }
            Self::push_unification_branch(frontier, branch, frontier_limit)?;
            return Ok(());
        }
        if state.collection.target_arguments.is_empty() {
            return Ok(());
        }
        let candidates = match state.collection.collection {
            CollectionKind::List => 0..1,
            _ => 0..state.collection.target_arguments.len(),
        };
        for candidate_index in candidates {
            self.charge()?;
            let mut candidate = Self::clone_unification_branch(&branch)?;
            let target = state.collection.target_arguments[candidate_index];
            let mut continuation = self.comprehension_state_copy(state_index)?;
            continuation.next_row += 1;
            continuation.collection.target_arguments =
                Self::remove_copy_at(&continuation.collection.target_arguments, candidate_index)?;
            let continuation = self.store_comprehension_state(continuation)?;
            candidate
                .pending
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            candidate
                .pending
                .push(HornConstraint::ComprehensionRow(continuation));
            let mut equations = clone_copy_slice(&state.row_seeds[state.next_row])?;
            equations
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            equations.push((state.row_bodies[state.next_row], target));
            Self::extend_unification_equations(&mut candidate.pending, &equations)?;
            Self::push_unification_branch(frontier, candidate, frontier_limit)?;
        }
        Ok(())
    }

    fn expand_finalize_derived_constraint(
        &mut self,
        mut branch: HornUnificationBranch,
        state_index: usize,
        frontier: &mut VecDeque<HornUnificationBranch>,
        frontier_limit: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        let state = self
            .derived_collections
            .get(state_index)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let variable = state.variable;
        let sort = state.sort;
        let elements = clone_copy_slice(&state.elements)?;
        let TheorySortKindImageV1::Collection { kind: CollectionKind::List, element, .. } =
            runtime_sort_kind(self.image, sort)?
        else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let element = *element;
        for item in &elements {
            let view = self.view(*item, &branch.substitution)?;
            if view.sort != element
                || matches!(
                    view.form,
                    HornTermForm::Variable(_) | HornTermForm::Comprehension { .. }
                )
            {
                return Ok(());
            }
        }
        let synthetic = self.synthetic_collection(
            sort,
            theory_operator_to_machine(&TheoryImageOperatorV1::Collection {
                sort,
                element,
                kind: CollectionKind::List,
            }),
            CollectionKind::List,
            elements,
            None,
            None,
        )?;
        branch
            .pending
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        branch
            .pending
            .push(HornConstraint::Equation(HornTermRef::Variable { variable, sort }, synthetic));
        Self::push_unification_branch(frontier, branch, frontier_limit)
    }

    fn collection_fragment(
        &mut self,
        sort: TheorySortId,
        operator: &FramedSemanticOperator,
        collection: CollectionKind,
        arguments: Vec<HornTermRef>,
        remainder: Option<HornTermRef>,
        pathmap_mode: Option<PathMapModeV1>,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        if collection != CollectionKind::PathMap && pathmap_mode.is_some() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        if collection == CollectionKind::PathMap
            && pathmap_mode.is_none()
            && (!arguments.is_empty() || remainder.is_none())
        {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        if arguments.is_empty() && (collection != CollectionKind::PathMap || pathmap_mode.is_none())
        {
            if let Some(remainder) = remainder {
                return Ok(remainder);
            }
        }
        self.charge()?;
        self.synthetic_collection(
            sort,
            operator.clone(),
            collection,
            arguments,
            remainder,
            pathmap_mode,
        )
    }

    fn expand_ordered_collection(
        &mut self,
        mut branch: HornUnificationBranch,
        equation: HornCollectionEquation,
    ) -> Result<Option<HornUnificationBranch>, SemanticMatchUndetermined> {
        let HornCollectionEquation {
            sort,
            operator,
            left_arguments,
            left_remainder,
            right_arguments,
            right_remainder,
            ..
        } = equation;
        let common = left_arguments.len().min(right_arguments.len());
        let mut equations = Vec::new();
        equations
            .try_reserve_exact(common.saturating_add(1))
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        equations.extend(
            left_arguments[..common]
                .iter()
                .copied()
                .zip(right_arguments[..common].iter().copied()),
        );

        match left_arguments.len().cmp(&right_arguments.len()) {
            std::cmp::Ordering::Equal => match (left_remainder, right_remainder) {
                (Some(left), Some(right)) => equations.push((left, right)),
                (Some(left), None) => {
                    let empty = self.collection_fragment(
                        sort,
                        &operator,
                        CollectionKind::List,
                        Vec::new(),
                        None,
                        None,
                    )?;
                    equations.push((left, empty));
                },
                (None, Some(right)) => {
                    let empty = self.collection_fragment(
                        sort,
                        &operator,
                        CollectionKind::List,
                        Vec::new(),
                        None,
                        None,
                    )?;
                    equations.push((empty, right));
                },
                (None, None) => {},
            },
            std::cmp::Ordering::Greater => {
                let Some(right_tail) = right_remainder else {
                    return Ok(None);
                };
                let left_extra = clone_copy_slice(&left_arguments[common..])?;
                let fragment = self.collection_fragment(
                    sort,
                    &operator,
                    CollectionKind::List,
                    left_extra,
                    left_remainder,
                    None,
                )?;
                equations.push((right_tail, fragment));
            },
            std::cmp::Ordering::Less => {
                let Some(left_tail) = left_remainder else {
                    return Ok(None);
                };
                let right_extra = clone_copy_slice(&right_arguments[common..])?;
                let fragment = self.collection_fragment(
                    sort,
                    &operator,
                    CollectionKind::List,
                    right_extra,
                    right_remainder,
                    None,
                )?;
                equations.push((left_tail, fragment));
            },
        }
        Self::extend_unification_equations(&mut branch.pending, &equations)?;
        Ok(Some(branch))
    }

    fn clone_row_pairing_branch(
        branch: &HornRowPairingBranch,
    ) -> Result<HornRowPairingBranch, SemanticMatchUndetermined> {
        Ok(HornRowPairingBranch {
            next_left: branch.next_left,
            used_right: clone_copy_slice(&branch.used_right)?,
            equations: clone_copy_slice(&branch.equations)?,
            unmatched_left: clone_copy_slice(&branch.unmatched_left)?,
        })
    }

    fn expand_unordered_collection(
        &mut self,
        branch: &HornUnificationBranch,
        equation: &HornCollectionEquation,
        frontier_limit: usize,
    ) -> Result<Vec<HornUnificationBranch>, SemanticMatchUndetermined> {
        let HornCollectionEquation {
            sort,
            operator,
            collection,
            left_arguments,
            left_remainder,
            left_pathmap_mode,
            right_arguments,
            right_remainder,
            right_pathmap_mode,
        } = equation;
        let resolved_pathmap_mode = match collection {
            CollectionKind::PathMap => match (left_pathmap_mode, right_pathmap_mode) {
                (Some(left), Some(right)) if left != right => return Ok(Vec::new()),
                (Some(mode), _) | (_, Some(mode)) => Some(*mode),
                (None, None) => None,
            },
            _ if left_pathmap_mode.is_some() || right_pathmap_mode.is_some() => {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            },
            _ => None,
        };
        let mut pairing_frontier = VecDeque::new();
        let mut used_right = Vec::new();
        used_right
            .try_reserve_exact(right_arguments.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        used_right.resize(right_arguments.len(), false);
        Self::push_row_pairing_branch(
            &mut pairing_frontier,
            HornRowPairingBranch {
                next_left: 0,
                used_right,
                equations: Vec::new(),
                unmatched_left: Vec::new(),
            },
            frontier_limit,
        )?;
        let mut expanded = Vec::new();

        while let Some(pairing) = pairing_frontier.pop_front() {
            self.charge()?;
            if pairing.next_left < left_arguments.len() {
                let left = left_arguments[pairing.next_left];
                for (right_index, &right) in right_arguments.iter().enumerate() {
                    if pairing.used_right[right_index] {
                        continue;
                    }
                    let mut candidate = Self::clone_row_pairing_branch(&pairing)?;
                    candidate.next_left += 1;
                    candidate.used_right[right_index] = true;
                    candidate
                        .equations
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    candidate.equations.push((left, right));
                    Self::push_row_pairing_branch(
                        &mut pairing_frontier,
                        candidate,
                        frontier_limit,
                    )?;
                }
                if right_remainder.is_some() {
                    let mut unmatched = Self::clone_row_pairing_branch(&pairing)?;
                    unmatched.next_left += 1;
                    unmatched
                        .unmatched_left
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    unmatched.unmatched_left.push(left);
                    Self::push_row_pairing_branch(
                        &mut pairing_frontier,
                        unmatched,
                        frontier_limit,
                    )?;
                }
                continue;
            }

            let mut unmatched_right = Vec::new();
            unmatched_right
                .try_reserve_exact(right_arguments.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            unmatched_right.extend(
                right_arguments
                    .iter()
                    .zip(&pairing.used_right)
                    .filter_map(|(&term, &used)| (!used).then_some(term)),
            );
            if left_remainder.is_none() && !unmatched_right.is_empty() {
                continue;
            }

            let mut equations = pairing.equations;
            match (*left_remainder, *right_remainder) {
                (None, None) => {
                    if !pairing.unmatched_left.is_empty() {
                        continue;
                    }
                },
                (Some(left_tail), None) => {
                    if !pairing.unmatched_left.is_empty() {
                        continue;
                    }
                    let right_fragment = self.collection_fragment(
                        *sort,
                        operator,
                        *collection,
                        unmatched_right,
                        None,
                        *right_pathmap_mode,
                    )?;
                    equations.push((left_tail, right_fragment));
                },
                (None, Some(right_tail)) => {
                    let left_fragment = self.collection_fragment(
                        *sort,
                        operator,
                        *collection,
                        pairing.unmatched_left,
                        None,
                        *left_pathmap_mode,
                    )?;
                    equations.push((right_tail, left_fragment));
                },
                (Some(left_tail), Some(right_tail)) => {
                    let residual = HornTermRef::Variable {
                        variable: ScopedClauseVariable {
                            activation: self.fresh_activation()?,
                            variable: TheoryVariableId(0),
                        },
                        sort: *sort,
                    };
                    let left_fragment = self.collection_fragment(
                        *sort,
                        operator,
                        *collection,
                        unmatched_right,
                        Some(residual),
                        resolved_pathmap_mode,
                    )?;
                    let right_fragment = self.collection_fragment(
                        *sort,
                        operator,
                        *collection,
                        pairing.unmatched_left,
                        Some(residual),
                        resolved_pathmap_mode,
                    )?;
                    equations.push((left_tail, left_fragment));
                    equations.push((right_tail, right_fragment));
                },
            }

            if expanded.len() == frontier_limit {
                return Err(SemanticMatchUndetermined::FrontierLimitExceeded);
            }
            expanded
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            let mut pending = clone_copy_slice(&branch.pending)?;
            Self::extend_unification_equations(&mut pending, &equations)?;
            expanded.push(HornUnificationBranch {
                pending,
                substitution: clone_copy_slice(&branch.substitution)?,
            });
        }
        Ok(expanded)
    }

    fn push_row_pairing_branch(
        frontier: &mut VecDeque<HornRowPairingBranch>,
        branch: HornRowPairingBranch,
        frontier_limit: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        if frontier.len() == frontier_limit {
            return Err(SemanticMatchUndetermined::FrontierLimitExceeded);
        }
        frontier
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        frontier.push_back(branch);
        Ok(())
    }

    fn unify_all(
        &mut self,
        equations: &[(HornTermRef, HornTermRef)],
        substitution: &HornSubstitution,
        frontier_limit: usize,
    ) -> Result<Vec<HornSubstitution>, SemanticMatchUndetermined> {
        let mut pending = Vec::new();
        Self::extend_unification_equations(&mut pending, equations)?;
        let mut frontier = VecDeque::new();
        Self::push_unification_branch(
            &mut frontier,
            HornUnificationBranch {
                pending,
                substitution: clone_copy_slice(substitution)?,
            },
            frontier_limit,
        )?;
        let mut solutions = Vec::new();

        while let Some(mut branch) = frontier.pop_front() {
            self.charge()?;
            let Some(constraint) = branch.pending.pop() else {
                branch
                    .substitution
                    .sort_unstable_by_key(|(variable, _)| *variable);
                if solutions.len() == frontier_limit {
                    return Err(SemanticMatchUndetermined::FrontierLimitExceeded);
                }
                solutions
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                solutions.push(branch.substitution);
                continue;
            };
            let (left, right) = match constraint {
                HornConstraint::Equation(left, right) => (left, right),
                HornConstraint::Collection(state) => {
                    self.expand_collection_constraint(
                        branch,
                        state,
                        &mut frontier,
                        frontier_limit,
                    )?;
                    continue;
                },
                HornConstraint::ComprehensionRow(state) => {
                    self.expand_comprehension_row_constraint(
                        branch,
                        state,
                        &mut frontier,
                        frontier_limit,
                    )?;
                    continue;
                },
                HornConstraint::FinalizeDerived(state) => {
                    self.expand_finalize_derived_constraint(
                        branch,
                        state,
                        &mut frontier,
                        frontier_limit,
                    )?;
                    continue;
                },
            };
            let left = self.view(left, &branch.substitution)?;
            let right = self.view(right, &branch.substitution)?;
            if left.sort != right.sort {
                continue;
            }
            let sort = left.sort;
            let left_term = left.term;
            let right_term = right.term;
            match (left.form, right.form) {
                (HornTermForm::Variable(left), HornTermForm::Variable(right)) if left == right => {
                    Self::push_unification_branch(&mut frontier, branch, frontier_limit)?;
                },
                (HornTermForm::Variable(variable), _) => {
                    if self.occurs(variable, right_term, &branch.substitution)? {
                        continue;
                    }
                    branch
                        .substitution
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    branch.substitution.push((variable, right_term));
                    Self::push_unification_branch(&mut frontier, branch, frontier_limit)?;
                },
                (_, HornTermForm::Variable(variable)) => {
                    if self.occurs(variable, left_term, &branch.substitution)? {
                        continue;
                    }
                    branch
                        .substitution
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    branch.substitution.push((variable, left_term));
                    Self::push_unification_branch(&mut frontier, branch, frontier_limit)?;
                },
                (HornTermForm::Comprehension { .. }, _)
                | (_, HornTermForm::Comprehension { .. }) => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
                (
                    HornTermForm::Application {
                        operator: left_operator,
                        arguments: left_arguments,
                        collection: left_collection,
                        remainder: left_remainder,
                        pathmap_mode: left_pathmap_mode,
                    },
                    HornTermForm::Application {
                        operator: right_operator,
                        arguments: right_arguments,
                        collection: right_collection,
                        remainder: right_remainder,
                        pathmap_mode: right_pathmap_mode,
                    },
                ) => {
                    if left_operator != right_operator || left_collection != right_collection {
                        continue;
                    }
                    // Map is collection-splice metasyntax, never an ordinary
                    // constructor child. Avoid re-viewing every child on the
                    // positional constructor path; an invalid direct Map is
                    // still rejected when its own equation is reached.
                    let (left_has_comprehension, right_has_comprehension) =
                        if left_collection.is_some() {
                            (
                                self.arguments_contain_comprehension(
                                    &left_arguments,
                                    &branch.substitution,
                                )?,
                                self.arguments_contain_comprehension(
                                    &right_arguments,
                                    &branch.substitution,
                                )?,
                            )
                        } else {
                            (false, false)
                        };
                    if left_has_comprehension || right_has_comprehension {
                        if left_has_comprehension == right_has_comprehension {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        let Some(collection) = left_collection else {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        };
                        let (
                            patterns,
                            target_arguments,
                            remainder,
                            pattern_pathmap_mode,
                            target_pathmap_mode,
                            target_remainder,
                        ) = if left_has_comprehension {
                            (
                                left_arguments,
                                right_arguments,
                                left_remainder,
                                left_pathmap_mode,
                                right_pathmap_mode,
                                right_remainder,
                            )
                        } else {
                            (
                                right_arguments,
                                left_arguments,
                                right_remainder,
                                right_pathmap_mode,
                                left_pathmap_mode,
                                left_remainder,
                            )
                        };
                        if target_remainder.is_some() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        let state = self.store_collection_state(HornCollectionPatternState {
                            sort,
                            operator: left_operator,
                            collection,
                            patterns,
                            target_arguments,
                            remainder,
                            pattern_pathmap_mode,
                            target_pathmap_mode,
                        })?;
                        branch
                            .pending
                            .try_reserve(1)
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        branch.pending.push(HornConstraint::Collection(state));
                        Self::push_unification_branch(&mut frontier, branch, frontier_limit)?;
                    } else {
                        match left_collection {
                            None => {
                                if left_pathmap_mode.is_some()
                                    || right_pathmap_mode.is_some()
                                    || left_remainder.is_some()
                                    || right_remainder.is_some()
                                    || left_arguments.len() != right_arguments.len()
                                {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                let equations = left_arguments
                                    .into_iter()
                                    .zip(right_arguments)
                                    .collect::<Vec<_>>();
                                Self::extend_unification_equations(
                                    &mut branch.pending,
                                    &equations,
                                )?;
                                Self::push_unification_branch(
                                    &mut frontier,
                                    branch,
                                    frontier_limit,
                                )?;
                            },
                            Some(CollectionKind::List) => {
                                if let Some(branch) = self.expand_ordered_collection(
                                    branch,
                                    HornCollectionEquation {
                                        sort,
                                        operator: left_operator,
                                        collection: CollectionKind::List,
                                        left_arguments,
                                        left_remainder,
                                        left_pathmap_mode,
                                        right_arguments,
                                        right_remainder,
                                        right_pathmap_mode,
                                    },
                                )? {
                                    Self::push_unification_branch(
                                        &mut frontier,
                                        branch,
                                        frontier_limit,
                                    )?;
                                }
                            },
                            Some(collection) => {
                                let equation = HornCollectionEquation {
                                    sort,
                                    operator: left_operator,
                                    collection,
                                    left_arguments,
                                    left_remainder,
                                    left_pathmap_mode,
                                    right_arguments,
                                    right_remainder,
                                    right_pathmap_mode,
                                };
                                for branch in self.expand_unordered_collection(
                                    &branch,
                                    &equation,
                                    frontier_limit,
                                )? {
                                    Self::push_unification_branch(
                                        &mut frontier,
                                        branch,
                                        frontier_limit,
                                    )?;
                                }
                            },
                        }
                    }
                },
            }
        }
        solutions.sort_unstable();
        solutions.dedup();
        Ok(solutions)
    }
}

fn exact_theory_operator_bytes(operator: &FramedSemanticOperator) -> Option<&[u8]> {
    let segments = operator.payload_segments();
    (operator.stable_discriminant() == THEORY_OPERATOR_DISCRIMINANT
        && segments.len() == 2
        && segments[0].as_slice() == THEORY_OPERATOR_DOMAIN)
        .then(|| segments[1].as_slice())
}

fn exact_theory_pathmap_mode(
    operator: &FramedSemanticOperator,
    expected_sort: TheorySortId,
) -> Option<PathMapModeV1> {
    let segments = operator.payload_segments();
    if operator.stable_discriminant() != THEORY_OPERATOR_DISCRIMINANT
        || segments.len() != 3
        || segments[0].as_slice() != THEORY_PATHMAP_MODE_DOMAIN
        || segments[1].as_slice() != expected_sort.0.to_le_bytes()
    {
        return None;
    }
    match segments[2].as_slice() {
        [0] => Some(PathMapModeV1::NeutralEmpty),
        [1] => Some(PathMapModeV1::Set),
        [2] => Some(PathMapModeV1::Map),
        _ => None,
    }
}

fn runtime_sort_kind(
    image: &TheorySemanticImageV1,
    sort: TheorySortId,
) -> Result<&TheorySortKindImageV1, SemanticMatchUndetermined> {
    image
        .sorts
        .get(sort.0 as usize)
        .filter(|candidate| candidate.id == sort)
        .map(|candidate| &candidate.kind)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
}

#[derive(Clone, Copy)]
struct RuntimeKeyedCollectionSorts {
    pair: TheorySortId,
    key: TheorySortId,
    value: TheorySortId,
}

fn runtime_keyed_collection_sorts(
    image: &TheorySemanticImageV1,
    sort: TheorySortId,
    expected_kind: CollectionKind,
    expected_pair: TheorySortId,
) -> Result<RuntimeKeyedCollectionSorts, SemanticMatchUndetermined> {
    let TheorySortKindImageV1::Collection { kind, key: Some(key), element } =
        runtime_sort_kind(image, sort)?
    else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    if *kind != expected_kind || *element != expected_pair {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    let TheorySortKindImageV1::Product { factors } = runtime_sort_kind(image, *element)? else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    let [pair_key, value] = factors.as_slice() else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    if pair_key != key {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    Ok(RuntimeKeyedCollectionSorts { pair: *element, key: *key, value: *value })
}

fn keys_are_nondecreasing(keys: &[ContentKey]) -> bool {
    keys.windows(2).all(|pair| pair[0] <= pair[1])
}

fn keys_are_strictly_increasing(keys: &[ContentKey]) -> bool {
    keys.windows(2).all(|pair| pair[0] < pair[1])
}

fn runtime_operator_signature(
    image: &TheorySemanticImageV1,
    operator: &TheoryImageOperatorV1,
    pathmap_mode: Option<PathMapModeV1>,
) -> Result<RuntimeOperatorSignature, SemanticMatchUndetermined> {
    if pathmap_mode.is_some()
        && !matches!(
            operator,
            TheoryImageOperatorV1::Collection { kind: CollectionKind::PathMap, .. }
        )
    {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    let (result, children) = match operator {
        TheoryImageOperatorV1::Constructor(constructor) => {
            let signature = image
                .constructors
                .get(constructor.0 as usize)
                .filter(|candidate| candidate.id == *constructor)
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
            (
                signature.codomain,
                RuntimeChildSortContract::Fixed(clone_copy_slice(&signature.domain)?),
            )
        },
        TheoryImageOperatorV1::Abstraction { sort } => {
            let TheorySortKindImageV1::Function { domain, codomain, .. } =
                runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            let mut children = Vec::new();
            children
                .try_reserve_exact(2)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            children.extend([*domain, *codomain]);
            (*sort, RuntimeChildSortContract::Fixed(children))
        },
        TheoryImageOperatorV1::Substitution { sort, function } => {
            let TheorySortKindImageV1::Function { domain, codomain, .. } =
                runtime_sort_kind(image, *function)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if codomain != sort {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let mut children = Vec::new();
            children
                .try_reserve_exact(2)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            children.extend([*function, *domain]);
            (*sort, RuntimeChildSortContract::Fixed(children))
        },
        TheoryImageOperatorV1::Collection { sort, element, kind } => {
            let TheorySortKindImageV1::Collection {
                kind: declared_kind,
                key,
                element: declared_element,
            } = runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if declared_kind != kind || declared_element != element {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let children = match kind {
                CollectionKind::List | CollectionKind::Bag | CollectionKind::Set => {
                    if pathmap_mode.is_some() || key.is_some() {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    RuntimeChildSortContract::Homogeneous(*element)
                },
                CollectionKind::Map => {
                    if pathmap_mode.is_some() {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    runtime_keyed_collection_sorts(image, *sort, *kind, *element)?;
                    RuntimeChildSortContract::Homogeneous(*element)
                },
                CollectionKind::PathMap => {
                    let sorts = runtime_keyed_collection_sorts(image, *sort, *kind, *element)?;
                    match pathmap_mode {
                        Some(PathMapModeV1::NeutralEmpty) => {
                            RuntimeChildSortContract::Fixed(Vec::new())
                        },
                        Some(PathMapModeV1::Set) => {
                            RuntimeChildSortContract::Homogeneous(sorts.key)
                        },
                        Some(PathMapModeV1::Map) => {
                            RuntimeChildSortContract::Homogeneous(sorts.pair)
                        },
                        None => RuntimeChildSortContract::RemainderOnly,
                    }
                },
            };
            (*sort, children)
        },
        TheoryImageOperatorV1::Product { sort } => {
            let TheorySortKindImageV1::Product { factors } = runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            (*sort, RuntimeChildSortContract::Fixed(clone_copy_slice(factors)?))
        },
        TheoryImageOperatorV1::Literal { sort, value } => {
            let TheorySortKindImageV1::Syntax { literal: Some(carrier) } =
                runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if !theory_literal_matches_carrier(value, carrier) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            (*sort, RuntimeChildSortContract::Fixed(Vec::new()))
        },
        TheoryImageOperatorV1::Judgment { .. } | TheoryImageOperatorV1::PathMapMode { .. } => {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        },
    };
    Ok(RuntimeOperatorSignature { result, children })
}

fn theory_literal_matches_carrier(
    literal: &mettail_grammar_core::TheoryLiteralV1,
    carrier: &TheoryLiteralCarrierV1,
) -> bool {
    matches!(
        (literal, carrier),
        (mettail_grammar_core::TheoryLiteralV1::String(_), TheoryLiteralCarrierV1::String)
            | (mettail_grammar_core::TheoryLiteralV1::Bytes(_), TheoryLiteralCarrierV1::Bytes)
            | (
                mettail_grammar_core::TheoryLiteralV1::Integer(_),
                TheoryLiteralCarrierV1::Integer
            )
            | (
                mettail_grammar_core::TheoryLiteralV1::FloatBits(_),
                TheoryLiteralCarrierV1::Float
            )
            | (
                mettail_grammar_core::TheoryLiteralV1::Boolean(_),
                TheoryLiteralCarrierV1::Boolean
            )
            | (mettail_grammar_core::TheoryLiteralV1::Unit, TheoryLiteralCarrierV1::Unit)
    )
}

fn decode_runtime_collection_kind(tag: u8) -> Result<CollectionKind, SemanticMatchUndetermined> {
    match tag {
        0 => Ok(CollectionKind::Bag),
        1 => Ok(CollectionKind::Set),
        2 => Ok(CollectionKind::List),
        3 => Ok(CollectionKind::Map),
        4 => Ok(CollectionKind::PathMap),
        _ => Err(SemanticMatchUndetermined::InvalidImageEvidence),
    }
}

fn read_u32(bytes: &[u8]) -> u32 {
    let mut value = [0; 4];
    value.copy_from_slice(&bytes[..4]);
    u32::from_le_bytes(value)
}

fn literal_payload_matches_carrier(payload: &[u8], carrier: &TheoryLiteralCarrierV1) -> bool {
    let Some((&tag, value)) = payload.split_first() else {
        return false;
    };
    let canonical = match tag {
        0 | 1 => {
            if value.len() < 8 {
                return false;
            }
            let mut length = [0; 8];
            length.copy_from_slice(&value[..8]);
            let Ok(length) = usize::try_from(u64::from_le_bytes(length)) else {
                return false;
            };
            let Some(expected) = 8usize.checked_add(length) else {
                return false;
            };
            value.len() == expected && (tag == 1 || std::str::from_utf8(&value[8..]).is_ok())
        },
        2 => value.len() == 16,
        3 => value.len() == 8,
        4 => value.len() == 1 && value[0] <= 1,
        5 => value.is_empty(),
        _ => false,
    };
    canonical
        && matches!(
            (tag, carrier),
            (0, TheoryLiteralCarrierV1::String)
                | (1, TheoryLiteralCarrierV1::Bytes)
                | (2, TheoryLiteralCarrierV1::Integer)
                | (3, TheoryLiteralCarrierV1::Float)
                | (4, TheoryLiteralCarrierV1::Boolean)
                | (5, TheoryLiteralCarrierV1::Unit)
        )
}

fn clone_copy_slice<T: Copy>(source: &[T]) -> Result<Vec<T>, SemanticMatchUndetermined> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(source.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    output.extend_from_slice(source);
    Ok(output)
}

fn clone_byte_vectors(source: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, SemanticMatchUndetermined> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(source.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for value in source {
        output.push(clone_copy_slice(value)?);
    }
    Ok(output)
}

fn clone_horn_goal(source: &HornGoal) -> Result<HornGoal, SemanticMatchUndetermined> {
    Ok(HornGoal {
        judgment: source.judgment,
        terms: clone_copy_slice(&source.terms)?,
        parent_activation: source.parent_activation,
        premise_index: source.premise_index,
    })
}

fn clone_horn_branch(source: &HornBranch) -> Result<HornBranch, SemanticMatchUndetermined> {
    let mut goals = VecDeque::new();
    goals
        .try_reserve_exact(source.goals.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for goal in &source.goals {
        goals.push_back(clone_horn_goal(goal)?);
    }
    Ok(HornBranch {
        goals,
        substitution: clone_copy_slice(&source.substitution)?,
        steps: clone_copy_slice(&source.steps)?,
    })
}

fn action_substitution_from_map(
    source: BTreeMap<TheoryVariableId, EClassId>,
) -> Result<ActionSubstitution, SemanticMatchUndetermined> {
    let mut output = Vec::new();
    output
        .try_reserve_exact(source.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    output.extend(source);
    Ok(output)
}

fn action_lookup(
    substitution: &ActionSubstitution,
    variable: TheoryVariableId,
) -> Option<EClassId> {
    substitution
        .binary_search_by_key(&variable, |(candidate, _)| *candidate)
        .ok()
        .map(|index| substitution[index].1)
}

fn action_bind_new(
    substitution: &mut ActionSubstitution,
    variable: TheoryVariableId,
    value: EClassId,
) -> Result<(), SemanticMatchUndetermined> {
    match substitution.binary_search_by_key(&variable, |(candidate, _)| *candidate) {
        Ok(_) => Err(SemanticMatchUndetermined::InvalidImageEvidence),
        Err(index) => {
            substitution
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            substitution.insert(index, (variable, value));
            Ok(())
        },
    }
}

fn action_bind_overlay(
    substitution: &mut ActionSubstitution,
    variable: TheoryVariableId,
    value: EClassId,
) -> Result<(), SemanticMatchUndetermined> {
    match substitution.binary_search_by_key(&variable, |(candidate, _)| *candidate) {
        Ok(index) => substitution[index].1 = value,
        Err(index) => {
            substitution
                .try_reserve(1)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            substitution.insert(index, (variable, value));
        },
    }
    Ok(())
}

fn clone_action_frame(source: &ActionFrame) -> Result<ActionFrame, SemanticMatchUndetermined> {
    let mut pending = VecDeque::new();
    pending
        .try_reserve_exact(source.pending.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    pending.extend(source.pending.iter().copied());
    let mut saved_forall_scopes = Vec::new();
    saved_forall_scopes
        .try_reserve_exact(source.saved_forall_scopes.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for scope in &source.saved_forall_scopes {
        saved_forall_scopes.push(clone_copy_slice(scope)?);
    }
    Ok(ActionFrame {
        rule: source.rule,
        redex: source.redex,
        substitution: clone_copy_slice(&source.substitution)?,
        pending,
        saved_forall_scopes,
        return_to_parent: source.return_to_parent,
    })
}

fn clone_action_branch(source: &ActionBranch) -> Result<ActionBranch, SemanticMatchUndetermined> {
    let mut frames = Vec::new();
    frames
        .try_reserve_exact(source.frames.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for frame in &source.frames {
        frames.push(clone_action_frame(frame)?);
    }
    Ok(ActionBranch {
        frames,
        premises: clone_copy_slice(&source.premises)?,
    })
}

fn push_action_branch(
    frontier: &mut VecDeque<ActionBranch>,
    branch: ActionBranch,
    limit: usize,
) -> Result<(), SemanticMatchUndetermined> {
    if frontier.len() == limit {
        return Err(SemanticMatchUndetermined::FrontierLimitExceeded);
    }
    frontier
        .try_reserve(1)
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    frontier.push_back(branch);
    Ok(())
}

fn push_premise_receipt(
    branch: &mut ActionBranch,
    receipt: SemanticPremiseReceipt,
    limit: usize,
) -> Result<(), SemanticMatchUndetermined> {
    if branch.premises.len() == limit {
        return Err(SemanticMatchUndetermined::ProofLimitExceeded);
    }
    branch
        .premises
        .try_reserve(1)
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    branch.premises.push(receipt);
    Ok(())
}

fn action_frame(
    rule: &mettail_grammar_core::TheoryRuleProgramV1,
    redex: EClassId,
    substitution: ActionSubstitution,
    return_to_parent: Option<ActionReturnFrame>,
) -> Result<ActionFrame, SemanticMatchUndetermined> {
    let mut pending = VecDeque::new();
    pending
        .try_reserve_exact(rule.premise_roots.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    pending.extend(
        rule.premise_roots
            .iter()
            .copied()
            .map(|premise| ActionPremiseTask::Evaluate { premise }),
    );
    Ok(ActionFrame {
        rule: rule.id,
        redex,
        substitution,
        pending,
        saved_forall_scopes: Vec::new(),
        return_to_parent,
    })
}

fn add_matcher_stats(target: &mut SetAutomatonStats, source: SetAutomatonStats) -> Result<(), ()> {
    target.root_classes = target
        .root_classes
        .checked_add(source.root_classes)
        .ok_or(())?;
    target.root_nodes = target.root_nodes.checked_add(source.root_nodes).ok_or(())?;
    target.application_roots = target
        .application_roots
        .checked_add(source.application_roots)
        .ok_or(())?;
    target.candidate_evaluations = target
        .candidate_evaluations
        .checked_add(source.candidate_evaluations)
        .ok_or(())?;
    target.state_evaluations = target
        .state_evaluations
        .checked_add(source.state_evaluations)
        .ok_or(())?;
    target.state_cache_hits = target
        .state_cache_hits
        .checked_add(source.state_cache_hits)
        .ok_or(())?;
    Ok(())
}

fn absorb_matcher_accounting(
    work: &mut u64,
    work_limit: u64,
    stats: &mut SetAutomatonStats,
    added_work: u64,
    added_stats: SetAutomatonStats,
) -> Result<(), SemanticMatchUndetermined> {
    add_matcher_stats(stats, added_stats)
        .map_err(|()| SemanticMatchUndetermined::InvalidImageEvidence)?;
    let total = work
        .checked_add(added_work)
        .filter(|total| *total <= work_limit)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
    *work = total;
    Ok(())
}

fn semantic_stop_reason(reason: SetAutomatonSearchStop) -> SemanticMatchUndetermined {
    match reason {
        SetAutomatonSearchStop::WorkBudgetExhausted => {
            SemanticMatchUndetermined::WorkBudgetExhausted
        },
        SetAutomatonSearchStop::Cancelled => SemanticMatchUndetermined::Cancelled,
        SetAutomatonSearchStop::AllocationFailed => SemanticMatchUndetermined::AllocationFailed,
    }
}

fn project_automaton_substitution<C>(
    slot_variables: &[TheoryVariableId],
    matched: &Subst,
    egraph: &EGraph<FramedSemanticOperator>,
    work: &mut u64,
    work_limit: u64,
    is_cancelled: &mut C,
) -> Result<BTreeMap<TheoryVariableId, EClassId>, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let mut substitution = BTreeMap::new();
    for variable in slot_variables {
        charge_work(work, work_limit, is_cancelled)?;
        let name = format!("v{}", variable.0);
        let value = matched
            .get(&name)
            .copied()
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if substitution.insert(*variable, egraph.find(value)).is_some() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
    }
    Ok(substitution)
}

fn charge_work<C>(
    work: &mut u64,
    limit: u64,
    is_cancelled: &mut C,
) -> Result<(), SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    if is_cancelled() {
        return Err(SemanticMatchUndetermined::Cancelled);
    }
    if *work == limit {
        return Err(SemanticMatchUndetermined::WorkBudgetExhausted);
    }
    *work += 1;
    Ok(())
}

fn absorb_reported_work(
    work: &mut u64,
    limit: u64,
    reported: u64,
) -> Result<(), SemanticMatchUndetermined> {
    *work = work
        .checked_add(reported)
        .filter(|total| *total <= limit)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
    Ok(())
}

fn freshness_holds<C>(
    egraph: &EGraph<FramedSemanticOperator>,
    needle: EClassId,
    target: EClassId,
    work: &mut u64,
    work_limit: u64,
    is_cancelled: &mut C,
) -> Result<bool, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let needle = egraph.find(needle);
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(1)
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    pending.push(egraph.find(target));
    let mut visited = BTreeSet::new();
    while let Some(term) = pending.pop() {
        charge_work(work, work_limit, is_cancelled)?;
        let term = egraph.find(term);
        if term == needle {
            return Ok(false);
        }
        if !visited.insert(term) {
            continue;
        }
        let [node] = egraph.nodes(term) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let exact = exact_theory_operator_bytes(&node.op)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if exact.first() == Some(&1) {
            if exact.len() != 5 || node.children.len() != 2 {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let binder = egraph.find(node.children[0]);
            if binder != needle {
                pending
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                pending.push(egraph.find(node.children[1]));
            }
            continue;
        }
        pending
            .try_reserve(node.children.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.extend(node.children.iter().rev().map(|child| egraph.find(*child)));
    }
    Ok(true)
}

fn concrete_collection_elements<C>(
    image: &TheorySemanticImageV1,
    egraph: &EGraph<FramedSemanticOperator>,
    collection: EClassId,
    expected_sort: TheorySortId,
    work: &mut u64,
    work_limit: u64,
    is_cancelled: &mut C,
) -> Result<(TheorySortId, Vec<EClassId>), SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    charge_work(work, work_limit, is_cancelled)?;
    let TheorySortKindImageV1::Collection { kind, key, element } =
        runtime_sort_kind(image, expected_sort)?
    else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    let collection = egraph.find(collection);
    let [node] = egraph.nodes(collection) else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    let exact = exact_theory_operator_bytes(&node.op)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
    if exact.first() != Some(&3) {
        return Err(SemanticMatchUndetermined::PremiseEvaluationUnavailable);
    }
    if exact.len() != 10
        || TheorySortId(read_u32(&exact[1..5])) != expected_sort
        || TheorySortId(read_u32(&exact[5..9])) != *element
        || decode_runtime_collection_kind(exact[9])? != *kind
    {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    let (element_sort, children) = if *kind == CollectionKind::PathMap {
        let Some((&marker, entries)) = node.children.split_first() else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let marker = egraph.find(marker);
        let [marker_node] = egraph.nodes(marker) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let mode = exact_theory_pathmap_mode(&marker_node.op, expected_sort)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        match mode {
            PathMapModeV1::NeutralEmpty if !entries.is_empty() => {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            },
            PathMapModeV1::NeutralEmpty | PathMapModeV1::Map => (*element, entries),
            PathMapModeV1::Set => {
                (key.ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?, entries)
            },
        }
    } else {
        (*element, node.children.as_slice())
    };
    let mut elements = Vec::new();
    elements
        .try_reserve_exact(children.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    elements.extend(children.iter().map(|child| egraph.find(*child)));
    Ok((element_sort, elements))
}

fn construction_lookup<C>(
    environments: &[TermConstructionEnvironment],
    mut environment: Option<usize>,
    variable: TheoryVariableId,
    context: ConstructionLookupContext<'_, '_, '_, '_, C>,
) -> Result<EClassId, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let ConstructionLookupContext {
        substitution,
        egraph,
        work,
        work_limit,
        is_cancelled,
    } = context;
    while let Some(index) = environment {
        charge_work(work, work_limit, is_cancelled)?;
        let frame = environments
            .get(index)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if let Some((_, class)) = frame.bindings.iter().find(|(name, _)| *name == variable) {
            return Ok(egraph.find(*class));
        }
        if frame.parent.is_some_and(|parent| parent >= index) {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        environment = frame.parent;
    }
    action_lookup(substitution, variable)
        .map(|class| egraph.find(class))
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
}

fn take_construction_values(
    values: &mut Vec<EClassId>,
    value_base: usize,
    expected: usize,
) -> Result<Vec<EClassId>, SemanticMatchUndetermined> {
    if value_base > values.len() || values.len() - value_base != expected {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    Ok(values.split_off(value_base))
}

fn concrete_product_factors(
    image: &TheorySemanticImageV1,
    egraph: &EGraph<FramedSemanticOperator>,
    product: EClassId,
    product_sort: TheorySortId,
) -> Result<Vec<EClassId>, SemanticMatchUndetermined> {
    let TheorySortKindImageV1::Product { factors } = runtime_sort_kind(image, product_sort)? else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    let product = egraph.find(product);
    let [node] = egraph.nodes(product) else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    if node.op != theory_operator_to_machine(&TheoryImageOperatorV1::Product { sort: product_sort })
        || node.children.len() != factors.len()
    {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    let mut values = Vec::new();
    values
        .try_reserve_exact(node.children.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    values.extend(node.children.iter().map(|child| egraph.find(*child)));
    Ok(values)
}

fn collection_construction_operator(
    image: &TheorySemanticImageV1,
    sort: TheorySortId,
) -> Result<(TheoryImageOperatorV1, Option<PathMapModeV1>), SemanticMatchUndetermined> {
    let TheorySortKindImageV1::Collection { kind, element, .. } = runtime_sort_kind(image, sort)?
    else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    Ok((
        TheoryImageOperatorV1::Collection { sort, element: *element, kind: *kind },
        (*kind == CollectionKind::PathMap).then_some(PathMapModeV1::Map),
    ))
}

fn instantiate_rule_term<C>(
    request: TermInstantiation<'_, '_, '_>,
    egraph: &mut EGraph<FramedSemanticOperator>,
    work: &mut u64,
    is_cancelled: &mut C,
) -> Result<EClassId, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let TermInstantiation { image, rule, substitution, root, limits } = request;
    let mut tasks = Vec::new();
    tasks
        .try_reserve_exact(1)
        .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
    tasks.push(TermConstructionTask::Evaluate { term: root, environment: None });
    let mut values = Vec::new();
    let mut environments = Vec::new();

    while let Some(task) = tasks.pop() {
        charge_work(work, limits.work, is_cancelled)?;
        match task {
            TermConstructionTask::Evaluate { term, environment } => {
                let node = rule
                    .terms
                    .get(term.0 as usize)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                match &node.form {
                    TheoryImageTermFormV1::Slot(variable) => {
                        let value = construction_lookup(
                            &environments,
                            environment,
                            *variable,
                            ConstructionLookupContext {
                                substitution,
                                egraph: &mut *egraph,
                                work: &mut *work,
                                work_limit: limits.work,
                                is_cancelled: &mut *is_cancelled,
                            },
                        )?;
                        values
                            .try_reserve(1)
                            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                        values.push(value);
                    },
                    TheoryImageTermFormV1::Apply {
                        operator,
                        arguments,
                        slots,
                        remainder,
                        pathmap_mode,
                    } => {
                        let signature = runtime_operator_signature(image, operator, *pathmap_mode)?;
                        if signature.result != node.sort {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        tasks
                            .try_reserve(arguments.len().saturating_add(1))
                            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                        tasks.push(TermConstructionTask::FinishApply {
                            operator: operator.clone(),
                            arguments: clone_copy_slice(arguments)?,
                            slots: clone_copy_slice(slots)?,
                            remainder: *remainder,
                            pathmap_mode: *pathmap_mode,
                            environment,
                            value_base: values.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(TermConstructionTask::Evaluate {
                                term: *argument,
                                environment,
                            });
                        }
                    },
                    TheoryImageTermFormV1::Map { sources, parameters, body } => {
                        if sources.is_empty() || parameters.is_empty() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        if !matches!(
                            runtime_sort_kind(image, node.sort)?,
                            TheorySortKindImageV1::Collection { .. }
                        ) {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        tasks
                            .try_reserve(sources.len().saturating_add(1))
                            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                        tasks.push(TermConstructionTask::FinishMapSources {
                            target_sort: node.sort,
                            sources: clone_copy_slice(sources)?,
                            parameters: clone_copy_slice(parameters)?,
                            body: *body,
                            environment,
                            value_base: values.len(),
                        });
                        for source in sources.iter().rev() {
                            tasks.push(TermConstructionTask::Evaluate {
                                term: *source,
                                environment,
                            });
                        }
                    },
                }
            },
            TermConstructionTask::FinishApply {
                operator,
                arguments,
                slots,
                remainder,
                pathmap_mode,
                environment,
                value_base,
            } => {
                let argument_values =
                    take_construction_values(&mut values, value_base, arguments.len())?;
                let capacity = slots
                    .len()
                    .checked_add(argument_values.len())
                    .and_then(|count| count.checked_add(usize::from(remainder.is_some())))
                    .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                let mut children = Vec::new();
                children
                    .try_reserve_exact(capacity)
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                for variable in &slots {
                    charge_work(work, limits.work, is_cancelled)?;
                    children.push(construction_lookup(
                        &environments,
                        environment,
                        *variable,
                        ConstructionLookupContext {
                            substitution,
                            egraph: &mut *egraph,
                            work: &mut *work,
                            work_limit: limits.work,
                            is_cancelled: &mut *is_cancelled,
                        },
                    )?);
                }
                for (argument, value) in arguments.iter().zip(argument_values) {
                    charge_work(work, limits.work, is_cancelled)?;
                    let argument_node = rule
                        .terms
                        .get(argument.0 as usize)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    let splice = matches!(operator, TheoryImageOperatorV1::Collection { .. })
                        && matches!(argument_node.form, TheoryImageTermFormV1::Map { .. });
                    if splice {
                        append_collection_remainder(egraph, &operator, value, &mut children)?;
                    } else {
                        children.push(value);
                    }
                }
                if let Some(remainder) = remainder {
                    charge_work(work, limits.work, is_cancelled)?;
                    let remainder = construction_lookup(
                        &environments,
                        environment,
                        remainder,
                        ConstructionLookupContext {
                            substitution,
                            egraph: &mut *egraph,
                            work: &mut *work,
                            work_limit: limits.work,
                            is_cancelled: &mut *is_cancelled,
                        },
                    )?;
                    append_collection_remainder(egraph, &operator, remainder, &mut children)?;
                }
                canonicalize_collection_children(
                    CollectionCanonicalization {
                        image,
                        operator: &operator,
                        pathmap_mode,
                        limits,
                    },
                    egraph,
                    &mut children,
                    work,
                    is_cancelled,
                )?;
                let value = egraph
                    .try_add_with_budget(ENode::new(
                        theory_operator_to_machine(&operator),
                        children,
                    ))
                    .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
                values
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                values.push(egraph.find(value));
            },
            TermConstructionTask::FinishMapSources {
                target_sort,
                sources,
                parameters,
                body,
                environment,
                value_base,
            } => {
                let source_values =
                    take_construction_values(&mut values, value_base, sources.len())?;
                let mut parameter_sorts = Vec::new();
                parameter_sorts
                    .try_reserve_exact(parameters.len())
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                for parameter in &parameters {
                    let declaration = rule
                        .variables
                        .get(parameter.0 as usize)
                        .filter(|candidate| candidate.id == *parameter)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    if declaration.role != mettail_grammar_core::TheoryVariableRoleV1::Binder {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    parameter_sorts.push(declaration.sort);
                }

                let mut source_rows = Vec::new();
                source_rows
                    .try_reserve_exact(sources.len())
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                for (source, value) in sources.iter().zip(source_values) {
                    let source_sort = rule
                        .terms
                        .get(source.0 as usize)
                        .map(|node| node.sort)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    if sources.len() > 1
                        && !matches!(
                            runtime_sort_kind(image, source_sort)?,
                            TheorySortKindImageV1::Collection { kind: CollectionKind::List, .. }
                        )
                    {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let (element_sort, elements) = concrete_collection_elements(
                        image,
                        egraph,
                        value,
                        source_sort,
                        work,
                        limits.work,
                        is_cancelled,
                    )?;
                    source_rows.push((element_sort, elements));
                }
                let row_count = source_rows
                    .first()
                    .map(|(_, rows)| rows.len())
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                if source_rows.iter().any(|(_, rows)| rows.len() != row_count) {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }

                let mut row_environments = Vec::new();
                row_environments
                    .try_reserve_exact(row_count)
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                for row in 0..row_count {
                    charge_work(work, limits.work, is_cancelled)?;
                    let mut bindings = Vec::new();
                    bindings
                        .try_reserve_exact(parameters.len())
                        .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                    if source_rows.len() == 1 {
                        let (element_sort, elements) = &source_rows[0];
                        match runtime_sort_kind(image, *element_sort)? {
                            TheorySortKindImageV1::Product { factors } => {
                                if factors.as_slice() != parameter_sorts.as_slice() {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                let factors = concrete_product_factors(
                                    image,
                                    egraph,
                                    elements[row],
                                    *element_sort,
                                )?;
                                bindings.extend(parameters.iter().copied().zip(factors));
                            },
                            _ => {
                                if parameters.len() != 1
                                    || parameter_sorts.first() != Some(element_sort)
                                {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                bindings.push((parameters[0], elements[row]));
                            },
                        }
                    } else {
                        if source_rows.len() != parameters.len() {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        for (index, (element_sort, elements)) in source_rows.iter().enumerate() {
                            if parameter_sorts[index] != *element_sort {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            bindings.push((parameters[index], elements[row]));
                        }
                    }
                    environments
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                    let index = environments.len();
                    environments
                        .push(TermConstructionEnvironment { parent: environment, bindings });
                    row_environments.push(index);
                }

                tasks
                    .try_reserve(row_count.saturating_add(1))
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                tasks.push(TermConstructionTask::FinishMapBodies {
                    target_sort,
                    row_count,
                    value_base: values.len(),
                });
                for environment in row_environments.into_iter().rev() {
                    tasks.push(TermConstructionTask::Evaluate {
                        term: body,
                        environment: Some(environment),
                    });
                }
            },
            TermConstructionTask::FinishMapBodies { target_sort, row_count, value_base } => {
                let mut children = take_construction_values(&mut values, value_base, row_count)?;
                let (operator, pathmap_mode) =
                    collection_construction_operator(image, target_sort)?;
                canonicalize_collection_children(
                    CollectionCanonicalization {
                        image,
                        operator: &operator,
                        pathmap_mode,
                        limits,
                    },
                    egraph,
                    &mut children,
                    work,
                    is_cancelled,
                )?;
                let value = egraph
                    .try_add_with_budget(ENode::new(
                        theory_operator_to_machine(&operator),
                        children,
                    ))
                    .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
                values
                    .try_reserve(1)
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                values.push(egraph.find(value));
            },
        }
    }
    match values.as_slice() {
        [value] => Ok(*value),
        _ => Err(SemanticMatchUndetermined::InvalidImageEvidence),
    }
}

fn append_collection_remainder(
    egraph: &EGraph<FramedSemanticOperator>,
    operator: &TheoryImageOperatorV1,
    remainder: EClassId,
    children: &mut Vec<EClassId>,
) -> Result<(), SemanticMatchUndetermined> {
    let machine_operator = theory_operator_to_machine(operator);
    let nodes = egraph.nodes(remainder);
    let [node] = nodes else {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    };
    if node.op != machine_operator {
        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
    }
    children
        .try_reserve(node.children.len())
        .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
    children.extend(node.children.iter().map(|child| egraph.find(*child)));
    Ok(())
}

fn canonicalize_collection_children<C>(
    request: CollectionCanonicalization<'_, '_>,
    egraph: &mut EGraph<FramedSemanticOperator>,
    children: &mut Vec<EClassId>,
    work: &mut u64,
    is_cancelled: &mut C,
) -> Result<(), SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let CollectionCanonicalization { image, operator, pathmap_mode, limits } = request;
    let TheoryImageOperatorV1::Collection { sort, element, kind } = operator else {
        if pathmap_mode.is_some() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        return Ok(());
    };
    match kind {
        CollectionKind::List => {
            if pathmap_mode.is_some() {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let TheorySortKindImageV1::Collection { key: None, .. } =
                runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
        },
        CollectionKind::Bag | CollectionKind::Set => {
            if pathmap_mode.is_some() {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let TheorySortKindImageV1::Collection { key: None, .. } =
                runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            let mut construction = CollectionConstructionContext {
                image,
                egraph,
                work,
                limits,
                is_cancelled,
            };
            let mut keyed = construction.exact_value_keys(children)?;
            keyed.sort_unstable();
            if *kind == CollectionKind::Set {
                keyed.dedup_by(|left, right| left.0 == right.0);
            }
            children.clear();
            children.extend(keyed.into_iter().map(|(_, child)| child));
        },
        CollectionKind::Map => {
            if pathmap_mode.is_some() {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let sorts = runtime_keyed_collection_sorts(image, *sort, *kind, *element)?;
            let mut construction = CollectionConstructionContext {
                image,
                egraph,
                work,
                limits,
                is_cancelled,
            };
            let mut keyed = construction.exact_pair_keys(children, sorts)?;
            keyed.sort_unstable();
            construction.reject_duplicate_construction_keys(&keyed)?;
            children.clear();
            children.extend(keyed.into_iter().map(|(_, child)| child));
        },
        CollectionKind::PathMap => {
            let sorts = runtime_keyed_collection_sorts(image, *sort, *kind, *element)?;
            let mut construction = CollectionConstructionContext {
                image,
                egraph,
                work,
                limits,
                is_cancelled,
            };
            construction.canonicalize_pathmap_children(children, *sort, sorts, pathmap_mode)?;
        },
    }
    Ok(())
}

struct CollectionConstructionContext<'image, 'graph, 'work, 'cancel, C> {
    image: &'image TheorySemanticImageV1,
    egraph: &'graph mut EGraph<FramedSemanticOperator>,
    work: &'work mut u64,
    limits: TermConstructionLimits,
    is_cancelled: &'cancel mut C,
}

enum HornMaterializationTask {
    Visit(HornTermRef),
    Finish { synthetic: usize, value_base: usize },
}

fn materialize_horn_substitution<C>(
    egraph: &mut EGraph<FramedSemanticOperator>,
    synthetic_terms: &[HornSyntheticTerm],
    projected: &[(TheoryVariableId, HornTermRef)],
    work: &mut u64,
    limits: TermConstructionLimits,
    is_cancelled: &mut C,
) -> Result<ActionSubstitution, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let initial_nodes = egraph.node_count();
    let mut published_bytes = 0usize;
    let mut memo = Vec::new();
    memo.try_reserve_exact(synthetic_terms.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    memo.resize(synthetic_terms.len(), None);
    let mut visiting = Vec::new();
    visiting
        .try_reserve_exact(synthetic_terms.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    visiting.resize(synthetic_terms.len(), false);
    let mut output = Vec::new();
    output
        .try_reserve_exact(projected.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;

    for (variable, root) in projected {
        let mut tasks = Vec::new();
        tasks
            .try_reserve_exact(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        tasks.push(HornMaterializationTask::Visit(*root));
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            charge_work(work, limits.work, is_cancelled)?;
            match task {
                HornMaterializationTask::Visit(HornTermRef::Ground { class, .. }) => {
                    values
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    values.push(egraph.find(class));
                },
                HornMaterializationTask::Visit(HornTermRef::Synthetic { term, .. }) => {
                    if let Some(value) = memo.get(term).copied().flatten() {
                        values
                            .try_reserve(1)
                            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                        values.push(egraph.find(value));
                        continue;
                    }
                    let state = synthetic_terms
                        .get(term)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    let marker = visiting
                        .get_mut(term)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    if std::mem::replace(marker, true) {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let child_count = state
                        .arguments
                        .len()
                        .checked_add(usize::from(state.remainder.is_some()))
                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                    tasks
                        .try_reserve(child_count.saturating_add(1))
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    tasks.push(HornMaterializationTask::Finish {
                        synthetic: term,
                        value_base: values.len(),
                    });
                    if let Some(remainder) = state.remainder {
                        tasks.push(HornMaterializationTask::Visit(remainder));
                    }
                    for argument in state.arguments.iter().rev() {
                        tasks.push(HornMaterializationTask::Visit(*argument));
                    }
                },
                HornMaterializationTask::Visit(
                    HornTermRef::Variable { .. } | HornTermRef::Clause { .. },
                ) => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
                HornMaterializationTask::Finish { synthetic, value_base } => {
                    let state = synthetic_terms
                        .get(synthetic)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    let expected = state
                        .arguments
                        .len()
                        .checked_add(usize::from(state.remainder.is_some()))
                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                    if value_base > values.len() || values.len() - value_base != expected {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    let mut children = values.split_off(value_base);
                    let remainder = state
                        .remainder
                        .map(|_| {
                            children
                                .pop()
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
                        })
                        .transpose()?;
                    if children.len() != state.arguments.len() {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    match state.collection {
                        None => {
                            if remainder.is_some() || state.pathmap_mode.is_some() {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                        },
                        Some(CollectionKind::PathMap) => {
                            let mut mode = state.pathmap_mode;
                            if let Some(remainder) = remainder {
                                let [node] = egraph.nodes(remainder) else {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                };
                                if node.op != state.operator {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                let Some((&marker, entries)) = node.children.split_first() else {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                };
                                let [marker_node] = egraph.nodes(marker) else {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                };
                                let actual = exact_theory_pathmap_mode(&marker_node.op, state.sort)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                if mode.is_some_and(|expected| expected != actual) {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                mode = Some(actual);
                                children
                                    .try_reserve(entries.len())
                                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                                children.extend(entries.iter().map(|child| egraph.find(*child)));
                            }
                            let mode =
                                mode.ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            let marker_node = ENode::new(
                                theory_pathmap_mode_to_machine(state.sort, mode),
                                Vec::new(),
                            );
                            published_bytes = published_bytes
                                .checked_add(
                                    publication_node_bytes(&marker_node)
                                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?,
                                )
                                .filter(|bytes| *bytes <= limits.bytes)
                                .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                            let marker = egraph
                                .try_add_with_budget(marker_node)
                                .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
                            children
                                .try_reserve(1)
                                .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                            children.insert(0, egraph.find(marker));
                        },
                        Some(_) => {
                            if state.pathmap_mode.is_some() {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            if let Some(remainder) = remainder {
                                let [node] = egraph.nodes(remainder) else {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                };
                                if node.op != state.operator {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                children
                                    .try_reserve(node.children.len())
                                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                                children
                                    .extend(node.children.iter().map(|child| egraph.find(*child)));
                            }
                        },
                    }
                    let node = ENode::new(state.operator.clone(), children);
                    published_bytes = published_bytes
                        .checked_add(
                            publication_node_bytes(&node)
                                .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?,
                        )
                        .filter(|bytes| *bytes <= limits.bytes)
                        .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                    let value = egraph
                        .try_add_with_budget(node)
                        .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?;
                    if egraph.node_count().saturating_sub(initial_nodes) > limits.nodes {
                        return Err(SemanticMatchUndetermined::EGraphNodeBudgetExhausted);
                    }
                    memo[synthetic] = Some(egraph.find(value));
                    visiting[synthetic] = false;
                    values
                        .try_reserve(1)
                        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                    values.push(egraph.find(value));
                },
            }
        }
        let [value] = values.as_slice() else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        output.push((*variable, *value));
    }
    output.sort_unstable_by_key(|(variable, _)| *variable);
    output.dedup_by_key(|(variable, _)| *variable);
    Ok(output)
}

impl<C> CollectionConstructionContext<'_, '_, '_, '_, C>
where
    C: FnMut() -> bool,
{
    fn exact_value_keys(
        &mut self,
        children: &[EClassId],
    ) -> Result<Vec<(ContentKey, EClassId)>, SemanticMatchUndetermined> {
        let mut keyed = Vec::new();
        keyed
            .try_reserve_exact(children.len())
            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
        for child in children.iter().copied() {
            let child = self.egraph.find(child);
            let key = exact_ground_key(
                self.egraph,
                child,
                self.work,
                GroundKeyLimits {
                    work: self.limits.work,
                    nodes: self.limits.nodes,
                    bytes: self.limits.bytes,
                    limit_reason: SemanticMatchUndetermined::OutputLimitExceeded,
                },
                self.is_cancelled,
            )?;
            keyed.push((key, child));
        }
        Ok(keyed)
    }

    fn exact_pair_keys(
        &mut self,
        children: &[EClassId],
        sorts: RuntimeKeyedCollectionSorts,
    ) -> Result<Vec<(ContentKey, EClassId)>, SemanticMatchUndetermined> {
        let mut keyed = Vec::new();
        keyed
            .try_reserve_exact(children.len())
            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
        for child in children.iter().copied() {
            charge_work(self.work, self.limits.work, self.is_cancelled)?;
            let child = self.egraph.find(child);
            let [node] = self.egraph.nodes(child) else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            let exact = exact_theory_operator_bytes(&node.op)
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
            if exact.len() != 5
                || exact[0] != 4
                || TheorySortId(read_u32(&exact[1..])) != sorts.pair
                || node.children.len() != 2
                || self.ground_root_sort(node.children[0])? != sorts.key
                || self.ground_root_sort(node.children[1])? != sorts.value
            {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let key = exact_ground_key(
                self.egraph,
                node.children[0],
                self.work,
                GroundKeyLimits {
                    work: self.limits.work,
                    nodes: self.limits.nodes,
                    bytes: self.limits.bytes,
                    limit_reason: SemanticMatchUndetermined::OutputLimitExceeded,
                },
                self.is_cancelled,
            )?;
            keyed.push((key, child));
        }
        Ok(keyed)
    }

    fn reject_duplicate_construction_keys(
        &self,
        keyed: &[(ContentKey, EClassId)],
    ) -> Result<(), SemanticMatchUndetermined> {
        if keyed.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            Err(SemanticMatchUndetermined::InvalidImageEvidence)
        } else {
            Ok(())
        }
    }

    fn ground_root_sort(&self, root: EClassId) -> Result<TheorySortId, SemanticMatchUndetermined> {
        let root = self.egraph.find(root);
        let [node] = self.egraph.nodes(root) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let exact = exact_theory_operator_bytes(&node.op)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let (&tag, payload) = exact
            .split_first()
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        let sort = match tag {
            0 if payload.len() == 4 => {
                let constructor = mettail_grammar_core::TheoryConstructorId(read_u32(payload));
                self.image
                    .constructors
                    .get(constructor.0 as usize)
                    .filter(|candidate| candidate.id == constructor)
                    .map(|constructor| constructor.codomain)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?
            },
            1 if payload.len() == 4 => TheorySortId(read_u32(payload)),
            2 if payload.len() == 8 => TheorySortId(read_u32(&payload[..4])),
            3 if payload.len() == 9 => TheorySortId(read_u32(&payload[..4])),
            4 if payload.len() == 4 => TheorySortId(read_u32(payload)),
            5 if payload.len() >= 5 => TheorySortId(read_u32(&payload[..4])),
            _ => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
        };
        runtime_sort_kind(self.image, sort)?;
        Ok(sort)
    }

    fn canonicalize_pathmap_children(
        &mut self,
        children: &mut Vec<EClassId>,
        sort: TheorySortId,
        sorts: RuntimeKeyedCollectionSorts,
        declared_mode: Option<PathMapModeV1>,
    ) -> Result<(), SemanticMatchUndetermined> {
        let mut marker = None;
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(children.len())
            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
        for child in children.iter().copied() {
            charge_work(self.work, self.limits.work, self.is_cancelled)?;
            let child = self.egraph.find(child);
            let [node] = self.egraph.nodes(child) else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if node.children.is_empty() {
                if let Some(mode) = exact_theory_pathmap_mode(&node.op, sort) {
                    if marker.replace((mode, child)).is_some() {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                    continue;
                }
            }
            entries.push(child);
        }

        let mode = match (declared_mode, marker.map(|(mode, _)| mode)) {
            (Some(expected), Some(actual)) if expected == actual => expected,
            (Some(_), Some(_)) => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
            (Some(mode), None) | (None, Some(mode)) => mode,
            (None, None) => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
        };
        if marker.is_none() {
            children
                .try_reserve_exact(1)
                .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
        }

        let mut keyed = match mode {
            PathMapModeV1::NeutralEmpty if entries.is_empty() => Vec::new(),
            PathMapModeV1::NeutralEmpty => {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            },
            PathMapModeV1::Set => {
                for entry in &entries {
                    if self.ground_root_sort(*entry)? != sorts.key {
                        return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                    }
                }
                self.exact_value_keys(&entries)?
            },
            PathMapModeV1::Map => self.exact_pair_keys(&entries, sorts)?,
        };
        keyed.sort_unstable();
        self.reject_duplicate_construction_keys(&keyed)?;

        let marker = match marker {
            Some((existing_mode, marker)) if existing_mode == mode => marker,
            Some(_) => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
            None => self
                .egraph
                .try_add_with_budget(ENode::new(
                    theory_pathmap_mode_to_machine(sort, mode),
                    Vec::new(),
                ))
                .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?,
        };
        children.clear();
        children.push(self.egraph.find(marker));
        children.extend(keyed.into_iter().map(|(_, entry)| entry));
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum ProjectionState {
    Visiting,
    Published(EClassId),
}

type EClassRemap = HashMap<EClassId, ProjectionState>;

/// Copy exactly the source classes reachable from the successful output and
/// substitution roots into a fresh bounded graph.  The source graph stays
/// private until the complete projection and identifier remap succeed.
fn project_reachable_egraph<C>(
    source: &EGraph<FramedSemanticOperator>,
    roots: &[EClassId],
    work: &mut u64,
    limits: ProjectionLimits,
    is_cancelled: &mut C,
) -> Result<(EGraph<FramedSemanticOperator>, EClassRemap), SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let ProjectionLimits {
        work: work_limit,
        nodes: node_limit,
        bytes: byte_limit,
        limit_reason,
    } = limits;
    let mut remap = HashMap::default();
    let mut stack = Vec::new();
    stack
        .try_reserve_exact(roots.len())
        .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
    for root in roots.iter().rev() {
        stack.push((source.find(*root), false));
    }

    let mut projected = EGraph::with_config(EGraphConfig { max_nodes: node_limit });
    let mut published_bytes = 0usize;
    while let Some((class, expanded)) = stack.pop() {
        charge_work(work, work_limit, is_cancelled)?;
        let class = source.find(class);
        if expanded {
            if !matches!(remap.get(&class), Some(ProjectionState::Visiting)) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let [node] = source.nodes(class) else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            let mut children = Vec::new();
            children
                .try_reserve_exact(node.children.len())
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            for child in &node.children {
                let child = source.find(*child);
                children.push(remapped_eclass(&remap, child)?);
            }
            published_bytes = published_bytes
                .checked_add(publication_node_bytes(node).ok_or(limit_reason)?)
                .filter(|bytes| *bytes <= byte_limit)
                .ok_or(limit_reason)?;
            let target = projected
                .try_add_with_budget(ENode::new(node.op.clone(), children))
                .ok_or(limit_reason)?;
            remap.insert(class, ProjectionState::Published(projected.find(target)));
            continue;
        }
        match remap.get(&class) {
            Some(ProjectionState::Published(_)) => continue,
            Some(ProjectionState::Visiting) => {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            },
            None => {},
        }
        if remap.len() >= node_limit {
            return Err(limit_reason);
        }
        remap
            .try_reserve(1)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        remap.insert(class, ProjectionState::Visiting);
        let [node] = source.nodes(class) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        let additional = node.children.len().checked_add(1).ok_or(limit_reason)?;
        stack
            .try_reserve(additional)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        stack.push((class, true));
        for child in node.children.iter().rev() {
            let child = source.find(*child);
            match remap.get(&child) {
                Some(ProjectionState::Visiting) => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
                Some(ProjectionState::Published(_)) => {},
                None => stack.push((child, false)),
            }
        }
    }
    for root in roots {
        remapped_eclass(&remap, source.find(*root))?;
    }
    Ok((projected, remap))
}

fn remapped_eclass(
    remap: &HashMap<EClassId, ProjectionState>,
    class: EClassId,
) -> Result<EClassId, SemanticMatchUndetermined> {
    match remap.get(&class) {
        Some(ProjectionState::Published(target)) => Ok(*target),
        Some(ProjectionState::Visiting) | None => {
            Err(SemanticMatchUndetermined::InvalidImageEvidence)
        },
    }
}

fn publication_node_bytes(node: &ENode<FramedSemanticOperator>) -> Option<usize> {
    let mut bytes = 8usize.checked_add(std::mem::size_of::<u32>())?;
    for segment in node.op.payload_segments() {
        bytes = bytes
            .checked_add(8)
            .and_then(|total| total.checked_add(segment.len()))?;
    }
    let child_bytes = node
        .children
        .len()
        .checked_mul(8 + std::mem::size_of::<u32>())?;
    bytes.checked_add(child_bytes)
}

/// Compute a recursive exact key for a canonical, acyclic ground e-graph.
/// Each reachable e-class must contain exactly one e-node. Equality saturation
/// produces multi-node classes and therefore cannot masquerade as an input
/// term; callers must first select and re-project one canonical representative.
fn exact_ground_key<C>(
    egraph: &EGraph<FramedSemanticOperator>,
    root: EClassId,
    work: &mut u64,
    limits: GroundKeyLimits,
    is_cancelled: &mut C,
) -> Result<ContentKey, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let root = egraph.find(root);
    let mut keys = BTreeMap::new();
    let mut visiting = BTreeSet::new();
    let mut stack = vec![(root, false)];
    while let Some((class, expanded)) = stack.pop() {
        charge_work(work, limits.work, is_cancelled)?;
        let class = egraph.find(class);
        if keys.contains_key(&class) {
            continue;
        }
        let nodes = egraph.nodes(class);
        let [node] = nodes else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        if expanded {
            let mut children = Vec::new();
            children
                .try_reserve_exact(node.children.len())
                .map_err(|_| limits.limit_reason)?;
            for child in &node.children {
                children.push(
                    keys.get(&egraph.find(*child))
                        .cloned()
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
                );
            }
            let key = ContentKey::tree(&node.op, children);
            if key.len() > limits.bytes {
                return Err(limits.limit_reason);
            }
            visiting.remove(&class);
            keys.insert(class, key);
            if keys.len() > limits.nodes {
                return Err(limits.limit_reason);
            }
            continue;
        }
        if !visiting.insert(class) {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        stack.push((class, true));
        for child in node.children.iter().rev() {
            let child = egraph.find(*child);
            if visiting.contains(&child) {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            if !keys.contains_key(&child) {
                stack.push((child, false));
            }
        }
    }
    keys.remove(&root)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        TheoryConstructorId, TheoryConstructorImageV1, TheoryJudgmentPatternAutomatonV1,
        TheoryLiteralV1, TheoryPatternAutomatonV1, TheorySortImageV1,
        THEORY_IMAGE_COMPILER_ABI_CURRENT, THEORY_SEMANTIC_IMAGE_ABI_CURRENT,
    };

    fn sort(id: u32, kind: TheorySortKindImageV1) -> TheorySortImageV1 {
        TheorySortImageV1 { id: TheorySortId(id), kind }
    }

    fn signature_image() -> TheorySemanticImageV1 {
        TheorySemanticImageV1 {
            abi: THEORY_SEMANTIC_IMAGE_ABI_CURRENT,
            compiler_abi: THEORY_IMAGE_COMPILER_ABI_CURRENT,
            language_fingerprint: [0; 32],
            grammar_fingerprint: [0; 32],
            theory_fingerprint: [0; 32],
            resource_profile: TheoryResourceProfileV1::Uncosted,
            sorts: vec![
                sort(
                    0,
                    TheorySortKindImageV1::Syntax {
                        literal: Some(TheoryLiteralCarrierV1::String),
                    },
                ),
                sort(
                    1,
                    TheorySortKindImageV1::Syntax {
                        literal: Some(TheoryLiteralCarrierV1::Integer),
                    },
                ),
                sort(2, TheorySortKindImageV1::Syntax { literal: None }),
                sort(
                    3,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::List,
                        key: None,
                        element: TheorySortId(2),
                    },
                ),
                sort(
                    4,
                    TheorySortKindImageV1::Product {
                        factors: vec![TheorySortId(2), TheorySortId(1)],
                    },
                ),
                sort(
                    5,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::List,
                        key: None,
                        element: TheorySortId(4),
                    },
                ),
                sort(
                    6,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::List,
                        key: None,
                        element: TheorySortId(1),
                    },
                ),
                sort(
                    7,
                    TheorySortKindImageV1::Function {
                        domain: TheorySortId(2),
                        codomain: TheorySortId(2),
                        multiple: false,
                    },
                ),
                sort(
                    8,
                    TheorySortKindImageV1::Function {
                        domain: TheorySortId(1),
                        codomain: TheorySortId(2),
                        multiple: false,
                    },
                ),
                sort(
                    9,
                    TheorySortKindImageV1::Function {
                        domain: TheorySortId(2),
                        codomain: TheorySortId(2),
                        multiple: true,
                    },
                ),
                sort(10, TheorySortKindImageV1::Opaque { abi: "test/opaque/1".into() }),
                sort(
                    11,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::Bag,
                        key: None,
                        element: TheorySortId(2),
                    },
                ),
                sort(
                    12,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::Map,
                        key: Some(TheorySortId(2)),
                        element: TheorySortId(4),
                    },
                ),
                sort(
                    13,
                    TheorySortKindImageV1::Collection {
                        kind: CollectionKind::PathMap,
                        key: Some(TheorySortId(2)),
                        element: TheorySortId(4),
                    },
                ),
            ],
            constructors: vec![
                TheoryConstructorImageV1 {
                    id: TheoryConstructorId(0),
                    domain: Vec::new(),
                    codomain: TheorySortId(2),
                    grammar: None,
                },
                TheoryConstructorImageV1 {
                    id: TheoryConstructorId(1),
                    domain: Vec::new(),
                    codomain: TheorySortId(2),
                    grammar: None,
                },
                TheoryConstructorImageV1 {
                    id: TheoryConstructorId(2),
                    domain: vec![TheorySortId(2)],
                    codomain: TheorySortId(2),
                    grammar: None,
                },
            ],
            rules: Vec::new(),
            patterns: TheoryPatternAutomatonV1 { states: Vec::new(), entries: Vec::new() },
            judgments: Vec::new(),
            judgment_rules: Vec::new(),
            judgment_patterns: TheoryJudgmentPatternAutomatonV1 {
                states: Vec::new(),
                entries: Vec::new(),
            },
            actions: Vec::new(),
        }
    }

    fn comprehension_image() -> TheorySemanticImageV1 {
        let mut image = signature_image();
        image.constructors.push(TheoryConstructorImageV1 {
            id: TheoryConstructorId(3),
            domain: vec![TheorySortId(3)],
            codomain: TheorySortId(2),
            grammar: None,
        });
        image.constructors.push(TheoryConstructorImageV1 {
            id: TheoryConstructorId(4),
            domain: vec![TheorySortId(2), TheorySortId(2)],
            codomain: TheorySortId(2),
            grammar: None,
        });
        let variables = vec![
            mettail_grammar_core::TheoryImageVariableV1 {
                id: TheoryVariableId(0),
                sort: TheorySortId(3),
                role: mettail_grammar_core::TheoryVariableRoleV1::Input,
            },
            mettail_grammar_core::TheoryImageVariableV1 {
                id: TheoryVariableId(1),
                sort: TheorySortId(3),
                role: mettail_grammar_core::TheoryVariableRoleV1::Derived,
            },
            mettail_grammar_core::TheoryImageVariableV1 {
                id: TheoryVariableId(2),
                sort: TheorySortId(2),
                role: mettail_grammar_core::TheoryVariableRoleV1::Binder,
            },
            mettail_grammar_core::TheoryImageVariableV1 {
                id: TheoryVariableId(3),
                sort: TheorySortId(2),
                role: mettail_grammar_core::TheoryVariableRoleV1::Binder,
            },
            mettail_grammar_core::TheoryImageVariableV1 {
                id: TheoryVariableId(4),
                sort: TheorySortId(11),
                role: mettail_grammar_core::TheoryVariableRoleV1::Remainder,
            },
        ];
        let slot = |sort, variable| mettail_grammar_core::TheoryImageTermNodeV1 {
            sort: TheorySortId(sort),
            form: TheoryImageTermFormV1::Slot(TheoryVariableId(variable)),
        };
        let apply =
            |sort, operator, arguments, remainder| mettail_grammar_core::TheoryImageTermNodeV1 {
                sort: TheorySortId(sort),
                form: TheoryImageTermFormV1::Apply {
                    operator,
                    arguments,
                    slots: Vec::new(),
                    remainder,
                    pathmap_mode: None,
                },
            };
        let bag = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(11),
            element: TheorySortId(2),
            kind: CollectionKind::Bag,
        };
        let terms = vec![
            slot(3, 0),
            apply(
                2,
                TheoryImageOperatorV1::Constructor(TheoryConstructorId(3)),
                vec![mettail_grammar_core::TheoryTermId(0)],
                None,
            ),
            slot(3, 1),
            slot(2, 2),
            slot(2, 3),
            apply(
                2,
                TheoryImageOperatorV1::Constructor(TheoryConstructorId(4)),
                vec![mettail_grammar_core::TheoryTermId(3), mettail_grammar_core::TheoryTermId(4)],
                None,
            ),
            mettail_grammar_core::TheoryImageTermNodeV1 {
                sort: TheorySortId(11),
                form: TheoryImageTermFormV1::Map {
                    sources: vec![
                        mettail_grammar_core::TheoryTermId(0),
                        mettail_grammar_core::TheoryTermId(2),
                    ],
                    parameters: vec![TheoryVariableId(2), TheoryVariableId(3)],
                    body: mettail_grammar_core::TheoryTermId(5),
                },
            },
            apply(
                11,
                bag.clone(),
                vec![mettail_grammar_core::TheoryTermId(1), mettail_grammar_core::TheoryTermId(6)],
                Some(TheoryVariableId(4)),
            ),
            apply(
                2,
                TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
                vec![mettail_grammar_core::TheoryTermId(4)],
                None,
            ),
            mettail_grammar_core::TheoryImageTermNodeV1 {
                sort: TheorySortId(11),
                form: TheoryImageTermFormV1::Map {
                    sources: vec![mettail_grammar_core::TheoryTermId(2)],
                    parameters: vec![TheoryVariableId(3)],
                    body: mettail_grammar_core::TheoryTermId(8),
                },
            },
            apply(11, bag, vec![mettail_grammar_core::TheoryTermId(9)], Some(TheoryVariableId(4))),
        ];
        image.rules.push(TheoryRuleProgramV1 {
            id: TheoryRuleProgramId(0),
            origin: TheoryRuleOriginV1::Rewrite { source: 0 },
            disposition: TheoryRuleDispositionV1::Executable,
            name: "correlated-map".into(),
            variables,
            terms,
            premises: Vec::new(),
            premise_roots: Vec::new(),
            left: mettail_grammar_core::TheoryTermId(7),
            right: mettail_grammar_core::TheoryTermId(10),
            charge: mettail_grammar_core::TheoryWorkChargeV1 {
                pattern_nodes: 11,
                template_nodes: 11,
                premise_nodes: 0,
                variable_slots: 5,
            },
        });
        image
            .actions
            .push(mettail_grammar_core::TheoryActionImageV1 {
                id: TheoryActionId(0),
                domain: vec![TheorySortId(11)],
                codomain: TheorySortId(11),
                transitions: vec![TheoryRuleProgramId(0)],
                effect: TheoryEffectId(0),
                effect_class: SemanticEffectClassV1::Pure,
                required_rights: LanguageRights::from_rights([LanguageRight::Reduce]),
                grade: TheorySortId(2),
            });
        image
    }

    fn add_canonical_bag(
        image: &TheorySemanticImageV1,
        egraph: &mut EGraph<FramedSemanticOperator>,
        mut children: Vec<EClassId>,
    ) -> EClassId {
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(11),
            element: TheorySortId(2),
            kind: CollectionKind::Bag,
        };
        let mut work = 0;
        canonicalize_collection_children(
            CollectionCanonicalization {
                image,
                operator: &operator,
                pathmap_mode: None,
                limits: TermConstructionLimits {
                    work: 100_000,
                    nodes: 1_000,
                    bytes: 1 << 20,
                },
            },
            egraph,
            &mut children,
            &mut work,
            &mut || false,
        )
        .expect("canonical test bag");
        add(egraph, operator, children)
    }

    fn add(
        egraph: &mut EGraph<FramedSemanticOperator>,
        operator: TheoryImageOperatorV1,
        children: Vec<EClassId>,
    ) -> EClassId {
        egraph.add(ENode::new(theory_operator_to_machine(&operator), children))
    }

    fn add_pathmap(
        egraph: &mut EGraph<FramedSemanticOperator>,
        operator: &TheoryImageOperatorV1,
        mode: PathMapModeV1,
        entries: Vec<EClassId>,
    ) -> EClassId {
        let marker = add(
            egraph,
            TheoryImageOperatorV1::PathMapMode { sort: TheorySortId(13), mode },
            Vec::new(),
        );
        let mut children = vec![marker];
        children.extend(entries);
        add(egraph, operator.clone(), children)
    }

    fn semantic_limits() -> SemanticTransitionLimits {
        SemanticTransitionLimits {
            work: 100_000,
            outputs: 8,
            frontier: 64,
            proofs: 16,
            proof_nodes: 1_000,
            term_nodes: 1_000,
            term_bytes: 64 * 1024,
            output_nodes: 1_000,
            output_bytes: 64 * 1024,
        }
    }

    fn comprehension_input(
        image: &TheorySemanticImageV1,
        complete: bool,
    ) -> SemanticTransitionInput {
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let wrapped_zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![zero],
        );
        let wrapped_one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![one],
        );
        let drivers = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![zero, one],
        );
        let driver = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(3)),
            vec![drivers],
        );
        let first_pair = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(4)),
            vec![zero, wrapped_zero],
        );
        let second_pair = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(4)),
            vec![one, wrapped_one],
        );
        let mut elements = vec![one, driver, first_pair];
        if complete {
            elements.push(second_pair);
        }
        let root = add_canonical_bag(image, &mut egraph, elements);
        match SemanticTransitionInput::admit(
            egraph,
            root,
            SemanticInputLimits {
                work: 10_000,
                nodes: 1_000,
                bytes: 64 * 1024,
            },
            || false,
        ) {
            SemanticInputDecision::Proven(input) => input,
            _ => panic!("admit comprehension input"),
        }
    }

    fn validate(
        image: &TheorySemanticImageV1,
        egraph: &EGraph<FramedSemanticOperator>,
        root: EClassId,
        sort: TheorySortId,
        work_limit: u64,
    ) -> Result<(), SemanticMatchUndetermined> {
        HornEvaluator {
            image,
            egraph,
            work: 0,
            work_limit,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 0,
        }
        .validate_ground_term(root, sort)
    }

    #[test]
    fn correlated_exact_zip_captures_and_rhs_map_splices() {
        let image = comprehension_image();
        let matcher = SemanticTransitionMatcher::restore(&image)
            .expect("restore generalized comprehension rule");
        let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
        let decision = matcher.execute_action(
            SemanticActionExecutionRequest {
                image: &image,
                action: TheoryActionId(0),
                granted_rights: &rights,
                input: comprehension_input(&image, true),
                limits: semantic_limits(),
            },
            || false,
        );
        let SemanticTransitionDecision::Proven(proven) = decision else {
            panic!("the complete correlated collection must rewrite");
        };
        assert_eq!(proven.transitions.len(), 1);
        let (mut egraph, transitions) = proven.into_parts();
        let transition = &transitions[0];

        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let wrapped_zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![zero],
        );
        let wrapped_one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![one],
        );
        let expected_derived = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![wrapped_zero, wrapped_one],
        );
        let derived = transition
            .substitution
            .get(TheoryVariableId(1))
            .expect("the exact-zip derived source must be published");
        assert!(egraph.equiv(derived, expected_derived));

        let double_wrapped_zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![wrapped_zero],
        );
        let double_wrapped_one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
            vec![wrapped_one],
        );
        let expected_output = add_canonical_bag(
            &image,
            &mut egraph,
            vec![one, double_wrapped_zero, double_wrapped_one],
        );
        assert!(egraph.equiv(transition.output, expected_output));
        assert!(transition.substitution.get(TheoryVariableId(2)).is_none());
        assert!(transition.substitution.get(TheoryVariableId(3)).is_none());
    }

    #[test]
    fn correlated_exact_zip_rejects_truncation_reuse_and_partial_effects() {
        let image = comprehension_image();
        let matcher = SemanticTransitionMatcher::restore(&image)
            .expect("restore generalized comprehension rule");
        let rights = LanguageRights::from_rights([LanguageRight::Reduce]);
        assert!(matches!(
            matcher.execute_action(
                SemanticActionExecutionRequest {
                    image: &image,
                    action: TheoryActionId(0),
                    granted_rights: &rights,
                    input: comprehension_input(&image, false),
                    limits: semantic_limits(),
                },
                || false,
            ),
            SemanticTransitionDecision::Refuted(SemanticMatchRefutation::NoTransition)
        ));

        assert!(matches!(
            matcher.execute_action(
                SemanticActionExecutionRequest {
                    image: &image,
                    action: TheoryActionId(0),
                    granted_rights: &rights,
                    input: comprehension_input(&image, true),
                    limits: semantic_limits(),
                },
                || true,
            ),
            SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::Cancelled,
                ..
            }
        ));

        let input = comprehension_input(&image, true);
        let mut limits = semantic_limits();
        limits.work = input.admission_work();
        assert!(matches!(
            matcher.execute_action(
                SemanticActionExecutionRequest {
                    image: &image,
                    action: TheoryActionId(0),
                    granted_rights: &rights,
                    input,
                    limits,
                },
                || false,
            ),
            SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::WorkBudgetExhausted,
                ..
            }
        ));
    }

    #[test]
    fn rhs_exact_zip_rejects_mismatched_source_lengths() {
        let image = comprehension_image();
        let rule = &image.rules[0];
        let mut egraph = EGraph::new();
        assert!(egraph.set_additional_node_budget(64));
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let left = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![zero, one],
        );
        let right = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![zero],
        );
        let mut work = 0;
        assert_eq!(
            instantiate_rule_term(
                TermInstantiation {
                    image: &image,
                    rule,
                    substitution: &vec![(TheoryVariableId(0), left), (TheoryVariableId(1), right),],
                    root: mettail_grammar_core::TheoryTermId(6),
                    limits: TermConstructionLimits {
                        work: 10_000,
                        nodes: 64,
                        bytes: 64 * 1024,
                    },
                },
                &mut egraph,
                &mut work,
                &mut || false,
            ),
            Err(SemanticMatchUndetermined::InvalidImageEvidence)
        );
    }

    #[test]
    fn rhs_map_construction_is_stack_safe_for_wide_sources() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let image = comprehension_image();
                let rule = &image.rules[0];
                let mut egraph = EGraph::new();
                assert!(egraph.set_additional_node_budget(64));
                let zero = add(
                    &mut egraph,
                    TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
                    Vec::new(),
                );
                let source = add(
                    &mut egraph,
                    TheoryImageOperatorV1::Collection {
                        sort: TheorySortId(3),
                        element: TheorySortId(2),
                        kind: CollectionKind::List,
                    },
                    vec![zero; 20_000],
                );
                let mut work = 0;
                let output = instantiate_rule_term(
                    TermInstantiation {
                        image: &image,
                        rule,
                        substitution: &vec![(TheoryVariableId(1), source)],
                        root: mettail_grammar_core::TheoryTermId(9),
                        limits: TermConstructionLimits {
                            work: 500_000,
                            nodes: 64,
                            bytes: 64 * 1024 * 1024,
                        },
                    },
                    &mut egraph,
                    &mut work,
                    &mut || false,
                )
                .expect("iterative pmap construction must fit on a 64 KiB thread stack");
                let (_, elements) = concrete_collection_elements(
                    &image,
                    &egraph,
                    output,
                    TheorySortId(11),
                    &mut work,
                    500_000,
                    &mut || false,
                )
                .expect("inspect mapped bag");
                assert_eq!(elements.len(), 20_000);
            })
            .expect("spawn small-stack map test")
            .join()
            .expect("wide map construction must not overflow its stack");
    }

    fn horn_variable(activation: u64, variable: u32, sort: u32) -> HornTermRef {
        HornTermRef::Variable {
            variable: ScopedClauseVariable {
                activation,
                variable: TheoryVariableId(variable),
            },
            sort: TheorySortId(sort),
        }
    }

    fn horn_ground(class: EClassId, sort: u32) -> HornTermRef {
        HornTermRef::Ground { class, sort: TheorySortId(sort) }
    }

    #[test]
    fn reachable_projection_state_is_bounded_by_reachable_classes_only() {
        let mut source = EGraph::new();
        let root = add(
            &mut source,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        for id in 1..=1_024 {
            add(
                &mut source,
                TheoryImageOperatorV1::Constructor(TheoryConstructorId(id)),
                Vec::new(),
            );
        }
        let mut work = 0;
        let (projected, remap) = project_reachable_egraph(
            &source,
            &[root],
            &mut work,
            ProjectionLimits {
                work: 2,
                nodes: 1,
                bytes: 1_024,
                limit_reason: SemanticMatchUndetermined::InputLimitExceeded,
            },
            &mut || false,
        )
        .expect("one reachable leaf must fit independently of unrelated classes");
        assert_eq!(work, 2);
        assert_eq!(projected.node_count(), 1);
        assert_eq!(remap.len(), 1);
        assert_eq!(
            projected
                .nodes(remapped_eclass(&remap, root).expect("root remap"))
                .len(),
            1
        );
    }

    #[test]
    fn complete_runtime_sort_signatures_validate_every_structural_operator() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let integer = add(
            &mut egraph,
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(1),
                value: TheoryLiteralV1::Integer(7),
            },
            Vec::new(),
        );
        let string = add(
            &mut egraph,
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::String("seven".into()),
            },
            Vec::new(),
        );
        let abstraction = add(
            &mut egraph,
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) },
            vec![zero, zero],
        );
        let multiple_abstraction = add(
            &mut egraph,
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(9) },
            vec![zero, zero],
        );
        let substitution = add(
            &mut egraph,
            TheoryImageOperatorV1::Substitution {
                sort: TheorySortId(2),
                function: TheorySortId(7),
            },
            vec![abstraction, zero],
        );
        let list = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![zero],
        );
        let pair = add(
            &mut egraph,
            TheoryImageOperatorV1::Product { sort: TheorySortId(4) },
            vec![zero, integer],
        );
        let source = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(5),
                element: TheorySortId(4),
                kind: CollectionKind::List,
            },
            vec![pair],
        );
        for (root, sort) in [
            (zero, 2),
            (integer, 1),
            (string, 0),
            (abstraction, 7),
            (multiple_abstraction, 9),
            (substitution, 2),
            (list, 3),
            (pair, 4),
            (source, 5),
        ] {
            validate(&image, &egraph, root, TheorySortId(sort), 1_000)
                .expect("declared operator signature must validate");
        }
    }

    #[test]
    fn runtime_sort_validation_rejects_forged_carriers_and_signatures() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let wrong_literal = add(
            &mut egraph,
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(0),
                value: TheoryLiteralV1::Integer(7),
            },
            Vec::new(),
        );
        let wrong_collection = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(1),
                kind: CollectionKind::List,
            },
            vec![zero],
        );
        let abstraction = add(
            &mut egraph,
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) },
            vec![zero, zero],
        );
        let wrong_substitution = add(
            &mut egraph,
            TheoryImageOperatorV1::Substitution {
                sort: TheorySortId(2),
                function: TheorySortId(8),
            },
            vec![abstraction, wrong_literal],
        );
        let wrong_product = add(
            &mut egraph,
            TheoryImageOperatorV1::Product { sort: TheorySortId(4) },
            vec![zero, zero],
        );
        let judgment = add(
            &mut egraph,
            TheoryImageOperatorV1::Judgment { judgment: TheoryJudgmentId(0) },
            vec![zero],
        );

        for (root, sort) in [
            (wrong_literal, 0),
            (wrong_collection, 3),
            (wrong_substitution, 2),
            (wrong_product, 4),
            (judgment, 2),
        ] {
            assert_eq!(
                validate(&image, &egraph, root, TheorySortId(sort), 1_000),
                Err(SemanticMatchUndetermined::InvalidImageEvidence),
            );
        }
        assert_eq!(
            validate(&image, &egraph, zero, TheorySortId(10), 1_000),
            Err(SemanticMatchUndetermined::InvalidImageEvidence),
        );
    }

    #[test]
    fn pathmap_application_contract_is_explicit_and_mode_directed() {
        let image = signature_image();
        let pathmap = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(13),
            element: TheorySortId(4),
            kind: CollectionKind::PathMap,
        };

        let neutral =
            runtime_operator_signature(&image, &pathmap, Some(PathMapModeV1::NeutralEmpty))
                .expect("neutral PathMap signature");
        assert!(matches!(
            neutral.children,
            RuntimeChildSortContract::Fixed(ref sorts) if sorts.is_empty()
        ));

        let set = runtime_operator_signature(&image, &pathmap, Some(PathMapModeV1::Set))
            .expect("set PathMap signature");
        assert!(matches!(set.children, RuntimeChildSortContract::Homogeneous(TheorySortId(2))));

        let map = runtime_operator_signature(&image, &pathmap, Some(PathMapModeV1::Map))
            .expect("map PathMap signature");
        assert!(matches!(map.children, RuntimeChildSortContract::Homogeneous(TheorySortId(4))));

        let polymorphic = runtime_operator_signature(&image, &pathmap, None)
            .expect("mode-polymorphic PathMap signature");
        assert!(matches!(polymorphic.children, RuntimeChildSortContract::RemainderOnly));

        let list = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(3),
            element: TheorySortId(2),
            kind: CollectionKind::List,
        };
        assert_eq!(
            runtime_operator_signature(&image, &list, Some(PathMapModeV1::Set)).err(),
            Some(SemanticMatchUndetermined::InvalidImageEvidence),
        );
    }

    #[test]
    fn ground_pathmap_admission_preserves_all_modes_and_rejects_forgery() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let key = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let value = add(
            &mut egraph,
            TheoryImageOperatorV1::Literal {
                sort: TheorySortId(1),
                value: TheoryLiteralV1::Integer(7),
            },
            Vec::new(),
        );
        let pair = add(
            &mut egraph,
            TheoryImageOperatorV1::Product { sort: TheorySortId(4) },
            vec![key, value],
        );
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(13),
            element: TheorySortId(4),
            kind: CollectionKind::PathMap,
        };
        let neutral = add_pathmap(&mut egraph, &operator, PathMapModeV1::NeutralEmpty, Vec::new());
        let set = add_pathmap(&mut egraph, &operator, PathMapModeV1::Set, vec![key]);
        let map = add_pathmap(&mut egraph, &operator, PathMapModeV1::Map, vec![pair]);
        for root in [neutral, set, map] {
            validate(&image, &egraph, root, TheorySortId(13), 1_000)
                .expect("each explicit PathMap mode must be admitted exactly");
        }

        let missing_marker = add(&mut egraph, operator.clone(), Vec::new());
        let duplicate_set = add_pathmap(&mut egraph, &operator, PathMapModeV1::Set, vec![key, key]);
        let malformed_map = add_pathmap(&mut egraph, &operator, PathMapModeV1::Map, vec![key]);
        let nonempty_neutral =
            add_pathmap(&mut egraph, &operator, PathMapModeV1::NeutralEmpty, vec![key]);
        for root in [missing_marker, duplicate_set, malformed_map, nonempty_neutral] {
            assert_eq!(
                validate(&image, &egraph, root, TheorySortId(13), 1_000),
                Err(SemanticMatchUndetermined::InvalidImageEvidence),
            );
        }
    }

    #[test]
    fn freshness_is_free_occurrence_with_abstraction_shielding() {
        let mut egraph = EGraph::new();
        let needle = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let other = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let bound = add(
            &mut egraph,
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) },
            vec![needle, needle],
        );
        let free = add(
            &mut egraph,
            TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) },
            vec![other, needle],
        );

        let mut work = 0;
        assert!(freshness_holds(&egraph, needle, bound, &mut work, 64, &mut || false)
            .expect("bound occurrences are shielded"));
        let mut work = 0;
        assert!(!freshness_holds(&egraph, needle, free, &mut work, 64, &mut || false)
            .expect("an unshielded occurrence is free"));
        let mut work = 0;
        assert_eq!(
            freshness_holds(&egraph, needle, free, &mut work, 64, &mut || true),
            Err(SemanticMatchUndetermined::Cancelled),
        );
    }

    #[test]
    fn wide_ground_terms_are_charged_before_child_vector_allocation() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let wide = add(
            &mut egraph,
            TheoryImageOperatorV1::Collection {
                sort: TheorySortId(3),
                element: TheorySortId(2),
                kind: CollectionKind::List,
            },
            vec![zero; 32],
        );
        assert_eq!(
            validate(&image, &egraph, wide, TheorySortId(3), 2),
            Err(SemanticMatchUndetermined::WorkBudgetExhausted),
        );
    }

    #[test]
    fn horn_ordered_row_unification_binds_the_exact_suffix() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(3),
            element: TheorySortId(2),
            kind: CollectionKind::List,
        };
        let subject = add(&mut egraph, operator.clone(), vec![zero, one]);
        let tail = horn_variable(7, 0, 3);
        let mut evaluator = HornEvaluator {
            image: &image,
            egraph: &egraph,
            work: 0,
            work_limit: 10_000,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 100,
        };
        let pattern = evaluator
            .synthetic_collection(
                TheorySortId(3),
                theory_operator_to_machine(&operator),
                CollectionKind::List,
                vec![horn_ground(zero, 2)],
                Some(tail),
                None,
            )
            .expect("allocate ordered row pattern");
        let solutions = evaluator
            .unify_all(&[(pattern, horn_ground(subject, 3))], &Vec::new(), 16)
            .expect("unify ordered row");
        assert_eq!(solutions.len(), 1);
        let view = evaluator
            .view(tail, &solutions[0])
            .expect("view exact suffix");
        let HornTermForm::Application { arguments, collection, remainder, .. } = view.form else {
            panic!("the ordered remainder must be a list");
        };
        assert_eq!(collection, Some(CollectionKind::List));
        assert_eq!(remainder, None);
        assert_eq!(arguments, vec![horn_ground(one, 2)]);
    }

    #[test]
    fn horn_unordered_row_unification_enumerates_selection_and_exact_complement() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(11),
            element: TheorySortId(2),
            kind: CollectionKind::Bag,
        };
        let subject = add(&mut egraph, operator.clone(), vec![zero, one]);
        let selected = horn_variable(7, 0, 2);
        let remainder = horn_variable(7, 1, 11);
        let mut evaluator = HornEvaluator {
            image: &image,
            egraph: &egraph,
            work: 0,
            work_limit: 10_000,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 100,
        };
        let pattern = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![selected],
                Some(remainder),
                None,
            )
            .expect("allocate unordered row pattern");
        let solutions = evaluator
            .unify_all(&[(pattern, horn_ground(subject, 11))], &Vec::new(), 16)
            .expect("unify unordered row");
        assert_eq!(solutions.len(), 2);

        let mut selections = Vec::new();
        for solution in &solutions {
            let selected_view = evaluator.view(selected, solution).expect("view selection");
            let HornTermRef::Ground { class: selected_class, .. } = selected_view.term else {
                panic!("selection must be ground");
            };
            let remainder_view = evaluator
                .view(remainder, solution)
                .expect("view complement");
            let HornTermForm::Application {
                arguments,
                collection: Some(CollectionKind::Bag),
                remainder: None,
                ..
            } = remainder_view.form
            else {
                panic!("complement must be one closed bag");
            };
            let [complement] = arguments.as_slice() else {
                panic!("complement must preserve one occurrence");
            };
            let HornTermRef::Ground { class: complement_class, .. } = complement else {
                panic!("complement occurrence must be ground");
            };
            selections.push((selected_class, *complement_class));
        }
        selections.sort_unstable();
        assert_eq!(selections, vec![(zero, one), (one, zero)]);
    }

    #[test]
    fn horn_open_rows_share_a_fresh_non_capturing_residual() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(11),
            element: TheorySortId(2),
            kind: CollectionKind::Bag,
        };
        let left_tail = horn_variable(7, 0, 11);
        let right_tail = horn_variable(8, 0, 11);
        let mut evaluator = HornEvaluator {
            image: &image,
            egraph: &egraph,
            work: 0,
            work_limit: 10_000,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 100,
        };
        let left = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_ground(zero, 2)],
                Some(left_tail),
                None,
            )
            .expect("allocate left row");
        let right = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_ground(one, 2)],
                Some(right_tail),
                None,
            )
            .expect("allocate right row");
        let solutions = evaluator
            .unify_all(&[(left, right)], &Vec::new(), 16)
            .expect("unify two open rows");
        assert_eq!(solutions.len(), 1);

        let left_view = evaluator
            .view(left_tail, &solutions[0])
            .expect("view left tail");
        let right_view = evaluator
            .view(right_tail, &solutions[0])
            .expect("view right tail");
        let HornTermForm::Application {
            arguments: left_arguments,
            remainder: Some(left_residual),
            ..
        } = left_view.form
        else {
            panic!("left tail must retain the shared residual");
        };
        let HornTermForm::Application {
            arguments: right_arguments,
            remainder: Some(right_residual),
            ..
        } = right_view.form
        else {
            panic!("right tail must retain the shared residual");
        };
        assert_eq!(left_arguments, vec![horn_ground(one, 2)]);
        assert_eq!(right_arguments, vec![horn_ground(zero, 2)]);
        assert_eq!(left_residual, right_residual);
        let HornTermRef::Variable { variable: residual, .. } = left_residual else {
            panic!("the residual must remain a fresh row variable");
        };
        assert_ne!(residual.activation, 7);
        assert_ne!(residual.activation, 8);
    }

    #[test]
    fn horn_row_unification_bounds_branching_and_cancellation_without_partial_results() {
        let image = signature_image();
        let mut egraph = EGraph::new();
        let zero = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            Vec::new(),
        );
        let one = add(
            &mut egraph,
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(1)),
            Vec::new(),
        );
        let operator = TheoryImageOperatorV1::Collection {
            sort: TheorySortId(11),
            element: TheorySortId(2),
            kind: CollectionKind::Bag,
        };
        let subject = add(&mut egraph, operator.clone(), vec![zero, one]);
        let mut bounded = HornEvaluator {
            image: &image,
            egraph: &egraph,
            work: 0,
            work_limit: 10_000,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 100,
        };
        let pattern = bounded
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_variable(7, 0, 2)],
                Some(horn_variable(7, 1, 11)),
                None,
            )
            .expect("allocate bounded pattern");
        assert_eq!(
            bounded.unify_all(&[(pattern, horn_ground(subject, 11))], &Vec::new(), 1),
            Err(SemanticMatchUndetermined::FrontierLimitExceeded),
        );

        let mut cancelled = HornEvaluator {
            image: &image,
            egraph: &egraph,
            work: 0,
            work_limit: 10_000,
            ground_key_nodes: usize::MAX,
            ground_key_bytes: usize::MAX,
            ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
            is_cancelled: || true,
            synthetic_terms: Vec::new(),
            lexical_scopes: Vec::new(),
            collection_states: Vec::new(),
            comprehension_states: Vec::new(),
            derived_collections: Vec::new(),
            next_activation: 100,
        };
        assert_eq!(
            cancelled.unify_all(&[(horn_ground(zero, 2), horn_ground(zero, 2))], &Vec::new(), 16,),
            Err(SemanticMatchUndetermined::Cancelled),
        );
    }

    #[test]
    fn horn_unification_is_stack_safe_at_twenty_thousand_constructor_layers() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let image = signature_image();
                let mut egraph = EGraph::new();
                let mut root = add(
                    &mut egraph,
                    TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
                    Vec::new(),
                );
                for _ in 0..20_000 {
                    root = add(
                        &mut egraph,
                        TheoryImageOperatorV1::Constructor(TheoryConstructorId(2)),
                        vec![root],
                    );
                }
                let mut evaluator = HornEvaluator {
                    image: &image,
                    egraph: &egraph,
                    work: 0,
                    work_limit: 200_000,
                    ground_key_nodes: usize::MAX,
                    ground_key_bytes: usize::MAX,
                    ground_key_limit_reason: SemanticMatchUndetermined::WorkBudgetExhausted,
                    is_cancelled: || false,
                    synthetic_terms: Vec::new(),
                    lexical_scopes: Vec::new(),
                    collection_states: Vec::new(),
                    comprehension_states: Vec::new(),
                    derived_collections: Vec::new(),
                    next_activation: 0,
                };
                assert_eq!(
                    evaluator
                        .unify_all(&[(horn_ground(root, 2), horn_ground(root, 2))], &Vec::new(), 1,)
                        .expect("unify deep ground terms")
                        .len(),
                    1,
                );
            })
            .expect("spawn small-stack unifier test")
            .join()
            .expect("small-stack unifier test must not overflow");
    }
}
