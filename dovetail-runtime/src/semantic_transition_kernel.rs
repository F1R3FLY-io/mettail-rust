//! Runtime execution boundary for verified GSLT semantic images.
//!
//! This module restores the compiler-produced positional pattern quotient and
//! source-exact generalized flat patterns directly into Dovetail's bounded
//! evaluators. It does not rebuild source syntax, parse text, or introduce a
//! second semantic evaluator.

use crate::theory_image_compiler::flat_pattern_from_roots;
use dovetail::flat_matcher::{match_flat_eclass_bounded, FlatMatchLimits, FlatMatchStop};
use dovetail::key::{ContentKey, FramedSemanticOperator, SemanticHash};
use dovetail::rules::Subst;
use dovetail::set_automaton::{
    FlatAutomatonEntryImage, FlatAutomatonImage, FlatAutomatonInvocationImage,
    FlatAutomatonNodeImage, FlatAutomatonRestoreError, FlatAutomatonStateImage, FlatPattern,
    FlatPatternNode, PatternId, SetAutomaton, SetAutomatonSearchStop, SetAutomatonStats,
};
use dovetail::{egraph::EClassId, egraph::EGraph, egraph::ENode};
use mettail_grammar_core::{
    CollectionKind, LanguageRight, LanguageRights, SemanticEffectClassV1, TheoryActionId,
    TheoryEffectId, TheoryImageOperatorV1, TheoryImageTermFormV1, TheoryJudgmentId,
    TheoryJudgmentPatternAutomatonV1, TheoryJudgmentRuleProgramId, TheoryLimitsV1,
    TheoryLiteralCarrierV1, TheoryPatternAutomatonV1, TheoryPatternStateFormV1,
    TheoryPatternStateId, TheoryPatternStateV1, TheoryResourceProfileV1, TheoryRuleDispositionV1,
    TheoryRuleProgramId, TheorySemanticImageV1, TheorySortId, TheorySortKindImageV1,
    TheoryVariableId,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

const THEORY_OPERATOR_DISCRIMINANT: u32 = u32::MAX;
const THEORY_OPERATOR_DOMAIN: &[u8] = b"mettail-theory-machine-operator/1";

/// Inject one closed theory-image operator into the shared semantic-machine
/// carrier.  The stable discriminant selects the theory namespace and the two
/// framed payload segments retain the domain and the operator's complete exact
/// content, so no finite digest becomes semantic identity.
pub fn theory_operator_to_machine(operator: &TheoryImageOperatorV1) -> FramedSemanticOperator {
    let mut exact = Vec::new();
    operator.write_content(&mut exact);
    FramedSemanticOperator::new(
        THEORY_OPERATOR_DISCRIMINANT,
        vec![THEORY_OPERATOR_DOMAIN.to_vec(), exact],
    )
}

/// Failure restoring an admitted theory's reusable matchers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoryPatternRestoreError {
    /// A dense image identifier cannot be represented on this target.
    IdentifierOverflow,
    /// The image violated Dovetail's canonical flat-automaton contract.
    Automaton(FlatAutomatonRestoreError),
    /// A source-exact rule program could not be projected to the generalized
    /// flat algebra. An admitted image must never reach this state.
    InvalidGeneralizedPattern,
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

fn theory_flat_pattern_to_machine(
    source: FlatPattern<TheoryImageOperatorV1>,
) -> Result<FlatPattern<FramedSemanticOperator>, TheoryPatternRestoreError> {
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(source.nodes.len())
        .map_err(|_| TheoryPatternRestoreError::Allocation)?;
    for node in source.nodes {
        nodes.push(match node {
            FlatPatternNode::Var(name) => FlatPatternNode::Var(name),
            FlatPatternNode::App { op, args } => FlatPatternNode::App {
                op: theory_operator_to_machine(&op),
                args,
            },
            FlatPatternNode::OrderedCollection { op, fixed, rest } => {
                FlatPatternNode::OrderedCollection {
                    op: theory_operator_to_machine(&op),
                    fixed,
                    rest,
                }
            },
            FlatPatternNode::UnorderedCollection { op, fixed, rest } => {
                FlatPatternNode::UnorderedCollection {
                    op: theory_operator_to_machine(&op),
                    fixed,
                    rest,
                }
            },
        });
    }
    Ok(FlatPattern { nodes, root: source.root })
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
        if egraph.nodes(root).is_empty() {
            return SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected);
        }
        let mut work = 0;
        match exact_ground_key(
            &egraph,
            root,
            &mut work,
            limits.work,
            limits.nodes,
            limits.bytes,
            SemanticMatchUndetermined::InputLimitExceeded,
            &mut is_cancelled,
        ) {
            Ok(exact_key) => SemanticInputDecision::Proven(Self {
                root: egraph.find(root),
                egraph,
                exact_key,
                admission_work: work,
            }),
            Err(SemanticMatchUndetermined::InvalidImageEvidence) => {
                SemanticInputDecision::Refuted(SemanticMatchRefutation::RequestRejected)
            },
            Err(reason) => SemanticInputDecision::Undetermined { reason, work },
        }
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

/// Verified matcher shared by action execution and OSLF checking.
///
/// Construction restores the exact positional quotient and prepares only the
/// non-positional flat rule programs once. Calls never mutate the matcher; all
/// per-request substitutions and diagnostics remain private until a complete
/// bounded scan and action filter have succeeded.
pub struct SemanticTransitionMatcher {
    transition_automaton: SetAutomaton<FramedSemanticOperator>,
    judgment_automaton: SetAutomaton<FramedSemanticOperator>,
    generalized_transition_patterns: Vec<Option<FlatPattern<FramedSemanticOperator>>>,
}

impl SemanticTransitionMatcher {
    pub fn restore(image: &TheorySemanticImageV1) -> Result<Self, TheoryPatternRestoreError> {
        let positional: BTreeSet<_> = image
            .patterns
            .entries
            .iter()
            .map(|entry| entry.rule)
            .collect();
        let mut generalized_transition_patterns = Vec::new();
        generalized_transition_patterns
            .try_reserve_exact(image.rules.len())
            .map_err(|_| TheoryPatternRestoreError::Allocation)?;
        for rule in &image.rules {
            let pattern = if rule.disposition == TheoryRuleDispositionV1::Executable
                && !positional.contains(&rule.id)
            {
                let source = flat_pattern_from_roots(&rule.terms, &[rule.left], None, rule.id.0)
                    .map_err(|_| TheoryPatternRestoreError::InvalidGeneralizedPattern)?;
                Some(theory_flat_pattern_to_machine(source)?)
            } else {
                None
            };
            generalized_transition_patterns.push(pattern);
        }
        Ok(Self {
            transition_automaton: restore_theory_pattern_automaton(&image.patterns)?,
            judgment_automaton: restore_theory_judgment_pattern_automaton(
                &image.judgment_patterns,
            )?,
            generalized_transition_patterns,
        })
    }

    /// Match one action at one canonical root under explicit authority and
    /// work bounds. Nested redexes found by the shared e-graph scan are not
    /// action successors of `root` and are discarded before publication.
    pub(crate) fn match_action<C>(
        &self,
        image: &TheorySemanticImageV1,
        action: TheoryActionId,
        granted_rights: &LanguageRights,
        egraph: &mut EGraph<FramedSemanticOperator>,
        root: EClassId,
        limits: SemanticTransitionLimits,
        mut is_cancelled: C,
    ) -> SemanticMatchDecision
    where
        C: FnMut() -> bool,
    {
        let Some(action) = image
            .actions
            .get(action.0 as usize)
            .filter(|candidate| candidate.id == action)
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
        let mut validator = HornEvaluator {
            image,
            egraph,
            work: 0,
            work_limit: limits.work,
            is_cancelled: &mut is_cancelled,
            synthetic_terms: Vec::new(),
            next_activation: 0,
        };
        if let Err(reason) = validator.validate_ground_term(root, *input_sort) {
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

        let selected: BTreeSet<_> = action.transitions.iter().copied().collect();
        let entries: BTreeMap<_, _> = image
            .patterns
            .entries
            .iter()
            .map(|entry| (entry.rule, entry))
            .collect();
        let mut stats = scan.run.stats;
        let Some(mut work) = validation_work.checked_add(scan.work) else {
            return SemanticMatchDecision::Undetermined {
                reason: SemanticMatchUndetermined::InvalidImageEvidence,
                work: validation_work,
                stats,
            };
        };
        let mut matches = Vec::new();
        if matches.try_reserve_exact(action.transitions.len()).is_err() {
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
            if !selected.contains(&rule_id) || !egraph.equiv(matched.root, root) {
                continue;
            }
            let Some(entry) = entries.get(&rule_id) else {
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
            matches.push(SemanticRuleMatch {
                rule: rule_id,
                root: egraph.find(matched.root),
                substitution,
            });
        }

        let positional: BTreeSet<_> = entries.keys().copied().collect();
        for &rule_id in &action.transitions {
            if positional.contains(&rule_id) {
                continue;
            }
            let Some(rule) = image.rules.get(rule_id.0 as usize).filter(|candidate| {
                candidate.id == rule_id
                    && candidate.disposition == TheoryRuleDispositionV1::Executable
            }) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(pattern) = self
                .generalized_transition_patterns
                .get(rule_id.0 as usize)
                .and_then(Option::as_ref)
            else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(remaining_work) = limits.work.checked_sub(work) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::InvalidImageEvidence,
                    work,
                    stats,
                };
            };
            let Some(remaining_outputs) = limits.outputs.checked_sub(matches.len()) else {
                return SemanticMatchDecision::Undetermined {
                    reason: SemanticMatchUndetermined::OutputLimitExceeded,
                    work,
                    stats,
                };
            };
            let generalized = match match_flat_eclass_bounded(
                egraph,
                pattern,
                root,
                FlatMatchLimits {
                    work: remaining_work,
                    outputs: remaining_outputs,
                    frontier: limits.frontier,
                },
                &mut is_cancelled,
            ) {
                Ok(run) => run,
                Err(failure) => {
                    let reason = flat_match_stop_reason(failure.reason);
                    if absorb_matcher_accounting(
                        &mut work,
                        limits.work,
                        &mut stats,
                        failure.work,
                        failure.stats,
                    )
                    .is_err()
                    {
                        return SemanticMatchDecision::Undetermined {
                            reason: SemanticMatchUndetermined::InvalidImageEvidence,
                            work,
                            stats,
                        };
                    }
                    return SemanticMatchDecision::Undetermined { reason, work, stats };
                },
            };
            if let Err(reason) = absorb_matcher_accounting(
                &mut work,
                limits.work,
                &mut stats,
                generalized.work,
                generalized.stats,
            ) {
                return SemanticMatchDecision::Undetermined { reason, work, stats };
            }
            for matched in generalized.matches {
                let substitution = match project_named_substitution(
                    rule,
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
                matches.push(SemanticRuleMatch {
                    rule: rule_id,
                    root: egraph.find(matched.root),
                    substitution,
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
        image: &TheorySemanticImageV1,
        judgment: TheoryJudgmentId,
        granted_rights: &LanguageRights,
        egraph: &EGraph<FramedSemanticOperator>,
        arguments: &[EClassId],
        work_limit: u64,
        mut is_cancelled: C,
    ) -> SemanticJudgmentHeadDecision
    where
        C: FnMut() -> bool,
    {
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
        image: &TheorySemanticImageV1,
        judgment: TheoryJudgmentId,
        granted_rights: &LanguageRights,
        egraph: &EGraph<FramedSemanticOperator>,
        arguments: &[EClassId],
        limits: SemanticJudgmentLimits,
        is_cancelled: C,
    ) -> SemanticJudgmentDecision
    where
        C: FnMut() -> bool,
    {
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
            is_cancelled,
            synthetic_terms: Vec::new(),
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
                limits.work,
                limits.term_nodes,
                limits.term_bytes,
                SemanticMatchUndetermined::InputLimitExceeded,
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
                            image,
                            goal.judgment,
                            granted_rights,
                            egraph,
                            &ground_arguments,
                            remaining,
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
                            rule: rule.id,
                            term: conclusion,
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
                                rule: rule.id,
                                term: *term,
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
        image: &TheorySemanticImageV1,
        action: TheoryActionId,
        granted_rights: &LanguageRights,
        input: SemanticTransitionInput,
        limits: SemanticTransitionLimits,
        mut is_cancelled: C,
    ) -> SemanticTransitionDecision
    where
        C: FnMut() -> bool,
    {
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
        let matches = self.match_action(
            image,
            action,
            granted_rights,
            &mut egraph,
            root,
            SemanticTransitionLimits {
                work: limits.work.saturating_sub(prefix_work),
                ..limits
            },
            &mut is_cancelled,
        );
        let ProvenSemanticMatches { matches, work: match_work, stats } = match matches {
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
        if matches.len() > limits.outputs {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::OutputLimitExceeded,
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
        let resource = match image.resource_profile {
            TheoryResourceProfileV1::Uncosted => SemanticResourceReceipt::NoSemanticGrade,
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
        let input = input_key.as_bytes().to_vec();
        let mut private = egraph;
        let initial_nodes = private.node_count();
        let mut transitions = Vec::new();
        if transitions.try_reserve_exact(matches.len()).is_err() {
            return SemanticTransitionDecision::Undetermined {
                reason: SemanticMatchUndetermined::OutputLimitExceeded,
                work,
                stats,
            };
        }
        for matched in matches {
            if let Err(reason) = charge_work(&mut work, limits.work, &mut is_cancelled) {
                return SemanticTransitionDecision::Undetermined { reason, work, stats };
            }
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
            if !rule.premise_roots.is_empty() {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::PremiseEvaluationUnavailable,
                    work,
                    stats,
                };
            }
            let output = match instantiate_rule_rhs(
                rule,
                &matched.substitution,
                &mut private,
                &mut work,
                limits.work,
                limits.output_nodes,
                limits.output_bytes,
                &mut is_cancelled,
            ) {
                Ok(output) => output,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            let added_nodes = private.node_count().saturating_sub(initial_nodes);
            if added_nodes > limits.output_nodes {
                return SemanticTransitionDecision::Undetermined {
                    reason: SemanticMatchUndetermined::OutputLimitExceeded,
                    work,
                    stats,
                };
            }
            let output_key = match exact_ground_key(
                &private,
                output,
                &mut work,
                limits.work,
                limits.output_nodes,
                limits.output_bytes,
                SemanticMatchUndetermined::OutputLimitExceeded,
                &mut is_cancelled,
            ) {
                Ok(key) => key,
                Err(reason) => {
                    return SemanticTransitionDecision::Undetermined { reason, work, stats };
                },
            };
            transitions.push(SemanticTransition {
                output,
                output_sort: rule.terms[rule.right.0 as usize].sort,
                substitution: matched.substitution,
                receipt: SemanticTransitionReceipt {
                    language_fingerprint: image.language_fingerprint,
                    theory_fingerprint: image.theory_fingerprint,
                    image_fingerprint,
                    action,
                    rule: rule.id,
                    input: input.clone(),
                    output: output_key.as_bytes().to_vec(),
                    effect: action_image.effect,
                    effect_class: action_image.effect_class,
                    resource: resource.clone(),
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
        });
        transitions.dedup_by(|left, right| {
            left.receipt.output == right.receipt.output
                && left.receipt.rule == right.receipt.rule
                && left.substitution == right.substitution
        });
        for transition in &mut transitions {
            transition.receipt.work = work;
        }
        if transitions.is_empty() {
            SemanticTransitionDecision::Refuted(SemanticMatchRefutation::NoTransition)
        } else {
            SemanticTransitionDecision::Proven(ProvenSemanticTransitions {
                egraph: private,
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
    pub output_nodes: usize,
    pub output_bytes: usize,
}

impl From<TheoryLimitsV1> for SemanticTransitionLimits {
    fn from(limits: TheoryLimitsV1) -> Self {
        Self {
            work: u64::from(limits.max_steps),
            outputs: limits.max_frontier as usize,
            frontier: limits.max_frontier as usize,
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
    pub work: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticTransition {
    pub output: EClassId,
    pub output_sort: TheorySortId,
    pub substitution: BTreeMap<TheoryVariableId, EClassId>,
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
        rule: TheoryJudgmentRuleProgramId,
        term: mettail_grammar_core::TheoryTermId,
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

struct HornUnificationBranch {
    pending: Vec<(HornTermRef, HornTermRef)>,
    substitution: HornSubstitution,
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
    right_arguments: Vec<HornTermRef>,
    right_remainder: Option<HornTermRef>,
}

enum HornTermForm {
    Variable(ScopedClauseVariable),
    Application {
        operator: FramedSemanticOperator,
        arguments: Vec<HornTermRef>,
        collection: Option<CollectionKind>,
        remainder: Option<HornTermRef>,
    },
}

struct HornSyntheticTerm {
    sort: TheorySortId,
    operator: FramedSemanticOperator,
    arguments: Vec<HornTermRef>,
    collection: CollectionKind,
    remainder: Option<HornTermRef>,
}

struct HornTermView {
    term: HornTermRef,
    sort: TheorySortId,
    form: HornTermForm,
}

enum RuntimeChildSortContract {
    Fixed(Vec<TheorySortId>),
    Homogeneous(TheorySortId),
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
    is_cancelled: C,
    synthetic_terms: Vec<HornSyntheticTerm>,
    next_activation: u64,
}

impl<'a, C> HornEvaluator<'a, C>
where
    C: FnMut() -> bool,
{
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
        });
        Ok(HornTermRef::Synthetic { term, sort })
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
                HornTermRef::Clause { activation, rule, term: term_id } => {
                    let rule = self
                        .image
                        .judgment_rules
                        .get(rule.0 as usize)
                        .filter(|candidate| candidate.id == rule)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    let node = rule
                        .terms
                        .get(term_id.0 as usize)
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    match &node.form {
                        TheoryImageTermFormV1::Slot(variable) => {
                            let declaration = rule
                                .variables
                                .get(variable.0 as usize)
                                .filter(|candidate| candidate.id == *variable)
                                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                            if declaration.sort != node.sort {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            term = HornTermRef::Variable {
                                variable: ScopedClauseVariable { activation, variable: *variable },
                                sort: declaration.sort,
                            };
                        },
                        TheoryImageTermFormV1::Apply { operator, arguments, slots, remainder } => {
                            let signature = runtime_operator_signature(self.image, operator)?;
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
                                _ => {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                },
                            }
                            self.charge_units(child_count)?;
                            let mut children = Vec::new();
                            children
                                .try_reserve_exact(child_count)
                                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                            for (index, variable) in slots.iter().enumerate() {
                                let declaration = rule
                                    .variables
                                    .get(variable.0 as usize)
                                    .filter(|candidate| candidate.id == *variable)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                let expected = match &signature.children {
                                    RuntimeChildSortContract::Fixed(sorts) => sorts[index],
                                    RuntimeChildSortContract::Homogeneous(sort) => *sort,
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
                                let argument_node = rule
                                    .terms
                                    .get(argument.0 as usize)
                                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                                let expected = match &signature.children {
                                    RuntimeChildSortContract::Fixed(sorts) => {
                                        sorts[slots.len() + offset]
                                    },
                                    RuntimeChildSortContract::Homogeneous(sort) => *sort,
                                };
                                if argument_node.sort != expected {
                                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                                }
                                children.push(HornTermRef::Clause {
                                    activation,
                                    rule: rule.id,
                                    term: *argument,
                                });
                            }
                            let remainder = match remainder {
                                Some(variable) => {
                                    let RuntimeChildSortContract::Homogeneous(_) =
                                        &signature.children
                                    else {
                                        return Err(
                                            SemanticMatchUndetermined::InvalidImageEvidence,
                                        );
                                    };
                                    let declaration = rule
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
                                        variable: ScopedClauseVariable {
                                            activation,
                                            variable: *variable,
                                        },
                                        sort: node.sort,
                                    })
                                },
                                None => None,
                            };
                            let collection = match operator {
                                TheoryImageOperatorV1::Collection { kind, .. } => Some(*kind),
                                _ => None,
                            };
                            return Ok(HornTermView {
                                term,
                                sort: node.sort,
                                form: HornTermForm::Application {
                                    operator: theory_operator_to_machine(operator),
                                    arguments: children,
                                    collection,
                                    remainder,
                                },
                            });
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
                            collection: Some(synthetic.collection),
                            remainder: synthetic.remainder,
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
                    element: declared_element,
                    ..
                } = runtime_sort_kind(self.image, sort)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if sort != expected_sort || kind != *declared_kind || element != *declared_element {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                collection = Some(kind);
                arguments
                    .try_reserve_exact(node.children.len())
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for &child in &node.children {
                    arguments.push(HornTermRef::Ground {
                        class: self.egraph.find(child),
                        sort: element,
                    });
                }
            },
            4 => {
                if payload.len() < 16 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let target = TheorySortId(read_u32(&payload[..4]));
                let source = TheorySortId(read_u32(&payload[4..8]));
                let parameter_count = usize::try_from(read_u64(&payload[8..16]))
                    .map_err(|_| SemanticMatchUndetermined::InvalidImageEvidence)?;
                let expected_payload = parameter_count
                    .checked_mul(4)
                    .and_then(|length| length.checked_add(16))
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                let expected_children = parameter_count
                    .checked_add(2)
                    .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                if payload.len() != expected_payload
                    || node.children.len() != expected_children
                    || target != expected_sort
                {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let TheorySortKindImageV1::Collection {
                    kind: source_kind,
                    element: source_element,
                    ..
                } = runtime_sort_kind(self.image, source)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                let TheorySortKindImageV1::Collection {
                    kind: target_kind,
                    element: target_element,
                    ..
                } = runtime_sort_kind(self.image, target)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if source_kind != target_kind {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let encoded_parameters = &payload[16..];
                match runtime_sort_kind(self.image, *source_element)? {
                    TheorySortKindImageV1::Product { factors } => {
                        if factors.len() != parameter_count {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        for (encoded, expected) in encoded_parameters.chunks_exact(4).zip(factors) {
                            if TheorySortId(read_u32(encoded)) != *expected {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                        }
                    },
                    _ => {
                        if parameter_count != 1
                            || TheorySortId(read_u32(encoded_parameters)) != *source_element
                        {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                    },
                }
                arguments
                    .try_reserve_exact(expected_children)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for (index, encoded) in encoded_parameters.chunks_exact(4).enumerate() {
                    arguments.push(HornTermRef::Ground {
                        class: self.egraph.find(node.children[index]),
                        sort: TheorySortId(read_u32(encoded)),
                    });
                }
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[parameter_count]),
                    sort: source,
                });
                arguments.push(HornTermRef::Ground {
                    class: self.egraph.find(node.children[parameter_count + 1]),
                    sort: *target_element,
                });
            },
            5 => {
                if payload.len() != 4 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                let product = TheorySortId(read_u32(payload));
                let TheorySortKindImageV1::Product { factors } =
                    runtime_sort_kind(self.image, product)?
                else {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                };
                if product != expected_sort || factors.len() != 2 || node.children.len() != 2 {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                }
                arguments
                    .try_reserve_exact(2)
                    .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
                for (&child, &sort) in node.children.iter().zip(factors) {
                    arguments.push(HornTermRef::Ground { class: self.egraph.find(child), sort });
                }
            },
            6 => {
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
        pending: &mut Vec<(HornTermRef, HornTermRef)>,
        equations: &[(HornTermRef, HornTermRef)],
    ) -> Result<(), SemanticMatchUndetermined> {
        pending
            .try_reserve(equations.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        pending.extend(equations.iter().copied().rev());
        Ok(())
    }

    fn collection_fragment(
        &mut self,
        sort: TheorySortId,
        operator: &FramedSemanticOperator,
        collection: CollectionKind,
        arguments: Vec<HornTermRef>,
        remainder: Option<HornTermRef>,
    ) -> Result<HornTermRef, SemanticMatchUndetermined> {
        if arguments.is_empty() {
            if let Some(remainder) = remainder {
                return Ok(remainder);
            }
        }
        self.charge()?;
        self.synthetic_collection(sort, operator.clone(), collection, arguments, remainder)
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
            right_arguments,
            right_remainder,
        } = equation;
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
                    )?;
                    let right_fragment = self.collection_fragment(
                        *sort,
                        operator,
                        *collection,
                        pairing.unmatched_left,
                        Some(residual),
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
            let Some((left, right)) = branch.pending.pop() else {
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
                (
                    HornTermForm::Application {
                        operator: left_operator,
                        arguments: left_arguments,
                        collection: left_collection,
                        remainder: left_remainder,
                    },
                    HornTermForm::Application {
                        operator: right_operator,
                        arguments: right_arguments,
                        collection: right_collection,
                        remainder: right_remainder,
                    },
                ) => {
                    if left_operator != right_operator || left_collection != right_collection {
                        continue;
                    }
                    match left_collection {
                        None => {
                            if left_remainder.is_some()
                                || right_remainder.is_some()
                                || left_arguments.len() != right_arguments.len()
                            {
                                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                            }
                            let equations = left_arguments
                                .into_iter()
                                .zip(right_arguments)
                                .collect::<Vec<_>>();
                            Self::extend_unification_equations(&mut branch.pending, &equations)?;
                            Self::push_unification_branch(&mut frontier, branch, frontier_limit)?;
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
                                    right_arguments,
                                    right_remainder,
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
                                right_arguments,
                                right_remainder,
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

fn runtime_operator_signature(
    image: &TheorySemanticImageV1,
    operator: &TheoryImageOperatorV1,
) -> Result<RuntimeOperatorSignature, SemanticMatchUndetermined> {
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
                element: declared_element,
                ..
            } = runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if declared_kind != kind || declared_element != element {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            (*sort, RuntimeChildSortContract::Homogeneous(*element))
        },
        TheoryImageOperatorV1::Map { sort, source, parameters } => {
            let TheorySortKindImageV1::Collection {
                kind: source_kind,
                element: source_element,
                ..
            } = runtime_sort_kind(image, *source)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            let TheorySortKindImageV1::Collection {
                kind: target_kind,
                element: target_element,
                ..
            } = runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if source_kind != target_kind {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            match runtime_sort_kind(image, *source_element)? {
                TheorySortKindImageV1::Product { factors } if factors == parameters => {},
                TheorySortKindImageV1::Product { .. } => {
                    return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                },
                _ if parameters.len() == 1 && parameters[0] == *source_element => {},
                _ => return Err(SemanticMatchUndetermined::InvalidImageEvidence),
            }
            let capacity = parameters
                .len()
                .checked_add(2)
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
            let mut children = Vec::new();
            children
                .try_reserve_exact(capacity)
                .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
            children.extend_from_slice(parameters);
            children.extend([*source, *target_element]);
            (*sort, RuntimeChildSortContract::Fixed(children))
        },
        TheoryImageOperatorV1::Zip { sort } => {
            let TheorySortKindImageV1::Product { factors } = runtime_sort_kind(image, *sort)?
            else {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            };
            if factors.len() != 2 {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
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
        TheoryImageOperatorV1::Judgment { .. } => {
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

fn read_u64(bytes: &[u8]) -> u64 {
    let mut value = [0; 8];
    value.copy_from_slice(&bytes[..8]);
    u64::from_le_bytes(value)
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

fn flat_match_stop_reason(reason: FlatMatchStop) -> SemanticMatchUndetermined {
    match reason {
        FlatMatchStop::InvalidPattern(_) => SemanticMatchUndetermined::InvalidImageEvidence,
        FlatMatchStop::WorkBudgetExhausted => SemanticMatchUndetermined::WorkBudgetExhausted,
        FlatMatchStop::Cancelled => SemanticMatchUndetermined::Cancelled,
        FlatMatchStop::OutputLimitExceeded => SemanticMatchUndetermined::OutputLimitExceeded,
        FlatMatchStop::FrontierLimitExceeded => SemanticMatchUndetermined::FrontierLimitExceeded,
        FlatMatchStop::EGraphNodeBudgetExhausted => {
            SemanticMatchUndetermined::EGraphNodeBudgetExhausted
        },
        FlatMatchStop::AllocationFailed => SemanticMatchUndetermined::AllocationFailed,
    }
}

fn project_named_substitution<C>(
    rule: &mettail_grammar_core::TheoryRuleProgramV1,
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
    for (name, &value) in matched {
        charge_work(work, work_limit, is_cancelled)?;
        let variable = name
            .strip_prefix('v')
            .and_then(|digits| digits.parse::<u32>().ok())
            .map(TheoryVariableId)
            .filter(|variable| format!("v{}", variable.0) == *name)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        rule.variables
            .get(variable.0 as usize)
            .filter(|declaration| declaration.id == variable)
            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
        if substitution.insert(variable, egraph.find(value)).is_some() {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
    }
    Ok(substitution)
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

fn instantiate_rule_rhs<C>(
    rule: &mettail_grammar_core::TheoryRuleProgramV1,
    substitution: &BTreeMap<TheoryVariableId, EClassId>,
    egraph: &mut EGraph<FramedSemanticOperator>,
    work: &mut u64,
    work_limit: u64,
    output_node_limit: usize,
    output_byte_limit: usize,
    is_cancelled: &mut C,
) -> Result<EClassId, SemanticMatchUndetermined>
where
    C: FnMut() -> bool,
{
    let mut reachable = vec![false; rule.terms.len()];
    let mut pending = vec![rule.right];
    while let Some(term) = pending.pop() {
        charge_work(work, work_limit, is_cancelled)?;
        let Some(mark) = reachable.get_mut(term.0 as usize) else {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        };
        if std::mem::replace(mark, true) {
            continue;
        }
        let node = &rule.terms[term.0 as usize];
        if let TheoryImageTermFormV1::Apply { arguments, .. } = &node.form {
            pending.extend(arguments.iter().copied());
        }
    }

    let mut values = vec![None; rule.terms.len()];
    for (index, node) in rule.terms.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        charge_work(work, work_limit, is_cancelled)?;
        let value = match &node.form {
            TheoryImageTermFormV1::Slot(variable) => substitution
                .get(variable)
                .copied()
                .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
            TheoryImageTermFormV1::Apply { operator, arguments, slots, remainder } => {
                let capacity = slots
                    .len()
                    .checked_add(arguments.len())
                    .and_then(|count| count.checked_add(usize::from(remainder.is_some())))
                    .ok_or(SemanticMatchUndetermined::OutputLimitExceeded)?;
                let mut children = Vec::new();
                children
                    .try_reserve_exact(capacity)
                    .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
                for variable in slots {
                    charge_work(work, work_limit, is_cancelled)?;
                    children.push(
                        substitution
                            .get(variable)
                            .copied()
                            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
                    );
                }
                for argument in arguments {
                    charge_work(work, work_limit, is_cancelled)?;
                    children.push(
                        values
                            .get(argument.0 as usize)
                            .and_then(|value| *value)
                            .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
                    );
                }
                if let Some(remainder) = remainder {
                    charge_work(work, work_limit, is_cancelled)?;
                    let remainder = substitution
                        .get(remainder)
                        .copied()
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?;
                    append_collection_remainder(egraph, operator, remainder, &mut children)?;
                }
                canonicalize_collection_children(
                    egraph,
                    operator,
                    &mut children,
                    work,
                    work_limit,
                    output_node_limit,
                    output_byte_limit,
                    is_cancelled,
                )?;
                egraph
                    .try_add_with_budget(ENode::new(theory_operator_to_machine(operator), children))
                    .ok_or(SemanticMatchUndetermined::EGraphNodeBudgetExhausted)?
            },
        };
        values[index] = Some(egraph.find(value));
    }
    values
        .get(rule.right.0 as usize)
        .and_then(|value| *value)
        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)
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

fn canonicalize_collection_children(
    egraph: &EGraph<FramedSemanticOperator>,
    operator: &TheoryImageOperatorV1,
    children: &mut Vec<EClassId>,
    work: &mut u64,
    work_limit: u64,
    output_node_limit: usize,
    output_byte_limit: usize,
    is_cancelled: &mut impl FnMut() -> bool,
) -> Result<(), SemanticMatchUndetermined> {
    let TheoryImageOperatorV1::Collection { kind, .. } = operator else {
        return Ok(());
    };
    if matches!(kind, CollectionKind::Bag | CollectionKind::Set) {
        let mut keyed = Vec::new();
        keyed
            .try_reserve_exact(children.len())
            .map_err(|_| SemanticMatchUndetermined::OutputLimitExceeded)?;
        for child in children.iter().copied() {
            let key = exact_ground_key(
                egraph,
                child,
                work,
                work_limit,
                output_node_limit,
                output_byte_limit,
                SemanticMatchUndetermined::OutputLimitExceeded,
                is_cancelled,
            )?;
            keyed.push((key, egraph.find(child)));
        }
        keyed.sort_unstable();
        if *kind == CollectionKind::Set {
            keyed.dedup_by(|left, right| left.0 == right.0);
        }
        children.clear();
        children.extend(keyed.into_iter().map(|(_, child)| child));
    }
    Ok(())
}

/// Compute a recursive exact key for a canonical, acyclic ground e-graph.
/// Each reachable e-class must contain exactly one e-node. Equality saturation
/// produces multi-node classes and therefore cannot masquerade as an input
/// term; callers must first select and re-project one canonical representative.
fn exact_ground_key<C>(
    egraph: &EGraph<FramedSemanticOperator>,
    root: EClassId,
    work: &mut u64,
    work_limit: u64,
    node_limit: usize,
    byte_limit: usize,
    limit_reason: SemanticMatchUndetermined,
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
        charge_work(work, work_limit, is_cancelled)?;
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
                .map_err(|_| limit_reason)?;
            for child in &node.children {
                children.push(
                    keys.get(&egraph.find(*child))
                        .cloned()
                        .ok_or(SemanticMatchUndetermined::InvalidImageEvidence)?,
                );
            }
            let key = ContentKey::tree(&node.op, children);
            if key.len() > byte_limit {
                return Err(limit_reason);
            }
            visiting.remove(&class);
            keys.insert(class, key);
            if keys.len() > node_limit {
                return Err(limit_reason);
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
        TheoryLiteralV1, TheoryPatternAutomatonV1, TheorySortImageV1, THEORY_IMAGE_COMPILER_ABI_V1,
        THEORY_SEMANTIC_IMAGE_ABI_V1,
    };

    fn sort(id: u32, kind: TheorySortKindImageV1) -> TheorySortImageV1 {
        TheorySortImageV1 { id: TheorySortId(id), kind }
    }

    fn signature_image() -> TheorySemanticImageV1 {
        TheorySemanticImageV1 {
            abi: THEORY_SEMANTIC_IMAGE_ABI_V1,
            compiler_abi: THEORY_IMAGE_COMPILER_ABI_V1,
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

    fn add(
        egraph: &mut EGraph<FramedSemanticOperator>,
        operator: TheoryImageOperatorV1,
        children: Vec<EClassId>,
    ) -> EClassId {
        egraph.add(ENode::new(theory_operator_to_machine(&operator), children))
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
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            next_activation: 0,
        }
        .validate_ground_term(root, sort)
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
            TheoryImageOperatorV1::Zip { sort: TheorySortId(4) },
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
        let mapped = add(
            &mut egraph,
            TheoryImageOperatorV1::Map {
                sort: TheorySortId(6),
                source: TheorySortId(5),
                parameters: vec![TheorySortId(2), TheorySortId(1)],
            },
            vec![zero, integer, source, integer],
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
            (mapped, 6),
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
        let wrong_map = add(
            &mut egraph,
            TheoryImageOperatorV1::Map {
                sort: TheorySortId(6),
                source: TheorySortId(5),
                parameters: vec![TheorySortId(4)],
            },
            vec![zero, zero, wrong_collection],
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
            (wrong_map, 6),
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
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            next_activation: 100,
        };
        let pattern = evaluator
            .synthetic_collection(
                TheorySortId(3),
                theory_operator_to_machine(&operator),
                CollectionKind::List,
                vec![horn_ground(zero, 2)],
                Some(tail),
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
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            next_activation: 100,
        };
        let pattern = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![selected],
                Some(remainder),
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
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            next_activation: 100,
        };
        let left = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_ground(zero, 2)],
                Some(left_tail),
            )
            .expect("allocate left row");
        let right = evaluator
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_ground(one, 2)],
                Some(right_tail),
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
            is_cancelled: || false,
            synthetic_terms: Vec::new(),
            next_activation: 100,
        };
        let pattern = bounded
            .synthetic_collection(
                TheorySortId(11),
                theory_operator_to_machine(&operator),
                CollectionKind::Bag,
                vec![horn_variable(7, 0, 2)],
                Some(horn_variable(7, 1, 11)),
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
            is_cancelled: || true,
            synthetic_terms: Vec::new(),
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
                    is_cancelled: || false,
                    synthetic_terms: Vec::new(),
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
