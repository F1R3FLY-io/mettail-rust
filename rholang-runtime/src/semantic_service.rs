//! Capability-authorized execution of installed semantic theories.
//!
//! Kernel execution ceilings and cumulative boundary payload reservations are
//! different measures. In particular, a kernel output-size ceiling is not an
//! allocation budget, and logical work is not a semantic Cost(G) grade.

use crate::installed_flt::{InstalledFltAdapter, InstalledFltBindingError, InstalledFltError};
use crate::language_install::{LanguageRuntimeError, RholangLanguageRuntime};
use mettail_dovetail_runtime::{
    SemanticActionExecutionRequest, SemanticInputLimits, SemanticMatchRefutation,
    SemanticMatchUndetermined, SemanticPremiseReceipt, SemanticResourceReceipt, SemanticTransition,
    SemanticTransitionDecision, SemanticTransitionInput, SemanticTransitionLimits,
    SemanticTransitionMatcher, SemanticTransitionReceipt, TheoryPatternRestoreError,
};
use mettail_grammar_core::{
    InstalledLanguage, InstalledLanguageHandle, InstalledLanguageTable, LanguageAccessError,
    LanguageRight, TheoryActionExecutionImageV1, TheoryActionId, TheoryActionImageV1,
    TheoryImageOperatorV1, TheoryLimitsV1, TheoryLiteralV1, TheoryPatternStateFormV1,
    TheoryPatternStateV1, TheoryResourceProfileV1, TheoryRuleDispositionV1, TheorySemanticImageV1,
    TheorySortId, TheoryVariableId,
};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use models::rhoapi::Par;
use rspace_plus_plus::rspace::{errors::RSpaceError, rspace_interface::ProduceCommitGuard};
use std::sync::Arc;

const SEMANTIC_SETUP_SCHEDULE_V1: u128 = 1;
const SEMANTIC_RECEIPT_SCHEDULE_V1: u128 = 1;
const DEFAULT_BOUNDARY_PAYLOAD_BYTES: usize = 16 * 1024 * 1024;

/// Host ceilings or caller-requested attenuation for a semantic operation.
/// Execution meets all three installed/host/request policies. The separate
/// boundary payload allowance meets host/request only: TheoryCore has no
/// cumulative boundary-allocation coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticServiceLimits {
    pub execution: SemanticTransitionLimits,
    pub boundary_payload_bytes: usize,
}

impl Default for SemanticServiceLimits {
    fn default() -> Self {
        Self {
            execution: TheoryLimitsV1::default().into(),
            boundary_payload_bytes: DEFAULT_BOUNDARY_PAYLOAD_BYTES,
        }
    }
}

impl SemanticServiceLimits {
    /// Compute only attenuation; no authority is conferred by a limit value.
    pub fn effective(self, installed: TheoryLimitsV1, requested: Self) -> Self {
        Self {
            execution: meet_execution(
                installed.into(),
                meet_execution(self.execution, requested.execution),
            ),
            boundary_payload_bytes: self
                .boundary_payload_bytes
                .min(requested.boundary_payload_bytes),
        }
    }

    /// Fixed-order numeric words, subsequently encoded as sixteen-byte big-
    /// endian values by the installation policy writer. Native pointer widths
    /// and allocator capacities never enter the commitment.
    pub(crate) fn commitment_words(self) -> [u128; 13] {
        let e = self.execution;
        [
            SEMANTIC_SETUP_SCHEDULE_V1,
            u128::from(e.work),
            e.normalization_steps as u128,
            e.outputs as u128,
            e.frontier as u128,
            e.proofs as u128,
            e.proof_nodes as u128,
            e.term_nodes as u128,
            e.term_bytes as u128,
            e.output_nodes as u128,
            e.output_bytes as u128,
            self.boundary_payload_bytes as u128,
            SEMANTIC_RECEIPT_SCHEDULE_V1,
        ]
    }
}

fn meet_execution(
    a: SemanticTransitionLimits,
    b: SemanticTransitionLimits,
) -> SemanticTransitionLimits {
    SemanticTransitionLimits {
        work: a.work.min(b.work),
        normalization_steps: a.normalization_steps.min(b.normalization_steps),
        outputs: a.outputs.min(b.outputs),
        frontier: a.frontier.min(b.frontier),
        proofs: a.proofs.min(b.proofs),
        proof_nodes: a.proof_nodes.min(b.proof_nodes),
        term_nodes: a.term_nodes.min(b.term_nodes),
        term_bytes: a.term_bytes.min(b.term_bytes),
        output_nodes: a.output_nodes.min(b.output_nodes),
        output_bytes: a.output_bytes.min(b.output_bytes),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstalledSemanticError {
    InvalidHandleShape,
    UnknownHandle,
    Access(LanguageAccessError),
    MissingSemanticImage,
    UnknownAction,
    UnknownObservation,
    InvalidSelection(&'static str),
    InvalidEvidence(&'static str),
    Refuted(SemanticMatchRefutation),
    Undetermined(SemanticMatchUndetermined),
    Resource(DynamicReflectionError),
    Restore(TheoryPatternRestoreError),
}

impl From<DynamicReflectionError> for InstalledSemanticError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Resource(error)
    }
}

/// Names identify declarations only within the already authorized owner. An
/// observation selects its declared action; it is not an alias for Reduce.
#[derive(Clone, Copy, Debug)]
pub enum SemanticOperation<'a> {
    Reduce(&'a str),
    Observe(&'a str),
}

/// A structural invocation of an installed theory, never guest source text.
pub struct SemanticServiceRequest<'a> {
    pub handle: &'a Par,
    pub operation: SemanticOperation<'a>,
    pub input: &'a Par,
    pub limits: SemanticServiceLimits,
}

/// One complete reflected result and its original, unmodified kernel receipt.
/// Temporary e-graph and substitution coordinates are deliberately absent.
#[derive(Debug)]
pub struct SemanticServiceResult {
    pub term: Par,
    pub receipt: SemanticTransitionReceipt,
}

/// All outcomes retain their consumed logical work. A negative outcome contains
/// no successful prefix. This service commit does not commit node effects or
/// settle funding; those remain the host's separately authorized transaction.
#[derive(Debug)]
pub struct SemanticServiceReport {
    pub outcome: Result<Vec<SemanticServiceResult>, InstalledSemanticError>,
    pub work: u64,
    pub kernel_work: Option<u64>,
    pub effective_limits: Option<SemanticServiceLimits>,
    pub remaining_boundary_payload_bytes: usize,
}

impl From<InstalledFltError> for InstalledSemanticError {
    fn from(error: InstalledFltError) -> Self {
        match error {
            InstalledFltError::Resource(error)
            | InstalledFltError::Binding(InstalledFltBindingError::Resource(error)) => {
                Self::Resource(error)
            },
            InstalledFltError::Kernel(reason) => Self::Undetermined(reason),
            InstalledFltError::Refuted(reason) => Self::Refuted(reason),
            InstalledFltError::UnsupportedOrMalformed(reason) => Self::InvalidSelection(reason),
            InstalledFltError::Binding(InstalledFltBindingError::MissingSemanticImage) => {
                Self::MissingSemanticImage
            },
            InstalledFltError::Binding(InstalledFltBindingError::InconsistentBinding(reason)) => {
                Self::InvalidEvidence(reason)
            },
            InstalledFltError::Binding(InstalledFltBindingError::ConflictingGrammarLabel(_)) => {
                Self::InvalidEvidence("conflicting constructor binding")
            },
            InstalledFltError::Binding(InstalledFltBindingError::ReservedConstructorLabel(_)) => {
                Self::InvalidSelection("reserved constructor label")
            },
        }
    }
}

/// Retained authority, not an authorization lease. Every commit rechecks the
/// sealed handle and the complete selected-right roster under the table lock.
/// The host invokes this only after candidate preparation and releases it
/// before observers or receiver dispatch, as modeled by GuardedReplyPublication.
struct InstalledSemanticPublication {
    table: Arc<InstalledLanguageTable>,
    handle: InstalledLanguageHandle,
    required: Vec<LanguageRight>,
}

impl InstalledSemanticPublication {
    fn authorize<R>(&self, commit: impl FnOnce() -> R) -> Result<R, LanguageAccessError> {
        self.table
            .with_authorized_all(&self.handle, &self.required, |_| commit())
    }
}

impl ProduceCommitGuard for InstalledSemanticPublication {
    fn with_commit(&self, commit: Box<dyn FnOnce() + '_>) -> Result<(), RSpaceError> {
        self.authorize(commit)
            .map_err(|_| RSpaceError::ProduceCommitDenied)
    }
}

#[derive(Default)]
struct SemanticServicePrefix {
    work: u64,
    payload_bytes: usize,
}

struct SemanticServiceUsage {
    work: u64,
    kernel_work: Option<u64>,
    effective_limits: Option<SemanticServiceLimits>,
    remaining_boundary_payload_bytes: usize,
}

struct PreparedSemanticReport {
    outcome: Result<Vec<SemanticServiceResult>, InstalledSemanticError>,
    publication: Option<InstalledSemanticPublication>,
    usage: SemanticServiceUsage,
}

impl PreparedSemanticReport {
    fn commit(self) -> SemanticServiceReport {
        let outcome = self.outcome.and_then(|results| {
            let publication = self
                .publication
                .ok_or(InstalledSemanticError::InvalidEvidence(
                    "prepared success has no publication context",
                ))?;
            // Move already prepared results only; no user callback, directory
            // access, encoding or receiver dispatch runs under this table lock.
            publication
                .authorize(|| results)
                .map_err(InstalledSemanticError::Access)
        });
        SemanticServiceReport {
            outcome,
            work: self.usage.work,
            kernel_work: self.usage.kernel_work,
            effective_limits: self.usage.effective_limits,
            remaining_boundary_payload_bytes: self.usage.remaining_boundary_payload_bytes,
        }
    }
}

impl RholangLanguageRuntime {
    /// Execute one exact installed action or declared observation using the
    /// existing semantic kernel. Input is an already constructed structural FLT.
    pub fn execute_semantic<C: FnMut() -> bool>(
        &self,
        request: SemanticServiceRequest<'_>,
        is_cancelled: C,
    ) -> SemanticServiceReport {
        self.prepare_semantic(request, SemanticServicePrefix::default(), is_cancelled)
            .commit()
    }

    fn prepare_semantic<C: FnMut() -> bool>(
        &self,
        request: SemanticServiceRequest<'_>,
        prefix: SemanticServicePrefix,
        mut is_cancelled: C,
    ) -> PreparedSemanticReport {
        let mut work = prefix.work;
        let mut kernel_work = None;
        let mut effective_limits = None;
        let mut publication = None;
        let host = self.service().policy().semantic_service;
        let mut remaining = 0;
        let outcome = (|| {
            remaining = host
                .boundary_payload_bytes
                .min(request.limits.boundary_payload_bytes)
                .checked_sub(prefix.payload_bytes)
                .ok_or(DynamicReflectionError::PayloadByteLimit)?;
            let handle = self
                .resolve(request.handle, request.operation.right())
                .map_err(|error| match error {
                    LanguageRuntimeError::InvalidHandleShape => {
                        InstalledSemanticError::InvalidHandleShape
                    },
                    LanguageRuntimeError::UnknownHandle => InstalledSemanticError::UnknownHandle,
                    LanguageRuntimeError::Access(error) => InstalledSemanticError::Access(error),
                    LanguageRuntimeError::Poisoned => {
                        InstalledSemanticError::Access(LanguageAccessError::Poisoned)
                    },
                    _ => InstalledSemanticError::InvalidEvidence(
                        "unexpected capability resolution failure",
                    ),
                })?;
            let table = self.service().table();
            let installed = table
                .authorize_all(&handle, &[request.operation.right()])
                .map_err(InstalledSemanticError::Access)?;
            let limits = host.effective(installed.language_core().theory.limits, request.limits);
            effective_limits = Some(limits);
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                limits.execution.work,
                remaining,
                &mut is_cancelled,
            );
            let prepared = (|| {
                let SelectedSemanticOperation { action, input_sort, required } =
                    select_semantic_operation(&installed, request.operation, &mut budget)?;
                let authorized = table
                    .authorize_all(&handle, &required)
                    .map_err(InstalledSemanticError::Access)?;
                let retained = publication.insert(InstalledSemanticPublication {
                    table: Arc::clone(table),
                    handle,
                    required,
                });
                if !Arc::ptr_eq(&authorized, &installed) {
                    return Err(InstalledSemanticError::InvalidEvidence("installed owner changed"));
                }
                let bundle = InstalledSemanticBundle::prepare_authorized(
                    authorized,
                    &retained.handle,
                    &mut budget,
                )?;
                prepare_semantic_results(
                    &bundle,
                    SelectedSemanticExecution { action, input_sort },
                    request.input,
                    limits,
                    &mut budget,
                    &mut kernel_work,
                )
            })();
            remaining = budget.finish();
            prepared
        })();
        PreparedSemanticReport {
            outcome,
            publication,
            usage: SemanticServiceUsage {
                work,
                kernel_work,
                effective_limits,
                remaining_boundary_payload_bytes: remaining,
            },
        }
    }
}

fn prepare_semantic_results<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    selection: SelectedSemanticExecution<'_>,
    input: &Par,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<Vec<SemanticServiceResult>, InstalledSemanticError> {
    let installed = prepared.installed();
    let adapter = InstalledFltAdapter::new(prepared.installed(), budget)?;
    let category = adapter.input_category(selection.input_sort, budget)?;
    let input = adapter.to_kernel(
        input,
        category,
        SemanticInputLimits {
            work: limits.execution.work,
            nodes: limits.execution.term_nodes,
            bytes: limits.execution.term_bytes,
        },
        budget,
    )?;
    let admission = input.admission_work();
    budget.charge(1, 8)?; // one shared key handle, not a key/tree copy
    let expected_input = input.exact_key().clone();
    let decision = budget.run_accounted_stage(|remaining, cancel| {
        let Some(ceiling) = admission.checked_add(remaining) else {
            return (Err(InstalledSemanticError::InvalidEvidence("admission ceiling overflow")), 0);
        };
        let execution = prepared.execute_accounted(
            selection.action.id,
            input,
            SemanticTransitionLimits { work: ceiling, ..limits.execution },
            cancel,
        );
        match execution {
            Err(error) => (Err(error), 0),
            Ok((decision, aggregate)) => {
                *kernel_work = Some(aggregate);
                match aggregate.checked_sub(admission) {
                    Some(increment) => (Ok(decision), increment),
                    None => (
                        Err(InstalledSemanticError::InvalidEvidence(
                            "kernel underreported admission",
                        )),
                        0,
                    ),
                }
            },
        }
    })??;
    let proven = match decision {
        SemanticTransitionDecision::Proven(proven) => proven,
        SemanticTransitionDecision::Refuted(reason) => {
            return Err(InstalledSemanticError::Refuted(reason))
        },
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            return Err(InstalledSemanticError::Undetermined(reason))
        },
    };
    if Some(proven.work) != *kernel_work || proven.work < admission || proven.transitions.is_empty()
    {
        return Err(InstalledSemanticError::InvalidEvidence("kernel result aggregate"));
    }
    // This helper sees only the immediate fresh kernel result above, never an
    // externally supplied or mutated ProvenSemanticTransitions. The shared key
    // already has its byte cache populated by successful kernel execution.
    let expected_input = expected_input.as_bytes();
    for transition in &proven.transitions {
        validate_fresh_receipt(
            installed,
            selection.action,
            expected_input,
            proven.work,
            transition,
            budget,
        )?;
        charge_receipt_transport(&transition.receipt, budget)?;
    }
    let terms = adapter.reflect_transitions(&proven, selection.action.codomain, budget)?;
    let (_graph, transitions) = proven.into_parts();
    pair_semantic_results(terms, transitions, budget)
}

/// Whole-record move refinement of SemanticReceiptTransport.pair_results.
/// The caller owns the complete fresh kernel roster and reflected output list.
fn pair_semantic_results<C: FnMut() -> bool>(
    terms: Vec<Par>,
    transitions: Vec<SemanticTransition>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<SemanticServiceResult>, InstalledSemanticError> {
    if terms.len() != transitions.len() {
        return Err(InstalledSemanticError::InvalidEvidence("result/receipt count mismatch"));
    }
    let slots = terms
        .len()
        .checked_mul(16)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(terms.len(), slots)?;
    let mut results = Vec::new();
    results
        .try_reserve_exact(terms.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    // Vec lengths are checked above; this zip cannot discard an unmatched tail.
    for (term, transition) in terms.into_iter().zip(transitions) {
        budget.charge(1, 0)?;
        results.push(SemanticServiceResult { term, receipt: transition.receipt });
    }
    budget.charge(0, 0)?;
    Ok(results)
}

fn validate_fresh_receipt<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    action: &TheoryActionImageV1,
    expected_input: &[u8],
    aggregate: u64,
    transition: &SemanticTransition,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), InstalledSemanticError> {
    budget.charge(1, 0)?;
    budget.charge(96, 0)?;
    let receipt = &transition.receipt;
    let commitment = installed.commitment();
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    if receipt.language_fingerprint != commitment.language_fingerprint
        || receipt.theory_fingerprint != commitment.theory_fingerprint
        || Some(receipt.image_fingerprint) != commitment.semantic_image_fingerprint
        || receipt.action != action.id
        || receipt.work != aggregate
        || transition.output_sort != action.codomain
        || receipt.effect != action.effect
        || receipt.effect_class != action.effect_class
    {
        return Err(InstalledSemanticError::InvalidEvidence("receipt envelope"));
    }
    budget.charge(expected_input.len(), 0)?;
    if receipt.input != expected_input {
        return Err(InstalledSemanticError::InvalidEvidence("receipt input key"));
    }
    let mut selected_rule = false;
    for rule in &action.transitions {
        budget.charge(1, 0)?;
        if *rule == receipt.rule {
            selected_rule = true;
            break;
        }
    }
    if !selected_rule
        || !image
            .rules
            .get(receipt.rule.0 as usize)
            .is_some_and(|rule| {
                rule.id == receipt.rule && rule.disposition == TheoryRuleDispositionV1::Executable
            })
    {
        return Err(InstalledSemanticError::InvalidEvidence("receipt entry rule"));
    }
    match (image.resource_profile, &receipt.resource) {
        (TheoryResourceProfileV1::Uncosted, SemanticResourceReceipt::NoSemanticGrade) => {},
        (TheoryResourceProfileV1::Costed { .. }, _) => {
            return Err(InstalledSemanticError::Undetermined(
                SemanticMatchUndetermined::ResourceGradeUnavailable,
            ))
        },
        _ => return Err(InstalledSemanticError::InvalidEvidence("receipt resource profile")),
    }
    if matches!(action.execution, TheoryActionExecutionImageV1::OneStep)
        && !receipt.normalization_hops.is_empty()
    {
        return Err(InstalledSemanticError::InvalidEvidence("unexpected normalization hops"));
    }
    let mut previous: Option<&[u8]> = None;
    for hop in &receipt.normalization_hops {
        budget.charge(1, 0)?;
        if let Some(before) = previous {
            budget.charge(before.len(), 0)?;
            if before != hop.before {
                return Err(InstalledSemanticError::InvalidEvidence("normalization chain"));
            }
        }
        previous = Some(&hop.after);
    }
    if let Some(last) = previous {
        budget.charge(last.len(), 0)?;
        if last != receipt.output {
            return Err(InstalledSemanticError::InvalidEvidence("normalization final output"));
        }
    }
    Ok(())
}

impl SemanticOperation<'_> {
    pub(crate) fn right(self) -> LanguageRight {
        match self {
            Self::Reduce(_) => LanguageRight::Reduce,
            Self::Observe(_) => LanguageRight::Observe,
        }
    }
}

pub(crate) struct SelectedSemanticOperation<'a> {
    pub(crate) action: &'a TheoryActionImageV1,
    pub(crate) input_sort: TheorySortId,
    pub(crate) required: Vec<LanguageRight>,
}

struct SelectedSemanticExecution<'a> {
    action: &'a TheoryActionImageV1,
    input_sort: TheorySortId,
}

fn find_exact_name<'a, C: FnMut() -> bool>(
    names: impl Iterator<Item = &'a str>,
    requested: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<usize>, DynamicReflectionError> {
    budget.charge(requested.len(), 0)?;
    for (index, name) in names.enumerate() {
        budget.charge(1, 0)?;
        budget.charge(name.len(), 0)?;
        if name == requested {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

pub(crate) fn select_semantic_operation<'a, C: FnMut() -> bool>(
    installed: &'a InstalledLanguage,
    operation: SemanticOperation<'_>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SelectedSemanticOperation<'a>, InstalledSemanticError> {
    budget.charge(1, 0)?;
    let theory = &installed.language_core().theory;
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let (action_name, observation_result) = match operation {
        SemanticOperation::Reduce(name) => (name, None),
        SemanticOperation::Observe(name) => {
            let index =
                find_exact_name(theory.observations.iter().map(|o| o.name.as_str()), name, budget)?
                    .ok_or(InstalledSemanticError::UnknownObservation)?;
            let observation = &theory.observations[index];
            (observation.action.as_str(), Some(observation.result.as_str()))
        },
    };
    let index = find_exact_name(theory.actions.iter().map(|a| a.id.as_str()), action_name, budget)?
        .ok_or(InstalledSemanticError::UnknownAction)?;
    let source = &theory.actions[index];
    let action = image
        .actions
        .get(index)
        .filter(|a| a.id.0 as usize == index)
        .ok_or(InstalledSemanticError::InvalidSelection("action source/image coordinate"))?;
    budget.charge(1, 0)?;
    let ([input_sort], [input_name]) = (action.domain.as_slice(), source.domain.as_slice()) else {
        return Err(InstalledSemanticError::InvalidSelection(
            "rule-backed action must have one input",
        ));
    };
    for (sort, name) in
        [(*input_sort, input_name.as_str()), (action.codomain, source.codomain.as_str())]
    {
        budget.charge(1, 0)?;
        let source_sort = theory
            .sorts
            .get(sort.0 as usize)
            .ok_or(InstalledSemanticError::InvalidSelection("action sort coordinate"))?;
        budget.charge(source_sort.name.len(), 0)?;
        if source_sort.name != name {
            return Err(InstalledSemanticError::InvalidSelection("action sort name"));
        }
    }
    if let Some(result) = observation_result {
        budget.charge(result.len(), 0)?;
        if result != source.codomain {
            return Err(InstalledSemanticError::InvalidSelection("observation result sort"));
        }
    }
    // Rights are a closed twelve-variant set. This count is bounded by the
    // carrier, not by source text. Reserve once before collecting the slice
    // consumed by the existing table's single-lock authorize_all operation.
    let count = 1 + source.required_rights.iter().count();
    budget.charge(count, count)?;
    if action.required_rights != source.required_rights {
        return Err(InstalledSemanticError::InvalidSelection("action required rights"));
    }
    let mut required = Vec::new();
    required
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    required.push(operation.right());
    required.extend(source.required_rights.iter());
    Ok(SelectedSemanticOperation {
        action,
        input_sort: *input_sort,
        required,
    })
}

/// The matcher and its immutable source owner cannot be independently supplied.
/// This is an operation-local preparation, not authority to publish a result:
/// the service must recheck the same handle and required rights at publication.
pub(crate) struct InstalledSemanticBundle<'a> {
    installed: Arc<InstalledLanguage>,
    matcher: SemanticTransitionMatcher,
    handle: &'a InstalledLanguageHandle,
}

impl<'a> InstalledSemanticBundle<'a> {
    pub(crate) fn prepare<C: FnMut() -> bool>(
        table: &InstalledLanguageTable,
        handle: &'a InstalledLanguageHandle,
        required: &[LanguageRight],
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, InstalledSemanticError> {
        let installed = table
            .authorize_all(handle, required)
            .map_err(InstalledSemanticError::Access)?;
        Self::prepare_authorized(installed, handle, budget)
    }

    fn prepare_authorized<C: FnMut() -> bool>(
        installed: Arc<InstalledLanguage>,
        handle: &'a InstalledLanguageHandle,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, InstalledSemanticError> {
        let image = installed
            .semantic_image()
            .ok_or(InstalledSemanticError::MissingSemanticImage)?;
        charge_matcher_setup(image, budget)?;
        let matcher =
            SemanticTransitionMatcher::restore(image).map_err(InstalledSemanticError::Restore)?;
        // The existing restorer has no cancellation callback. Never expose its
        // completed preparation if cancellation arrived during restoration.
        budget.charge(0, 0)?;
        Ok(Self { installed, matcher, handle })
    }

    pub(crate) fn installed(&self) -> &Arc<InstalledLanguage> {
        &self.installed
    }

    /// This reports the kernel's aggregate, INCLUDING input admission. The
    /// outer service absorbs only the increment beyond that admitted prefix.
    /// No caller can pair this matcher with another image or amplify its grant.
    pub(crate) fn execute_accounted<C: FnMut() -> bool>(
        &self,
        action: TheoryActionId,
        input: SemanticTransitionInput,
        limits: SemanticTransitionLimits,
        is_cancelled: C,
    ) -> Result<(SemanticTransitionDecision, u64), InstalledSemanticError> {
        let image = self
            .installed
            .semantic_image()
            .ok_or(InstalledSemanticError::MissingSemanticImage)?;
        Ok(self.matcher.execute_action_accounted(
            SemanticActionExecutionRequest {
                image,
                action,
                granted_rights: self.handle.rights(),
                input,
                limits,
            },
            is_cancelled,
        ))
    }
}

/// Setup schedule v1. These are logical image coordinates/payload reservations,
/// not a second image encoding, allocator sizes, or a physical resource bound.
/// The fixed descriptor covers every operator variant, including non-positional
/// forms; only String/Bytes have variable payload. Restoration/encoding remains
/// entirely owned by the existing SemanticTransitionMatcher implementation.
fn charge_matcher_setup<C: FnMut() -> bool>(
    image: &TheorySemanticImageV1,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    charge_pattern_states(&image.patterns.states, budget)?;
    for entry in &image.patterns.entries {
        charge_pattern_entry(&entry.slot_variables, budget)?;
    }
    charge_pattern_states(&image.judgment_patterns.states, budget)?;
    for entry in &image.judgment_patterns.entries {
        charge_pattern_entry(&entry.slot_variables, budget)?;
    }
    budget.charge(0, 0)
}

fn charge_pattern_states<C: FnMut() -> bool>(
    states: &[TheoryPatternStateV1],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    // Two 64-bit roster counts; charged even for an empty automaton.
    budget.charge(1, 16)?;
    for state in states {
        // id, slot count, form tag, argument count (4 + 4 + 1 + 8).
        budget.charge(1, 17)?;
        if let TheoryPatternStateFormV1::Apply { operator, arguments } = &state.form {
            budget.charge(1, 32)?;
            let payload = match operator {
                TheoryImageOperatorV1::Literal { value: TheoryLiteralV1::String(s), .. } => s.len(),
                TheoryImageOperatorV1::Literal { value: TheoryLiteralV1::Bytes(b), .. } => b.len(),
                _ => 0,
            };
            budget.charge(payload, payload)?;
            for invocation in arguments {
                budget.charge(1, 12)?; // target coordinate and slot count
                for _ in &invocation.parent_slots {
                    budget.charge(1, 4)?;
                }
            }
        }
    }
    Ok(())
}

fn charge_pattern_entry<C: FnMut() -> bool>(
    variables: &[TheoryVariableId],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    budget.charge(1, 20)?; // id, rule, root, 64-bit slot count
    for _ in variables {
        // u32 coordinate + length + at most eleven UTF-8 bytes for "v{u32}".
        // A fixed maximum avoids allocating or formatting in the planning pass.
        budget.charge(12, 23)?;
    }
    Ok(())
}

/// Receipt export schedule v1, matching SemanticReceiptTransport.receipt_events.
/// This borrows the whole fresh receipt; it neither clones evidence nor encodes
/// the future wire reply. Finite nesting uses bounded loops, not recursive calls.
fn charge_receipt_transport<C: FnMut() -> bool>(
    receipt: &SemanticTransitionReceipt,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    budget.charge(1, 117)?; // fingerprints, action/rule/effect, class, work
    charge_receipt_payload(&receipt.input, budget)?;
    charge_receipt_payload(&receipt.output, budget)?;
    match &receipt.resource {
        SemanticResourceReceipt::NoSemanticGrade => budget.charge(1, 1)?,
        SemanticResourceReceipt::Checked { grade, .. } => {
            budget.charge(1, 37)?; // tag, sort, cost-image commitment
            charge_receipt_payload(grade, budget)?;
        },
    }
    charge_receipt_premises(&receipt.premises, budget)?;
    budget.charge(1, 8)?; // hop count
    for hop in &receipt.normalization_hops {
        budget.charge(1, 8)?; // hop's work is data, not another execution charge
        charge_receipt_payload(&hop.before, budget)?;
        charge_receipt_payload(&hop.after, budget)?;
        budget.charge(1, 8)?; // exhaustive proof count
        for proof in &hop.exhaustive_proofs {
            budget.charge(1, 4)?;
            charge_receipt_payload(&proof.before, budget)?;
            charge_receipt_payload(&proof.after, budget)?;
            charge_receipt_premises(&proof.premises, budget)?;
        }
    }
    Ok(())
}

fn charge_receipt_payload<C: FnMut() -> bool>(
    bytes: &[u8],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    let work = bytes
        .len()
        .checked_add(1)
        .ok_or(DynamicReflectionError::WorkLimit)?;
    let payload = bytes
        .len()
        .checked_add(8)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(work, payload)
}

fn charge_receipt_premises<C: FnMut() -> bool>(
    premises: &[SemanticPremiseReceipt],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), DynamicReflectionError> {
    budget.charge(1, 8)?;
    for premise in premises {
        budget.charge(1, 9)?; // tag, owning rule, premise coordinate
        match premise {
            SemanticPremiseReceipt::Freshness { .. } => {},
            SemanticPremiseReceipt::Transition { .. } | SemanticPremiseReceipt::ForAll { .. } => {
                budget.charge(1, 4)?;
            },
            SemanticPremiseReceipt::Judgment { .. } => budget.charge(1, 12)?,
            SemanticPremiseReceipt::Guard { .. } => budget.charge(1, 64)?,
            SemanticPremiseReceipt::Intrinsic { receipt, .. } => {
                budget.charge(1, 9)?; // opcode and intrinsic-local work
                for keys in [&receipt.inputs, &receipt.outputs] {
                    budget.charge(1, 8)?;
                    for key in keys {
                        charge_receipt_payload(key, budget)?;
                    }
                }
            },
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use mettail_dovetail_runtime::{
        SemanticIntrinsicOpcodeV1, SemanticIntrinsicReceiptV1, SemanticNormalizationHopReceiptV1,
        SemanticNormalizationStepReceiptV1,
    };
    use mettail_grammar_core::{
        CollectionKind, PathMapModeV1, SemanticEffectClassV1, TheoryConstructorId, TheoryEffectId,
        TheoryJudgmentId, TheoryJudgmentPatternAutomatonV1, TheoryJudgmentPatternEntryV1,
        TheoryJudgmentRuleProgramId, TheoryPatternAutomatonV1, TheoryPatternEntryId,
        TheoryPatternEntryV1, TheoryPatternInvocationV1, TheoryPatternStateId,
        TheoryResourceProfileV1, TheoryRuleProgramId, TheorySortId,
    };

    #[test]
    fn semantic_service_preparation_preserves_wire_prefixes_and_delays_publication() {
        use mettail_grammar_core::RuntimeTemplatePiece;
        use std::collections::BTreeMap;

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let input = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("actual installed guest parser");
        let request = |limits| SemanticServiceRequest {
            handle: &token,
            operation: SemanticOperation::Reduce("expand-plus"),
            input: &input,
            limits,
        };
        let baseline =
            runtime.execute_semantic(request(SemanticServiceLimits::default()), || false);
        let baseline_results = baseline.outcome.expect("baseline reduction");
        let payload = baseline
            .effective_limits
            .expect("effective limits")
            .boundary_payload_bytes
            - baseline.remaining_boundary_payload_bytes;
        let mut limits = SemanticServiceLimits::default();
        limits.execution.work = baseline.work + 7;
        limits.boundary_payload_bytes = payload + 11;
        let prefix = || SemanticServicePrefix { work: 7, payload_bytes: 11 };
        let prepared = runtime.prepare_semantic(request(limits), prefix(), || false);
        assert_eq!(prepared.usage.work, baseline.work + 7);
        assert_eq!(prepared.usage.kernel_work, baseline.kernel_work);
        assert_eq!(prepared.usage.remaining_boundary_payload_bytes, 0);
        let results = prepared.commit().outcome.expect("commit");
        assert_eq!(results.len(), baseline_results.len());
        for (actual, expected) in results.iter().zip(&baseline_results) {
            assert_eq!(actual.term, expected.term);
            assert_eq!(actual.receipt, expected.receipt);
        }

        for (work_delta, byte_delta, expected) in [
            (1, 0, DynamicReflectionError::WorkLimit),
            (0, 1, DynamicReflectionError::PayloadByteLimit),
        ] {
            let mut short = limits;
            short.execution.work -= work_delta;
            short.boundary_payload_bytes -= byte_delta;
            let rejected = runtime.prepare_semantic(request(short), prefix(), || false);
            assert!(matches!(rejected.outcome,
                Err(InstalledSemanticError::Resource(actual)) if actual == expected));
            assert!(rejected.usage.work >= 7 && rejected.usage.work <= short.execution.work);
            assert_eq!(rejected.usage.kernel_work, baseline.kernel_work);
            assert!(rejected.publication.is_some(), "late failure retains full authority context");
        }

        let mut overdrawn = limits;
        overdrawn.boundary_payload_bytes = 10;
        let rejected = runtime.prepare_semantic(request(overdrawn), prefix(), || {
            panic!("overdrawn payload must fail before preparation")
        });
        assert!(matches!(
            rejected.outcome,
            Err(InstalledSemanticError::Resource(DynamicReflectionError::PayloadByteLimit))
        ));
        assert_eq!(rejected.usage.work, 7);
        assert_eq!(rejected.usage.remaining_boundary_payload_bytes, 0);
        assert_eq!(rejected.usage.kernel_work, None);

        overdrawn = limits;
        overdrawn.execution.work = 6;
        let rejected = runtime.prepare_semantic(request(overdrawn), prefix(), || false);
        assert!(matches!(
            rejected.outcome,
            Err(InstalledSemanticError::Resource(DynamicReflectionError::WorkLimit))
        ));
        assert_eq!(rejected.usage.work, 7, "retain, do not reset or saturate the prior usage");
        assert_eq!(rejected.usage.kernel_work, None);

        let cancelled = runtime.prepare_semantic(request(limits), prefix(), || true);
        assert!(matches!(
            cancelled.outcome,
            Err(InstalledSemanticError::Resource(DynamicReflectionError::Cancelled))
        ));
        assert_eq!(cancelled.usage.work, 7);
        assert_eq!(cancelled.usage.remaining_boundary_payload_bytes, payload);
        assert_eq!(cancelled.usage.kernel_work, None);
        assert!(cancelled.publication.is_none(), "selection never completed");

        let pending = runtime.prepare_semantic(request(limits), prefix(), || false);
        assert!(pending.outcome.is_ok(), "private prepared results");
        assert_eq!(pending.usage.kernel_work, baseline.kernel_work);
        runtime
            .revoke(&token)
            .expect("preparation retains no authority lock");
        assert!(matches!(
            pending.commit().outcome,
            Err(InstalledSemanticError::Access(LanguageAccessError::StaleHandle))
        ));
    }

    #[test]
    fn semantic_service_retains_context_before_setup_but_not_before_full_authorization() {
        use crate::language_install::tests::MemoryRegistry;
        use crate::language_install::{
            InstallCandidate, LanguageInstallPolicy, LanguageInstallService,
            LANGUAGE_CAPABILITY_ABI_V1,
        };
        use mettail_grammar_core::{LanguageRights, RuntimePolicy, RuntimeTemplatePiece};
        use std::collections::BTreeMap;

        let (runtime, token, installed) =
            crate::language_install::tests::installed_flt_adapter_fixture();
        let input = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("actual guest parser");
        let operation = SemanticOperation::Reduce("expand-plus");
        let mut work = 7;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let selected =
            select_semantic_operation(&installed, operation, &mut budget).expect("selection");
        let selection_bytes = 1_000_000 - budget.finish();
        let mut limits = SemanticServiceLimits::default();
        limits.execution.work = work;
        let report = runtime.prepare_semantic(
            SemanticServiceRequest {
                handle: &token,
                operation,
                input: &input,
                limits,
            },
            SemanticServicePrefix { work: 7, payload_bytes: 11 },
            || false,
        );
        assert_eq!(
            report.outcome.unwrap_err(),
            InstalledSemanticError::Resource(DynamicReflectionError::WorkLimit)
        );
        let retained = report
            .publication
            .expect("context retained before setup fails");
        assert_eq!(retained.required, selected.required);
        assert_eq!(report.usage.work, work);
        assert_eq!(report.usage.kernel_work, None);
        assert_eq!(
            report.usage.remaining_boundary_payload_bytes,
            limits.boundary_payload_bytes - 11 - selection_bytes
        );

        let report = runtime.prepare_semantic(
            SemanticServiceRequest {
                handle: &token,
                operation: SemanticOperation::Reduce("not-an-action"),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            SemanticServicePrefix::default(),
            || false,
        );
        assert_eq!(report.outcome.unwrap_err(), InstalledSemanticError::UnknownAction);
        assert!(report.publication.is_none());
        assert_eq!(report.usage.kernel_work, None);

        let value = mettail_elab::core_value::language_core_to_value(installed.language_core())
            .expect("canonical source");
        let attenuated = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::new(
                LanguageRights::from_rights([
                    LanguageRight::Parse,
                    LanguageRight::Construct,
                    LanguageRight::Observe,
                ]),
                RuntimePolicy::default(),
                LANGUAGE_CAPABILITY_ABI_V1,
            ),
        )));
        let other = attenuated
            .install(InstallCandidate::Canonical(value))
            .expect("attenuated installation");
        let report = attenuated.prepare_semantic(
            SemanticServiceRequest {
                handle: &other,
                operation: SemanticOperation::Observe("ExpandedPlus"),
                input: &input,
                limits: SemanticServiceLimits::default(),
            },
            SemanticServicePrefix::default(),
            || false,
        );
        assert_eq!(
            report.outcome.unwrap_err(),
            InstalledSemanticError::Access(LanguageAccessError::MissingRight(
                LanguageRight::Reduce
            ))
        );
        assert!(report.publication.is_none(), "operation right alone is insufficient");
        assert_eq!(report.usage.kernel_work, None);
    }

    #[test]
    fn semantic_service_negative_context_rechecks_authority_without_changing_typed_error() {
        use mettail_grammar_core::RuntimeTemplatePiece;
        use rspace_plus_plus::rspace::rspace_interface::commit_produce;
        use std::collections::BTreeMap;

        for undetermined in [false, true] {
            let (runtime, token, _) =
                crate::language_install::tests::installed_flt_adapter_fixture();
            let source = if undetermined { "a+" } else { "a" };
            let input = runtime
                .construct_template(
                    &token,
                    &[RuntimeTemplatePiece::Text(source.into())],
                    &[],
                    Some("Pattern"),
                    &BTreeMap::new(),
                )
                .expect("actual guest parser");
            let mut limits = SemanticServiceLimits::default();
            if undetermined {
                limits.execution.outputs = 0;
            }
            let report = runtime.prepare_semantic(
                SemanticServiceRequest {
                    handle: &token,
                    operation: SemanticOperation::Reduce("expand-plus"),
                    input: &input,
                    limits,
                },
                SemanticServicePrefix::default(),
                || false,
            );
            let error = report
                .outcome
                .as_ref()
                .expect_err("negative judgment")
                .clone();
            if undetermined {
                assert!(matches!(error, InstalledSemanticError::Undetermined(_)), "{error:?}");
            } else {
                assert_eq!(
                    error,
                    InstalledSemanticError::Refuted(SemanticMatchRefutation::NoTransition)
                );
            }
            let retained = report
                .publication
                .as_ref()
                .expect("negative retains publication context");
            assert!(retained.required.contains(&LanguageRight::Reduce));
            assert!(report
                .usage
                .kernel_work
                .is_some_and(|w| w > 0 && w < report.usage.work));
            let mut calls = 0;
            assert_eq!(commit_produce(Some(retained), || calls += 1), Ok(()));
            assert_eq!(calls, 1);
            runtime
                .revoke(&token)
                .expect("context holds no registry lock");
            assert_eq!(
                commit_produce(Some(retained), || calls += 1),
                Err(RSpaceError::ProduceCommitDenied)
            );
            assert_eq!(calls, 1, "revoked negative cannot mutate");
            let work = report.usage.work;
            let kernel = report.usage.kernel_work;
            let typed = report.commit();
            assert_eq!(
                typed.outcome.unwrap_err(),
                error,
                "typed negative is not replaced by a stale-handle error"
            );
            assert_eq!((typed.work, typed.kernel_work), (work, kernel));
        }
    }

    #[test]
    fn semantic_service_publication_rechecks_every_required_right_and_table_identity() {
        use mettail_grammar_core::LanguageRights;
        use rspace_plus_plus::rspace::rspace_interface::commit_produce;

        let (runtime, token, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("installed handle");
        let required = vec![LanguageRight::Reduce, LanguageRight::ReflectAst];
        let mut publication = InstalledSemanticPublication {
            table: Arc::clone(runtime.service().table()),
            handle: handle.attenuate(&LanguageRights::from_rights([LanguageRight::Reduce])),
            required,
        };
        let mut calls = 0;
        assert_eq!(
            commit_produce(Some(&publication), || calls += 1),
            Err(RSpaceError::ProduceCommitDenied)
        );
        assert_eq!(calls, 0, "the operation right alone cannot authorize reflection");

        publication.handle = handle;
        assert_eq!(commit_produce(Some(&publication), || calls += 1), Ok(()));
        assert_eq!(calls, 1);

        let (foreign, _, _) = crate::language_install::tests::installed_flt_adapter_fixture();
        publication.table = Arc::clone(foreign.service().table());
        assert_eq!(
            commit_produce(Some(&publication), || calls += 1),
            Err(RSpaceError::ProduceCommitDenied)
        );
        assert_eq!(calls, 1, "an identical language in another table is not authority");

        publication.table = Arc::clone(runtime.service().table());
        runtime
            .revoke(&token)
            .expect("no authority lock retained after commit");
        assert_eq!(
            commit_produce(Some(&publication), || calls += 1),
            Err(RSpaceError::ProduceCommitDenied)
        );
        assert_eq!(calls, 1, "a previous successful commit cannot renew stale authority");
    }

    #[tokio::test]
    async fn semantic_service_publication_guards_actual_matched_and_unmatched_space_mutation() {
        use models::rhoapi::{
            tagged_continuation::TaggedCont, BindPattern, ListParWithRandom, TaggedContinuation,
        };
        use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par};
        use rspace_plus_plus::rspace::rspace_interface::ISpace;
        use std::collections::BTreeSet;

        for matched in [false, true] {
            for revoke_before_poll in [false, true] {
                let (runtime, token, _) =
                    crate::language_install::tests::installed_flt_adapter_fixture();
                let publication = InstalledSemanticPublication {
                    table: Arc::clone(runtime.service().table()),
                    handle: runtime
                        .resolve(&token, LanguageRight::Reduce)
                        .expect("handle"),
                    required: vec![LanguageRight::Reduce, LanguageRight::ReflectAst],
                };
                let space = crate::speculation::publication_tests::new_space().await;
                let channel = new_gstring_par("semantic-publication".into(), Vec::new(), false);
                let data = ListParWithRandom {
                    pars: vec![new_gint_par(42, Vec::new(), false)],
                    random_state: vec![7; 32],
                };
                if matched {
                    space
                        .consume(
                            vec![channel.clone()],
                            vec![BindPattern {
                                patterns: vec![new_freevar_par(0, Vec::new())],
                                remainder: None,
                                free_count: 1,
                            }],
                            TaggedContinuation {
                                tagged_cont: Some(TaggedCont::ScalaBodyRef(777)),
                                guard: None,
                            },
                            false,
                            BTreeSet::new(),
                        )
                        .await
                        .expect("waiting receiver");
                }
                let pending =
                    space.produce_guarded(channel.clone(), data.clone(), false, &publication);
                if revoke_before_poll {
                    runtime
                        .revoke(&token)
                        .expect("revoke after future creation");
                }
                let result = pending.await;
                if revoke_before_poll {
                    assert_eq!(
                        result.expect_err("stale authority"),
                        RSpaceError::ProduceCommitDenied
                    );
                    assert!(space.get_data(&channel).await.is_empty());
                    assert_eq!(
                        space
                            .get_waiting_continuations(vec![channel.clone()])
                            .await
                            .len(),
                        usize::from(matched),
                    );
                } else {
                    let result = result.expect("authorized actual publication");
                    assert_eq!(result.is_some(), matched);
                    if let Some((_, results, _)) = result {
                        assert_eq!(results.len(), 1);
                        assert_eq!(results[0].matched_datum, data);
                    } else {
                        let stored = space.get_data(&channel).await;
                        assert_eq!(stored.len(), 1);
                        assert_eq!(*stored[0].a, data);
                    }
                    runtime
                        .revoke(&token)
                        .expect("release before later revocation");
                }
                assert_eq!(
                    space
                        .produce_guarded(channel.clone(), data, false, &publication)
                        .await
                        .expect_err("revoked next reply"),
                    RSpaceError::ProduceCommitDenied,
                );
            }
        }
    }

    fn installed_transition_fixture() -> (Arc<InstalledLanguage>, SemanticTransition) {
        use mettail_grammar_core::RuntimeTemplatePiece;
        use std::collections::BTreeMap;
        let (runtime, token, installed) =
            crate::language_install::tests::installed_flt_adapter_fixture();
        let reflected = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("actual installed guest parser");
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("reduce authority");
        let mut work = 0;
        let mut cancel = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
        let bundle = InstalledSemanticBundle::prepare(
            runtime.service().table(),
            &handle,
            &[LanguageRight::Reduce],
            &mut budget,
        )
        .expect("same-owner bundle");
        let selected = select_semantic_operation(
            &installed,
            SemanticOperation::Reduce("expand-plus"),
            &mut budget,
        )
        .expect("exact action");
        let adapter =
            InstalledFltAdapter::new(&installed, &mut budget).expect("same-owner adapter");
        let category = adapter
            .input_category(selected.input_sort, &mut budget)
            .expect("input category");
        let input = adapter
            .to_kernel(
                &reflected,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000,
                },
                &mut budget,
            )
            .expect("structural input");
        let (decision, _) = bundle
            .execute_accounted(
                selected.action.id,
                input,
                installed.language_core().theory.limits.into(),
                || false,
            )
            .expect("existing kernel");
        let SemanticTransitionDecision::Proven(proven) = decision else {
            panic!("fixture reduction")
        };
        let (_, mut transitions) = proven.into_parts();
        assert_eq!(transitions.len(), 1);
        (installed, transitions.pop().expect("one transition"))
    }

    #[test]
    fn semantic_service_checks_every_fresh_receipt_envelope_coordinate() {
        let (installed, transition) = installed_transition_fixture();
        let action = &installed.semantic_image().expect("image").actions[0];
        let validate = |candidate: &SemanticTransition| {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
            validate_fresh_receipt(
                &installed,
                action,
                &transition.receipt.input,
                transition.receipt.work,
                candidate,
                &mut budget,
            )
        };
        assert_eq!(validate(&transition), Ok(()));
        // Mutation is deliberately confined to this private check test. The
        // production helper accepts only its own immediate kernel result.
        let mutations: &[fn(&mut SemanticTransition)] = &[
            |t| t.receipt.language_fingerprint[0] ^= 1,
            |t| t.receipt.theory_fingerprint[0] ^= 1,
            |t| t.receipt.image_fingerprint[0] ^= 1,
            |t| t.receipt.action = TheoryActionId(u32::MAX),
            |t| t.receipt.work += 1,
            |t| t.output_sort = TheorySortId(u32::MAX),
            |t| t.receipt.effect = TheoryEffectId(u32::MAX),
            |t| t.receipt.effect_class = SemanticEffectClassV1::External,
            |t| t.receipt.input.push(0),
            |t| t.receipt.rule = TheoryRuleProgramId(u32::MAX),
            |t| {
                t.receipt.resource = SemanticResourceReceipt::Checked {
                    grade_sort: TheorySortId(0),
                    grade: vec![],
                    cost_image_fingerprint: [0; 32],
                }
            },
            |t| t.receipt.normalization_hops = transport_receipt().normalization_hops,
        ];
        for (index, mutate) in mutations.iter().enumerate() {
            let mut candidate = transition.clone();
            mutate(&mut candidate);
            assert!(
                matches!(validate(&candidate), Err(InstalledSemanticError::InvalidEvidence(_))),
                "mutation {index} must fail before export"
            );
        }
    }

    #[test]
    fn semantic_service_normalization_chain_starts_after_the_entry_rewrite() {
        let (installed, mut transition) = installed_transition_fixture();
        let mut action = installed.semantic_image().expect("image").actions[0].clone();
        action.execution = TheoryActionExecutionImageV1::Normalize {
            relation_sort: action.codomain,
            terminal_constructors: vec![],
            branching: mettail_grammar_core::SemanticNormalizationBranchingV1::FairAllNormalForms,
        };
        let validate = |candidate: &SemanticTransition| {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancel);
            validate_fresh_receipt(
                &installed,
                &action,
                &candidate.receipt.input,
                candidate.receipt.work,
                candidate,
                &mut budget,
            )
        };
        assert_eq!(validate(&transition), Ok(()), "zero-hop terminal is permitted");
        let synthetic = transport_receipt();
        transition.receipt.output = synthetic.output;
        transition.receipt.normalization_hops = synthetic.normalization_hops;
        assert_ne!(transition.receipt.normalization_hops[0].before, transition.receipt.input);
        assert_eq!(validate(&transition), Ok(()), "chain check is not a second proof verifier");
        let mut broken = transition.clone();
        broken.receipt.normalization_hops[1].before.push(0);
        assert_eq!(
            validate(&broken),
            Err(InstalledSemanticError::InvalidEvidence("normalization chain"))
        );
        broken = transition;
        broken.receipt.output.push(0);
        assert_eq!(
            validate(&broken),
            Err(InstalledSemanticError::InvalidEvidence("normalization final output"))
        );
    }

    #[test]
    fn semantic_service_pairs_whole_receipts_and_never_returns_a_partial_prefix() {
        let (_, mut transition) = installed_transition_fixture();
        // Every nested field, repeated proof and intrinsic key is retained by
        // transport; this test does not assert semantic validity of synthesis.
        transition.receipt = transport_receipt();
        let mut distinct = transition.clone();
        distinct.receipt.rule = TheoryRuleProgramId(42);
        let transitions = vec![transition.clone(), distinct, transition];
        let terms = vec![
            Par::default(),
            models::rust::utils::new_gint_par(7, Vec::new(), false),
            Par::default(),
        ];
        for (limit, bytes, expected) in [
            (6, 48, None),
            (5, 48, Some(DynamicReflectionError::WorkLimit)),
            (6, 47, Some(DynamicReflectionError::PayloadByteLimit)),
        ] {
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, limit, bytes, &mut cancel);
            let paired = pair_semantic_results(terms.clone(), transitions.clone(), &mut budget);
            match expected {
                None => {
                    let paired = paired.expect("complete pairing");
                    assert_eq!(paired.len(), 3, "retain duplicates and distinct ordered entries");
                    for (index, result) in paired.iter().enumerate() {
                        assert_eq!(result.term, terms[index]);
                        assert_eq!(result.receipt, transitions[index].receipt);
                    }
                    assert_eq!(budget.work_used(), 6);
                    assert_eq!(budget.remaining_bytes(), 0);
                },
                Some(expected) => assert!(matches!(paired,
                    Err(InstalledSemanticError::Resource(actual)) if actual == expected)),
            }
        }
        for (term_count, receipt_count) in [(0, 1), (1, 0), (1, 2), (2, 1)] {
            let mut work = 0;
            let mut cancel = || panic!("mismatch must fail before pairing allocation");
            let mut budget = ReflectedCodecBudget::new(&mut work, 6, 48, &mut cancel);
            assert!(matches!(
                pair_semantic_results(
                    terms[..term_count].to_vec(),
                    transitions[..receipt_count].to_vec(),
                    &mut budget,
                ),
                Err(InstalledSemanticError::InvalidEvidence("result/receipt count mismatch"))
            ));
        }
        for stop in 1..=5 {
            let mut work = 0;
            let mut calls = 0;
            let mut cancel = || {
                calls += 1;
                calls == stop
            };
            let mut budget = ReflectedCodecBudget::new(&mut work, 6, 48, &mut cancel);
            assert!(matches!(
                pair_semantic_results(terms.clone(), transitions.clone(), &mut budget),
                Err(InstalledSemanticError::Resource(DynamicReflectionError::Cancelled))
            ));
        }
    }

    pub(crate) fn transport_receipt() -> SemanticTransitionReceipt {
        let rule = TheoryRuleProgramId(9); // nested premise, not the entry rule
        let premises = vec![
            SemanticPremiseReceipt::Freshness { rule, premise: 0 },
            SemanticPremiseReceipt::Transition {
                rule,
                premise: 1,
                child_rule: TheoryRuleProgramId(10),
            },
            SemanticPremiseReceipt::Judgment {
                rule,
                premise: 2,
                judgment: TheoryJudgmentId(3),
                proofs: 4,
                proof_steps: 5,
            },
            SemanticPremiseReceipt::ForAll { rule, premise: 3, elements: 6 },
            SemanticPremiseReceipt::Intrinsic {
                rule,
                premise: 4,
                receipt: SemanticIntrinsicReceiptV1 {
                    opcode: SemanticIntrinsicOpcodeV1::Utf8Slice,
                    inputs: vec![vec![1, 2], vec![]],
                    outputs: vec![vec![3]],
                    work: u64::MAX,
                },
            },
            SemanticPremiseReceipt::Guard {
                rule,
                premise: 5,
                guard_commitment: [6; 32],
                evidence_commitment: [7; 32],
            },
        ];
        let first = SemanticNormalizationStepReceiptV1 {
            rule: TheoryRuleProgramId(11),
            before: vec![1, 2, 3, 4],
            after: vec![2, 3, 4],
            premises: premises.clone(),
        };
        let second = SemanticNormalizationStepReceiptV1 {
            rule: TheoryRuleProgramId(12),
            before: vec![2, 3, 4],
            after: vec![3, 4, 5],
            premises: premises.clone(),
        };
        SemanticTransitionReceipt {
            language_fingerprint: [1; 32],
            theory_fingerprint: [2; 32],
            image_fingerprint: [3; 32],
            action: TheoryActionId(0),
            rule: TheoryRuleProgramId(1),
            input: vec![1, 2],
            output: vec![3, 4, 5],
            effect: TheoryEffectId(0),
            effect_class: SemanticEffectClassV1::Pure,
            resource: SemanticResourceReceipt::NoSemanticGrade,
            premises,
            normalization_hops: vec![
                SemanticNormalizationHopReceiptV1 {
                    before: first.before.clone(),
                    after: first.after.clone(),
                    exhaustive_proofs: vec![first.clone(), first],
                    charged_work: u64::MAX,
                },
                SemanticNormalizationHopReceiptV1 {
                    before: second.before.clone(),
                    after: second.after.clone(),
                    exhaustive_proofs: vec![second.clone(), second],
                    charged_work: u64::MAX,
                },
            ],
            work: u64::MAX,
        }
    }

    #[test]
    fn semantic_service_receipt_walk_covers_all_evidence_without_recharging_execution() {
        let mut receipt = transport_receipt();
        // Includes two hops, two proofs per hop, all six premise variants in
        // the top receipt AND each proof, empty and nonempty intrinsic keys.
        // The first hop deliberately starts after the entry rewrite.
        assert_ne!(receipt.normalization_hops[0].before, receipt.input);
        for (resource, expected_work, expected_bytes) in [
            (SemanticResourceReceipt::NoSemanticGrade, 169, 1320),
            (
                SemanticResourceReceipt::Checked {
                    grade_sort: TheorySortId(4),
                    grade: vec![5; 5],
                    cost_image_fingerprint: [6; 32],
                },
                175,
                1369,
            ),
        ] {
            receipt.resource = resource;
            let mut work = 7;
            let mut checkpoints = 0;
            let mut cancel = || {
                checkpoints += 1;
                false
            };
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                7 + expected_work,
                expected_bytes,
                &mut cancel,
            );
            charge_receipt_transport(&receipt, &mut budget).expect("complete receipt walk");
            assert_eq!(budget.work_used(), 7 + expected_work);
            assert_eq!(budget.remaining_bytes(), 0);
            budget.finish();
            for (limit, bytes, expected) in [
                (7 + expected_work - 1, expected_bytes, DynamicReflectionError::WorkLimit),
                (7 + expected_work, expected_bytes - 1, DynamicReflectionError::PayloadByteLimit),
            ] {
                let mut work = 7;
                let mut cancel = || false;
                let mut budget = ReflectedCodecBudget::new(&mut work, limit, bytes, &mut cancel);
                assert_eq!(charge_receipt_transport(&receipt, &mut budget), Err(expected));
            }
            for stop in 1..=checkpoints {
                let mut work = 7;
                let mut calls = 0;
                let mut cancel = || {
                    calls += 1;
                    calls == stop
                };
                let mut budget = ReflectedCodecBudget::new(
                    &mut work,
                    7 + expected_work,
                    expected_bytes,
                    &mut cancel,
                );
                assert_eq!(
                    charge_receipt_transport(&receipt, &mut budget),
                    Err(DynamicReflectionError::Cancelled)
                );
                assert!(budget.work_used() < 7 + expected_work);
                assert!(budget.remaining_bytes() > 0);
            }
            // Neither the aggregate nor the hop/intrinsic counters are added
            // again; only their fixed-width field reservation contributes.
            receipt.work = 1;
            for hop in &mut receipt.normalization_hops {
                hop.charged_work = 1;
            }
            let mut work = 7;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                7 + expected_work,
                expected_bytes,
                &mut cancel,
            );
            charge_receipt_transport(&receipt, &mut budget)
                .expect("same field sizes regardless of recorded work");
            assert_eq!(budget.work_used(), 7 + expected_work);
            assert_eq!(budget.remaining_bytes(), 0);
        }
    }

    // This fixture tests the setup schedule, not semantic-image admission.
    // Both rosters deliberately have the same shape, with a three-byte literal.
    fn setup_image() -> TheorySemanticImageV1 {
        let states = vec![
            TheoryPatternStateV1 {
                id: TheoryPatternStateId(0),
                slot_count: 1,
                form: TheoryPatternStateFormV1::Bind,
            },
            TheoryPatternStateV1 {
                id: TheoryPatternStateId(1),
                slot_count: 1,
                form: TheoryPatternStateFormV1::Apply {
                    operator: TheoryImageOperatorV1::Literal {
                        sort: TheorySortId(0),
                        value: TheoryLiteralV1::String("λ\0".into()),
                    },
                    arguments: vec![TheoryPatternInvocationV1 {
                        state: TheoryPatternStateId(0),
                        parent_slots: vec![0],
                    }],
                },
            },
        ];
        TheorySemanticImageV1 {
            abi: 0,
            compiler_abi: 0,
            primitive_substrate_abi: 0,
            language_fingerprint: [0; 32],
            grammar_fingerprint: [0; 32],
            theory_fingerprint: [0; 32],
            resource_profile: TheoryResourceProfileV1::Uncosted,
            sorts: vec![],
            constructors: vec![],
            rules: vec![],
            judgments: vec![],
            judgment_rules: vec![],
            actions: vec![],
            patterns: TheoryPatternAutomatonV1 {
                states: states.clone(),
                entries: vec![TheoryPatternEntryV1 {
                    id: TheoryPatternEntryId(0),
                    rule: TheoryRuleProgramId(0),
                    root: TheoryPatternStateId(1),
                    slot_variables: vec![TheoryVariableId(u32::MAX)],
                }],
            },
            judgment_patterns: TheoryJudgmentPatternAutomatonV1 {
                states,
                entries: vec![TheoryJudgmentPatternEntryV1 {
                    id: TheoryPatternEntryId(0),
                    rule: TheoryJudgmentRuleProgramId(0),
                    root: TheoryPatternStateId(1),
                    slot_variables: vec![TheoryVariableId(0)],
                }],
            },
        }
    }

    #[test]
    fn semantic_service_setup_preserves_exact_prefix_and_charges_both_automata() {
        let image = setup_image();
        for (limit, bytes, expected) in [
            (51, 288, Ok(())),
            (50, 288, Err(DynamicReflectionError::WorkLimit)),
            (51, 287, Err(DynamicReflectionError::PayloadByteLimit)),
            (7, 288, Err(DynamicReflectionError::WorkLimit)),
        ] {
            let mut work = 7;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, limit, bytes, &mut cancel);
            let result = charge_matcher_setup(&image, &mut budget);
            assert_eq!(result, expected);
            if result.is_ok() {
                assert_eq!(budget.work_used(), 51);
                assert_eq!(budget.remaining_bytes(), 0);
            }
        }
        // Every cancellation checkpoint preserves precisely the accepted prefix.
        let charges =
            [(1, 16), (1, 17), (1, 17), (1, 32), (3, 3), (1, 12), (1, 4), (1, 20), (12, 23)];
        let events: Vec<(u64, usize)> =
            charges.into_iter().chain(charges).chain([(0, 0)]).collect();
        for stop in 0..events.len() {
            let mut calls = 0;
            let mut cancel = || {
                let current = calls;
                calls += 1;
                current == stop
            };
            let mut work = 7;
            let mut budget = ReflectedCodecBudget::new(&mut work, 51, 288, &mut cancel);
            assert_eq!(
                charge_matcher_setup(&image, &mut budget),
                Err(DynamicReflectionError::Cancelled)
            );
            assert_eq!(budget.work_used(), 7 + events[..stop].iter().map(|c| c.0).sum::<u64>());
            assert_eq!(
                budget.remaining_bytes(),
                288 - events[..stop].iter().map(|c| c.1).sum::<usize>()
            );
        }
    }

    #[test]
    fn semantic_service_setup_accepts_all_operator_forms_without_an_encoding_fork() {
        let sort = TheorySortId(0);
        let operators = vec![
            TheoryImageOperatorV1::Constructor(TheoryConstructorId(0)),
            TheoryImageOperatorV1::Abstraction { sort },
            TheoryImageOperatorV1::Substitution { sort, function: sort },
            TheoryImageOperatorV1::Collection {
                sort,
                element: sort,
                kind: CollectionKind::Map,
            },
            TheoryImageOperatorV1::Product { sort },
            TheoryImageOperatorV1::Judgment { judgment: TheoryJudgmentId(0) },
            TheoryImageOperatorV1::PathMapMode { sort, mode: PathMapModeV1::Map },
        ];
        let literals = [
            TheoryLiteralV1::String("λ\0".into()),
            TheoryLiteralV1::Bytes(vec![0, 255, 1]),
            TheoryLiteralV1::Integer(i128::MIN),
            TheoryLiteralV1::FloatBits(u64::MAX),
            TheoryLiteralV1::Boolean(true),
            TheoryLiteralV1::Unit,
        ];
        for operator in operators.into_iter().chain(
            literals
                .into_iter()
                .map(|value| TheoryImageOperatorV1::Literal { sort, value }),
        ) {
            let payload = match &operator {
                TheoryImageOperatorV1::Literal {
                    value: TheoryLiteralV1::String(_) | TheoryLiteralV1::Bytes(_),
                    ..
                } => 3,
                _ => 0,
            };
            let states = [TheoryPatternStateV1 {
                id: TheoryPatternStateId(0),
                slot_count: 0,
                form: TheoryPatternStateFormV1::Apply { operator, arguments: vec![] },
            }];
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                3 + payload,
                65 + payload as usize,
                &mut cancel,
            );
            charge_pattern_states(&states, &mut budget)
                .expect("every existing operator has a setup schedule");
            assert_eq!(budget.work_used(), 3 + payload);
            assert_eq!(budget.remaining_bytes(), 0);
        }
    }

    fn uniform(value: usize, payload: usize) -> SemanticServiceLimits {
        SemanticServiceLimits {
            execution: SemanticTransitionLimits {
                work: value as u64,
                normalization_steps: value,
                outputs: value,
                frontier: value,
                proofs: value,
                proof_nodes: value,
                term_nodes: value,
                term_bytes: value,
                output_nodes: value,
                output_bytes: value,
            },
            boundary_payload_bytes: payload,
        }
    }

    #[test]
    fn semantic_service_limits_meet_each_coordinate_without_relabeling_payload() {
        let installed = TheoryLimitsV1 {
            max_steps: 31,
            max_frontier: 29,
            max_proof_nodes: 23,
            max_term_nodes: 19,
            max_output_nodes: 17,
            max_output_bytes: 13,
            ..TheoryLimitsV1::default()
        };
        let source = SemanticServiceLimits {
            execution: installed.into(),
            boundary_payload_bytes: usize::MAX,
        }
        .commitment_words();
        for host_bound in [0, 7, 21, 100] {
            for request_bound in [0, 11, 27, 100] {
                let host = uniform(host_bound, 101);
                let request = uniform(request_bound, 67);
                let actual = host.effective(installed, request).commitment_words();
                let h = host.commitment_words();
                let r = request.commitment_words();
                assert_eq!(actual[0], SEMANTIC_SETUP_SCHEDULE_V1);
                for index in 1..11 {
                    assert_eq!(actual[index], source[index].min(h[index]).min(r[index]));
                }
                assert_eq!(actual[11], 67, "not the installed thirteen-byte output ceiling");
                assert_eq!(actual[12], SEMANTIC_RECEIPT_SCHEDULE_V1);
            }
        }
    }

    #[test]
    fn semantic_service_commitment_words_preserve_order_and_full_width() {
        let limits = SemanticServiceLimits {
            execution: SemanticTransitionLimits {
                work: u64::MAX,
                normalization_steps: 2,
                outputs: 3,
                frontier: 4,
                proofs: 5,
                proof_nodes: 6,
                term_nodes: 7,
                term_bytes: 8,
                output_nodes: 9,
                output_bytes: 10,
            },
            boundary_payload_bytes: usize::MAX,
        };
        assert_eq!(
            limits.commitment_words(),
            [1, u128::from(u64::MAX), 2, 3, 4, 5, 6, 7, 8, 9, 10, usize::MAX as u128, 1]
        );
        for word in limits.commitment_words() {
            assert_eq!(u128::from_be_bytes(word.to_be_bytes()), word);
        }
    }
}
