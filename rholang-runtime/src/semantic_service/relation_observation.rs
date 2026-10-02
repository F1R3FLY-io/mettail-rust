//! Exact, actionless observation of authored GSLT rewrite relations.
//!
//! This is a service adapter over the installed semantic kernel and projected
//! matcher. It neither parses source text nor creates an alternate evaluator.

use super::*;
use mettail_dovetail_runtime::{
    ProvenSemanticRelationNormalForms, SemanticInputDecision, SemanticProjectionReceipt,
};
use mettail_grammar_core::TheoryConstructorId;

/// A structurally parsed guest term and exact names inside one installed image.
pub struct RelationObservationRequest<'a> {
    pub handle: &'a Par,
    pub relation_category: &'a str,
    pub terminal_judgment: &'a str,
    pub terminal_projection: &'a str,
    pub input: &'a Par,
    pub limits: SemanticServiceLimits,
}

/// A published result keeps every derivation used to establish both the
/// direct normal form and its accepted terminal judgment.
#[derive(Debug)]
pub struct RelationObservationResult {
    pub term: Par,
    pub relation_receipt: SemanticRelationNormalFormReceipt,
    pub terminal_receipts: Vec<SemanticRelationNormalFormReceipt>,
    pub projection_receipts: Vec<SemanticProjectionReceipt>,
}

#[derive(Debug)]
pub struct RelationObservationReport {
    pub outcome: Result<Vec<RelationObservationResult>, InstalledSemanticError>,
    pub work: u64,
    pub kernel_work: Option<u64>,
    pub effective_limits: Option<SemanticServiceLimits>,
    pub remaining_boundary_payload_bytes: usize,
}

pub(super) struct PreparedRelationObservationReport {
    pub outcome: Result<Vec<RelationObservationResult>, InstalledSemanticError>,
    pub publication: Option<InstalledSemanticPublication>,
    pub usage: SemanticServiceUsage,
}

impl PreparedRelationObservationReport {
    fn commit(self) -> RelationObservationReport {
        let outcome = self.outcome.and_then(|results| {
            let publication = self
                .publication
                .ok_or(InstalledSemanticError::InvalidEvidence(
                    "prepared relation observation has no publication context",
                ))?;
            publication
                .authorize(|| results)
                .map_err(InstalledSemanticError::Access)
        });
        RelationObservationReport {
            outcome,
            work: self.usage.work,
            kernel_work: self.usage.kernel_work,
            effective_limits: self.usage.effective_limits,
            remaining_boundary_payload_bytes: self.usage.remaining_boundary_payload_bytes,
        }
    }
}

struct SelectedRelationQuery {
    relation_sort: TheorySortId,
    judgment: TheoryConstructorId,
    query_sort: TheorySortId,
    projection: predicate::SelectedBooleanProjection,
    required: Vec<LanguageRight>,
}

fn select_relation_query<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    relation_category: &str,
    terminal_judgment: &str,
    terminal_projection: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SelectedRelationQuery, InstalledSemanticError> {
    let source = &installed.language_core().theory;
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let relation_index = find_exact_name(
        source.sorts.iter().map(|sort| sort.name.as_str()),
        relation_category,
        budget,
    )?
    .ok_or(InstalledSemanticError::InvalidSelection("unknown relation category"))?;
    let relation_sort = TheorySortId(
        u32::try_from(relation_index)
            .map_err(|_| InstalledSemanticError::InvalidSelection("relation sort overflow"))?,
    );
    let judgment_index = find_exact_name(
        source.constructors.iter().map(|ctor| ctor.name.as_str()),
        terminal_judgment,
        budget,
    )?
    .ok_or(InstalledSemanticError::InvalidSelection("unknown terminal judgment"))?;
    let judgment = TheoryConstructorId(
        u32::try_from(judgment_index)
            .map_err(|_| InstalledSemanticError::InvalidSelection("judgment overflow"))?,
    );
    let signature = image
        .constructors
        .get(judgment_index)
        .filter(|ctor| ctor.id == judgment && ctor.domain.as_slice() == [relation_sort])
        .ok_or(InstalledSemanticError::InvalidSelection("terminal judgment signature"))?;
    let source_signature = &source.constructors[judgment_index];
    let name_bytes = source_signature
        .domain
        .iter()
        .try_fold(source_signature.codomain.len(), |total, name| total.checked_add(name.len()))
        .ok_or(DynamicReflectionError::WorkLimit)?;
    budget.charge(name_bytes, 0)?;
    if !matches!(source_signature.domain.as_slice(), [only] if only == relation_category)
        || source
            .sorts
            .get(signature.codomain.0 as usize)
            .is_none_or(|sort| sort.name != source_signature.codomain)
    {
        return Err(InstalledSemanticError::InvalidSelection(
            "terminal judgment source/image mismatch",
        ));
    }
    let projection = predicate::select_named_boolean_projection(
        installed,
        signature.codomain,
        terminal_projection,
        budget,
    )?
    .ok_or(InstalledSemanticError::InvalidSelection("terminal projection not found"))?;
    let count = 3usize
        .checked_add(projection.required.len())
        .ok_or(DynamicReflectionError::WorkLimit)?;
    budget.charge(count, count)?;
    let mut required = Vec::new();
    required
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    required.extend([LanguageRight::Observe, LanguageRight::Reduce, LanguageRight::Construct]);
    for right in &projection.required {
        if !required.contains(right) {
            required.push(*right);
        }
    }
    Ok(SelectedRelationQuery {
        relation_sort,
        judgment,
        query_sort: signature.codomain,
        projection,
        required,
    })
}

impl RholangLanguageRuntime {
    pub fn execute_relation_observation<C: FnMut() -> bool>(
        &self,
        request: RelationObservationRequest<'_>,
        is_cancelled: C,
    ) -> RelationObservationReport {
        self.prepare_relation_observation(request, SemanticServicePrefix::default(), is_cancelled)
            .commit()
    }

    pub(super) fn prepare_relation_observation<C: FnMut() -> bool>(
        &self,
        request: RelationObservationRequest<'_>,
        prefix: SemanticServicePrefix,
        mut is_cancelled: C,
    ) -> PreparedRelationObservationReport {
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
                .resolve(request.handle, LanguageRight::Observe)
                .map_err(|error| match error {
                    LanguageRuntimeError::InvalidHandleShape => {
                        InstalledSemanticError::InvalidHandleShape
                    },
                    LanguageRuntimeError::UnknownHandle => InstalledSemanticError::UnknownHandle,
                    LanguageRuntimeError::Access(error) => InstalledSemanticError::Access(error),
                    LanguageRuntimeError::Poisoned => {
                        InstalledSemanticError::Access(LanguageAccessError::Poisoned)
                    },
                    _ => InstalledSemanticError::InvalidEvidence("capability resolution failure"),
                })?;
            let table = self.service().table();
            let installed = table
                .authorize_all(&handle, &[LanguageRight::Observe])
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
                let mut selected = select_relation_query(
                    &installed,
                    request.relation_category,
                    request.terminal_judgment,
                    request.terminal_projection,
                    &mut budget,
                )?;
                let required = std::mem::take(&mut selected.required);
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
                run_selected_relation_query(
                    &bundle,
                    &selected,
                    request.input,
                    limits,
                    &mut budget,
                    &mut kernel_work,
                )
            })();
            remaining = budget.finish();
            prepared
        })();
        PreparedRelationObservationReport {
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

fn admitted_input<C: FnMut() -> bool>(
    decision: SemanticInputDecision,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<SemanticTransitionInput, InstalledSemanticError> {
    budget.charge(0, 0)?;
    match decision {
        SemanticInputDecision::Proven(input) => Ok(input),
        SemanticInputDecision::Refuted(reason) => Err(InstalledSemanticError::Refuted(reason)),
        SemanticInputDecision::Undetermined { reason, .. } => {
            Err(InstalledSemanticError::Undetermined(reason))
        },
    }
}

fn normalize_relation<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    sort: TheorySortId,
    input: SemanticTransitionInput,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<ProvenSemanticRelationNormalForms, InstalledSemanticError> {
    let admission = input.admission_work();
    let key = input.exact_key().as_bytes();
    budget.charge(
        key.len()
            .checked_add(1)
            .ok_or(DynamicReflectionError::WorkLimit)?,
        key.len(),
    )?;
    let mut expected_input = Vec::new();
    expected_input
        .try_reserve_exact(key.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    expected_input.extend_from_slice(key);
    let (decision, aggregate) = budget.run_accounted_stage(|remaining, cancel| {
        let Some(ceiling) = admission.checked_add(remaining) else {
            return (Err(InstalledSemanticError::InvalidEvidence("relation ceiling overflow")), 0);
        };
        match prepared.execute_relation_accounted(
            sort,
            input,
            SemanticTransitionLimits { work: ceiling, ..limits.execution },
            cancel,
        ) {
            Err(error) => (Err(error), 0),
            Ok((decision, aggregate)) => match aggregate.checked_sub(admission) {
                Some(increment) => (Ok((decision, aggregate)), increment),
                None => (
                    Err(InstalledSemanticError::InvalidEvidence(
                        "relation underreported admission",
                    )),
                    0,
                ),
            },
        }
    })??;
    *kernel_work = Some(
        kernel_work
            .unwrap_or(0)
            .checked_add(aggregate)
            .ok_or(InstalledSemanticError::InvalidEvidence("kernel work overflow"))?,
    );
    let proven = match decision {
        SemanticTransitionDecision::ProvenRelation(proven) => proven,
        SemanticTransitionDecision::Proven(_) => {
            return Err(InstalledSemanticError::InvalidEvidence(
                "relation returned a named action result",
            ));
        },
        SemanticTransitionDecision::Refuted(reason) => {
            return Err(InstalledSemanticError::Refuted(reason));
        },
        SemanticTransitionDecision::Undetermined { reason, .. } => {
            return Err(InstalledSemanticError::Undetermined(reason));
        },
    };
    if proven.work != aggregate || aggregate < admission || proven.normal_forms().is_empty() {
        return Err(InstalledSemanticError::InvalidEvidence("relation result aggregate"));
    }
    for form in proven.normal_forms() {
        validate_fresh_relation_receipt(
            prepared.installed(),
            sort,
            &expected_input,
            aggregate,
            &form.receipt,
            form.output_sort,
            budget,
        )?;
        charge_relation_receipt_transport(&form.receipt, budget)?;
    }
    Ok(proven)
}

/// A Data-free where guard normalizes the same installed directed rewrite
/// relation and projects *every* normal form through one exact Boolean
/// relation. An exhaustive projection no-match is not Boolean false: it says
/// that normal form has no Boolean evidence, so the whole guard is unknown.
/// No source parsing, alternate evaluator, first-result selection, or
/// synthetic action descriptor is involved.
pub(super) fn prepare_authored_predicate_results<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    sort: TheorySortId,
    source: &Par,
    projection: &predicate::SelectedBooleanProjection,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<
    (Vec<SemanticRelationNormalFormReceipt>, mettail_prattail::algebra_tower::Sat3),
    InstalledSemanticError,
> {
    use mettail_prattail::algebra_tower::Sat3;
    if projection.input_sort != sort {
        return Err(InstalledSemanticError::InvalidEvidence(
            "authored predicate category/projection sort mismatch",
        ));
    }
    let adapter = InstalledFltAdapter::new(prepared.installed(), budget)?;
    let category = adapter.input_category(sort, budget)?;
    let input = adapter.to_kernel(
        source,
        category,
        SemanticInputLimits {
            work: limits.execution.work,
            nodes: limits.execution.term_nodes,
            bytes: limits.execution.term_bytes,
        },
        budget,
    )?;
    let proven = normalize_relation(prepared, sort, input, limits, budget, kernel_work)?;
    let mut verdict = None;
    for index in 0..proven.normal_forms().len() {
        budget.charge(1, 0)?;
        let decision = budget.run_accounted_stage(|remaining, cancel| {
            proven.admit_output_at(
                index,
                SemanticInputLimits {
                    work: remaining,
                    nodes: limits.execution.term_nodes,
                    bytes: limits.execution.term_bytes,
                },
                cancel,
            )
        })?;
        let input = admitted_input(decision, budget)?;
        let (current, proofs) =
            execute_terminal_projection(prepared, projection, input, limits, budget, kernel_work)?;
        verdict = predicate::fold_uniform_candidate(
            verdict,
            if proofs.is_empty() {
                Sat3::DontKnow
            } else {
                current
            },
        );
    }
    let count = proven.normal_forms().len();
    let bytes = count
        .checked_mul(8)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(count, bytes)?;
    let mut receipts = Vec::new();
    receipts
        .try_reserve_exact(count)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    let (_graph, forms) = proven.into_parts();
    receipts.extend(forms.into_iter().map(|form| form.receipt));
    Ok((receipts, verdict.unwrap_or(Sat3::DontKnow)))
}

struct AcceptedRelationCandidate {
    index: usize,
    terminal_receipts: Vec<SemanticRelationNormalFormReceipt>,
    projection_receipts: Vec<SemanticProjectionReceipt>,
}

fn run_selected_relation_query<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    selected: &SelectedRelationQuery,
    source: &Par,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<Vec<RelationObservationResult>, InstalledSemanticError> {
    let installed = prepared.installed();
    let adapter = InstalledFltAdapter::new(installed, budget)?;
    let category = adapter.input_category(selected.relation_sort, budget)?;
    let input = adapter.to_kernel(
        source,
        category,
        SemanticInputLimits {
            work: limits.execution.work,
            nodes: limits.execution.term_nodes,
            bytes: limits.execution.term_bytes,
        },
        budget,
    )?;
    let proven =
        normalize_relation(prepared, selected.relation_sort, input, limits, budget, kernel_work)?;
    let mut accepted = Vec::new();
    for index in 0..proven.normal_forms().len() {
        budget.charge(1, 0)?;
        if let Some((terminal_receipts, projection_receipts)) = classify_terminal_candidate(
            prepared,
            selected,
            &proven,
            index,
            limits,
            budget,
            kernel_work,
        )? {
            accepted
                .try_reserve(1)
                .map_err(|_| DynamicReflectionError::AllocationFailed)?;
            accepted.push(AcceptedRelationCandidate {
                index,
                terminal_receipts,
                projection_receipts,
            });
        }
    }
    if accepted.is_empty() {
        return Err(InstalledSemanticError::Refuted(SemanticMatchRefutation::StuckNonterminal));
    }
    let selection_bytes = accepted
        .len()
        .checked_mul(8)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(accepted.len(), selection_bytes)?;
    let mut indices = Vec::new();
    indices
        .try_reserve_exact(accepted.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    indices.extend(accepted.iter().map(|candidate| candidate.index));
    let terms =
        adapter.reflect_relation_selected(&proven, &indices, selected.relation_sort, budget)?;
    if terms.len() != accepted.len() {
        return Err(InstalledSemanticError::InvalidEvidence("relation reflection arity"));
    }
    budget.charge(accepted.len(), selection_bytes)?;
    let mut results = Vec::new();
    results
        .try_reserve_exact(accepted.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    let (_graph, forms) = proven.into_parts();
    let mut selected = accepted.into_iter().peekable();
    let mut terms = terms.into_iter();
    for (index, form) in forms.into_iter().enumerate() {
        if selected
            .peek()
            .is_some_and(|candidate| candidate.index == index)
        {
            let candidate = selected
                .next()
                .ok_or(InstalledSemanticError::InvalidEvidence("relation selection disappeared"))?;
            let term = terms.next().ok_or(InstalledSemanticError::InvalidEvidence(
                "relation reflection disappeared",
            ))?;
            results.push(RelationObservationResult {
                term,
                relation_receipt: form.receipt,
                terminal_receipts: candidate.terminal_receipts,
                projection_receipts: candidate.projection_receipts,
            });
        }
    }
    if selected.next().is_some() || terms.next().is_some() {
        return Err(InstalledSemanticError::InvalidEvidence("relation selection remainder"));
    }
    Ok(results)
}

fn classify_terminal_candidate<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    selected: &SelectedRelationQuery,
    relation: &ProvenSemanticRelationNormalForms,
    index: usize,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<
    Option<(Vec<SemanticRelationNormalFormReceipt>, Vec<SemanticProjectionReceipt>)>,
    InstalledSemanticError,
> {
    use mettail_prattail::algebra_tower::Sat3;
    let image = prepared
        .installed()
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let decision = budget.run_accounted_stage(|remaining, cancel| {
        relation.admit_unary_query_at(
            index,
            image,
            selected.judgment,
            SemanticInputLimits {
                work: remaining,
                nodes: limits.execution.term_nodes,
                bytes: limits.execution.term_bytes,
            },
            cancel,
        )
    })?;
    let input = admitted_input(decision, budget)?;
    let terminal =
        normalize_relation(prepared, selected.query_sort, input, limits, budget, kernel_work)?;
    let mut verdict = None;
    let mut projection_receipts = Vec::new();
    for terminal_index in 0..terminal.normal_forms().len() {
        budget.charge(1, 0)?;
        let decision = budget.run_accounted_stage(|remaining, cancel| {
            terminal.admit_output_at(
                terminal_index,
                SemanticInputLimits {
                    work: remaining,
                    nodes: limits.execution.term_nodes,
                    bytes: limits.execution.term_bytes,
                },
                cancel,
            )
        })?;
        let input = admitted_input(decision, budget)?;
        let (current, mut receipts) = execute_terminal_projection(
            prepared,
            &selected.projection,
            input,
            limits,
            budget,
            kernel_work,
        )?;
        verdict = predicate::fold_uniform_candidate(verdict, current);
        projection_receipts
            .try_reserve(receipts.len())
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        projection_receipts.append(&mut receipts);
    }
    match verdict.unwrap_or(Sat3::DontKnow) {
        Sat3::Sat => {
            let (_graph, normal_forms) = terminal.into_parts();
            let mut terminal_receipts = Vec::new();
            terminal_receipts
                .try_reserve_exact(normal_forms.len())
                .map_err(|_| DynamicReflectionError::AllocationFailed)?;
            terminal_receipts.extend(normal_forms.into_iter().map(|form| form.receipt));
            Ok(Some((terminal_receipts, projection_receipts)))
        },
        Sat3::Unsat => Ok(None),
        Sat3::DontKnow => Err(InstalledSemanticError::AmbiguousTerminalQuery),
    }
}

fn execute_terminal_projection<C: FnMut() -> bool>(
    prepared: &InstalledSemanticBundle<'_>,
    projection: &predicate::SelectedBooleanProjection,
    input: SemanticTransitionInput,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
    kernel_work: &mut Option<u64>,
) -> Result<
    (mettail_prattail::algebra_tower::Sat3, Vec<SemanticProjectionReceipt>),
    InstalledSemanticError,
> {
    use mettail_prattail::algebra_tower::Sat3;
    let installed = prepared.installed();
    let image = installed
        .projected_image()
        .ok_or(InstalledSemanticError::InvalidEvidence("terminal projection image missing"))?;
    let admission = input.admission_work();
    let key = input.exact_key().as_bytes();
    budget.charge(
        key.len()
            .checked_add(1)
            .ok_or(DynamicReflectionError::WorkLimit)?,
        key.len(),
    )?;
    let mut expected_input = Vec::new();
    expected_input
        .try_reserve_exact(key.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    expected_input.extend_from_slice(key);
    let (decision, aggregate) = budget.run_accounted_stage(|remaining, cancel| {
        let Some(ceiling) = admission.checked_add(remaining) else {
            return (
                Err(InstalledSemanticError::InvalidEvidence("projection ceiling overflow")),
                0,
            );
        };
        let (decision, aggregate) = prepared.matcher.execute_rule_projection_accounted(
            SemanticProjectionExecutionRequest {
                image,
                projection: projection.projection,
                direction: ProjectionDirectionV1::GuestToHost,
                granted_rights: prepared.handle.rights(),
                input,
                limits: SemanticTransitionLimits { work: ceiling, ..limits.execution },
            },
            cancel,
        );
        match aggregate.checked_sub(admission) {
            Some(increment) => (Ok((decision, aggregate)), increment),
            None => (
                Err(InstalledSemanticError::InvalidEvidence("projection underreported admission")),
                0,
            ),
        }
    })??;
    *kernel_work = Some(
        kernel_work
            .unwrap_or(0)
            .checked_add(aggregate)
            .ok_or(InstalledSemanticError::InvalidEvidence("projection work overflow"))?,
    );
    let proven = match decision {
        SemanticProjectionDecision::Proven(proven) => proven,
        SemanticProjectionDecision::Refuted(SemanticMatchRefutation::NoTransition) => {
            return Ok((Sat3::Unsat, Vec::new()));
        },
        SemanticProjectionDecision::Refuted(reason) => {
            return Err(InstalledSemanticError::Refuted(reason));
        },
        SemanticProjectionDecision::Undetermined { reason, .. } => {
            return Err(InstalledSemanticError::Undetermined(reason));
        },
    };
    if proven.work != aggregate || proven.work < admission || proven.values.is_empty() {
        return Err(InstalledSemanticError::InvalidEvidence("projection result aggregate"));
    }
    let mut verdict = None;
    let mut receipts = Vec::new();
    receipts
        .try_reserve_exact(proven.values.len())
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    for value in &proven.values {
        let current = classify_fresh_projection_value(
            installed,
            image,
            projection,
            &proven,
            value,
            &expected_input,
            aggregate,
            budget,
        )?;
        charge_projection_receipt_transport(&value.receipt, budget)?;
        verdict = predicate::fold_uniform_candidate(verdict, current);
    }
    let (_graph, values) = proven.into_parts();
    receipts.extend(values.into_iter().map(|value| value.receipt));
    Ok((verdict.unwrap_or(Sat3::DontKnow), receipts))
}
