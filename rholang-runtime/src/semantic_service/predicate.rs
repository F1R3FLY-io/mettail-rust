//! Where predicates select canonical roles and reuse the ordinary semantic service.
use super::*;
use dovetail::key::ContentKey;
use mettail_grammar_core::{
    ProjectionDirectionV1, ProjectionRelationBodyImageV1, SemanticEffectClassV1,
    TheoryImageOperatorV1, TheoryImageTermFormV1,
};
use mettail_prattail::algebra_tower::Sat3;
use mettail_rholang_codegen::ReflectedPositionalContext;

pub(super) fn select_role<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    input: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<usize>, InstalledSemanticError> {
    budget.charge(87, 87)?;
    let owner = crate::language_install::grammar_fingerprint_label(
        installed.commitment().language_fingerprint,
    );
    let context = ReflectedPositionalContext::new(&owner, budget)?;
    let Some(head) = context.view(input, budget)? else {
        return Ok(None);
    };
    let mut selected = None;
    for (index, observation) in installed
        .language_core()
        .theory
        .observations
        .iter()
        .enumerate()
    {
        budget.charge(1, 0)?;
        if let Some(role) = &observation.predicate_role {
            budget.charge(role.input_constructor.len(), 0)?;
            if role.input_constructor == head.label() {
                if selected.replace(index).is_some() {
                    return Err(InstalledSemanticError::InvalidSelection(
                        "duplicate predicate role",
                    ));
                }
            }
        }
    }
    Ok(selected)
}

/// Conservative structural dispatch for a projected guard. A constructor
/// mismatch proves an action entry cannot match this FLT head; a matching or
/// wildcard entry is only a *possible* candidate and is still checked by the
/// existing action matcher. Never choose the first candidate on overlap.
pub(super) fn select_projected_observation<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    input: &Par,
    category: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<usize>, InstalledSemanticError> {
    if installed.projected_image().is_none() {
        return Ok(None);
    }
    let owner = crate::language_install::grammar_fingerprint_label(
        installed.commitment().language_fingerprint,
    );
    let context = ReflectedPositionalContext::new(&owner, budget)?;
    let head = context
        .view(input, budget)?
        .ok_or(InstalledSemanticError::InvalidSelection("projected guard input is not an FLT"))?;
    let language = installed.language_core();
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let mut selected = None;
    for (observation_index, observation) in language.theory.observations.iter().enumerate() {
        budget.charge(1, 0)?;
        let action_index = super::find_exact_name(
            language
                .theory
                .actions
                .iter()
                .map(|action| action.id.as_str()),
            &observation.action,
            budget,
        )?
        .ok_or(InstalledSemanticError::InvalidEvidence("observation action coordinate"))?;
        let source_action = &language.theory.actions[action_index];
        if source_action.domain.len() != 1 || source_action.domain[0] != category {
            continue;
        }
        let action = image
            .actions
            .get(action_index)
            .filter(|action| action.id.0 as usize == action_index)
            .ok_or(InstalledSemanticError::InvalidEvidence("action image coordinate"))?;
        let mut possible = false;
        for rule_id in &action.transitions {
            budget.charge(1, 0)?;
            let rule = image
                .rules
                .get(rule_id.0 as usize)
                .ok_or(InstalledSemanticError::InvalidEvidence("action entry rule"))?;
            let root = rule
                .terms
                .get(rule.left.0 as usize)
                .ok_or(InstalledSemanticError::InvalidEvidence("action entry root"))?;
            match &root.form {
                TheoryImageTermFormV1::Apply {
                    operator: TheoryImageOperatorV1::Constructor(id),
                    ..
                } => {
                    let constructor = language
                        .theory
                        .constructors
                        .get(id.0 as usize)
                        .ok_or(InstalledSemanticError::InvalidEvidence("entry constructor"))?;
                    budget.charge(constructor.name.len(), 0)?;
                    possible |= constructor.name == head.label();
                },
                _ => possible = true,
            }
        }
        if !possible || select_boolean_projection(installed, action.codomain, budget)?.is_none() {
            continue;
        }
        if action.effect_class != SemanticEffectClassV1::Pure {
            return Err(InstalledSemanticError::InvalidSelection(
                "projected where action is not pure",
            ));
        }
        if selected.replace(observation_index).is_some() {
            return Err(InstalledSemanticError::InvalidSelection(
                "multiple projected observations may match this FLT head",
            ));
        }
    }
    Ok(selected)
}

/// The category is an exact source/image coordinate, never an inferred name
/// such as `Bool` or a constructor whose spelling happens to be `yes`.
pub(super) fn native_boolean_sort<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    category: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<TheorySortId, InstalledSemanticError> {
    let language = installed.language_core();
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let mut grammar_coordinate = None;
    for entry in &language.grammar.categories {
        budget.charge(
            entry
                .name
                .len()
                .checked_add(1)
                .ok_or(DynamicReflectionError::WorkLimit)?,
            0,
        )?;
        if entry.name == category {
            if grammar_coordinate.replace(entry.id).is_some() {
                return Err(InstalledSemanticError::InvalidEvidence("duplicate grammar category"));
            }
            if !matches!(&entry.carrier, Carrier::Builtin(BuiltinCarrier::Boolean)) {
                return Err(InstalledSemanticError::InvalidSelection(
                    "predicate category is not a native Boolean carrier",
                ));
            }
        }
    }
    grammar_coordinate
        .ok_or(InstalledSemanticError::InvalidSelection("unknown predicate category"))?;
    let mut selected = None;
    for (index, source) in language.theory.sorts.iter().enumerate() {
        budget.charge(
            source
                .name
                .len()
                .checked_add(1)
                .ok_or(DynamicReflectionError::WorkLimit)?,
            0,
        )?;
        if source.name != category {
            continue;
        }
        if selected.is_some() {
            return Err(InstalledSemanticError::InvalidEvidence("duplicate theory sort"));
        }
        let id = TheorySortId(u32::try_from(index).map_err(|_| {
            InstalledSemanticError::InvalidEvidence("theory sort coordinate overflow")
        })?);
        let compiled = image.sorts.get(index).filter(|sort| sort.id == id).ok_or(
            InstalledSemanticError::InvalidEvidence("predicate sort source/image coordinate"),
        )?;
        if !matches!(
            &source.kind,
            TheorySortKindV1::Syntax {
                literal: Some(TheoryLiteralCarrierV1::Boolean)
            }
        ) || !matches!(
            &compiled.kind,
            TheorySortKindImageV1::Syntax {
                literal: Some(TheoryLiteralCarrierV1::Boolean)
            }
        ) {
            return Err(InstalledSemanticError::InvalidSelection(
                "predicate sort is not native Boolean",
            ));
        }
        selected = Some(id);
    }
    selected.ok_or(InstalledSemanticError::InvalidSelection("unbound predicate theory sort"))
}

pub(super) fn role_keys<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    index: usize,
    limits: SemanticServiceLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<[ContentKey; 2], InstalledSemanticError> {
    let image = installed
        .semantic_image()
        .ok_or(InstalledSemanticError::MissingSemanticImage)?;
    let bytes = budget.remaining_bytes().min(limits.execution.output_bytes);
    budget
        .run_accounted_stage(|work, cancel| {
            mettail_dovetail_runtime::observation_predicate_result_keys(
                installed.language_core(),
                image,
                index,
                SemanticInputLimits {
                    work,
                    nodes: limits.execution.output_nodes,
                    bytes,
                },
                cancel,
            )
        })?
        .map_err(InstalledSemanticError::PredicateRole)?
        .ok_or(InstalledSemanticError::InvalidSelection("missing selected predicate role"))
}

/// A qualified where FLT supplies the guest category; the host Boolean
/// endpoint is fixed by the Rholang guard contract. Exactly one installed
/// guest-to-host rule relation may connect those endpoints. No constructor
/// spelling, source text, or first-match ordering selects a projection.
pub(super) struct SelectedBooleanProjection {
    pub projection: u32,
    pub input_sort: TheorySortId,
    pub output_sort: TheorySortId,
    pub required: Vec<LanguageRight>,
}

pub(super) fn select_boolean_projection<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    action_output_sort: TheorySortId,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<SelectedBooleanProjection>, InstalledSemanticError> {
    select_boolean_projection_inner(installed, action_output_sort, None, budget)
}

/// An authored observation names its terminal projection exactly. Other
/// Boolean projections from the same guest sort remain valid independent
/// relations; they are not candidates for this request.
pub(super) fn select_named_boolean_projection<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    input_sort: TheorySortId,
    name: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<SelectedBooleanProjection>, InstalledSemanticError> {
    select_boolean_projection_inner(installed, input_sort, Some(name), budget)
}

fn select_boolean_projection_inner<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    action_output_sort: TheorySortId,
    requested_name: Option<&str>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<SelectedBooleanProjection>, InstalledSemanticError> {
    if let Some(name) = requested_name {
        budget.charge(name.len(), 0)?;
    }
    let Some(projected) = installed.projected_image() else {
        return Ok(None);
    };
    let core = installed
        .projected_core()
        .ok_or(InstalledSemanticError::InvalidEvidence("projected image has no projected core"))?;
    let guest_sort = installed
        .language_core()
        .theory
        .sorts
        .get(action_output_sort.0 as usize)
        .ok_or(InstalledSemanticError::InvalidEvidence("action output sort coordinate"))?;
    let mut selected = None;
    for relation in &projected.relations {
        budget.charge(1, 0)?;
        if relation.direction != ProjectionDirectionV1::GuestToHost
            || relation.input_sort != action_output_sort
        {
            continue;
        }
        let descriptor = core
            .projections
            .get(relation.projection as usize)
            .ok_or(InstalledSemanticError::InvalidEvidence("projection source coordinate"))?;
        budget.charge(descriptor.guest_category.len() + descriptor.host.category.len(), 0)?;
        if let Some(name) = requested_name {
            budget.charge(descriptor.name.len(), 0)?;
            if descriptor.name != name {
                continue;
            }
        }
        if descriptor.guest_category != guest_sort.name || descriptor.host.category != "Bool" {
            continue;
        }
        if selected.is_some() {
            return Err(InstalledSemanticError::InvalidSelection(
                "more than one Boolean projection matches the guard endpoint",
            ));
        }
        let output = projected
            .execution
            .sorts
            .get(relation.output_sort.0 as usize)
            .ok_or(InstalledSemanticError::InvalidEvidence("projection output sort coordinate"))?;
        if (relation.output_sort.0 as usize) < installed.language_core().theory.sorts.len()
            || !matches!(
                &output.kind,
                TheorySortKindImageV1::Syntax {
                    literal: Some(TheoryLiteralCarrierV1::Boolean)
                }
            )
        {
            return Err(InstalledSemanticError::InvalidEvidence(
                "selected host endpoint is not the checked Boolean carrier",
            ));
        }
        if !matches!(relation.body, ProjectionRelationBodyImageV1::Rules(_)) {
            return Err(InstalledSemanticError::InvalidSelection(
                "where requires an executable Boolean projection rule",
            ));
        }
        let action = relation
            .dispatch_action
            .and_then(|id| projected.execution.actions.get(id.0 as usize))
            .ok_or(InstalledSemanticError::InvalidEvidence("projection dispatch action"))?;
        let required = action.required_rights.iter().collect();
        selected = Some(SelectedBooleanProjection {
            projection: relation.projection,
            input_sort: relation.input_sort,
            output_sort: relation.output_sort,
            required,
        });
    }
    Ok(selected)
}

/// Every original result occurrence is inspected; no set conversion, first
/// result selection, or truthiness. These are the complete fresh receipts
/// already validated by prepare_semantic_results, not caller-supplied bytes.
pub(super) fn classify_results<C: FnMut() -> bool>(
    results: &[SemanticServiceResult],
    keys: &[ContentKey; 2],
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Sat3, InstalledSemanticError> {
    let mut uniform = None;
    for result in results {
        let output = &result.receipt.output;
        let work = output
            .len()
            .checked_add(keys[0].len())
            .and_then(|n| n.checked_add(keys[1].len()))
            .and_then(|n| n.checked_add(1))
            .ok_or(DynamicReflectionError::WorkLimit)?;
        budget.charge(work, 0)?;
        let current = if output.as_slice() == keys[0].as_bytes() {
            Sat3::Sat
        } else if output.as_slice() == keys[1].as_bytes() {
            Sat3::Unsat
        } else {
            Sat3::DontKnow
        };
        uniform = fold_uniform_candidate(uniform, current);
    }
    budget.charge(0, 0)?;
    Ok(uniform.unwrap_or(Sat3::DontKnow))
}

/// Consensus of complete result occurrences, not existential satisfiability.
/// A conflicting or unknown member is sticky under all later observations.
pub(super) fn fold_uniform_candidate(previous: Option<Sat3>, current: Sat3) -> Option<Sat3> {
    Some(match previous {
        None => current,
        Some(earlier) if earlier == current => current,
        Some(_) => Sat3::DontKnow,
    })
}

/// Private fresh service evidence retained until the actual COMM mutation.
pub(crate) struct PredicateEvidence(PreparedSemanticReport);

pub(crate) struct PredicateCommit {
    table: Arc<InstalledLanguageTable>,
    evidence: Vec<PredicateEvidence>,
    cancel: Option<Arc<dyn Fn() -> bool + Send + Sync>>,
}

impl PredicateCommit {
    pub(crate) fn new(
        evidence: Vec<PredicateEvidence>,
        cancel: Option<Arc<dyn Fn() -> bool + Send + Sync>>,
    ) -> Option<Self> {
        let table = Arc::clone(&evidence.first()?.0.publication.as_ref()?.table);
        if evidence.iter().any(|item| {
            item.0.outcome.is_err()
                || item.verdict() == Sat3::DontKnow
                || item
                    .0
                    .publication
                    .as_ref()
                    .is_none_or(|p| !Arc::ptr_eq(&table, &p.table))
        }) {
            return None;
        }
        Some(Self { table, evidence, cancel })
    }
}

impl ProduceCommitGuard for PredicateCommit {
    fn with_commit(&self, commit: Box<dyn FnOnce() + '_>) -> Result<(), RSpaceError> {
        if self.cancel.as_ref().is_some_and(|cancel| cancel()) {
            return Err(RSpaceError::ProduceCommitDenied);
        }
        self.table
            .with_authorized_batch(
                self.evidence.iter().map(|item| {
                    let publication = item
                        .0
                        .publication
                        .as_ref()
                        .expect("private checked evidence");
                    (&publication.handle, publication.required.as_slice())
                }),
                commit,
            )
            .map_err(|_| RSpaceError::ProduceCommitDenied)
    }
}

impl PredicateEvidence {
    pub(crate) fn verdict(&self) -> Sat3 {
        if self.0.outcome.as_ref().is_err()
            || matches!(&self.0.outcome, Ok(PreparedSemanticOutput::PredicateRelation(receipts)) if receipts.is_empty())
        {
            Sat3::DontKnow
        } else {
            self.0.predicate_verdict.unwrap_or(Sat3::DontKnow)
        }
    }
    pub(crate) fn work(&self) -> u64 {
        self.0.usage.work
    }
    pub(crate) fn remaining_bytes(&self) -> usize {
        self.0.usage.remaining_boundary_payload_bytes
    }
    pub(crate) fn error(&self) -> Option<&InstalledSemanticError> {
        self.0.outcome.as_ref().err()
    }
}

impl RholangLanguageRuntime {
    pub(crate) fn prepare_where_predicate<C: FnMut() -> bool>(
        &self,
        handle: &Par,
        input: &Par,
        category: &str,
        prefix_work: u64,
        prefix_bytes: usize,
        limits: SemanticServiceLimits,
        cancel: C,
    ) -> PredicateEvidence {
        PredicateEvidence(self.prepare_semantic_mode(
            SemanticServiceRequest {
                handle,
                input,
                operation: SemanticOperation::Predicate(category),
                limits,
            },
            SemanticServicePrefix {
                work: prefix_work,
                payload_bytes: prefix_bytes,
            },
            cancel,
            true,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    #[test]
    fn predicate_roster_classification_keeps_duplicates_and_never_selects_first() {
        let keys = [ContentKey::from_bytes(vec![1]), ContentKey::from_bytes(vec![2])];
        for (outputs, expected) in [
            (vec![], Sat3::DontKnow),
            (vec![1], Sat3::Sat),
            (vec![2], Sat3::Unsat),
            (vec![1, 1, 1], Sat3::Sat),
            (vec![2, 2], Sat3::Unsat),
            (vec![1, 2], Sat3::DontKnow),
            (vec![2, 1], Sat3::DontKnow),
            (vec![3], Sat3::DontKnow),
            (vec![1, 3, 1], Sat3::DontKnow),
        ] {
            let results: Vec<_> = outputs
                .into_iter()
                .map(|byte| {
                    let mut receipt = super::super::tests::transport_receipt();
                    receipt.output = vec![byte];
                    SemanticServiceResult { term: Par::default(), receipt }
                })
                .collect();
            let mut work = 0;
            let mut cancel = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 1000, &mut cancel);
            assert_eq!(classify_results(&results, &keys, &mut budget).unwrap(), expected);
            assert_eq!(budget.work_used(), results.len() as u64 * 4);
        }
    }

    proptest! {
        #[test]
        fn uniform_candidate_fold_is_order_independent_and_duplicate_stable(
            samples in proptest::collection::vec(0u8..3, 0..40)
        ) {
            let values: Vec<Sat3> = samples.iter().map(|sample| match sample {
                0 => Sat3::Sat,
                1 => Sat3::Unsat,
                _ => Sat3::DontKnow,
            }).collect();
            let classify = |items: &[Sat3]| items.iter().copied()
                .fold(None, fold_uniform_candidate)
                .unwrap_or(Sat3::DontKnow);
            let expected = if values.is_empty() || values.contains(&Sat3::DontKnow) {
                Sat3::DontKnow
            } else if values.iter().all(|v| *v == Sat3::Sat) {
                Sat3::Sat
            } else if values.iter().all(|v| *v == Sat3::Unsat) {
                Sat3::Unsat
            } else {
                Sat3::DontKnow
            };
            prop_assert_eq!(classify(&values), expected);
            let mut reversed = values.clone();
            reversed.reverse();
            prop_assert_eq!(classify(&reversed), expected);
            let duplicated = values.iter().copied().chain(values.iter().copied()).collect::<Vec<_>>();
            prop_assert_eq!(classify(&duplicated), expected);
        }
    }
}
