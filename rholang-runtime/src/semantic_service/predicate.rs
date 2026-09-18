//! Where predicates select canonical roles and reuse the ordinary semantic service.
use super::*;
use dovetail::key::ContentKey;
use mettail_prattail::algebra_tower::Sat3;
use mettail_rholang_codegen::ReflectedPositionalContext;

pub(super) fn select_role<C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    input: &Par,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<usize, InstalledSemanticError> {
    budget.charge(87, 87)?;
    let owner = crate::language_install::grammar_fingerprint_label(
        installed.commitment().language_fingerprint,
    );
    let context = ReflectedPositionalContext::new(&owner, budget)?;
    let head = context
        .view(input, budget)?
        .ok_or(InstalledSemanticError::InvalidSelection(
            "predicate input has no canonical installed constructor",
        ))?;
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
    selected.ok_or(InstalledSemanticError::InvalidSelection("constructor has no predicate role"))
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
        uniform = Some(match uniform {
            None => current,
            Some(previous) if previous == current => current,
            Some(_) => Sat3::DontKnow,
        });
    }
    budget.charge(0, 0)?;
    Ok(uniform.unwrap_or(Sat3::DontKnow))
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
        if self.0.outcome.is_err() {
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
        prefix_work: u64,
        prefix_bytes: usize,
        limits: SemanticServiceLimits,
        cancel: C,
    ) -> PredicateEvidence {
        PredicateEvidence(self.prepare_semantic_mode(
            SemanticServiceRequest {
                handle,
                input,
                operation: SemanticOperation::Observe(""),
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
}
