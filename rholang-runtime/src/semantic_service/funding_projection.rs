//! Checked, iterative projection of one installed V2 host result into the
//! generated language's structural input. This is still grade interpretation,
//! not funding authority: the caller must retain the selected Cost(G) receipt,
//! reauthorize the live host profile, then use the metered typed inverse and
//! canonical `Par` lowerer before offering anything to host resource logic.

use dovetail::egraph::EClassId;
use mettail_dovetail_runtime::{
    theory_positional_native_view, ProvenSemanticProjections, SemanticInputDecision,
    SemanticInputLimits, SemanticProjectionReceipt, SemanticResourceReceipt,
    TheoryPositionalNativeView,
};
use mettail_grammar_core::{
    DynamicTerm, DynamicValue, InstalledCompoundHostProfileSnapshotV2,
    InstalledHostConstructorRouteV2, InstalledLanguage, ProjectionDirectionV1,
    ProjectionRelationBodyImageV1, SemanticFieldSchemaV1, SourceSpan, TheorySortId,
};
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};

use super::InstalledSemanticError;

enum BuildTask<'a> {
    Visit(EClassId, TheorySortId),
    AssembleTerm(&'a InstalledHostConstructorRouteV2, usize),
    AssembleSequence(usize, usize),
}

fn push_task<'a, C: FnMut() -> bool>(
    tasks: &mut Vec<BuildTask<'a>>,
    task: BuildTask<'a>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), InstalledSemanticError> {
    budget.charge(1, std::mem::size_of::<BuildTask<'a>>())?;
    tasks
        .try_reserve(1)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    tasks.push(task);
    Ok(())
}

fn push_value<C: FnMut() -> bool>(
    values: &mut Vec<DynamicValue>,
    value: DynamicValue,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<(), InstalledSemanticError> {
    budget.charge(1, std::mem::size_of::<DynamicValue>())?;
    values
        .try_reserve(1)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    values.push(value);
    Ok(())
}

fn take_values<C: FnMut() -> bool>(
    values: &mut Vec<DynamicValue>,
    base: usize,
    expected: usize,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Vec<DynamicValue>, InstalledSemanticError> {
    if values.len().checked_sub(base) != Some(expected) {
        return Err(InstalledSemanticError::InvalidEvidence("host projection assembly arity"));
    }
    budget.charge(
        expected,
        expected
            .checked_mul(std::mem::size_of::<DynamicValue>())
            .ok_or(DynamicReflectionError::PayloadByteLimit)?,
    )?;
    let mut moved = Vec::new();
    moved
        .try_reserve_exact(expected)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    moved.extend(values.drain(base..));
    Ok(moved)
}

/// The receipt is borrowed from the complete kernel roster; identical output
/// terms with different source occurrences or proofs remain separate results.
pub(crate) struct CheckedProjectedHostValueV2<'a> {
    pub value: DynamicValue,
    pub receipt: &'a SemanticProjectionReceipt,
}

pub(crate) fn project_checked_host_value_v2<'a, C: FnMut() -> bool>(
    installed: &InstalledLanguage,
    host: &InstalledCompoundHostProfileSnapshotV2,
    proven: &'a ProvenSemanticProjections,
    candidate_index: usize,
    expected_input: &[u8],
    output_limits: SemanticInputLimits,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<CheckedProjectedHostValueV2<'a>, InstalledSemanticError> {
    let verified_image =
        installed
            .verified_projected_image()
            .ok_or(InstalledSemanticError::InvalidEvidence(
                "funding projection has no sealed image",
            ))?;
    let image = verified_image.image();
    let binding = installed
        .funding_projection_v2()
        .ok_or(InstalledSemanticError::InvalidEvidence("funding projection is not installed"))?;
    budget.charge(image.relations.len(), 0)?;
    let relation = image
        .relations
        .iter()
        .find(|relation| {
            relation.projection == binding.projection
                && relation.direction == ProjectionDirectionV1::GuestToHost
                && relation.output_sort == binding.host_proc_sort
        })
        .ok_or(InstalledSemanticError::InvalidEvidence("selected funding relation changed"))?;
    let host_digests = &host.record().claimed_digests;
    if installed
        .projected_host_profile()
        .map(|handle| handle.fingerprint())
        != Some(host_digests.profile_fingerprint)
        || image.host_signature_fingerprint != host_digests.signature_fingerprint
        || image.host_codec_profile_fingerprint != host_digests.codec_profile_fingerprint
    {
        return Err(InstalledSemanticError::InvalidEvidence(
            "funding host profile is not the installed compound profile",
        ));
    }
    let installed_image_fingerprint = installed
        .commitment()
        .semantic_image_fingerprint
        .ok_or(InstalledSemanticError::InvalidEvidence("funding image lacks commitment"))?;
    // Resolve the private roster slot directly. Equal output bytes do not
    // identify the source occurrence or its receipt.
    budget.charge(1, 0)?;
    let candidate = proven
        .values
        .get(candidate_index)
        .ok_or(InstalledSemanticError::InvalidEvidence("projection candidate index is absent"))?;
    let receipt = &candidate.receipt;
    budget.charge(
        receipt
            .input
            .len()
            .checked_add(receipt.output.len())
            .ok_or(DynamicReflectionError::WorkLimit)?,
        0,
    )?;
    if receipt.projected_language_fingerprint != installed.commitment().language_fingerprint
        || receipt.base_image_fingerprint != image.base_image_fingerprint
        || receipt.image_fingerprint != installed_image_fingerprint
        || receipt.host_signature_fingerprint != image.host_signature_fingerprint
        || receipt.host_codec_profile_fingerprint != image.host_codec_profile_fingerprint
        || receipt.projection != binding.projection
        || receipt.direction != ProjectionDirectionV1::GuestToHost
        || receipt.input_sort != relation.input_sort
        || receipt.output_sort != binding.host_proc_sort
        || candidate.output_sort != binding.host_proc_sort
        || receipt.input != expected_input
        || receipt.output.is_empty()
        || receipt.work != proven.work
        || receipt.resource != SemanticResourceReceipt::NoSemanticGrade
    {
        return Err(InstalledSemanticError::InvalidEvidence("funding projection receipt envelope"));
    }
    let ProjectionRelationBodyImageV1::Rules(rows) = &relation.body else {
        return Err(InstalledSemanticError::InvalidEvidence(
            "funding projection lacks a checked rule roster",
        ));
    };
    budget.charge(rows.len(), 0)?;
    if !rows.iter().any(|row| {
        row.program == receipt.rule && row.source_occurrence == receipt.source_occurrence
    }) {
        return Err(InstalledSemanticError::InvalidEvidence(
            "funding projection proof is not a selected source occurrence",
        ));
    }

    let admitted = budget.run_accounted_stage(|remaining, cancel| {
        proven.admit_output_at(
            candidate_index,
            SemanticInputLimits {
                work: remaining.min(output_limits.work),
                nodes: output_limits.nodes,
                bytes: output_limits.bytes,
            },
            cancel,
        )
    })?;
    match admitted {
        SemanticInputDecision::Proven(_) => {},
        SemanticInputDecision::Refuted(_) => {
            return Err(InstalledSemanticError::InvalidEvidence(
                "funding projection output root refuted",
            ));
        },
        SemanticInputDecision::Undetermined { reason, .. } => {
            return Err(InstalledSemanticError::Undetermined(reason));
        },
    }

    let mut tasks = Vec::new();
    let mut values = Vec::new();
    push_task(&mut tasks, BuildTask::Visit(candidate.output, binding.host_proc_sort), budget)?;
    while let Some(task) = tasks.pop() {
        budget.charge(1, 0)?;
        match task {
            BuildTask::Visit(class, sort) => {
                budget.charge(binding.host_sequences.len(), 0)?;
                if let Some(sequence) = binding
                    .host_sequences
                    .iter()
                    .find(|route| route.sort == sort)
                {
                    // Traverse the list spine before scheduling element jobs.
                    // Its exact Nil/Cons IDs and signatures were bound at
                    // installation. No length is inferred from one child.
                    let mut elements = Vec::new();
                    let mut cursor = class;
                    loop {
                        let view = budget
                            .run_accounted_stage(|limit, cancel| {
                                let mut work = 0;
                                let result = theory_positional_native_view(
                                    &image.execution,
                                    proven.egraph(),
                                    cursor,
                                    sort,
                                    &mut work,
                                    limit,
                                    cancel,
                                );
                                (result, work)
                            })?
                            .map_err(InstalledSemanticError::Undetermined)?;
                        match view {
                            Some(TheoryPositionalNativeView::Constructor {
                                signature,
                                children,
                            }) if signature.id == sequence.nil && children.is_empty() => break,
                            Some(TheoryPositionalNativeView::Constructor {
                                signature,
                                children,
                            }) if signature.id == sequence.cons && children.len() == 2 => {
                                budget.charge(1, std::mem::size_of::<EClassId>())?;
                                elements
                                    .try_reserve(1)
                                    .map_err(|_| DynamicReflectionError::AllocationFailed)?;
                                elements.push(children[0]);
                                cursor = children[1];
                            },
                            _ => {
                                return Err(InstalledSemanticError::InvalidEvidence(
                                    "host sequence is not exact Nil/Cons",
                                ));
                            },
                        }
                    }
                    let base = values.len();
                    push_task(
                        &mut tasks,
                        BuildTask::AssembleSequence(base, elements.len()),
                        budget,
                    )?;
                    for element in elements.into_iter().rev() {
                        push_task(&mut tasks, BuildTask::Visit(element, sequence.element), budget)?;
                    }
                    continue;
                }
                let view = budget
                    .run_accounted_stage(|limit, cancel| {
                        let mut work = 0;
                        let result = theory_positional_native_view(
                            &image.execution,
                            proven.egraph(),
                            class,
                            sort,
                            &mut work,
                            limit,
                            cancel,
                        );
                        (result, work)
                    })?
                    .map_err(InstalledSemanticError::Undetermined)?;
                let Some(TheoryPositionalNativeView::Constructor { signature, children }) = view
                else {
                    return Err(InstalledSemanticError::InvalidEvidence(
                        "host category has no selected constructor",
                    ));
                };
                budget.charge(binding.host_constructors.len(), 0)?;
                let route = binding
                    .host_constructors
                    .iter()
                    .find(|route| route.constructor == signature.id && route.codomain == sort)
                    .ok_or(InstalledSemanticError::InvalidEvidence(
                        "host constructor is outside selected profile",
                    ))?;
                if signature.domain != route.domain || children.len() != route.domain.len() {
                    return Err(InstalledSemanticError::InvalidEvidence(
                        "host constructor signature changed",
                    ));
                }
                let base = values.len();
                push_task(&mut tasks, BuildTask::AssembleTerm(route, base), budget)?;
                for (child, child_sort) in children.iter().zip(&route.domain).rev() {
                    push_task(&mut tasks, BuildTask::Visit(*child, *child_sort), budget)?;
                }
            },
            BuildTask::AssembleSequence(base, count) => {
                let elements = take_values(&mut values, base, count, budget)?;
                push_value(&mut values, DynamicValue::Sequence(elements), budget)?;
            },
            BuildTask::AssembleTerm(route, base) => {
                let children = take_values(&mut values, base, route.domain.len(), budget)?;
                let mut child_values = children.into_iter();
                budget.charge(
                    route.fields.len(),
                    route
                        .fields
                        .len()
                        .checked_mul(std::mem::size_of::<DynamicValue>())
                        .ok_or(DynamicReflectionError::PayloadByteLimit)?,
                )?;
                let mut fields = Vec::new();
                fields
                    .try_reserve_exact(route.fields.len())
                    .map_err(|_| DynamicReflectionError::AllocationFailed)?;
                for field in &route.fields {
                    fields.push(match field {
                        SemanticFieldSchemaV1::Child { .. }
                        | SemanticFieldSchemaV1::Sequence { .. } => {
                            child_values
                                .next()
                                .ok_or(InstalledSemanticError::InvalidEvidence(
                                    "host field lost a child",
                                ))?
                        },
                        SemanticFieldSchemaV1::Unit => DynamicValue::Unit,
                        _ => {
                            return Err(InstalledSemanticError::InvalidEvidence(
                                "unsupported selected host field",
                            ));
                        },
                    });
                }
                if child_values.next().is_some() {
                    return Err(InstalledSemanticError::InvalidEvidence(
                        "host field child surplus",
                    ));
                }
                budget.charge(1, std::mem::size_of::<DynamicTerm>())?;
                push_value(
                    &mut values,
                    DynamicValue::Term(Box::new(DynamicTerm {
                        category: route.category,
                        constructor: route.host_constructor,
                        fields,
                        span: SourceSpan::default(),
                    })),
                    budget,
                )?;
            },
        }
    }
    let [value] = values.as_mut_slice() else {
        return Err(InstalledSemanticError::InvalidEvidence("host root cardinality"));
    };
    let value = std::mem::replace(value, DynamicValue::Unit);
    Ok(CheckedProjectedHostValueV2 { value, receipt })
}
