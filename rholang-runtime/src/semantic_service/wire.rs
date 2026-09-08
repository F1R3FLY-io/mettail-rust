//! Compose the existing installed service, bounded transport, and owned guarded
//! producer. This module has no parser or evaluator of its own.

use super::*;
use crate::semantic_wire::{
    encode_results_v1, reserve_reply_payload, CompletionPermit, DiagnosticDomain,
    OwnedSemanticRequest, ReplyBody, SemanticWireError, SemanticWireUsage, StickyCancellation,
};
use mettail_rholang_codegen::LANGUAGE_SEMANTIC_BAND;
use models::rhoapi::ListParWithRandom;
use rholang::rust::interpreter::{
    contract_call::ContractCall, errors::InterpreterError, system_processes::Definition,
};
use std::{future::Future, pin::Pin};

pub const LANGUAGE_SEMANTIC_ABI_V1: &str = "mettail-language-semantic/1";
pub const LANGUAGE_SEMANTIC_REDUCE_URN: &str = "rho:mettail:flt:reduce";
pub const LANGUAGE_SEMANTIC_OBSERVE_URN: &str = "rho:mettail:flt:observe";

#[derive(Clone, Copy)]
enum Endpoint {
    Reduce,
    Observe,
}

impl Endpoint {
    fn index(self) -> u8 {
        match self {
            Self::Reduce => 0,
            Self::Observe => 1,
        }
    }

    fn urn(self) -> &'static str {
        match self {
            Self::Reduce => LANGUAGE_SEMANTIC_REDUCE_URN,
            Self::Observe => LANGUAGE_SEMANTIC_OBSERVE_URN,
        }
    }

    fn operation(self, name: &str) -> SemanticOperation<'_> {
        match self {
            Self::Reduce => SemanticOperation::Reduce(name),
            Self::Observe => SemanticOperation::Observe(name),
        }
    }
}

struct PreparedWireReply {
    payload: Vec<Par>,
    channel: Par,
    publication: Arc<dyn ProduceCommitGuard>,
}

fn prepare_reply<C: FnMut() -> bool>(
    runtime: &RholangLanguageRuntime,
    endpoint: Endpoint,
    payload: Vec<Par>,
    cancel: C,
) -> Result<PreparedWireReply, SemanticWireError> {
    let host = runtime.service().policy().semantic_service;
    let mut cancellation = StickyCancellation::new(cancel);
    let mut work = 0;
    let mut poll = || cancellation.poll();
    let mut header = ReflectedCodecBudget::new(
        &mut work,
        host.execution.work,
        host.boundary_payload_bytes,
        &mut poll,
    );
    let request = OwnedSemanticRequest::decode(payload, &mut header)?;
    let header_spent = host.boundary_payload_bytes - header.finish();
    let limits = SemanticServiceLimits {
        execution: meet_execution(host.execution, request.limits.execution),
        boundary_payload_bytes: host
            .boundary_payload_bytes
            .min(request.limits.boundary_payload_bytes),
    };
    let remaining = limits
        .boundary_payload_bytes
        .checked_sub(header_spent)
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    let mut budget =
        ReflectedCodecBudget::new(&mut work, limits.execution.work, remaining, &mut poll);
    let permit = CompletionPermit::reserve(limits, &mut budget)?;
    let mut output = reserve_reply_payload(&mut budget)?;
    // One fixed logical descriptor for the retained publication reference. This
    // is prepaid, not a physical Arc layout or allocation-size assertion.
    budget.charge(1, 16)?;
    let remaining = budget.finish();
    let prepared = runtime.prepare_semantic(
        SemanticServiceRequest {
            handle: request.handle(),
            operation: endpoint.operation(request.name()),
            input: request.input(),
            limits,
        },
        SemanticServicePrefix {
            work,
            payload_bytes: limits.boundary_payload_bytes - remaining,
        },
        &mut poll,
    );
    let PreparedSemanticReport { outcome, publication, usage } = prepared;
    let publication = publication.ok_or(SemanticWireError::Shape(
        "semantic call has no fully authorized publication context",
    ))?;
    let effective = usage
        .effective_limits
        .ok_or(SemanticWireError::Shape("authorized semantic call has no effective limits"))?;
    work = usage.work;
    let mut budget = ReflectedCodecBudget::new(
        &mut work,
        effective.execution.work,
        usage.remaining_boundary_payload_bytes,
        &mut poll,
    );
    let body = match outcome {
        Ok(results) => match encode_results_v1(results, &mut budget) {
            Ok(value) => ReplyBody::Proven(value),
            Err(error) => wire_diagnostic(error),
        },
        Err(error) => service_diagnostic(error),
    };
    let remaining = budget.finish();
    let response = permit.finish(
        body,
        SemanticWireUsage {
            work,
            kernel_work: usage.kernel_work,
            effective_limits: Some(effective),
            remaining_boundary_payload_bytes: remaining,
        },
        &mut cancellation,
    )?;
    output.push(response);
    Ok(PreparedWireReply {
        payload: output,
        channel: request.into_reply(),
        publication: Arc::new(publication),
    })
}

fn wire_diagnostic(error: SemanticWireError) -> ReplyBody {
    match error {
        SemanticWireError::Shape(_) => ReplyBody::Error(DiagnosticDomain::Wire, 0),
        SemanticWireError::IntegerRange => ReplyBody::Error(DiagnosticDomain::Wire, 1),
        SemanticWireError::NonCanonicalInteger => ReplyBody::Error(DiagnosticDomain::Wire, 2),
        SemanticWireError::Resource(error) => boundary_diagnostic(error),
    }
}

fn boundary_diagnostic(error: DynamicReflectionError) -> ReplyBody {
    use DynamicReflectionError::*;
    let code = match error {
        UnknownConstructor(_) => 0,
        ConflictingConstructorLabel { .. } => 1,
        UnknownHole(_) => 2,
        InvalidHoleId(_) => 3,
        HoleCategoryConflict(_) => 4,
        MissingHole(_) => 5,
        InvalidMapEntry => 6,
        WorkLimit => return ReplyBody::Undetermined(DiagnosticDomain::Boundary, 7),
        PayloadByteLimit => return ReplyBody::Undetermined(DiagnosticDomain::Boundary, 8),
        Cancelled => return ReplyBody::Undetermined(DiagnosticDomain::Boundary, 9),
        AllocationFailed => return ReplyBody::Undetermined(DiagnosticDomain::Boundary, 10),
        InvalidFingerprint => 11,
    };
    ReplyBody::Error(DiagnosticDomain::Boundary, code)
}

fn service_diagnostic(error: InstalledSemanticError) -> ReplyBody {
    use InstalledSemanticError::*;
    let code = match error {
        InvalidHandleShape => 0,
        UnknownHandle => 1,
        MissingSemanticImage => 2,
        UnknownAction => 3,
        UnknownObservation => 4,
        InvalidSelection(_) => 5,
        InvalidEvidence(_) => 6,
        Access(error) => {
            let code = match error {
                LanguageAccessError::WrongRegistry => 0,
                LanguageAccessError::UnknownLanguage => 1,
                LanguageAccessError::StaleHandle => 2,
                LanguageAccessError::Revoked => 3,
                LanguageAccessError::MissingRight(_) => 4,
                LanguageAccessError::AmplifiedHandle => 5,
                LanguageAccessError::EpochExhausted => 6,
                LanguageAccessError::Poisoned => 7,
            };
            return ReplyBody::Error(DiagnosticDomain::Access, code);
        },
        Refuted(reason) => {
            let code = match reason {
                SemanticMatchRefutation::RequestRejected => 0,
                SemanticMatchRefutation::NoTransition => 1,
                SemanticMatchRefutation::PremiseRefuted => 2,
                SemanticMatchRefutation::StuckNonterminal => 3,
                SemanticMatchRefutation::NormalizationDeterminismClaimViolated => 4,
            };
            return ReplyBody::Refuted(DiagnosticDomain::Kernel, code);
        },
        Undetermined(reason) => {
            let code = match reason {
                SemanticMatchUndetermined::WorkBudgetExhausted => 0,
                SemanticMatchUndetermined::Cancelled => 1,
                SemanticMatchUndetermined::InvalidImageEvidence => 2,
                SemanticMatchUndetermined::PremiseEvaluationUnavailable => 3,
                SemanticMatchUndetermined::ResourceGradeUnavailable => 4,
                SemanticMatchUndetermined::InputLimitExceeded => 5,
                SemanticMatchUndetermined::OutputLimitExceeded => 6,
                SemanticMatchUndetermined::EGraphNodeBudgetExhausted => 7,
                SemanticMatchUndetermined::AllocationFailed => 8,
                SemanticMatchUndetermined::FrontierLimitExceeded => 9,
                SemanticMatchUndetermined::ProofLimitExceeded => 10,
                SemanticMatchUndetermined::NormalizationStepLimitExceeded => 11,
                SemanticMatchUndetermined::NormalizationCycleDetected => 12,
            };
            return ReplyBody::Undetermined(DiagnosticDomain::Kernel, code);
        },
        Resource(error) => return boundary_diagnostic(error),
        Restore(error) => {
            let code = match error {
                TheoryPatternRestoreError::IdentifierOverflow => 0,
                TheoryPatternRestoreError::Automaton(_) => 1,
                TheoryPatternRestoreError::Allocation => 2,
            };
            return ReplyBody::Error(DiagnosticDomain::Restore, code);
        },
    };
    ReplyBody::Error(DiagnosticDomain::Service, code)
}

fn definition(runtime: Arc<RholangLanguageRuntime>, endpoint: Endpoint) -> Definition {
    Definition {
        urn: endpoint.urn().into(),
        fixed_channel: LANGUAGE_SEMANTIC_BAND.channel(endpoint.index(), LANGUAGE_SEMANTIC_ABI_V1),
        arity: 1,
        body_ref: LANGUAGE_SEMANTIC_BAND.body_ref(endpoint.index(), LANGUAGE_SEMANTIC_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let runtime = Arc::clone(&runtime);
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let runtime = Arc::clone(&runtime);
                Box::pin(async move {
                    let (produce, _, _, payload) = call.unapply_owned(args).ok_or_else(|| {
                        InterpreterError::IllegalArgumentError(
                            "semantic call requires exactly one message".into(),
                        )
                    })?;
                    // ProcessContext has no cancellation hook. The reusable
                    // preparation boundary accepts one; this endpoint enforces
                    // its deterministic work ceilings without inventing a hook.
                    let prepared = tokio::task::spawn_blocking(move || {
                        prepare_reply(&runtime, endpoint, payload, || false)
                    })
                    .await
                    .map_err(|_| {
                        InterpreterError::IllegalArgumentError(
                            "semantic preparation worker failed".into(),
                        )
                    })?
                    .map_err(|_| {
                        InterpreterError::IllegalArgumentError(
                            "semantic request could not prepare an authorized bounded reply".into(),
                        )
                    })?;
                    produce(prepared.payload, prepared.channel, Some(prepared.publication)).await
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

/// Both operations share the supplied runtime and its capability directory.
pub fn semantic_runtime_definitions(runtime: Arc<RholangLanguageRuntime>) -> Vec<Definition> {
    vec![
        definition(Arc::clone(&runtime), Endpoint::Reduce),
        definition(runtime, Endpoint::Observe),
    ]
}

#[cfg(test)]
mod tests;
