//! Explicit one-way structural display projection for admitted guest terms.
//!
//! This path invokes neither the guest source parser nor a second evaluator.
//! It uses the installed FLT adapter and kernel's checked positional/native
//! view, then the compiled Rholang ground-String host codec. Publication keeps
//! both the guest and host-profile revocation guards live atomically.

use super::*;
use crate::host_profile::RholangHostProfileProvider;
use mettail_grammar_core::{
    InstalledHostProfileHandle, LanguageAndHostAccessError, TheoryLiteralCarrierV1,
    TheorySortKindV1,
};

// A guest may reveal its checked structure only with ReflectAst. The distinct
// host-profile Bridge right authorizes materialization as a host String.
const DISPLAY_RIGHTS: [LanguageRight; 1] = [LanguageRight::ReflectAst];

pub struct DisplayServiceRequest<'a> {
    pub handle: &'a Par,
    pub category: &'a str,
    pub input: &'a Par,
    pub limits: SemanticServiceLimits,
}

#[derive(Debug)]
pub struct DisplayServiceReport {
    pub outcome: Result<Par, InstalledSemanticError>,
    pub work: u64,
    pub effective_limits: Option<SemanticServiceLimits>,
    pub remaining_boundary_payload_bytes: usize,
}

pub(super) struct DisplayPublication {
    table: Arc<InstalledLanguageTable>,
    language: InstalledLanguageHandle,
    host: InstalledHostProfileHandle,
}

impl DisplayPublication {
    fn authorize<R>(&self, commit: impl FnOnce() -> R) -> Result<R, InstalledSemanticError> {
        self.table
            .with_authorized_language_and_host(
                &self.language,
                &DISPLAY_RIGHTS,
                &self.host,
                &[LanguageRight::Bridge],
                commit,
            )
            .map_err(|error| match error {
                LanguageAndHostAccessError::Language(error) => {
                    InstalledSemanticError::Access(error)
                },
                LanguageAndHostAccessError::Host(_) => {
                    InstalledSemanticError::Access(LanguageAccessError::HostProfileUnavailable)
                },
            })
    }
}

impl ProduceCommitGuard for DisplayPublication {
    fn with_commit(&self, commit: Box<dyn FnOnce() + '_>) -> Result<(), RSpaceError> {
        self.authorize(commit)
            .map_err(|_| RSpaceError::ProduceCommitDenied)
    }
}

pub(super) struct PreparedDisplayReport {
    pub(super) outcome: Result<Par, InstalledSemanticError>,
    pub(super) publication: Option<DisplayPublication>,
    pub(super) usage: SemanticServiceUsage,
}

impl PreparedDisplayReport {
    fn commit(self) -> DisplayServiceReport {
        let outcome = self.outcome.and_then(|value| {
            let publication = self
                .publication
                .ok_or(InstalledSemanticError::InvalidEvidence(
                    "prepared display has no publication context",
                ))?;
            publication.authorize(|| value)
        });
        DisplayServiceReport {
            outcome,
            work: self.usage.work,
            effective_limits: self.usage.effective_limits,
            remaining_boundary_payload_bytes: self.usage.remaining_boundary_payload_bytes,
        }
    }
}

impl RholangLanguageRuntime {
    /// Derive one display value for one explicitly named guest category.
    /// This standalone entry performs the same final capability recheck as
    /// the guarded wire endpoint, but does not commit node effects.
    pub fn execute_display<C: FnMut() -> bool>(
        &self,
        request: DisplayServiceRequest<'_>,
        is_cancelled: C,
    ) -> DisplayServiceReport {
        self.prepare_display(request, SemanticServicePrefix::default(), is_cancelled)
            .commit()
    }

    pub(super) fn prepare_display<C: FnMut() -> bool>(
        &self,
        request: DisplayServiceRequest<'_>,
        prefix: SemanticServicePrefix,
        mut is_cancelled: C,
    ) -> PreparedDisplayReport {
        let mut work = prefix.work;
        let mut effective_limits = None;
        let mut publication = None;
        let mut remaining = 0;
        let host_policy = self.service().policy().semantic_service;
        let outcome = (|| {
            remaining = host_policy
                .boundary_payload_bytes
                .min(request.limits.boundary_payload_bytes)
                .checked_sub(prefix.payload_bytes)
                .ok_or(DynamicReflectionError::PayloadByteLimit)?;
            let handle = self
                .resolve(request.handle, LanguageRight::ReflectAst)
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
                        "unexpected display capability resolution failure",
                    ),
                })?;
            let table = self.service().table();
            let installed = table
                .authorize_all(&handle, &DISPLAY_RIGHTS)
                .map_err(InstalledSemanticError::Access)?;
            let (host_handle, host) =
                self.service().builtin_host_profile_binding().map_err(|_| {
                    InstalledSemanticError::Access(LanguageAccessError::HostProfileUnavailable)
                })?;
            if !host.record().payload.sorts.iter().any(|sort| {
                sort.name == "Str"
                    && sort.kind
                        == TheorySortKindV1::Syntax {
                            literal: Some(TheoryLiteralCarrierV1::String),
                        }
            }) {
                return Err(InstalledSemanticError::InvalidEvidence(
                    "selected host profile has no exact String fragment",
                ));
            }
            let limits =
                host_policy.effective(installed.language_core().theory.limits, request.limits);
            effective_limits = Some(limits);
            publication = Some(DisplayPublication {
                table: Arc::clone(table),
                language: handle,
                host: host_handle,
            });
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                limits.execution.work,
                remaining,
                &mut is_cancelled,
            );
            let value = (|| {
                let adapter = InstalledFltAdapter::new(&installed, &mut budget)?;
                let (category, sort) = adapter.select_category(request.category, &mut budget)?;
                let input = adapter.to_kernel(
                    request.input,
                    category,
                    SemanticInputLimits {
                        work: limits.execution.work,
                        nodes: limits.execution.term_nodes,
                        bytes: limits.execution.term_bytes,
                    },
                    &mut budget,
                )?;
                let text = adapter.project_admitted_display(
                    &input,
                    sort,
                    limits.execution.output_bytes,
                    &mut budget,
                )?;
                // The host value materializes a second copy of these bytes.
                budget.charge(text.len(), text.len())?;
                RholangHostProfileProvider::string_to_host(&text).map_err(|_| {
                    InstalledSemanticError::InvalidEvidence(
                        "Rholang String host codec refused display",
                    )
                })
            })();
            remaining = budget.finish();
            value
        })();
        PreparedDisplayReport {
            outcome,
            publication,
            usage: SemanticServiceUsage {
                work,
                kernel_work: None,
                effective_limits,
                remaining_boundary_payload_bytes: remaining,
            },
        }
    }
}
