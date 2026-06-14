//! Gate-preserving Rho backend execution boundary.
//!
//! `run_validated_program*` is intentionally still available for oracle and
//! debug code that needs to inject a shape-validated AST. Generated backend
//! execution should use [`PlannedRhoBackend`]: it can only be built from a
//! `RhoDefaultBackendPlan`, which is the codegen artifact produced after the
//! proof, oracle, coverage, scheduler-fairness, validation, and deadlock gates
//! pass.

#[cfg(feature = "runtime-report")]
use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "runtime-report")]
use std::thread;

use mettail_rho_codegen::{
    CallByNeedThunkPlan, RhoArtifactKind, RhoDefaultBackendPlan, ValidatedRhoProgram,
};
#[cfg(feature = "runtime-report")]
use mettail_runtime::{
    AscentResults, Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeBackendCapability,
    RuntimeBackendReport, RuntimeChannelObservation, RuntimeObservationReportError,
    RuntimeObservationValue, SeedFacts, Term, TermType, VarTypeInfo, WeightedRewriteSeed,
    WeightedSeedId,
};
use models::rhoapi::Par;

use crate::run::{
    run_validated_program, run_validated_program_and_read_bools,
    run_validated_program_and_read_ints, run_validated_program_and_read_string_channels,
    run_validated_program_and_read_strings, run_validated_program_with_call,
    run_validated_program_with_call_and_read_bools, run_validated_program_with_call_and_read_ints,
    run_validated_program_with_call_and_read_strings,
};
#[cfg(feature = "runtime-report")]
use crate::run::{
    run_validated_program_and_read_runtime_values,
    run_validated_program_with_call_and_read_runtime_values,
};

/// Runtime boundary that produced a Rho observation report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhoExecutionBoundary {
    /// The result came from a `RhoDefaultBackendPlan` accepted by the flip gate.
    PlannedDefaultBackend,
}

/// Typed observation of resting data on one quoted Rho output channel.
///
/// `values` preserves the runtime read order for diagnostics. Use
/// [`membership_fingerprint`](Self::membership_fingerprint) for the
/// order-insensitive set view, or
/// [`multiplicity_fingerprint`](Self::multiplicity_fingerprint) when duplicate
/// observations are semantically relevant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoObservationReport<T> {
    pub boundary: RhoExecutionBoundary,
    pub artifact_kind: RhoArtifactKind,
    pub channel: String,
    pub values: Vec<T>,
}

#[cfg(feature = "runtime-report")]
fn runtime_artifact_kind(
    kind: RhoArtifactKind,
) -> Result<RuntimeBackendArtifact, RuntimeReportConversionError> {
    match kind {
        RhoArtifactKind::NormalizedAst => Ok(RuntimeBackendArtifact::RhoNormalizedAst),
        _ => Err(RuntimeReportConversionError::UnsupportedArtifactKind),
    }
}

/// Failure converting a typed Rho observation report into the generic runtime
/// backend report envelope.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeReportConversionError {
    /// A future Rho artifact kind was observed before the generic runtime
    /// report layer learned how to represent it.
    UnsupportedArtifactKind,
    /// The generic runtime report layer rejected the backend/artifact/output
    /// combination as not observation-shaped.
    InvalidRuntimeReportShape(RuntimeObservationReportError),
}

/// Conversion from typed Rho observation payloads into the generic runtime
/// observation value domain.
#[cfg(feature = "runtime-report")]
pub trait IntoRuntimeObservationValue {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue;
}

#[cfg(feature = "runtime-report")]
impl IntoRuntimeObservationValue for i64 {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue {
        RuntimeObservationValue::Int(self)
    }
}

#[cfg(feature = "runtime-report")]
impl IntoRuntimeObservationValue for bool {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue {
        RuntimeObservationValue::Bool(self)
    }
}

#[cfg(feature = "runtime-report")]
impl IntoRuntimeObservationValue for String {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue {
        RuntimeObservationValue::Text(self)
    }
}

#[cfg(feature = "runtime-report")]
impl IntoRuntimeObservationValue for Vec<u8> {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue {
        RuntimeObservationValue::Bytes(self)
    }
}

#[cfg(feature = "runtime-report")]
impl IntoRuntimeObservationValue for RuntimeObservationValue {
    fn into_runtime_observation_value(self) -> RuntimeObservationValue {
        self
    }
}

impl<T> RhoObservationReport<T> {
    fn planned(artifact_kind: RhoArtifactKind, channel: impl Into<String>, values: Vec<T>) -> Self {
        Self {
            boundary: RhoExecutionBoundary::PlannedDefaultBackend,
            artifact_kind,
            channel: channel.into(),
            values,
        }
    }

    /// Number of values observed on the channel, before membership projection.
    pub fn observed_count(&self) -> usize {
        self.values.len()
    }
}

#[cfg(feature = "runtime-report")]
impl<T> RhoObservationReport<T>
where
    T: IntoRuntimeObservationValue,
{
    /// Convert this typed Rho observation into the generic `Language` backend
    /// report shape without routing through `AscentResults`.
    pub fn try_into_runtime_backend_report(
        self,
        evidence_refs: Vec<String>,
    ) -> Result<RuntimeBackendReport, RuntimeReportConversionError> {
        let artifact = runtime_artifact_kind(self.artifact_kind)?;
        let values = self
            .values
            .into_iter()
            .map(IntoRuntimeObservationValue::into_runtime_observation_value)
            .collect();
        RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            artifact,
            vec![RuntimeChannelObservation::new(self.channel, values)],
            evidence_refs,
        )
        .map_err(RuntimeReportConversionError::InvalidRuntimeReportShape)
    }
}

impl<T: Clone + Ord> RhoObservationReport<T> {
    /// Order-insensitive exact-membership fingerprint of the observed values.
    pub fn membership_fingerprint(&self) -> BTreeSet<T> {
        self.values.iter().cloned().collect()
    }

    /// Order-insensitive counted fingerprint of the observed values.
    pub fn multiplicity_fingerprint(&self) -> BTreeMap<T, usize> {
        self.values
            .iter()
            .cloned()
            .fold(BTreeMap::new(), |mut counts, value| {
                *counts.entry(value).or_insert(0) += 1;
                counts
            })
    }
}

/// Executable Rho backend selected by the Rho-default flip gate.
#[derive(Debug, Clone, PartialEq)]
pub struct PlannedRhoBackend {
    plan: RhoDefaultBackendPlan,
}

impl PlannedRhoBackend {
    /// Accept a Rho-default backend plan that has already passed the codegen
    /// flip gate.
    pub fn from_plan(plan: RhoDefaultBackendPlan) -> Self {
        Self { plan }
    }

    /// The plan that selected this generated backend.
    pub fn plan(&self) -> &RhoDefaultBackendPlan {
        &self.plan
    }

    /// The validation-gated executable artifact carried by the plan.
    pub fn program(&self) -> &ValidatedRhoProgram {
        self.plan.program()
    }

    /// Current artifact kind. This is bytecode-ready: future bytecode variants
    /// can be added without making source text the execution boundary.
    pub fn artifact_kind(&self) -> RhoArtifactKind {
        self.program().artifact_kind()
    }

    /// Normalized AST to inject into the host Rho runtime, when available.
    pub fn ast_par(&self) -> Option<&Par> {
        self.program().ast_par()
    }

    /// Reader/debug annotation. This text is not parsed for execution.
    pub fn text_annotation(&self) -> &str {
        self.program().text_annotation()
    }

    /// Evidence references inherited from the flip-gated backend plan. Generated
    /// language metadata can use this list when advertising `RhoMachine` as an
    /// executable default backend.
    pub fn evidence_refs(&self) -> &[String] {
        self.plan.evidence_refs()
    }

    /// Run the generated backend artifact to quiescence.
    pub async fn run(&self) -> Result<(), String> {
        run_validated_program(self.program()).await
    }

    /// Run the generated backend artifact together with a dynamic call process.
    pub async fn run_with_call(&self, call: &Par) -> Result<(), String> {
        run_validated_program_with_call(self.program(), call).await
    }

    /// Run the generated backend artifact and read ground integers from a
    /// quoted output channel.
    pub async fn run_and_read_ints(&self, out_channel: &str) -> Result<Vec<i64>, String> {
        run_validated_program_and_read_ints(self.program(), out_channel).await
    }

    /// Run the generated backend artifact together with a dynamic call process
    /// and read ground integers from a quoted output channel.
    pub async fn run_with_call_and_read_ints(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<Vec<i64>, String> {
        run_validated_program_with_call_and_read_ints(self.program(), call, out_channel).await
    }

    /// Run the generated backend artifact and return a typed observation report
    /// for ground integers resting on a quoted output channel.
    pub async fn run_and_observe_ints(
        &self,
        out_channel: &str,
    ) -> Result<RhoObservationReport<i64>, String> {
        let values = self.run_and_read_ints(out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact with a dynamic call process and
    /// return a typed observation report for ground integers resting on a quoted
    /// output channel.
    pub async fn run_with_call_and_observe_ints(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<RhoObservationReport<i64>, String> {
        let values = self.run_with_call_and_read_ints(call, out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact and read ground booleans from a quoted
    /// output channel.
    pub async fn run_and_read_bools(&self, out_channel: &str) -> Result<Vec<bool>, String> {
        run_validated_program_and_read_bools(self.program(), out_channel).await
    }

    /// Run the generated backend artifact together with a dynamic call process
    /// and read ground booleans from a quoted output channel.
    pub async fn run_with_call_and_read_bools(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<Vec<bool>, String> {
        run_validated_program_with_call_and_read_bools(self.program(), call, out_channel).await
    }

    /// Run the generated backend artifact and return a typed observation report
    /// for ground booleans resting on a quoted output channel.
    pub async fn run_and_observe_bools(
        &self,
        out_channel: &str,
    ) -> Result<RhoObservationReport<bool>, String> {
        let values = self.run_and_read_bools(out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact with a dynamic call process and
    /// return a typed observation report for ground booleans resting on a quoted
    /// output channel.
    pub async fn run_with_call_and_observe_bools(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<RhoObservationReport<bool>, String> {
        let values = self.run_with_call_and_read_bools(call, out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact and read ground strings from a quoted
    /// output channel.
    pub async fn run_and_read_strings(&self, out_channel: &str) -> Result<Vec<String>, String> {
        run_validated_program_and_read_strings(self.program(), out_channel).await
    }

    /// Run the generated backend artifact together with a dynamic call process
    /// and read ground strings from a quoted output channel.
    pub async fn run_with_call_and_read_strings(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<Vec<String>, String> {
        run_validated_program_with_call_and_read_strings(self.program(), call, out_channel).await
    }

    /// Run the generated backend artifact and return a typed observation report
    /// for ground strings resting on a quoted output channel.
    pub async fn run_and_observe_strings(
        &self,
        out_channel: &str,
    ) -> Result<RhoObservationReport<String>, String> {
        let values = self.run_and_read_strings(out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact with a dynamic call process and
    /// return a typed observation report for ground strings resting on a quoted
    /// output channel.
    pub async fn run_with_call_and_observe_strings(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<RhoObservationReport<String>, String> {
        let values = self
            .run_with_call_and_read_strings(call, out_channel)
            .await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact and read closed Rho ground values
    /// from a quoted output channel.
    #[cfg(feature = "runtime-report")]
    pub async fn run_and_read_runtime_values(
        &self,
        out_channel: &str,
    ) -> Result<Vec<RuntimeObservationValue>, String> {
        run_validated_program_and_read_runtime_values(self.program(), out_channel).await
    }

    /// Run the generated backend artifact together with a dynamic call process
    /// and read closed Rho ground values from a quoted output channel.
    #[cfg(feature = "runtime-report")]
    pub async fn run_with_call_and_read_runtime_values(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<Vec<RuntimeObservationValue>, String> {
        run_validated_program_with_call_and_read_runtime_values(self.program(), call, out_channel)
            .await
    }

    /// Run the generated backend artifact and return a typed observation report
    /// for closed Rho ground values resting on a quoted output channel.
    #[cfg(feature = "runtime-report")]
    pub async fn run_and_observe_runtime_values(
        &self,
        out_channel: &str,
    ) -> Result<RhoObservationReport<RuntimeObservationValue>, String> {
        let values = self.run_and_read_runtime_values(out_channel).await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Run the generated backend artifact with a dynamic call process and
    /// return a typed observation report for closed Rho ground values resting on
    /// a quoted output channel.
    #[cfg(feature = "runtime-report")]
    pub async fn run_with_call_and_observe_runtime_values(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<RhoObservationReport<RuntimeObservationValue>, String> {
        let values = self
            .run_with_call_and_read_runtime_values(call, out_channel)
            .await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }
}

/// Executable M-RHO.2 call-by-need thunk selected by the need planner.
///
/// This wrapper exists so call-by-need runtime tests and future generated need
/// paths consume [`CallByNeedThunkPlan`] rather than a raw
/// [`ValidatedRhoProgram`]. The raw validation helpers remain available for
/// oracle/debug code, but this is the production-shaped need boundary.
#[derive(Debug, Clone, PartialEq)]
pub struct PlannedCallByNeedThunk {
    plan: CallByNeedThunkPlan,
}

impl PlannedCallByNeedThunk {
    /// Accept a need plan that has passed budget admission, artifact
    /// validation, and evidence-reference checks.
    pub fn from_plan(plan: CallByNeedThunkPlan) -> Self {
        Self { plan }
    }

    pub fn plan(&self) -> &CallByNeedThunkPlan {
        &self.plan
    }

    pub fn program(&self) -> &ValidatedRhoProgram {
        self.plan.program()
    }

    pub fn artifact_kind(&self) -> RhoArtifactKind {
        self.program().artifact_kind()
    }

    pub fn evidence_refs(&self) -> &[String] {
        self.plan.evidence_refs()
    }

    /// Run the planned thunk artifact and read ground strings from each quoted
    /// output channel.
    pub async fn run_and_read_string_channels(
        &self,
        out_channels: &[&str],
    ) -> Result<BTreeMap<String, Vec<String>>, String> {
        let observed =
            run_validated_program_and_read_string_channels(self.program(), out_channels).await?;
        Ok(observed.into_iter().collect())
    }

    /// Run the planned thunk artifact and read the output/evaluation channels
    /// named by its generated-language thunk spec.
    pub async fn run_and_read_need_channels(
        &self,
    ) -> Result<BTreeMap<String, Vec<String>>, String> {
        let spec = self.plan.spec();
        self.run_and_read_string_channels(&[spec.out_channel(), spec.eval_channel()])
            .await
    }

    /// Run the planned thunk artifact and return a typed observation report for
    /// one quoted output channel.
    pub async fn run_and_observe_strings(
        &self,
        out_channel: &str,
    ) -> Result<RhoObservationReport<String>, String> {
        let mut channels = self.run_and_read_string_channels(&[out_channel]).await?;
        let values = channels.remove(out_channel).unwrap_or_default();
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }
}

/// Dynamic operation that a Rho-backed generated language wants to execute for
/// one typed input term.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone)]
pub enum RhoBackendInvocation {
    /// Run the planned backend and observe integer values on the channel.
    RunAndObserveInts { out_channel: String },
    /// Run the planned backend and observe boolean values on the channel.
    RunAndObserveBools { out_channel: String },
    /// Run the planned backend and observe string values on the channel.
    RunAndObserveStrings { out_channel: String },
    /// Run the planned backend and observe closed Rho ground values on the
    /// channel.
    RunAndObserveRuntimeValues { out_channel: String },
    /// Run the planned backend with a dynamic `rhoapi::Par` call and observe
    /// integer values on the channel.
    RunWithCallAndObserveInts { call: Par, out_channel: String },
    /// Run the planned backend with a dynamic `rhoapi::Par` call and observe
    /// boolean values on the channel.
    RunWithCallAndObserveBools { call: Par, out_channel: String },
    /// Run the planned backend with a dynamic `rhoapi::Par` call and observe
    /// string values on the channel.
    RunWithCallAndObserveStrings { call: Par, out_channel: String },
    /// Run the planned backend with a dynamic `rhoapi::Par` call and observe
    /// closed Rho ground values on the channel.
    RunWithCallAndObserveRuntimeValues { call: Par, out_channel: String },
}

#[cfg(feature = "runtime-report")]
impl RhoBackendInvocation {
    async fn execute(self, backend: &PlannedRhoBackend) -> Result<RuntimeBackendReport, String> {
        let evidence_refs = backend.evidence_refs().to_vec();
        match self {
            RhoBackendInvocation::RunAndObserveInts { out_channel } => backend
                .run_and_observe_ints(&out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| {
                    format!("failed to convert Rho integer observation report: {err:?}")
                }),
            RhoBackendInvocation::RunAndObserveBools { out_channel } => backend
                .run_and_observe_bools(&out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| {
                    format!("failed to convert Rho boolean observation report: {err:?}")
                }),
            RhoBackendInvocation::RunAndObserveStrings { out_channel } => backend
                .run_and_observe_strings(&out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| format!("failed to convert Rho string observation report: {err:?}")),
            RhoBackendInvocation::RunAndObserveRuntimeValues { out_channel } => backend
                .run_and_observe_runtime_values(&out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| {
                    format!("failed to convert Rho runtime value observation report: {err:?}")
                }),
            RhoBackendInvocation::RunWithCallAndObserveInts { call, out_channel } => backend
                .run_with_call_and_observe_ints(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| {
                    format!("failed to convert Rho integer observation report: {err:?}")
                }),
            RhoBackendInvocation::RunWithCallAndObserveBools { call, out_channel } => backend
                .run_with_call_and_observe_bools(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| {
                    format!("failed to convert Rho boolean observation report: {err:?}")
                }),
            RhoBackendInvocation::RunWithCallAndObserveStrings { call, out_channel } => backend
                .run_with_call_and_observe_strings(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report(evidence_refs)
                .map_err(|err| format!("failed to convert Rho string observation report: {err:?}")),
            RhoBackendInvocation::RunWithCallAndObserveRuntimeValues { call, out_channel } => {
                backend
                    .run_with_call_and_observe_runtime_values(&call, &out_channel)
                    .await?
                    .try_into_runtime_backend_report(evidence_refs)
                    .map_err(|err| {
                        format!("failed to convert Rho runtime value observation report: {err:?}")
                    })
            },
        }
    }
}

#[cfg(feature = "runtime-report")]
fn run_rho_invocation_blocking(
    backend: PlannedRhoBackend,
    invocation: RhoBackendInvocation,
) -> Result<RuntimeBackendReport, String> {
    let worker = thread::Builder::new()
        .name("mettail-rho-backend-report".to_string())
        .spawn(move || {
            let runtime = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|err| format!("failed to create Rho backend runtime: {err}"))?;
            runtime.block_on(invocation.execute(&backend))
        })
        .map_err(|err| format!("failed to spawn Rho backend runtime worker: {err}"))?;

    worker
        .join()
        .map_err(|_| "Rho backend runtime worker panicked".to_string())?
}

/// Runtime adapter that makes a generated language select a flip-gated
/// [`PlannedRhoBackend`] through the generic [`Language`] report API.
///
/// The wrapped language remains the source of parsing, environments, type
/// inference, and the Ascent oracle. The adapter changes only the runtime
/// backend selection surface: `RhoMachine` becomes the default, explicit Ascent
/// requests still delegate to the wrapped language, and the legacy
/// `AscentResults` compatibility methods reject Rho observation reports.
#[cfg(feature = "runtime-report")]
pub struct RhoRuntimeBackedLanguage<L, F> {
    inner: L,
    backend: PlannedRhoBackend,
    invocation: F,
}

#[cfg(feature = "runtime-report")]
impl<L, F> RhoRuntimeBackedLanguage<L, F>
where
    F: Fn(&dyn Term) -> Result<RhoBackendInvocation, String> + Send + Sync,
{
    pub fn new(inner: L, backend: PlannedRhoBackend, invocation: F) -> Self {
        Self { inner, backend, invocation }
    }

    pub fn inner(&self) -> &L {
        &self.inner
    }

    pub fn backend(&self) -> &PlannedRhoBackend {
        &self.backend
    }
}

#[cfg(feature = "runtime-report")]
impl<L, F> Language for RhoRuntimeBackedLanguage<L, F>
where
    L: Language,
    F: Fn(&dyn Term) -> Result<RhoBackendInvocation, String> + Send + Sync,
{
    fn name(&self) -> &'static str {
        self.inner.name()
    }

    fn metadata(&self) -> &'static dyn mettail_runtime::LanguageMetadata {
        self.inner.metadata()
    }

    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term(input)
    }

    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        self.inner.parse_term_for_env(input)
    }

    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        self.inner.parse_term_with_weighted_seed_ids(input)
    }

    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        self.inner.parse_term_with_weighted_rewrite_seeds(input)
    }

    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
        self.inner.run_ascent(term)
    }

    fn default_runtime_backend(&self) -> RuntimeBackend {
        RuntimeBackend::RhoMachine
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        let inner_capabilities = self.inner.runtime_backend_capabilities();
        let mut capabilities = Vec::with_capacity(inner_capabilities.len().saturating_add(1));
        capabilities.push(RuntimeBackendCapability {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
            evidence_refs: self.backend.evidence_refs().to_vec(),
        });
        capabilities.extend(
            inner_capabilities
                .into_iter()
                .filter(|capability| capability.backend != RuntimeBackend::RhoMachine)
                .map(|mut capability| {
                    capability.is_default = false;
                    capability
                }),
        );
        capabilities
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        backend == RuntimeBackend::RhoMachine || self.inner.supports_runtime_backend(backend)
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::RhoMachine => {
                let invocation = (self.invocation)(term).map_err(|err| {
                    format!(
                        "RhoMachine backend for language {} could not build an AST invocation: {err}",
                        self.name()
                    )
                })?;
                run_rho_invocation_blocking(self.backend.clone(), invocation)
            },
            other => self.inner.run_backend_report(other, term),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        self.inner.run_ascent_with_facts(term, facts)
    }

    fn run_backend_report_with_facts(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::RhoMachine if facts.is_empty() => {
                self.run_backend_report(backend, term)
            },
            RuntimeBackend::RhoMachine => Err(format!(
                "RhoMachine backend for language {} does not accept Ascent-shaped seeded facts",
                self.name()
            )),
            other => self.inner.run_backend_report_with_facts(other, term, facts),
        }
    }

    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        self.inner.try_direct_eval(term)
    }

    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        self.inner.normalize_term(term)
    }

    fn format_term(&self, term: &dyn Term) -> String {
        self.inner.format_term(term)
    }

    fn create_env(&self) -> Box<dyn Any + Send + Sync> {
        self.inner.create_env()
    }

    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
        self.inner.add_to_env(env, name, term)
    }

    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
        self.inner.remove_from_env(env, name)
    }

    fn clear_env(&self, env: &mut dyn Any) {
        self.inner.clear_env(env)
    }

    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env(term, env)
    }

    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.inner.substitute_env_preserve_structure(term, env)
    }

    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
        self.inner.list_env(env)
    }

    fn set_env_comment(
        &self,
        env: &mut dyn Any,
        name: &str,
        comment: String,
    ) -> Result<(), String> {
        self.inner.set_env_comment(env, name, comment)
    }

    fn is_env_empty(&self, env: &dyn Any) -> bool {
        self.inner.is_env_empty(env)
    }

    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        self.inner.get_env_term(env, name)
    }

    fn infer_term_type(&self, term: &dyn Term) -> TermType {
        self.inner.infer_term_type(term)
    }

    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
        self.inner.infer_var_types(term)
    }

    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
        self.inner.infer_var_type(term, var_name)
    }

    fn decompose_into_cek(
        &self,
        term: &dyn Term,
        evaluator: &mut mettail_prattail::cek_eval::CekEvaluator,
    ) -> bool {
        self.inner.decompose_into_cek(term, evaluator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observation_report_fingerprint_is_membership_not_runtime_order() {
        let report = RhoObservationReport::planned(
            RhoArtifactKind::NormalizedAst,
            "OUT",
            vec![3_i64, 1, 3, 2],
        );

        assert_eq!(report.boundary, RhoExecutionBoundary::PlannedDefaultBackend);
        assert_eq!(report.artifact_kind, RhoArtifactKind::NormalizedAst);
        assert_eq!(report.channel, "OUT");
        assert_eq!(report.observed_count(), 4);
        assert_eq!(report.membership_fingerprint(), BTreeSet::from([1_i64, 2, 3]));
        assert_eq!(
            report.multiplicity_fingerprint(),
            BTreeMap::from([(1_i64, 1_usize), (2, 1), (3, 2)])
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn observation_report_converts_to_runtime_backend_report() {
        let report =
            RhoObservationReport::planned(RhoArtifactKind::NormalizedAst, "OUT", vec![3_i64, 1, 3])
                .try_into_runtime_backend_report(vec![
                    "formal/rocq/rho_bridge/theories/RhoObservationReportBoundary.v".to_string(),
                    "formal/rocq/rho_bridge/theories/RhoRuntimeBackendReportBridge.v".to_string(),
                ])
                .expect("normalized AST observations must convert to runtime backend reports");

        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
        assert_eq!(
            report.evidence_refs(),
            vec![
                "formal/rocq/rho_bridge/theories/RhoObservationReportBoundary.v",
                "formal/rocq/rho_bridge/theories/RhoRuntimeBackendReportBridge.v",
            ]
        );

        let out = report
            .observations_for_channel("OUT")
            .expect("converted report must preserve the observed channel");
        assert_eq!(out.observed_count(), 3);
        assert_eq!(
            out.values,
            vec![
                RuntimeObservationValue::Int(3),
                RuntimeObservationValue::Int(1),
                RuntimeObservationValue::Int(3),
            ]
        );
        assert_eq!(
            out.membership_fingerprint(),
            BTreeSet::from([RuntimeObservationValue::Int(1), RuntimeObservationValue::Int(3)])
        );
        assert_eq!(
            out.multiplicity_fingerprint(),
            BTreeMap::from([
                (RuntimeObservationValue::Int(1), 1_usize),
                (RuntimeObservationValue::Int(3), 2_usize),
            ])
        );
    }
}
