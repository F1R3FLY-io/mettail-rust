//! Gate-preserving Rho backend execution boundary.
//!
//! `run_validated_program*` is intentionally still available for oracle and
//! debug code that needs to inject a shape-validated AST. Generated backend
//! execution should use [`PlannedRhoBackend`]: it can only be built from a
//! `RhoDefaultBackendPlan` whose coverage, validation, and deadlock gates
//! passed.

#[cfg(feature = "runtime-report")]
use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "runtime-report")]
use std::fmt;
#[cfg(feature = "runtime-report")]
use std::thread;

use mettail_rholang_codegen::{
    CallByNeedThunkPlan, RhoArtifactKind, RhoDefaultBackendPlan, ValidatedRhoProgram,
};
#[cfg(feature = "runtime-report")]
use mettail_rholang_codegen::{
    RhoAstBuildError, RhoAstLiteral, RhoAstSend, RhoFoldDataflowInvocation, RhoScalarContractAbi,
    RhoScalarContractInvocation, RhoScalarContractShape, RhoScalarType,
};
#[cfg(feature = "runtime-report")]
use mettail_runtime::{
    AscentResults, Language, RuntimeBackend, RuntimeBackendArtifact, RuntimeBackendCapability,
    RuntimeBackendReport, RuntimeChannelObservation, RuntimeDovetailRunReport,
    RuntimeObservationReportError, RuntimeObservationValue, SeedFacts, Term, TermType, VarTypeInfo,
    WeightedRewriteSeed, WeightedSeedId,
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
    run_installed_program_with_call_and_read_runtime_values,
    run_validated_program_and_read_runtime_value_and_string_channels,
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
    ) -> Result<RuntimeBackendReport, RuntimeReportConversionError> {
        let artifact = runtime_artifact_kind(self.artifact_kind)?;
        let values = self
            .values
            .into_iter()
            .map(IntoRuntimeObservationValue::into_runtime_observation_value)
            .collect();
        // Formal model: `formal/rocq/rho_bridge/theories/RhoRuntimeBackendReportBridge.v`.
        RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            artifact,
            vec![RuntimeChannelObservation::new(self.channel, values)],
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
    /// flip gate and artifact-validation boundary.
    ///
    /// Formal model: `formal/rocq/rho_bridge/theories/RhoPlannedExecutionBoundary.v`.
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

    /// Run this backend's **installed Rho-net program** — its base-rewrite
    /// σ-receivers and native-fold contracts
    /// ([`RhoDefaultBackendPlan::installed_rho_net_program_par`]) — composed with a
    /// dynamic σ-injection `call`, and return a typed observation report for
    /// closed Rho ground values resting on a quoted output channel.
    ///
    /// This is the Epic 4 injection-bridge execution surface. Unlike
    /// [`run_with_call_and_observe_runtime_values`](Self::run_with_call_and_observe_runtime_values),
    /// which composes the call against the scalar `program()` and therefore never
    /// installs the σ-receivers, this installs the σ-receiver program so a
    /// hand-built (or, in a later slice, Dovetail-report-derived) σ injection
    /// actually fires its receiver and lands the reflected RHS on the out channel.
    #[cfg(feature = "runtime-report")]
    pub async fn run_rho_net_with_call_and_observe_runtime_values(
        &self,
        call: &Par,
        out_channel: &str,
    ) -> Result<RhoObservationReport<RuntimeObservationValue>, String> {
        // Fail-closed install boundary (Epic 4 #2011): refuse to run a σ-receiver
        // program that dropped unlowered work, BEFORE any Rho reduction — so an
        // unsupported lowering surfaces here, never as a silent runtime no-op.
        let installed = self
            .plan()
            .installed_rho_net_program_par()
            .map_err(|err| err.to_string())?;
        let values =
            run_installed_program_with_call_and_read_runtime_values(&installed, call, out_channel)
                .await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// [`run_rho_net_with_call_and_observe_runtime_values`](Self::run_rho_net_with_call_and_observe_runtime_values)
    /// with EXPLICIT extra system-process `Definition`s (the MeTTaIL-injected held-fold / A-S3
    /// native-handler contracts) installed on the runtime before the composed program runs.
    ///
    /// The production exec path (`run_backend_report`) drains the contracts recorded by its
    /// invocation compiler and threads them through the worker-thread pending slot; this
    /// explicit variant serves callers that hold the `Definition`s directly — the A-S3
    /// trusted-handler probes, which corrupt the compiled call `Par` between compile and run
    /// (wrong-σ delivery) and therefore must drive the run themselves.
    #[cfg(feature = "runtime-report")]
    pub async fn run_rho_net_with_call_definitions_and_observe_runtime_values(
        &self,
        call: &Par,
        definitions: Vec<rholang::rust::interpreter::system_processes::Definition>,
        out_channel: &str,
    ) -> Result<RhoObservationReport<RuntimeObservationValue>, String> {
        let installed = self
            .plan()
            .installed_rho_net_program_par()
            .map_err(|err| err.to_string())?;
        let values = crate::run::run_installed_program_with_call_definitions_and_read_runtime_values(
            &installed,
            call,
            definitions,
            out_channel,
        )
        .await?;
        Ok(RhoObservationReport::planned(self.artifact_kind(), out_channel, values))
    }

    /// Stage 0 multi-firing replay: install the Rho-net σ-receiver program ONCE,
    /// then run it composed with each firing's σ-injection `call` (each on its own
    /// out channel) and collect every firing's observed closed Rho ground values
    /// into one report.
    ///
    /// Each firing is an independent atomic COMM against the installed σ-receivers
    /// — the host Dovetail report already computed every firing's σ, so a
    /// multi-redex reduction replays as one `c(ℓ)` COMM per redex, and the whole
    /// reduction's non-semantic-predicate rewrites all execute as COMMs. The
    /// combined report's `out_channel` records the per-firing channels (joined),
    /// and its values are every firing's observed `⟦R⟧σ` in firing order.
    ///
    /// Fail-closed BEFORE any Rho reduction (`installed_rho_net_program_par`): an
    /// unsupported lowering surfaces at the install boundary, never as a silent
    /// runtime no-op.
    #[cfg(feature = "runtime-report")]
    pub async fn run_rho_net_replay_and_observe_runtime_values(
        &self,
        firings: &[(Par, String)],
    ) -> Result<RhoObservationReport<RuntimeObservationValue>, String> {
        let installed = self
            .plan()
            .installed_rho_net_program_par()
            .map_err(|err| err.to_string())?;
        let mut values = Vec::new();
        let mut out_channels = Vec::with_capacity(firings.len());
        for (call, out_channel) in firings {
            let firing_values = run_installed_program_with_call_and_read_runtime_values(
                &installed,
                call,
                out_channel,
            )
            .await?;
            values.extend(firing_values);
            out_channels.push(out_channel.as_str());
        }
        let combined_out = out_channels.join(",");
        Ok(RhoObservationReport::planned(self.artifact_kind(), &combined_out, values))
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
    /// validation, and the call-by-need construction boundary.
    ///
    /// Formal models: `RhoCallByNeedObservation.v` and `RhoCallByNeedBudget.v`.
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
    /// named by its generated-language thunk spec as ground strings.
    ///
    /// This compatibility helper is for string-valued CBN fixtures. Generic
    /// runtime reports use [`Self::run_and_observe_need_report`] so typed
    /// generated-language values are preserved.
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

    /// Run the planned thunk artifact and convert its generated-language value
    /// and evaluation-trace channels into the generic runtime report envelope.
    #[cfg(feature = "runtime-report")]
    pub async fn run_and_observe_need_report(&self) -> Result<RuntimeBackendReport, String> {
        let spec = self.plan.spec();
        let (out_values, eval_strings) =
            run_validated_program_and_read_runtime_value_and_string_channels(
                self.program(),
                spec.out_channel(),
                spec.eval_channel(),
            )
            .await?;
        let eval_values = eval_strings
            .into_iter()
            .map(RuntimeObservationValue::Text)
            .collect();
        let artifact = runtime_artifact_kind(self.artifact_kind())
            .map_err(|err| format!("failed to convert CBN thunk artifact kind: {err:?}"))?;
        RuntimeBackendReport::try_observations(
            RuntimeBackend::RhoMachine,
            artifact,
            vec![
                RuntimeChannelObservation::new(spec.out_channel(), out_values),
                RuntimeChannelObservation::new(spec.eval_channel(), eval_values),
            ],
        )
        .map_err(|err| format!("failed to convert CBN thunk observations: {err:?}"))
    }
}

/// Dynamic operation that can execute directly on the Rho machine.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone)]
pub enum RhoMachineInvocation {
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
    /// Run this backend's INSTALLED Rho-net program (its base-rewrite σ-receivers)
    /// composed with a dynamic σ-injection `call`, and observe closed Rho ground
    /// values on the channel (the Epic 4 injection bridge).
    ///
    /// Unlike [`RunWithCallAndObserveRuntimeValues`](Self::RunWithCallAndObserveRuntimeValues),
    /// which composes the call against the scalar `program()` and therefore never
    /// installs the σ-receivers, this composes against
    /// `installed_rho_net_program_par()` so a Dovetail-report-derived σ injection
    /// actually fires its receiver and lands the reflected RHS on the out channel.
    RunRhoNetWithCallAndObserveRuntimeValues { call: Par, out_channel: String },
    /// Stage 0 multi-firing replay: run this backend's INSTALLED Rho-net program
    /// (`installed_rho_net_program_par`) once per rewrite firing, each composed
    /// with that firing's σ-injection `call` on its own out channel, and collect
    /// every firing's observed closed Rho ground values.
    ///
    /// A multi-redex term's Dovetail report yields one firing per redex; the
    /// replay driver fires each as its own atomic COMM against the same installed
    /// σ-receiver program (the host report already computed every firing's σ), so
    /// the whole reduction's rewrites all execute as `c(ℓ)` COMMs. Each element is
    /// `(call, out_channel)` from
    /// `<Lang>::rho_net_invocation_from_dovetail_to_firing`.
    RunRhoNetReplayAndObserveRuntimeValues { firings: Vec<(Par, String)> },
    /// Run a generated-language call-by-need thunk plan and report the
    /// spec-named value/evaluation channels.
    RunCallByNeedThunk { plan: Box<CallByNeedThunkPlan> },
}

/// Dynamic operation selected by a checked Dovetail+Rho backend.
///
/// Every executable branch is a [`RhoMachineInvocation`]. The only non-machine
/// branch is a semantic-predicate block whose observational payload is the
/// already checked Dovetail report owned by the composed wrapper.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone)]
pub enum RhoBackendInvocation {
    RhoMachine(RhoMachineInvocation),
    DeferToDovetailSemanticPredicate { predicate: String },
}

#[cfg(feature = "runtime-report")]
impl From<RhoMachineInvocation> for RhoBackendInvocation {
    fn from(value: RhoMachineInvocation) -> Self {
        Self::RhoMachine(value)
    }
}

/// A-S2 (D-stage demotion): why a REPORT-FREE invocation compile (`F2`) deferred instead of
/// producing a Rho-machine invocation.
///
/// This is the error type of the lazy wrapper's report-free compiler seam
/// (`F2: Fn(&dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral>`). A deferral is
/// NOT a failure: it routes the term to the LAZY D-stage — the wrapper then builds the checked
/// Dovetail report (`checked_complete_dovetail_report`) and takes today's report-carrying paths.
/// Only after that lazy stage can a hard error surface, and it surfaces with exactly the message
/// the eager pipeline produced (the D-stage error, or the report-carrying compiler's error).
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoInvocationDeferral {
    /// The term is admitted structurally but a SEMANTIC PREDICATE (safe-arithmetic ÷0/overflow,
    /// …) blocks Rho execution. The wrapper lazily builds the checked Dovetail report and returns
    /// it as the observational payload — the same `DeferToDovetailSemanticPredicate` outcome the
    /// eager pipeline produced, with the D-stage now run only on this deferral path.
    SemanticPredicate { predicate: String },
    /// The report-free compile cannot admit the term: the static capability gate rejected (a
    /// fireable rule is not matchable in Rho), the located shape is out of report-free scope
    /// (a located native rule with NO registrable machine-side handler — a non-scalar or
    /// non-ground-parseable native shape — needs the host D-stage value; a nested-entry
    /// multi-site install would contend), or the compile failed outright. The wrapper lazily
    /// builds the checked Dovetail report and runs the report-carrying fallback compiler —
    /// today's exact paths (the report-driven match, the σ-replay driver, or the fallback's own
    /// error). A-S3: a located native site whose rule HAS a registrable handler ADMITS instead
    /// (the machine invokes the registered evaluator at COMM time).
    GateReject { detail: String },
}

#[cfg(feature = "runtime-report")]
impl fmt::Display for RhoInvocationDeferral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SemanticPredicate { predicate } => {
                write!(f, "semantic-predicate deferral: {predicate}")
            },
            Self::GateReject { detail } => write!(f, "gate-reject deferral: {detail}"),
        }
    }
}

/// Runtime site selected for a compiled [`RhoBackendInvocation`].
///
/// This is the audit boundary for the Rho-native migration. `RhoMachine`
/// variants carry normalized `rhoapi::Par` work injected into the Rho runtime.
/// `SemanticPredicateHost` is the only non-Rho-machine site: it represents a
/// semantic-predicate block whose observational payload is the checked Dovetail
/// report.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoInvocationExecutionSite {
    RhoMachine,
    SemanticPredicateHost,
}

#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhoScalarInvocationLiteralType {
    Int,
    Bool,
    Str,
    NonScalar,
}

#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoScalarInvocationError {
    ArityMismatch {
        rule_label: String,
        expected: usize,
        actual: usize,
    },
    ArgumentTypeMismatch {
        rule_label: String,
        position: usize,
        expected: RhoScalarType,
        actual: RhoScalarInvocationLiteralType,
    },
    AstBuild(RhoAstBuildError),
}

#[cfg(feature = "runtime-report")]
impl fmt::Display for RhoScalarInvocationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArityMismatch { rule_label, expected, actual } => write!(
                f,
                "Rho scalar contract {rule_label} expected {expected} operand(s), got {actual}"
            ),
            Self::ArgumentTypeMismatch { rule_label, position, expected, actual } => write!(
                f,
                "Rho scalar contract {rule_label} expected {expected:?} at operand {position}, got {actual:?}"
            ),
            Self::AstBuild(err) => write!(f, "failed to build Rho scalar contract AST call: {err:?}"),
        }
    }
}

#[cfg(feature = "runtime-report")]
impl std::error::Error for RhoScalarInvocationError {}

#[cfg(feature = "runtime-report")]
impl From<RhoAstBuildError> for RhoScalarInvocationError {
    fn from(value: RhoAstBuildError) -> Self {
        Self::AstBuild(value)
    }
}

#[cfg(feature = "runtime-report")]
fn scalar_literal_type(literal: &RhoAstLiteral) -> RhoScalarInvocationLiteralType {
    match literal {
        RhoAstLiteral::Int(_) => RhoScalarInvocationLiteralType::Int,
        RhoAstLiteral::Bool(_) => RhoScalarInvocationLiteralType::Bool,
        RhoAstLiteral::String(_) => RhoScalarInvocationLiteralType::Str,
        _ => RhoScalarInvocationLiteralType::NonScalar,
    }
}

#[cfg(feature = "runtime-report")]
fn scalar_literal_matches(literal: &RhoAstLiteral, expected: RhoScalarType) -> bool {
    matches!(
        (scalar_literal_type(literal), expected),
        (RhoScalarInvocationLiteralType::Int, RhoScalarType::Int)
            | (RhoScalarInvocationLiteralType::Bool, RhoScalarType::Bool)
            | (RhoScalarInvocationLiteralType::Str, RhoScalarType::Str)
    )
}

#[cfg(feature = "runtime-report")]
fn check_scalar_arguments(
    abi: &RhoScalarContractAbi,
    arguments: &[RhoAstLiteral],
) -> Result<(), RhoScalarInvocationError> {
    if arguments.len() != abi.operand_count() {
        return Err(RhoScalarInvocationError::ArityMismatch {
            rule_label: abi.rule_label.clone(),
            expected: abi.operand_count(),
            actual: arguments.len(),
        });
    }

    match abi.shape {
        RhoScalarContractShape::UnaryPrefix { argument, .. } => {
            if !scalar_literal_matches(&arguments[0], argument) {
                return Err(RhoScalarInvocationError::ArgumentTypeMismatch {
                    rule_label: abi.rule_label.clone(),
                    position: 0,
                    expected: argument,
                    actual: scalar_literal_type(&arguments[0]),
                });
            }
        },
        RhoScalarContractShape::BinaryInfix { left, right, .. } => {
            for (position, expected) in [(0_usize, left), (1_usize, right)] {
                if !scalar_literal_matches(&arguments[position], expected) {
                    return Err(RhoScalarInvocationError::ArgumentTypeMismatch {
                        rule_label: abi.rule_label.clone(),
                        position,
                        expected,
                        actual: scalar_literal_type(&arguments[position]),
                    });
                }
            }
        },
    }
    Ok(())
}

/// Build a typed Rho backend invocation from a generated scalar-contract ABI.
///
/// Generated dispatch should use this helper after extracting scalar literal
/// operands from a typed term. The helper checks the ABI arity and operand
/// families, emits a normalized `rhoapi::Par` dynamic call, and chooses the
/// observation report shape from the ABI result family.
#[cfg(feature = "runtime-report")]
pub fn build_scalar_contract_invocation(
    abi: &RhoScalarContractAbi,
    arguments: Vec<RhoAstLiteral>,
    out_channel: impl Into<String>,
) -> Result<RhoMachineInvocation, RhoScalarInvocationError> {
    check_scalar_arguments(abi, &arguments)?;
    let out_channel = out_channel.into();
    let call = RhoAstSend::contract_call(abi.rule_label.clone(), arguments, out_channel.clone())?
        .par()
        .clone();
    Ok(match abi.result_type() {
        RhoScalarType::Int => RhoMachineInvocation::RunWithCallAndObserveInts { call, out_channel },
        RhoScalarType::Bool => {
            RhoMachineInvocation::RunWithCallAndObserveBools { call, out_channel }
        },
        RhoScalarType::Str => {
            RhoMachineInvocation::RunWithCallAndObserveStrings { call, out_channel }
        },
    })
}

/// Build a typed Rho backend invocation from the codegen-owned scalar call
/// description emitted by generated language helpers.
///
/// This is the dependency-clean generated-language boundary: generated AST code
/// constructs [`RhoScalarContractInvocation`] without linking to the runtime,
/// then runtime-facing adapters validate and normalize it here.
#[cfg(feature = "runtime-report")]
pub fn build_scalar_contract_invocation_from_contract(
    invocation: RhoScalarContractInvocation,
) -> Result<RhoMachineInvocation, RhoScalarInvocationError> {
    build_scalar_contract_invocation(&invocation.abi, invocation.arguments, invocation.out_channel)
}

/// Build a typed Rho backend invocation from a codegen-owned **fold-dataflow** description (E3).
///
/// The dynamic `call` `Par` (a nested dataflow of scalar-contract calls produced by
/// `<Lang>::rho_fold_dataflow_invocation_to`) is already assembled and structurally validated by
/// [`mettail_rholang_codegen::build_dataflow_call_par`]; this adapter only selects the observation
/// shape from the root scalar type. It is the N-node generalization of
/// [`build_scalar_contract_invocation_from_contract`] (the single-op, depth-1 case).
#[cfg(feature = "runtime-report")]
pub fn build_fold_dataflow_invocation_from_contract(
    invocation: RhoFoldDataflowInvocation,
) -> RhoMachineInvocation {
    let RhoFoldDataflowInvocation { call, out_channel, result_type } = invocation;
    match result_type {
        RhoScalarType::Int => RhoMachineInvocation::RunWithCallAndObserveInts { call, out_channel },
        RhoScalarType::Bool => {
            RhoMachineInvocation::RunWithCallAndObserveBools { call, out_channel }
        },
        RhoScalarType::Str => {
            RhoMachineInvocation::RunWithCallAndObserveStrings { call, out_channel }
        },
    }
}

/// Build a typed Rho backend invocation from a codegen-owned **Rho-net σ-injection**
/// description (Epic 4).
///
/// The `call` `Par` is the closed σ-injection assembled by
/// `<Lang>::rho_net_invocation_from_dovetail_to` (via
/// [`mettail_rholang_codegen::term_contract_call`] over reflected σ arguments). This
/// adapter selects the `RunRhoNet…` observation shape, which composes the call against
/// the backend's INSTALLED σ-receiver program (not the scalar `program()`), so the
/// fired base rewrite's σ-receiver actually reduces the injection. It is the Rho-net
/// analogue of [`build_fold_dataflow_invocation_from_contract`].
#[cfg(feature = "runtime-report")]
pub fn build_rho_net_injection_invocation_from_contract(
    invocation: mettail_rholang_codegen::RhoNetInjectionInvocation,
) -> RhoMachineInvocation {
    let mettail_rholang_codegen::RhoNetInjectionInvocation { call, out_channel } = invocation;
    RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { call, out_channel }
}

/// Build the Stage 0 multi-firing replay invocation from a codegen-owned
/// σ-injection SEQUENCE — one [`mettail_rholang_codegen::RhoNetInjectionInvocation`]
/// per rewrite firing, produced by `<Lang>::rho_net_replay_invocation_from_dovetail_to`.
///
/// The N-firing generalization of [`build_rho_net_injection_invocation_from_contract`]
/// (the single-firing case): each injection becomes one `(call, out_channel)` pair,
/// and the replay driver
/// ([`PlannedRhoBackend::run_rho_net_replay_and_observe_runtime_values`]) fires each
/// as its own atomic COMM against the same INSTALLED σ-receiver program — so a
/// multi-redex reduction replays every rewrite as a `c(ℓ)` COMM. An empty sequence
/// (a normal-form term) yields a no-op replay with no observations.
#[cfg(feature = "runtime-report")]
pub fn build_rho_net_replay_invocation_from_contracts(
    invocations: Vec<mettail_rholang_codegen::RhoNetInjectionInvocation>,
) -> RhoMachineInvocation {
    let firings = invocations
        .into_iter()
        .map(|mettail_rholang_codegen::RhoNetInjectionInvocation { call, out_channel }| {
            (call, out_channel)
        })
        .collect();
    RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings }
}

#[cfg(feature = "runtime-report")]
impl RhoMachineInvocation {
    /// Which runtime site executes this invocation.
    pub fn execution_site(&self) -> RhoInvocationExecutionSite {
        RhoInvocationExecutionSite::RhoMachine
    }

    /// True for every [`RhoMachineInvocation`].
    pub fn is_rho_machine_execution(&self) -> bool {
        true
    }

    /// The lowered program `Par` this invocation runs on the Rho machine, if any. The
    /// `RunWithCall*` variants carry it (a COMM / dataflow program — exactly what the reactive
    /// single-stepper `inj`s); the pure-observe and call-by-need variants do not.
    pub fn program_par(&self) -> Option<&Par> {
        match self {
            RhoMachineInvocation::RunWithCallAndObserveInts { call, .. }
            | RhoMachineInvocation::RunWithCallAndObserveBools { call, .. }
            | RhoMachineInvocation::RunWithCallAndObserveStrings { call, .. }
            | RhoMachineInvocation::RunWithCallAndObserveRuntimeValues { call, .. }
            | RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { call, .. } => {
                Some(call)
            },
            _ => None,
        }
    }

    /// The program's observation channel for the Observe variants (`None` for call-by-need).
    pub fn out_channel(&self) -> Option<&str> {
        match self {
            RhoMachineInvocation::RunAndObserveInts { out_channel }
            | RhoMachineInvocation::RunAndObserveBools { out_channel }
            | RhoMachineInvocation::RunAndObserveStrings { out_channel }
            | RhoMachineInvocation::RunAndObserveRuntimeValues { out_channel }
            | RhoMachineInvocation::RunWithCallAndObserveInts { out_channel, .. }
            | RhoMachineInvocation::RunWithCallAndObserveBools { out_channel, .. }
            | RhoMachineInvocation::RunWithCallAndObserveStrings { out_channel, .. }
            | RhoMachineInvocation::RunWithCallAndObserveRuntimeValues { out_channel, .. }
            | RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { out_channel, .. } => {
                Some(out_channel)
            },
            RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { .. }
            | RhoMachineInvocation::RunCallByNeedThunk { .. } => None,
        }
    }

    async fn execute(self, backend: &PlannedRhoBackend) -> Result<RuntimeBackendReport, String> {
        match self {
            RhoMachineInvocation::RunAndObserveInts { out_channel } => backend
                .run_and_observe_ints(&out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| {
                    format!("failed to convert Rho integer observation report: {err:?}")
                }),
            RhoMachineInvocation::RunAndObserveBools { out_channel } => backend
                .run_and_observe_bools(&out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| {
                    format!("failed to convert Rho boolean observation report: {err:?}")
                }),
            RhoMachineInvocation::RunAndObserveStrings { out_channel } => backend
                .run_and_observe_strings(&out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| format!("failed to convert Rho string observation report: {err:?}")),
            RhoMachineInvocation::RunAndObserveRuntimeValues { out_channel } => backend
                .run_and_observe_runtime_values(&out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| {
                    format!("failed to convert Rho runtime value observation report: {err:?}")
                }),
            RhoMachineInvocation::RunWithCallAndObserveInts { call, out_channel } => backend
                .run_with_call_and_observe_ints(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| {
                    format!("failed to convert Rho integer observation report: {err:?}")
                }),
            RhoMachineInvocation::RunWithCallAndObserveBools { call, out_channel } => backend
                .run_with_call_and_observe_bools(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| {
                    format!("failed to convert Rho boolean observation report: {err:?}")
                }),
            RhoMachineInvocation::RunWithCallAndObserveStrings { call, out_channel } => backend
                .run_with_call_and_observe_strings(&call, &out_channel)
                .await?
                .try_into_runtime_backend_report()
                .map_err(|err| format!("failed to convert Rho string observation report: {err:?}")),
            RhoMachineInvocation::RunWithCallAndObserveRuntimeValues { call, out_channel } => {
                backend
                    .run_with_call_and_observe_runtime_values(&call, &out_channel)
                    .await?
                    .try_into_runtime_backend_report()
                    .map_err(|err| {
                        format!("failed to convert Rho runtime value observation report: {err:?}")
                    })
            },
            RhoMachineInvocation::RunRhoNetWithCallAndObserveRuntimeValues { call, out_channel } => {
                // The Epic 4 composition fix: run the INSTALLED σ-receiver program
                // (`installed_rho_net_program_par`) ∥ call so the base-rewrite
                // σ-receiver actually fires, rather than the scalar `program()`.
                backend
                    .run_rho_net_with_call_and_observe_runtime_values(&call, &out_channel)
                    .await?
                    .try_into_runtime_backend_report()
                    .map_err(|err| {
                        format!("failed to convert Rho runtime value observation report: {err:?}")
                    })
            },
            RhoMachineInvocation::RunRhoNetReplayAndObserveRuntimeValues { firings } => {
                // Stage 0 multi-firing replay: install the σ-receiver program once
                // and fire every firing as its own atomic COMM against it.
                backend
                    .run_rho_net_replay_and_observe_runtime_values(&firings)
                    .await?
                    .try_into_runtime_backend_report()
                    .map_err(|err| {
                        format!("failed to convert Rho runtime value replay report: {err:?}")
                    })
            },
            RhoMachineInvocation::RunCallByNeedThunk { plan } => {
                PlannedCallByNeedThunk::from_plan(*plan)
                    .run_and_observe_need_report()
                    .await
            },
        }
    }
}

#[cfg(feature = "runtime-report")]
impl RhoBackendInvocation {
    pub fn execution_site(&self) -> RhoInvocationExecutionSite {
        match self {
            RhoBackendInvocation::RhoMachine(_) => RhoInvocationExecutionSite::RhoMachine,
            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => {
                RhoInvocationExecutionSite::SemanticPredicateHost
            },
        }
    }

    pub fn is_rho_machine_execution(&self) -> bool {
        self.execution_site() == RhoInvocationExecutionSite::RhoMachine
    }

    pub fn program_par(&self) -> Option<&Par> {
        match self {
            RhoBackendInvocation::RhoMachine(invocation) => invocation.program_par(),
            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => None,
        }
    }

    pub fn out_channel(&self) -> Option<&str> {
        match self {
            RhoBackendInvocation::RhoMachine(invocation) => invocation.out_channel(),
            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => None,
        }
    }
}

/// Tier-3 + A-S3: clear the pending system-process session state before an invocation compiler
/// runs, so the `Definition`s it registers can be collected afterwards with
/// [`drain_pending_fold_definitions`]. Covers BOTH bands: the rhocalc held-fold lift sites
/// (no-op unless the rhocalc lowering is compiled in — a dependency boundary, not a behavior
/// gate) and the A-S3 native-handler specs the generated report-free match body records
/// (`rho_net_match_invocation_to`).
#[cfg(feature = "runtime-report")]
fn clear_pending_fold_sites() {
    #[cfg(feature = "rhocalc-runtime")]
    crate::rhocalc_ast::clear_held_fold_sites();
    mettail_rholang_codegen::clear_pending_native_handler_specs();
}

/// Tier-3 + A-S3 + A-S4: drain every system-process `Definition` recorded by the just-run
/// invocation compiler — the fold contracts (A-S4: one per lifted width/precision fold site,
/// GROUND operands included — pre-A-S4 only COMM-held folds lifted) plus the A-S3 native-handler
/// contracts (empty unless the report-free compile ADMITTED
/// located native sites). Both ride the same `extra_system_processes` seam into
/// [`run_rho_invocation_blocking`]; their reserved bands are disjoint by construction
/// (`mettail_rholang_codegen::native_handler`, collision-tested). On a DEFERRAL return the
/// drained definitions are simply dropped — nothing leaks into the fallback compile, which
/// re-brackets itself.
#[cfg(feature = "runtime-report")]
fn drain_pending_fold_definitions() -> Vec<rholang::rust::interpreter::system_processes::Definition>
{
    #[cfg(feature = "rhocalc-runtime")]
    let mut definitions =
        crate::fold_contract::fold_definitions_for(&crate::rhocalc_ast::take_held_fold_sites());
    #[cfg(not(feature = "rhocalc-runtime"))]
    let mut definitions: Vec<rholang::rust::interpreter::system_processes::Definition> = Vec::new();
    definitions.extend(crate::native_contract::native_definitions_for(
        &mettail_rholang_codegen::take_pending_native_handler_specs(),
    ));
    definitions
}

#[cfg(feature = "runtime-report")]
fn run_rho_invocation_blocking(
    backend: PlannedRhoBackend,
    invocation: RhoMachineInvocation,
    fold_definitions: Vec<rholang::rust::interpreter::system_processes::Definition>,
) -> Result<RuntimeBackendReport, String> {
    let worker = thread::Builder::new()
        .name("mettail-rho-backend-report".to_string())
        .spawn(move || {
            // Hand the lifted held-fold contracts to `build_runtime` on THIS worker thread (the
            // thread-local can't cross the spawn, so it's re-stashed here, same thread as block_on).
            crate::run::set_pending_fold_definitions(fold_definitions);
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

/// A-S2 test-only instrumentation: a process-global counter of
/// [`checked_complete_dovetail_report`] invocations, so the zero-D-stage tests can assert that
/// an ADMITTED exec never builds a Dovetail report (count delta 0) while a deferred exec does
/// (delta ≥ 1). Compiled only under `cfg(test)` (this crate's own unit tests) or the
/// `dstage-instrumentation` feature (downstream integration tests, e.g. the REPL's); production
/// builds carry no counter and no atomic traffic. Counters are process-global — deterministic
/// under `cargo nextest` (process-per-test) — so callers should assert DELTAS around their own
/// exec calls.
#[cfg(any(test, feature = "dstage-instrumentation"))]
pub mod dstage_instrumentation {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DOVETAIL_REPORT_INVOCATIONS: AtomicUsize = AtomicUsize::new(0);

    /// How many times `checked_complete_dovetail_report` (the D-stage build+check) has run in
    /// this process.
    pub fn dovetail_report_invocations() -> usize {
        DOVETAIL_REPORT_INVOCATIONS.load(Ordering::SeqCst)
    }

    /// Record one D-stage build+check. Only [`super::checked_complete_dovetail_report`]
    /// (feature `runtime-report`) calls this; the `allow` keeps a
    /// `dstage-instrumentation`-without-`runtime-report` build warning-free.
    #[cfg_attr(not(feature = "runtime-report"), allow(dead_code))]
    pub(crate) fn record_dovetail_report_invocation() {
        DOVETAIL_REPORT_INVOCATIONS.fetch_add(1, Ordering::SeqCst);
    }
}

#[cfg(feature = "runtime-report")]
fn checked_complete_dovetail_report<L, D>(
    language: &L,
    term: &dyn Term,
    dovetail: &D,
) -> Result<RuntimeDovetailRunReport, String>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
{
    #[cfg(any(test, feature = "dstage-instrumentation"))]
    dstage_instrumentation::record_dovetail_report_invocation();
    let report = dovetail(term).map_err(|err| {
        format!(
            "Dovetail stage for language {} could not build a checked report: {err}",
            language.name()
        )
    })?;
    report.validate_shape().map_err(|err| {
        format!(
            "Dovetail stage for language {} produced malformed report: {err}",
            language.name()
        )
    })?;
    report.assert_complete().map_err(|status| {
        format!(
            "Dovetail stage for language {} produced incomplete report: {status}",
            language.name()
        )
    })?;
    Ok(report)
}

/// Runtime adapter that makes a generated language select a flip-gated
/// [`PlannedRhoBackend`] through the generic [`Language`] report API.
///
/// The wrapped language remains the source of parsing, environments, and type
/// inference. Transition-only oracle execution belongs outside the production
/// wrapper. This adapter changes the public runtime backend selection surface:
/// `RhoMachine` becomes the default, the legacy Ascent runtime is not exposed
/// through the wrapped value, and the legacy `AscentResults` compatibility
/// methods reject Rho observation reports.
#[cfg(feature = "runtime-report")]
pub struct RhoRuntimeBackedLanguage<L, F> {
    inner: L,
    backend: PlannedRhoBackend,
    invocation: RhoInvocationCompilerStage<F>,
}

/// Production runtime adapter for the replacement path:
///
/// ```text
/// parsed MeTTaIL term -> checked Dovetail report -> Rho AST invocation -> RSpace observations
/// ```
///
/// `RhoMachine` is the default executable backend. `Dovetail` remains exposed
/// as the checked intermediate report for diagnostics and query tooling. The
/// legacy Ascent runtime is not exposed through this wrapper.
#[cfg(feature = "runtime-report")]
pub struct DovetailRhoRuntimeBackedLanguage<L, D, F> {
    inner: L,
    backend: PlannedRhoBackend,
    dovetail: DovetailCompilerStage<D>,
    invocation: RhoInvocationCompilerStage<F>,
}

/// A-S2 (D-stage demotion): the LAZY-report production runtime adapter.
///
/// ```text
/// parsed MeTTaIL term ──F2 (report-free compile)──▶ Rho AST invocation ──▶ RSpace observations
///          │
///          └─ deferral (semantic predicate / gate reject)
///                └──▶ LAZY checked Dovetail report ──▶ today's report-carrying paths
///                        (predicate payload · report-driven F · σ-replay)
/// ```
///
/// Unlike [`DovetailRhoRuntimeBackedLanguage`] — whose default path builds + checks the Dovetail
/// report on EVERY exec before the invocation compiler runs — this wrapper compiles the
/// invocation REPORT-FREE first (`F2`). On success the Rho machine executes with ZERO Dovetail
/// work; only a typed [`RhoInvocationDeferral`] triggers the D-stage, lazily, after which the
/// term takes exactly the eager pipeline's paths (so no input loses its existing behavior — the
/// admitted subset simply stops paying for the D-stage). At runtime Dovetail therefore handles
/// ONLY semantic predicates (and the fail-closed report-carrying fallback).
///
/// `Dovetail` remains exposed as the checked intermediate report for the step/diagnostic
/// surfaces (`run_step_backend_report`, `start_reduction_stepper`), which stay report-eager by
/// design — their OUTPUT is derivation evidence. Formal model:
/// `DovetailRhoLanguageBackendWrapper.v` ("report checked ⟺ deferral path taken").
#[cfg(feature = "runtime-report")]
pub struct LazyDovetailRhoRuntimeBackedLanguage<L, D, F2, F> {
    inner: L,
    backend: PlannedRhoBackend,
    dovetail: DovetailCompilerStage<D>,
    invocation_free: RhoInvocationCompilerStage<F2>,
    invocation: RhoInvocationCompilerStage<F>,
}

/// Step-only Dovetail report producer (the generated `dovetail_step_report`). Boxed because it is a
/// distinct fn item from the production `compiler` (`dovetail_report_for`), hence a distinct type;
/// boxing keeps it off the wrapper's generic list. Reached only via `run_step_backend_report` (the
/// REPL `step` path); production `exec` never touches it.
#[cfg(feature = "runtime-report")]
pub type StepReportCompiler =
    Box<dyn Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync>;

/// Language-specific Dovetail compiler stage derived from a generated
/// `LanguageDef`.
#[cfg(feature = "runtime-report")]
pub struct DovetailCompilerStage<D> {
    definition_fingerprint: String,
    compiler: D,
    step_compiler: StepReportCompiler,
}

/// Language-specific Rho invocation compiler stage derived from a generated
/// `LanguageDef`.
#[cfg(feature = "runtime-report")]
pub struct RhoInvocationCompilerStage<F> {
    definition_fingerprint: String,
    compiler: F,
}

#[cfg(feature = "runtime-report")]
impl<D> DovetailCompilerStage<D> {
    pub fn new(
        definition_fingerprint: impl Into<String>,
        compiler: D,
        step_compiler: StepReportCompiler,
    ) -> Self {
        Self {
            definition_fingerprint: definition_fingerprint.into(),
            compiler,
            step_compiler,
        }
    }

    pub fn definition_fingerprint(&self) -> &str {
        &self.definition_fingerprint
    }
}

#[cfg(feature = "runtime-report")]
impl<F> RhoInvocationCompilerStage<F> {
    pub fn new(definition_fingerprint: impl Into<String>, compiler: F) -> Self {
        Self {
            definition_fingerprint: definition_fingerprint.into(),
            compiler,
        }
    }

    pub fn definition_fingerprint(&self) -> &str {
        &self.definition_fingerprint
    }
}

/// Install a generated language as a Rho-default runtime by deriving the
/// invocation-stage identity from the accepted [`PlannedRhoBackend`].
///
/// This is the production-shaped entry point that generated installers should
/// target. Callers supply only the generated language value, the flip-gated Rho
/// plan, and the language-specific AST invocation compiler. The stage
/// fingerprint is copied from the accepted plan, so the only remaining identity
/// check is whether that plan belongs to the wrapped generated language.
///
/// Formal model: `GeneratedLanguageInstallation.v`, especially the
/// plan-derived stage lemmas. Source text is not an execution boundary here;
/// `compiler` must produce a [`RhoMachineInvocation`] carrying `rhoapi::Par`
/// values or planned bytecode-ready artifacts.
#[cfg(feature = "runtime-report")]
pub fn install_rho_runtime_backend<L, F>(
    inner: L,
    backend: PlannedRhoBackend,
    compiler: F,
) -> Result<RhoRuntimeBackedLanguage<L, F>, RhoRuntimeBackedLanguageError>
where
    L: Language,
    F: Fn(&dyn Term) -> Result<RhoMachineInvocation, String> + Send + Sync,
{
    let definition_fingerprint = backend.plan().definition_fingerprint().to_string();
    let invocation = RhoInvocationCompilerStage::new(definition_fingerprint, compiler);
    RhoRuntimeBackedLanguage::new(inner, backend, invocation)
}

/// Install a generated language as the production replacement runtime:
///
/// ```text
/// parsed term -> checked Dovetail report -> Rho AST invocation -> RSpace observations
/// ```
///
/// The installer derives both compiler-stage identities from the accepted
/// [`PlannedRhoBackend`]. That makes the stage identities a function of the
/// same flip-gated `LanguageDef` plan and prevents generated installers from
/// accidentally wiring a Dovetail compiler for one definition to a Rho
/// invocation compiler for another. The wrapper constructor still verifies that
/// the plan-derived identity matches the wrapped generated language metadata.
///
/// Formal model: `GeneratedLanguageInstallation.v`. The implementation also
/// relies on `DovetailRhoLanguageBackendWrapper.v` for the runtime surface:
/// `RhoMachine` is default, `Dovetail` is an internal checked stage, and legacy
/// Ascent is not exposed through the wrapped value.
#[cfg(feature = "runtime-report")]
pub fn install_dovetail_rho_runtime_backend<L, D, DStep, F>(
    inner: L,
    backend: PlannedRhoBackend,
    dovetail: D,
    dovetail_step: DStep,
    invocation: F,
) -> Result<DovetailRhoRuntimeBackedLanguage<L, D, F>, RhoRuntimeBackedLanguageError>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    DStep: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync + 'static,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
{
    let definition_fingerprint = backend.plan().definition_fingerprint().to_string();
    let dovetail = DovetailCompilerStage::new(
        definition_fingerprint.clone(),
        dovetail,
        Box::new(dovetail_step),
    );
    let invocation = RhoInvocationCompilerStage::new(definition_fingerprint, invocation);
    DovetailRhoRuntimeBackedLanguage::new(inner, backend, dovetail, invocation)
}

/// A-S2 (D-stage demotion): install a generated language as the LAZY-report production runtime:
///
/// ```text
/// parsed term ──F2 (report-free)──▶ Rho AST invocation ──▶ RSpace observations
///      └─ deferral ──▶ LAZY checked Dovetail report ──▶ today's report-carrying paths
/// ```
///
/// The lazy analogue of [`install_dovetail_rho_runtime_backend`], taking one extra stage: the
/// REPORT-FREE invocation compiler `invocation_free`
/// (`F2: Fn(&dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral>`). On `Ok` the
/// term executes with NO D-stage; on [`RhoInvocationDeferral::SemanticPredicate`] the wrapper
/// lazily builds the checked report and returns it as the predicate payload; on
/// [`RhoInvocationDeferral::GateReject`] it lazily builds the checked report and runs the
/// report-carrying fallback `invocation` (today's exact paths — report-driven match, σ-replay,
/// or the fallback's own error). `dovetail`/`dovetail_step` remain the language's D-stage
/// producers, now reached only on deferral (exec) or through the step/stepper diagnostic
/// surfaces (which stay report-eager).
///
/// Every compiler-stage identity is derived from the accepted [`PlannedRhoBackend`]'s
/// definition fingerprint, exactly as the eager installer does, and the wrapper constructor
/// re-verifies them against the wrapped generated language metadata. Formal model:
/// `DovetailRhoLanguageBackendWrapper.v` ("report checked ⟺ deferral path taken") on top of
/// `GeneratedLanguageInstallation.v`'s plan-derived stage lemmas.
#[cfg(feature = "runtime-report")]
pub fn install_dovetail_rho_runtime_backend_lazy<L, D, DStep, F2, F>(
    inner: L,
    backend: PlannedRhoBackend,
    dovetail: D,
    dovetail_step: DStep,
    invocation_free: F2,
    invocation: F,
) -> Result<LazyDovetailRhoRuntimeBackedLanguage<L, D, F2, F>, RhoRuntimeBackedLanguageError>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    DStep: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync + 'static,
    F2: Fn(&dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral> + Send + Sync,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
{
    let definition_fingerprint = backend.plan().definition_fingerprint().to_string();
    let dovetail = DovetailCompilerStage::new(
        definition_fingerprint.clone(),
        dovetail,
        Box::new(dovetail_step),
    );
    let invocation_free =
        RhoInvocationCompilerStage::new(definition_fingerprint.clone(), invocation_free);
    let invocation = RhoInvocationCompilerStage::new(definition_fingerprint, invocation);
    LazyDovetailRhoRuntimeBackedLanguage::new(inner, backend, dovetail, invocation_free, invocation)
}

/// Failure installing a flip-gated Rho backend plan on a generated language.
#[cfg(feature = "runtime-report")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoRuntimeBackedLanguageError {
    /// The plan was produced from a different `LanguageDef` than the generated
    /// language being wrapped.
    LanguagePlanMismatch {
        language_name: String,
        plan_language_name: String,
    },
    /// The generated language metadata did not expose the macro-derived
    /// definition fingerprint required for production Dovetail/Rho
    /// installation.
    MissingLanguageDefinitionFingerprint { language_name: String },
    /// The Rho plan was derived from a different generated definition than the
    /// wrapped language.
    LanguagePlanDefinitionMismatch {
        language_name: String,
        language_definition_fingerprint: String,
        plan_definition_fingerprint: String,
    },
    /// The Dovetail compiler stage was derived from a different generated
    /// definition than the wrapped language.
    DovetailCompilerDefinitionMismatch {
        language_name: String,
        language_definition_fingerprint: String,
        compiler_definition_fingerprint: String,
    },
    /// The Rho invocation compiler stage was derived from a different generated
    /// definition than the wrapped language.
    InvocationCompilerDefinitionMismatch {
        language_name: String,
        language_definition_fingerprint: String,
        compiler_definition_fingerprint: String,
    },
}

#[cfg(feature = "runtime-report")]
impl fmt::Display for RhoRuntimeBackedLanguageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LanguagePlanMismatch { language_name, plan_language_name } => write!(
                f,
                "RhoMachine backend plan for language {plan_language_name} cannot be installed on generated language {language_name}"
            ),
            Self::MissingLanguageDefinitionFingerprint { language_name } => write!(
                f,
                "Dovetail+Rho production backend for language {language_name} requires generated LanguageDef fingerprint metadata"
            ),
            Self::LanguagePlanDefinitionMismatch {
                language_name,
                language_definition_fingerprint,
                plan_definition_fingerprint,
            } => write!(
                f,
                "RhoMachine backend plan fingerprint {plan_definition_fingerprint} cannot be installed on generated language {language_name} fingerprint {language_definition_fingerprint}"
            ),
            Self::DovetailCompilerDefinitionMismatch {
                language_name,
                language_definition_fingerprint,
                compiler_definition_fingerprint,
            } => write!(
                f,
                "Dovetail compiler fingerprint {compiler_definition_fingerprint} cannot be installed on generated language {language_name} fingerprint {language_definition_fingerprint}"
            ),
            Self::InvocationCompilerDefinitionMismatch {
                language_name,
                language_definition_fingerprint,
                compiler_definition_fingerprint,
            } => write!(
                f,
                "Rho invocation compiler fingerprint {compiler_definition_fingerprint} cannot be installed on generated language {language_name} fingerprint {language_definition_fingerprint}"
            ),
        }
    }
}

#[cfg(feature = "runtime-report")]
impl std::error::Error for RhoRuntimeBackedLanguageError {}

#[cfg(feature = "runtime-report")]
fn require_matching_plan_definition<L>(
    inner: &L,
    backend: &PlannedRhoBackend,
) -> Result<String, RhoRuntimeBackedLanguageError>
where
    L: Language,
{
    let language_name = inner.name();
    let language_definition_fingerprint =
        inner.metadata().definition_fingerprint().ok_or_else(|| {
            RhoRuntimeBackedLanguageError::MissingLanguageDefinitionFingerprint {
                language_name: language_name.to_string(),
            }
        })?;
    let plan_definition_fingerprint = backend.plan().definition_fingerprint();
    if language_definition_fingerprint != plan_definition_fingerprint {
        return Err(RhoRuntimeBackedLanguageError::LanguagePlanDefinitionMismatch {
            language_name: language_name.to_string(),
            language_definition_fingerprint: language_definition_fingerprint.to_string(),
            plan_definition_fingerprint: plan_definition_fingerprint.to_string(),
        });
    }
    Ok(language_definition_fingerprint.to_string())
}

#[cfg(feature = "runtime-report")]
impl<L, F> RhoRuntimeBackedLanguage<L, F>
where
    L: Language,
    F: Fn(&dyn Term) -> Result<RhoMachineInvocation, String> + Send + Sync,
{
    pub fn new(
        inner: L,
        backend: PlannedRhoBackend,
        invocation: RhoInvocationCompilerStage<F>,
    ) -> Result<Self, RhoRuntimeBackedLanguageError> {
        let language_name = inner.name();
        let plan_language_name = backend.plan().language_name();
        if language_name != plan_language_name {
            return Err(RhoRuntimeBackedLanguageError::LanguagePlanMismatch {
                language_name: language_name.to_string(),
                plan_language_name: plan_language_name.to_string(),
            });
        }
        let language_definition_fingerprint = require_matching_plan_definition(&inner, &backend)?;
        if language_definition_fingerprint != invocation.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint,
                compiler_definition_fingerprint: invocation.definition_fingerprint().to_string(),
            });
        }

        Ok(Self { inner, backend, invocation })
    }

    pub fn inner(&self) -> &L {
        &self.inner
    }

    pub fn backend(&self) -> &PlannedRhoBackend {
        &self.backend
    }
}

#[cfg(feature = "runtime-report")]
impl<L, D, F> DovetailRhoRuntimeBackedLanguage<L, D, F>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
{
    /// Install a generated language as a Dovetail-checked, Rho-executed
    /// production runtime.
    ///
    /// The `dovetail` closure is the language-specific rewrite compiler. The
    /// `invocation` closure receives the already shape-validated, complete
    /// Dovetail report and must produce a strict Rho-default invocation, not
    /// source text or non-semantic Dovetail execution.
    pub fn new(
        inner: L,
        backend: PlannedRhoBackend,
        dovetail: DovetailCompilerStage<D>,
        invocation: RhoInvocationCompilerStage<F>,
    ) -> Result<Self, RhoRuntimeBackedLanguageError> {
        let language_name = inner.name();
        let plan_language_name = backend.plan().language_name();
        if language_name != plan_language_name {
            return Err(RhoRuntimeBackedLanguageError::LanguagePlanMismatch {
                language_name: language_name.to_string(),
                plan_language_name: plan_language_name.to_string(),
            });
        }
        let language_definition_fingerprint = require_matching_plan_definition(&inner, &backend)?;
        if language_definition_fingerprint != dovetail.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::DovetailCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint: language_definition_fingerprint.clone(),
                compiler_definition_fingerprint: dovetail.definition_fingerprint().to_string(),
            });
        }
        if language_definition_fingerprint != invocation.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint,
                compiler_definition_fingerprint: invocation.definition_fingerprint().to_string(),
            });
        }

        Ok(Self { inner, backend, dovetail, invocation })
    }

    pub fn inner(&self) -> &L {
        &self.inner
    }

    pub fn backend(&self) -> &PlannedRhoBackend {
        &self.backend
    }
}

#[cfg(feature = "runtime-report")]
impl<L, D, F2, F> LazyDovetailRhoRuntimeBackedLanguage<L, D, F2, F>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    F2: Fn(&dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral> + Send + Sync,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
{
    /// Install a generated language as a LAZY-report Dovetail+Rho production runtime (A-S2).
    ///
    /// `invocation_free` is the report-free compiler `F2` (the default exec path);
    /// `invocation` is the report-carrying fallback compiler (today's paths, reached only on
    /// deferral) and the stepper's compiler; `dovetail` is the lazy D-stage producer. The same
    /// plan/fingerprint identity checks as [`DovetailRhoRuntimeBackedLanguage::new`] apply to
    /// EVERY stage, including the new report-free one.
    pub fn new(
        inner: L,
        backend: PlannedRhoBackend,
        dovetail: DovetailCompilerStage<D>,
        invocation_free: RhoInvocationCompilerStage<F2>,
        invocation: RhoInvocationCompilerStage<F>,
    ) -> Result<Self, RhoRuntimeBackedLanguageError> {
        let language_name = inner.name();
        let plan_language_name = backend.plan().language_name();
        if language_name != plan_language_name {
            return Err(RhoRuntimeBackedLanguageError::LanguagePlanMismatch {
                language_name: language_name.to_string(),
                plan_language_name: plan_language_name.to_string(),
            });
        }
        let language_definition_fingerprint = require_matching_plan_definition(&inner, &backend)?;
        if language_definition_fingerprint != dovetail.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::DovetailCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint: language_definition_fingerprint.clone(),
                compiler_definition_fingerprint: dovetail.definition_fingerprint().to_string(),
            });
        }
        if language_definition_fingerprint != invocation_free.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint: language_definition_fingerprint.clone(),
                compiler_definition_fingerprint: invocation_free
                    .definition_fingerprint()
                    .to_string(),
            });
        }
        if language_definition_fingerprint != invocation.definition_fingerprint() {
            return Err(RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch {
                language_name: language_name.to_string(),
                language_definition_fingerprint,
                compiler_definition_fingerprint: invocation.definition_fingerprint().to_string(),
            });
        }

        Ok(Self {
            inner,
            backend,
            dovetail,
            invocation_free,
            invocation,
        })
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
    F: Fn(&dyn Term) -> Result<RhoMachineInvocation, String> + Send + Sync,
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
        let _ = term;
        Err(format!(
            "legacy Ascent runtime is not exposed by Rho-backed language {}",
            self.name()
        ))
    }

    fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
        Some(RuntimeBackend::RhoMachine)
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        vec![RuntimeBackendCapability {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
        }]
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        match backend {
            RuntimeBackend::RhoMachine => true,
            RuntimeBackend::Ascent => false,
            _ => false,
        }
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::RhoMachine => {
                clear_pending_fold_sites();
                let invocation = (self.invocation.compiler)(term).map_err(|err| {
                    format!(
                        "RhoMachine backend for language {} could not build an AST invocation: {err}",
                        self.name()
                    )
                })?;
                let fold_definitions = drain_pending_fold_definitions();
                run_rho_invocation_blocking(self.backend.clone(), invocation, fold_definitions)
            },
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Rho-backed language {}",
                self.name()
            )),
            other => Err(format!(
                "{} backend is not exposed by Rho-backed language {}",
                other,
                self.name()
            )),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = (term, facts);
        Err(format!(
            "legacy Ascent runtime is not exposed by Rho-backed language {}",
            self.name()
        ))
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
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Rho-backed language {}",
                self.name()
            )),
            other => Err(format!(
                "{} backend is not exposed by Rho-backed language {}",
                other,
                self.name()
            )),
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
}

#[cfg(feature = "runtime-report")]
impl<L, D, F> Language for DovetailRhoRuntimeBackedLanguage<L, D, F>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
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
        let _ = term;
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
            self.name()
        ))
    }

    fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
        Some(RuntimeBackend::RhoMachine)
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        vec![RuntimeBackendCapability {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
        }]
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        match backend {
            RuntimeBackend::RhoMachine => true,
            RuntimeBackend::Ascent => false,
            _ => false,
        }
    }

    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::RhoMachine => {
                let dovetail_report =
                    checked_complete_dovetail_report(&self.inner, term, &self.dovetail.compiler)?;
                clear_pending_fold_sites();
                let invocation = (self.invocation.compiler)(term, &dovetail_report).map_err(|err| {
                    format!(
                        "RhoMachine backend for language {} could not build an AST invocation from the checked Dovetail report: {err}",
                        self.name()
                    )
                })?;
                let fold_definitions = drain_pending_fold_definitions();
                match invocation {
                    RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => {
                        RuntimeBackendReport::try_dovetail(dovetail_report).map_err(|err| {
                            format!(
                                "semantic-predicate Dovetail stage for language {} produced malformed report: {err}",
                                self.name()
                            )
                        })
                    },
                    RhoBackendInvocation::RhoMachine(machine_invocation) => run_rho_invocation_blocking(
                        self.backend.clone(),
                        machine_invocation,
                        fold_definitions,
                    ),
                }
            },
            RuntimeBackend::Dovetail => Err(format!(
                "Dovetail is an internal checked stage for Rho-default language {}; execute with \
                 RhoMachine or use the step report API for derivation evidence",
                self.name()
            )),
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
                self.name()
            )),
            _ => Err(format!(
                "{} backend is not exposed by Dovetail+Rho-backed language {}",
                backend,
                self.name()
            )),
        }
    }

    /// Step-mode report: a dedicated derivation-evidence surface that runs the generated
    /// `dovetail_step_report` (`self.dovetail.step_compiler`) so each term record carries its
    /// reconstructed `source_display` for comprehensible REPL `step` display. Production `exec` uses
    /// `run_backend_report`/`compiler` and cannot select Dovetail as a runtime backend.
    fn run_step_backend_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        let dovetail_report =
            checked_complete_dovetail_report(&self.inner, term, &self.dovetail.step_compiler)?;
        RuntimeBackendReport::try_dovetail(dovetail_report).map_err(|err| {
            format!(
                "Dovetail step stage for language {} produced malformed report: {err}",
                self.name()
            )
        })
    }

    /// Start the reactive single-stepper for a Rho-machine invocation: run the checked Dovetail
    /// stage, build the F-stage invocation, and `inj` its program `Par` under a
    /// [`crate::step::StepSession`]. COMM-bearing programs yield COMM steps, while pure observed
    /// values run to quiescence and yield terminal `Output` steps. Non-Rho invocations still fail
    /// here so the REPL can inspect the Dovetail derivation graph.
    fn start_reduction_stepper(
        &self,
        term: &dyn Term,
    ) -> Result<Box<dyn mettail_runtime::ReductionStepper>, String> {
        let dovetail_report =
            checked_complete_dovetail_report(&self.inner, term, &self.dovetail.compiler)?;
        // Tier-3: bracket the lowering so we can collect any held-fold contract sites it records
        // (rhocalc only; empty for Calculator).
        clear_pending_fold_sites();
        let invocation = (self.invocation.compiler)(term, &dovetail_report).map_err(|err| {
            format!(
                "live single-step for language {} could not build an AST invocation from the \
                 checked Dovetail report: {err}",
                self.name()
            )
        })?;
        // The program's observation channel (e.g. RhoCalc's `"OUT"`); the stepper reads its resting
        // value(s) post-quiescence to surface terminal output step(s). Extracted (owned) before the
        // `program_par` borrow so it does not conflict with it.
        match invocation {
            RhoBackendInvocation::RhoMachine(machine_invocation) => {
                let out_channel = machine_invocation.out_channel().map(String::from);
                let call = machine_invocation.program_par().ok_or_else(|| {
                    format!(
                        "term has no Rho-machine program to single-step for language {}; inspect the Dovetail derivation graph instead",
                        self.name()
                    )
                })?;
                // Compose the call with the backend's persistent contracts (e.g. Calculator's E3
                // `@"AddInt"`/`@"SubInt"`/`@"MulInt"` dataflow contracts) so their COMMs actually
                // fire — the SAME composition the wrapper's run path uses
                // (`run::evaluate_validated_program_with_call` → `par.append(call)`). For RhoCalc
                // the contract program is empty, so this is just the call (a direct COMM term).
                let program = match self.backend.program().ast_par() {
                    Some(contracts) => contracts.append(call.clone()),
                    None => call.clone(),
                };
                // The held-fold contract `Definition`s the lifted call targets (empty unless the
                // term had a fold over a COMM-received value).
                let fold_definitions = drain_pending_fold_definitions();
                let session =
                    crate::step::StepSession::start(program, fold_definitions, out_channel)?;
                Ok(Box::new(session))
            },
            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => Err(format!(
                "term has no Rho-machine program to single-step for language {}; inspect the \
                 Dovetail derivation graph instead",
                self.name()
            )),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = (term, facts);
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
            self.name()
        ))
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
                "{} backend for language {} does not accept Ascent-shaped seeded facts",
                backend,
                self.name()
            )),
            RuntimeBackend::Dovetail => Err(format!(
                "Dovetail is an internal checked stage for Rho-default language {}; execute with \
                 RhoMachine or use the step report API for derivation evidence",
                self.name()
            )),
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
                self.name()
            )),
            _ => Err(format!(
                "{} backend is not exposed by Dovetail+Rho-backed language {}",
                backend,
                self.name()
            )),
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
}

#[cfg(feature = "runtime-report")]
impl<L, D, F2, F> Language for LazyDovetailRhoRuntimeBackedLanguage<L, D, F2, F>
where
    L: Language,
    D: Fn(&dyn Term) -> Result<RuntimeDovetailRunReport, String> + Send + Sync,
    F2: Fn(&dyn Term) -> Result<RhoBackendInvocation, RhoInvocationDeferral> + Send + Sync,
    F: Fn(&dyn Term, &RuntimeDovetailRunReport) -> Result<RhoBackendInvocation, String>
        + Send
        + Sync,
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
        let _ = term;
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
            self.name()
        ))
    }

    fn default_runtime_backend(&self) -> Option<RuntimeBackend> {
        Some(RuntimeBackend::RhoMachine)
    }

    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        vec![RuntimeBackendCapability {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
        }]
    }

    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        match backend {
            RuntimeBackend::RhoMachine => true,
            RuntimeBackend::Ascent => false,
            _ => false,
        }
    }

    /// A-S2 (D-stage demotion): the LAZY default path. The report-free compiler `F2` runs
    /// FIRST; an admitted term executes on the Rho machine with ZERO Dovetail work. Only a
    /// typed deferral builds the checked Dovetail report — lazily — and then takes exactly the
    /// eager pipeline's paths: the semantic-predicate payload
    /// (`RuntimeBackendReport::try_dovetail`) or the report-carrying fallback compiler
    /// (report-driven match / σ-replay / the fallback's own error). Every error message on the
    /// deferral paths is the eager pipeline's message, so no caller-observable failure text
    /// changes. The held-fold `clear_pending_fold_sites`/`drain_pending_fold_definitions`
    /// bracket wraps EACH invocation-compiler run, exactly as the eager wrapper brackets its
    /// single run.
    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::RhoMachine => {
                // Tier-3 bracket around the REPORT-FREE compile: F2 may lift held-fold
                // contracts (e.g. the RhoCalc AST lowering); they ride the executed invocation.
                clear_pending_fold_sites();
                let free = (self.invocation_free.compiler)(term);
                let free_fold_definitions = drain_pending_fold_definitions();
                match free {
                    Ok(RhoBackendInvocation::RhoMachine(machine_invocation)) => {
                        // The admitted path: NO D-stage ran, no report exists.
                        run_rho_invocation_blocking(
                            self.backend.clone(),
                            machine_invocation,
                            free_fold_definitions,
                        )
                    },
                    // An F2 that expresses the predicate disposition through the invocation
                    // type is the same deferral as the typed error: the observational payload
                    // is the LAZILY checked Dovetail report (today's predicate arm).
                    Ok(RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. })
                    | Err(RhoInvocationDeferral::SemanticPredicate { .. }) => {
                        let dovetail_report = checked_complete_dovetail_report(
                            &self.inner,
                            term,
                            &self.dovetail.compiler,
                        )?;
                        RuntimeBackendReport::try_dovetail(dovetail_report).map_err(|err| {
                            format!(
                                "semantic-predicate Dovetail stage for language {} produced malformed report: {err}",
                                self.name()
                            )
                        })
                    },
                    Err(RhoInvocationDeferral::GateReject { .. }) => {
                        // The fail-closed path: LAZILY build + check the report, then run
                        // today's report-carrying compiler (its own fold bracket).
                        let dovetail_report = checked_complete_dovetail_report(
                            &self.inner,
                            term,
                            &self.dovetail.compiler,
                        )?;
                        clear_pending_fold_sites();
                        let invocation = (self.invocation.compiler)(term, &dovetail_report)
                            .map_err(|err| {
                                format!(
                                    "RhoMachine backend for language {} could not build an AST invocation from the checked Dovetail report: {err}",
                                    self.name()
                                )
                            })?;
                        let fold_definitions = drain_pending_fold_definitions();
                        match invocation {
                            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => {
                                RuntimeBackendReport::try_dovetail(dovetail_report).map_err(
                                    |err| {
                                        format!(
                                            "semantic-predicate Dovetail stage for language {} produced malformed report: {err}",
                                            self.name()
                                        )
                                    },
                                )
                            },
                            RhoBackendInvocation::RhoMachine(machine_invocation) => {
                                run_rho_invocation_blocking(
                                    self.backend.clone(),
                                    machine_invocation,
                                    fold_definitions,
                                )
                            },
                        }
                    },
                }
            },
            RuntimeBackend::Dovetail => Err(format!(
                "Dovetail is an internal checked stage for Rho-default language {}; execute with \
                 RhoMachine or use the step report API for derivation evidence",
                self.name()
            )),
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
                self.name()
            )),
            _ => Err(format!(
                "{} backend is not exposed by Dovetail+Rho-backed language {}",
                backend,
                self.name()
            )),
        }
    }

    /// Step-mode report: identical to [`DovetailRhoRuntimeBackedLanguage`]'s — a dedicated
    /// derivation-evidence surface that runs the generated `dovetail_step_report`. The step
    /// surface stays report-EAGER by design (its output IS the report); the A-S2 laziness
    /// applies to production `exec` (`run_backend_report`) only.
    fn run_step_backend_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        let dovetail_report =
            checked_complete_dovetail_report(&self.inner, term, &self.dovetail.step_compiler)?;
        RuntimeBackendReport::try_dovetail(dovetail_report).map_err(|err| {
            format!(
                "Dovetail step stage for language {} produced malformed report: {err}",
                self.name()
            )
        })
    }

    /// Start the reactive single-stepper: identical to
    /// [`DovetailRhoRuntimeBackedLanguage::start_reduction_stepper`] — the stepper is a
    /// diagnostic surface that builds the checked Dovetail report eagerly and compiles the
    /// F-stage invocation through the report-carrying fallback compiler.
    fn start_reduction_stepper(
        &self,
        term: &dyn Term,
    ) -> Result<Box<dyn mettail_runtime::ReductionStepper>, String> {
        let dovetail_report =
            checked_complete_dovetail_report(&self.inner, term, &self.dovetail.compiler)?;
        // Tier-3: bracket the lowering so we can collect any held-fold contract sites it
        // records (rhocalc only; empty for Calculator).
        clear_pending_fold_sites();
        let invocation = (self.invocation.compiler)(term, &dovetail_report).map_err(|err| {
            format!(
                "live single-step for language {} could not build an AST invocation from the \
                 checked Dovetail report: {err}",
                self.name()
            )
        })?;
        match invocation {
            RhoBackendInvocation::RhoMachine(machine_invocation) => {
                let out_channel = machine_invocation.out_channel().map(String::from);
                let call = machine_invocation.program_par().ok_or_else(|| {
                    format!(
                        "term has no Rho-machine program to single-step for language {}; inspect the Dovetail derivation graph instead",
                        self.name()
                    )
                })?;
                // Compose the call with the backend's persistent contracts so their COMMs
                // actually fire — the SAME composition the run path uses.
                let program = match self.backend.program().ast_par() {
                    Some(contracts) => contracts.append(call.clone()),
                    None => call.clone(),
                };
                let fold_definitions = drain_pending_fold_definitions();
                let session =
                    crate::step::StepSession::start(program, fold_definitions, out_channel)?;
                Ok(Box::new(session))
            },
            RhoBackendInvocation::DeferToDovetailSemanticPredicate { .. } => Err(format!(
                "term has no Rho-machine program to single-step for language {}; inspect the \
                 Dovetail derivation graph instead",
                self.name()
            )),
        }
    }

    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = (term, facts);
        Err(format!(
            "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
            self.name()
        ))
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
                "{} backend for language {} does not accept Ascent-shaped seeded facts",
                backend,
                self.name()
            )),
            RuntimeBackend::Dovetail => Err(format!(
                "Dovetail is an internal checked stage for Rho-default language {}; execute with \
                 RhoMachine or use the step report API for derivation evidence",
                self.name()
            )),
            RuntimeBackend::Ascent => Err(format!(
                "legacy Ascent runtime is not exposed by Dovetail+Rho-backed language {}",
                self.name()
            )),
            _ => Err(format!(
                "{} backend is not exposed by Dovetail+Rho-backed language {}",
                backend,
                self.name()
            )),
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "runtime-report")]
    use mettail_runtime::{
        LanguageMetadata, RuntimeBackendOutput, RuntimeDovetailCompleteness,
        RuntimeDovetailTermRecord,
    };

    #[cfg(feature = "runtime-report")]
    fn binary_abi(
        label: &str,
        left: RhoScalarType,
        right: RhoScalarType,
        result: RhoScalarType,
    ) -> RhoScalarContractAbi {
        RhoScalarContractAbi {
            rule_label: label.to_string(),
            shape: RhoScalarContractShape::BinaryInfix { left, right, result },
        }
    }

    #[cfg(feature = "runtime-report")]
    fn gstring(par: &Par) -> Option<&str> {
        match par.exprs.as_slice() {
            [expr] => match expr.expr_instance.as_ref()? {
                models::rhoapi::expr::ExprInstance::GString(s) => Some(s.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    #[cfg(feature = "runtime-report")]
    const MINI_RHO_FRAGMENT: &str = r#"
        name: MiniDefaultRho,
        types {
            ![i64] as Int
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
        }
    "#;

    #[cfg(feature = "runtime-report")]
    static MINI_TYPES: &[mettail_runtime::TypeDef] = &[mettail_runtime::TypeDef {
        name: "Int",
        native_type: Some("i64"),
        is_primary: true,
    }];

    #[cfg(feature = "runtime-report")]
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct MiniTerm {
        left: i64,
        right: i64,
    }

    #[cfg(feature = "runtime-report")]
    impl fmt::Display for MiniTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{} + {}", self.left, self.right)
        }
    }

    #[cfg(feature = "runtime-report")]
    impl Term for MiniTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            ((self.left as u64) << 32) ^ (self.right as u64)
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other
                .as_any()
                .downcast_ref::<MiniTerm>()
                .is_some_and(|other| other == self)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[cfg(feature = "runtime-report")]
    struct MiniMetadata;

    #[cfg(feature = "runtime-report")]
    static MINI_METADATA: MiniMetadata = MiniMetadata;

    #[cfg(feature = "runtime-report")]
    impl LanguageMetadata for MiniMetadata {
        fn name(&self) -> &'static str {
            "MiniDefaultRho"
        }

        fn definition_fingerprint(&self) -> Option<&'static str> {
            static FINGERPRINT: std::sync::OnceLock<String> = std::sync::OnceLock::new();
            Some(
                FINGERPRINT
                    .get_or_init(|| {
                        let def = mini_language_def();
                        mettail_ast::identity::language_definition_fingerprint(&def)
                    })
                    .as_str(),
            )
        }

        fn types(&self) -> &'static [mettail_runtime::TypeDef] {
            MINI_TYPES
        }

        fn terms(&self) -> &'static [mettail_runtime::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
            &[]
        }
    }

    #[cfg(feature = "runtime-report")]
    struct MiniLanguage;

    #[cfg(feature = "runtime-report")]
    impl Language for MiniLanguage {
        fn name(&self) -> &'static str {
            "MiniDefaultRho"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &MINI_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            match input.trim() {
                "2 + 3" => Ok(Box::new(MiniTerm { left: 2, right: 3 })),
                other => {
                    Err(format!("MiniDefaultRho test parser only accepts `2 + 3`, got {other:?}"))
                },
            }
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::base("Int")
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    #[cfg(feature = "runtime-report")]
    fn mini_language_def() -> mettail_ast::language::LanguageDef {
        syn::parse_str(MINI_RHO_FRAGMENT).expect("MiniDefaultRho fragment must parse")
    }

    #[cfg(feature = "runtime-report")]
    fn mini_requirements() -> mettail_rholang_codegen::RhoDefaultBackendRequirements {
        mettail_rholang_codegen::RhoDefaultBackendRequirements {
            coverage: mettail_rholang_codegen::RhoCoverageEvidence::AllRulesLowered,
            guard_coverage: mettail_rholang_codegen::RhoGuardCoverageEvidence::NoGuardObligations,
        }
    }

    #[cfg(feature = "runtime-report")]
    fn mini_backend_from_fragment(fragment: &str) -> PlannedRhoBackend {
        let def: mettail_ast::language::LanguageDef =
            syn::parse_str(fragment).expect("MiniDefaultRho test fragment must parse");
        let plan = mettail_rholang_codegen::plan_rho_default_backend(&def, mini_requirements())
            .expect("MiniDefaultRho scalar AddInt rule must pass the Rho-default gate");
        assert_eq!(plan.lowering.lowered, vec!["AddInt"]);
        assert!(plan.lowering.rejected.is_empty());
        PlannedRhoBackend::from_plan(plan)
    }

    #[cfg(feature = "runtime-report")]
    fn mini_backend() -> PlannedRhoBackend {
        mini_backend_from_fragment(MINI_RHO_FRAGMENT)
    }

    #[cfg(feature = "runtime-report")]
    fn complete_mini_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        let key = format!("mini:{term}").into_bytes();
        Ok(RuntimeDovetailRunReport {
            roots: vec![key.clone()],
            root_ordinals: vec![0],
            terms: vec![RuntimeDovetailTermRecord {
                ordinal: 0,
                class_id: 0,
                key,
                op_display: term.to_string(),
                weight_display: "0".to_string(),
                is_root: true,
                source_display: None,
            }],
            derivation_edges: Vec::new(),
            rule_firings: Vec::new(),
            rewrite_justifications: Vec::new(),
            completeness: RuntimeDovetailCompleteness::Complete,
            graph_kind: mettail_runtime::RuntimeDovetailGraphKind::Derivation,
        })
    }

    #[cfg(feature = "runtime-report")]
    fn bounded_mini_dovetail_report(term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        let mut report = complete_mini_dovetail_report(term)?;
        report.completeness = RuntimeDovetailCompleteness::BoundedByCycleCut;
        Ok(report)
    }

    #[cfg(feature = "runtime-report")]
    fn mini_invocation(term: &dyn Term) -> Result<RhoMachineInvocation, String> {
        let term = term
            .as_any()
            .downcast_ref::<MiniTerm>()
            .ok_or_else(|| format!("expected MiniTerm, got {term:?}"))?;
        build_scalar_contract_invocation(
            &binary_abi("AddInt", RhoScalarType::Int, RhoScalarType::Int, RhoScalarType::Int),
            vec![RhoAstLiteral::Int(term.left), RhoAstLiteral::Int(term.right)],
            "OUT",
        )
        .map_err(|err| err.to_string())
    }

    #[cfg(feature = "runtime-report")]
    fn mini_invocation_from_dovetail(
        term: &dyn Term,
        report: &RuntimeDovetailRunReport,
    ) -> Result<RhoBackendInvocation, String> {
        report.assert_complete().map_err(|status| {
            format!("MiniDefaultRho invocation requires a complete Dovetail report, got {status}")
        })?;
        Ok(RhoBackendInvocation::from(mini_invocation(term)?))
    }

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
                .try_into_runtime_backend_report()
                .expect("normalized AST observations must convert to runtime backend reports");

        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);

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

    #[cfg(feature = "runtime-report")]
    #[test]
    fn direct_rho_surface_rejects_seeded_facts_and_legacy_backends() {
        let language = install_rho_runtime_backend(MiniLanguage, mini_backend(), mini_invocation)
            .expect("default runtime-report surface should install the direct Rho wrapper");
        let term = language.parse_term("2 + 3").expect("mini parse");

        assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
        assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));

        let capabilities = language.runtime_backend_capabilities();
        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].backend, RuntimeBackend::RhoMachine);
        assert!(capabilities[0].is_default);

        let empty_seeded_report = language
            .run_default_backend_report_with_facts(term.as_ref(), &SeedFacts::new())
            .expect("empty seed facts are a no-op for a direct Rho wrapper");
        assert_eq!(empty_seeded_report.backend(), RuntimeBackend::RhoMachine);

        let mut facts = SeedFacts::new();
        facts.insert("seed".to_string(), vec![vec!["2 + 3".to_string()]]);
        let seeded_err = language
            .run_default_backend_report_with_facts(term.as_ref(), &facts)
            .expect_err("direct Rho wrapper must reject Ascent-shaped facts");
        assert!(
            seeded_err.contains("does not accept Ascent-shaped seeded facts"),
            "{seeded_err}"
        );

        let dovetail_err = language
            .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
            .expect_err("direct Rho wrapper must not expose Dovetail");
        assert!(dovetail_err.contains("Dovetail backend is not exposed"), "{dovetail_err}");

        let seeded_dovetail_err = language
            .run_backend_report_with_facts(
                RuntimeBackend::Dovetail,
                term.as_ref(),
                &SeedFacts::new(),
            )
            .expect_err("direct Rho wrapper must not delegate seeded Dovetail requests");
        assert!(
            seeded_dovetail_err.contains("Dovetail backend is not exposed"),
            "{seeded_dovetail_err}"
        );

        let ascent_report_err = language
            .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
            .expect_err("direct Rho wrapper must not expose Ascent reports");
        assert!(
            ascent_report_err.contains("legacy Ascent runtime is not exposed"),
            "{ascent_report_err}"
        );

        let seeded_ascent_report_err = language
            .run_backend_report_with_facts(RuntimeBackend::Ascent, term.as_ref(), &facts)
            .expect_err("direct Rho wrapper must not expose seeded Ascent reports");
        assert!(
            seeded_ascent_report_err.contains("legacy Ascent runtime is not exposed"),
            "{seeded_ascent_report_err}"
        );

        let ascent_err = language
            .run_ascent_with_facts(term.as_ref(), &facts)
            .expect_err("direct Rho wrapper must not expose seeded Ascent");
        assert!(ascent_err.contains("legacy Ascent runtime is not exposed"), "{ascent_err}");
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn default_surface_installs_dovetail_rho_wrapper_without_oracle_ascent() {
        let language = install_dovetail_rho_runtime_backend(
            MiniLanguage,
            mini_backend(),
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            mini_invocation_from_dovetail,
        )
        .expect("default runtime-report surface should install the Dovetail+Rho wrapper");
        let term = language.parse_term("2 + 3").expect("mini parse");

        assert_eq!(language.default_runtime_backend(), Some(RuntimeBackend::RhoMachine));
        assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Ascent));

        let capabilities = language.runtime_backend_capabilities();
        assert_eq!(capabilities.len(), 1);
        assert_eq!(capabilities[0].backend, RuntimeBackend::RhoMachine);
        assert!(capabilities[0].is_default);

        let dovetail_err = language
            .run_backend_report(RuntimeBackend::Dovetail, term.as_ref())
            .expect_err("Rho-default wrapper must not expose Dovetail as an executable backend");
        assert!(dovetail_err.contains("Dovetail is an internal checked stage"), "{dovetail_err}");

        let step_report = language
            .run_step_backend_report(term.as_ref())
            .expect("wrapper should expose checked Dovetail evidence through the step API");
        assert_eq!(step_report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(step_report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
        let RuntimeBackendOutput::Dovetail(dovetail_output) = step_report.into_output() else {
            panic!("Dovetail backend must return a Dovetail report");
        };
        assert!(dovetail_output.is_complete());
        assert_eq!(dovetail_output.root_count(), 1);

        let rho_report = language
            .run_default_backend_report(term.as_ref())
            .expect("wrapper should execute Rho after the checked Dovetail report");
        assert_eq!(rho_report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(rho_report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
        let out = rho_report
            .observations_for_channel("OUT")
            .expect("Rho report must expose OUT observations");
        assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);

        let ascent_err = language
            .run_backend_report(RuntimeBackend::Ascent, term.as_ref())
            .expect_err("production Dovetail+Rho wrapper must reject Ascent");
        assert!(ascent_err.contains("legacy Ascent runtime is not exposed"), "{ascent_err}");

        let mut facts = SeedFacts::new();
        facts.insert("seed".to_string(), vec![vec!["2 + 3".to_string()]]);
        let seeded_err = language
            .run_default_backend_report_with_facts(term.as_ref(), &facts)
            .expect_err("production Dovetail+Rho wrapper must reject Ascent-shaped facts");
        assert!(
            seeded_err.contains("does not accept Ascent-shaped seeded facts"),
            "{seeded_err}"
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn default_surface_checks_dovetail_completeness_before_rho_invocation() {
        let language = install_dovetail_rho_runtime_backend(
            MiniLanguage,
            mini_backend(),
            bounded_mini_dovetail_report,
            bounded_mini_dovetail_report,
            |_term, _report| Err("invocation should not run after incomplete Dovetail".to_string()),
        )
        .expect("capability installation is separate from per-term Dovetail completeness");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("bounded Dovetail reports must block Rho execution");
        assert!(err.contains("produced incomplete report: BoundedByCycleCut"), "{err}");
        assert!(!err.contains("invocation should not run"), "{err}");
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn default_surface_rejects_cross_definition_installs() {
        let other_backend = mini_backend_from_fragment(&MINI_RHO_FRAGMENT.replacen(
            "name: MiniDefaultRho",
            "name: OtherMiniDefaultRho",
            1,
        ));
        let err = match install_dovetail_rho_runtime_backend(
            MiniLanguage,
            other_backend,
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            mini_invocation_from_dovetail,
        ) {
            Ok(_) => panic!("cross-language Rho plan must not install on MiniDefaultRho"),
            Err(err) => err,
        };
        assert!(
            matches!(err, RhoRuntimeBackedLanguageError::LanguagePlanMismatch { .. }),
            "{err}"
        );

        let backend = mini_backend();
        let fingerprint = backend.plan().definition_fingerprint().to_string();
        let err = match DovetailRhoRuntimeBackedLanguage::new(
            MiniLanguage,
            backend,
            DovetailCompilerStage::new(
                "wrong-definition",
                complete_mini_dovetail_report,
                Box::new(complete_mini_dovetail_report),
            ),
            RhoInvocationCompilerStage::new(fingerprint, mini_invocation_from_dovetail),
        ) {
            Ok(_) => panic!("mismatched Dovetail compiler must not install"),
            Err(err) => err,
        };
        assert!(
            matches!(err, RhoRuntimeBackedLanguageError::DovetailCompilerDefinitionMismatch { .. }),
            "{err}"
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn direct_rho_wrapper_compiler_type_is_machine_only() {
        fn assert_machine_only_direct_wrapper<L, F>(_language: &RhoRuntimeBackedLanguage<L, F>)
        where
            L: Language,
            F: Fn(&dyn Term) -> Result<RhoMachineInvocation, String> + Send + Sync,
        {
        }

        let language = install_rho_runtime_backend(MiniLanguage, mini_backend(), mini_invocation)
            .expect("direct Rho wrapper should install with a machine-only compiler");
        assert_machine_only_direct_wrapper(&language);

        let term = language.parse_term("2 + 3").expect("mini parse");
        let invocation = mini_invocation(term.as_ref()).expect("mini invocation should lower");
        assert_eq!(invocation.execution_site(), RhoInvocationExecutionSite::RhoMachine);
        assert!(invocation.is_rho_machine_execution());
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn backend_invocation_has_no_non_semantic_dovetail_execution_site() {
        let sites = [
            RhoMachineInvocation::RunAndObserveInts { out_channel: "OUT".to_string() }
                .execution_site(),
            RhoBackendInvocation::DeferToDovetailSemanticPredicate {
                predicate: "safe scalar evaluation declined".to_string(),
            }
            .execution_site(),
        ];

        assert_eq!(
            sites,
            [
                RhoInvocationExecutionSite::RhoMachine,
                RhoInvocationExecutionSite::SemanticPredicateHost
            ]
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn default_surface_allows_semantic_predicate_deferral() {
        let language = install_dovetail_rho_runtime_backend(
            MiniLanguage,
            mini_backend(),
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            |_term, _report| {
                Ok(RhoBackendInvocation::DeferToDovetailSemanticPredicate {
                    predicate: "safe scalar evaluation declined".to_string(),
                })
            },
        )
        .expect("installation is separate from per-term invocation disposition");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("semantic-predicate deferral resolves to the checked Dovetail report");

        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn default_surface_rejects_semantic_predicate_deferral_before_dovetail_completeness() {
        let language = install_dovetail_rho_runtime_backend(
            MiniLanguage,
            mini_backend(),
            bounded_mini_dovetail_report,
            bounded_mini_dovetail_report,
            |_term, _report| {
                Ok(RhoBackendInvocation::DeferToDovetailSemanticPredicate {
                    predicate: "safe scalar evaluation declined".to_string(),
                })
            },
        )
        .expect("installation is separate from per-term Dovetail completeness");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("semantic-predicate deferral must require a complete Dovetail report");
        assert!(err.contains("produced incomplete report: BoundedByCycleCut"), "{err}");
        assert!(!err.contains("safe scalar evaluation declined"), "{err}");
    }

    // ————————————————————————————————————————————————————————————————————————————————
    // A-S2: the LAZY wrapper (`LazyDovetailRhoRuntimeBackedLanguage`) — report-free default
    // path, lazy D-stage on deferral, instrumented by `dstage_instrumentation`.
    // ————————————————————————————————————————————————————————————————————————————————

    /// The Mini report-free F2: the same scalar invocation as [`mini_invocation`], with a
    /// lowering failure mapped to a `GateReject` deferral.
    #[cfg(feature = "runtime-report")]
    fn mini_invocation_free(
        term: &dyn Term,
    ) -> Result<RhoBackendInvocation, RhoInvocationDeferral> {
        mini_invocation(term)
            .map(RhoBackendInvocation::from)
            .map_err(|detail| RhoInvocationDeferral::GateReject { detail })
    }

    /// A D-stage producer that FAILS LOUDLY: installing the lazy wrapper with this producer
    /// proves the admitted path never consults the D-stage — if it did, the exec would error
    /// with this marker instead of observing the Rho result.
    #[cfg(feature = "runtime-report")]
    fn poisoned_mini_dovetail_report(_term: &dyn Term) -> Result<RuntimeDovetailRunReport, String> {
        Err("D-stage must not run on the admitted report-free path".to_string())
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_default_surface_executes_report_free_with_zero_dovetail_work() {
        // The D-stage producer is POISONED and the report-carrying fallback F is poisoned too:
        // the admitted exec must reach the Rho machine purely through F2. The instrumentation
        // counter double-checks the D-stage never ran.
        let language = install_dovetail_rho_runtime_backend_lazy(
            MiniLanguage,
            mini_backend(),
            poisoned_mini_dovetail_report,
            poisoned_mini_dovetail_report,
            mini_invocation_free,
            |_term, _report| Err("fallback F must not run on the admitted path".to_string()),
        )
        .expect("the lazy Dovetail+Rho wrapper installs");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let before = dstage_instrumentation::dovetail_report_invocations();
        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("the admitted exec executes with NO D-stage");
        let after = dstage_instrumentation::dovetail_report_invocations();

        assert_eq!(after - before, 0, "the admitted path built a Dovetail report");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::RhoNormalizedAst);
        let out = report
            .observations_for_channel("OUT")
            .expect("Rho report must expose OUT observations");
        assert_eq!(out.values, vec![RuntimeObservationValue::Int(5)]);
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_default_surface_semantic_predicate_defers_to_the_lazy_report() {
        let language = install_dovetail_rho_runtime_backend_lazy(
            MiniLanguage,
            mini_backend(),
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            |_term| {
                Err(RhoInvocationDeferral::SemanticPredicate {
                    predicate: "safe scalar evaluation declined".to_string(),
                })
            },
            |_term, _report| Err("fallback F must not run on the predicate path".to_string()),
        )
        .expect("the lazy Dovetail+Rho wrapper installs");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let before = dstage_instrumentation::dovetail_report_invocations();
        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("the predicate deferral resolves to the LAZILY checked Dovetail report");
        let after = dstage_instrumentation::dovetail_report_invocations();

        assert!(after - before >= 1, "the predicate path must build the report lazily");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_default_surface_gate_reject_takes_todays_report_carrying_path() {
        // GateReject → LAZY checked report → the report-carrying fallback compiler → Rho
        // execution: byte-identical to the eager pipeline's outcome for the same F.
        let language = install_dovetail_rho_runtime_backend_lazy(
            MiniLanguage,
            mini_backend(),
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            |_term| {
                Err(RhoInvocationDeferral::GateReject {
                    detail: "report-free compile out of scope".to_string(),
                })
            },
            mini_invocation_from_dovetail,
        )
        .expect("the lazy Dovetail+Rho wrapper installs");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let before = dstage_instrumentation::dovetail_report_invocations();
        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("the gate-reject deferral executes through the report-carrying fallback");
        let after = dstage_instrumentation::dovetail_report_invocations();

        assert!(after - before >= 1, "the gate-reject path must build the report lazily");
        assert_eq!(report.backend(), RuntimeBackend::RhoMachine);
        let out = report
            .observations_for_channel("OUT")
            .expect("Rho report must expose OUT observations");
        assert_eq!(
            out.values,
            vec![RuntimeObservationValue::Int(5)],
            "the fallback path produces the eager pipeline's exact observation"
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_default_surface_gate_reject_surfaces_the_d_stage_error_first() {
        // On the deferral path the LAZY report is still CHECKED: a bounded report blocks the
        // fallback with the eager pipeline's exact D-stage error (report checked ⟺ deferral
        // path taken — `DovetailRhoLanguageBackendWrapper.v`).
        let language = install_dovetail_rho_runtime_backend_lazy(
            MiniLanguage,
            mini_backend(),
            bounded_mini_dovetail_report,
            bounded_mini_dovetail_report,
            |_term| {
                Err(RhoInvocationDeferral::GateReject {
                    detail: "report-free compile out of scope".to_string(),
                })
            },
            |_term, _report| Err("invocation should not run after incomplete Dovetail".to_string()),
        )
        .expect("the lazy Dovetail+Rho wrapper installs");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let err = language
            .run_default_backend_report(term.as_ref())
            .expect_err("a bounded lazy report must block the fallback");
        assert!(err.contains("produced incomplete report: BoundedByCycleCut"), "{err}");
        assert!(!err.contains("invocation should not run"), "{err}");
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_default_surface_fallback_predicate_disposition_returns_the_report() {
        // A fallback F that itself lands on the semantic-predicate disposition (after a
        // GateReject deferral) still resolves to the checked report — the eager wrapper's
        // predicate arm, reproduced on the lazy path.
        let language = install_dovetail_rho_runtime_backend_lazy(
            MiniLanguage,
            mini_backend(),
            complete_mini_dovetail_report,
            complete_mini_dovetail_report,
            |_term| {
                Err(RhoInvocationDeferral::GateReject {
                    detail: "report-free compile out of scope".to_string(),
                })
            },
            |_term, _report| {
                Ok(RhoBackendInvocation::DeferToDovetailSemanticPredicate {
                    predicate: "safe scalar evaluation declined".to_string(),
                })
            },
        )
        .expect("the lazy Dovetail+Rho wrapper installs");
        let term = language.parse_term("2 + 3").expect("mini parse");

        let report = language
            .run_default_backend_report(term.as_ref())
            .expect("the fallback predicate disposition resolves to the checked report");
        assert_eq!(report.backend(), RuntimeBackend::Dovetail);
        assert_eq!(report.artifact(), RuntimeBackendArtifact::DovetailRunReport);
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn lazy_wrapper_rejects_cross_definition_installs() {
        // The report-free stage carries the SAME plan-derived identity discipline as every
        // other stage: a wrong fingerprint on the F2 stage blocks installation.
        let backend = mini_backend();
        let fingerprint = backend.plan().definition_fingerprint().to_string();
        let err = match LazyDovetailRhoRuntimeBackedLanguage::new(
            MiniLanguage,
            backend,
            DovetailCompilerStage::new(
                fingerprint.clone(),
                complete_mini_dovetail_report,
                Box::new(complete_mini_dovetail_report),
            ),
            RhoInvocationCompilerStage::new("wrong-definition", mini_invocation_free),
            RhoInvocationCompilerStage::new(fingerprint, mini_invocation_from_dovetail),
        ) {
            Ok(_) => panic!("a mismatched report-free compiler must not install"),
            Err(err) => err,
        };
        assert!(
            matches!(
                err,
                RhoRuntimeBackedLanguageError::InvocationCompilerDefinitionMismatch { .. }
            ),
            "{err}"
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn scalar_contract_invocation_uses_generated_abi_shape() {
        let abi = binary_abi("AddStr", RhoScalarType::Str, RhoScalarType::Str, RhoScalarType::Str);
        let invocation = build_scalar_contract_invocation(
            &abi,
            vec![
                RhoAstLiteral::String("rho".to_string()),
                RhoAstLiteral::String("net".to_string()),
            ],
            "OUT",
        )
        .expect("valid ABI and arguments should produce a Rho invocation");

        match invocation {
            RhoMachineInvocation::RunWithCallAndObserveStrings { call, out_channel } => {
                assert_eq!(out_channel, "OUT");
                let send = call
                    .sends
                    .first()
                    .expect("scalar invocation must be one send");
                assert_eq!(
                    send.chan.as_ref().and_then(gstring),
                    Some("AddStr"),
                    "dynamic call channel must be the ABI rule label"
                );
                assert_eq!(
                    send.data.len(),
                    3,
                    "dynamic scalar call sends two operands plus return channel"
                );
            },
            other => panic!("Str result ABI must select string observation, got {other:?}"),
        }
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn invocation_execution_site_distinguishes_rho_machine_from_semantic_predicate_host() {
        let abi = binary_abi("AddInt", RhoScalarType::Int, RhoScalarType::Int, RhoScalarType::Int);
        let invocation = build_scalar_contract_invocation(
            &abi,
            vec![RhoAstLiteral::Int(2), RhoAstLiteral::Int(3)],
            "OUT",
        )
        .expect("valid scalar invocation should build");

        assert_eq!(invocation.execution_site(), RhoInvocationExecutionSite::RhoMachine);
        assert!(invocation.is_rho_machine_execution());
        assert!(invocation.program_par().is_some());
        assert_eq!(invocation.out_channel(), Some("OUT"));

        let blocked = RhoBackendInvocation::DeferToDovetailSemanticPredicate {
            predicate: "safe scalar evaluation declined".to_string(),
        };
        assert_eq!(blocked.execution_site(), RhoInvocationExecutionSite::SemanticPredicateHost);
        assert!(!blocked.is_rho_machine_execution());
        assert!(blocked.program_par().is_none());
        assert!(blocked.out_channel().is_none());
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn scalar_contract_invocation_rejects_bad_arity() {
        let abi = binary_abi("AddInt", RhoScalarType::Int, RhoScalarType::Int, RhoScalarType::Int);
        let err = build_scalar_contract_invocation(&abi, vec![RhoAstLiteral::Int(1)], "OUT")
            .expect_err("binary ABI must reject a single argument");

        assert_eq!(
            err,
            RhoScalarInvocationError::ArityMismatch {
                rule_label: "AddInt".to_string(),
                expected: 2,
                actual: 1,
            }
        );
    }

    #[cfg(feature = "runtime-report")]
    #[test]
    fn scalar_contract_invocation_rejects_type_mismatch() {
        let abi = binary_abi("AddInt", RhoScalarType::Int, RhoScalarType::Int, RhoScalarType::Int);
        let err = build_scalar_contract_invocation(
            &abi,
            vec![RhoAstLiteral::Int(1), RhoAstLiteral::Bool(true)],
            "OUT",
        )
        .expect_err("Int ABI must reject a Bool argument");

        assert_eq!(
            err,
            RhoScalarInvocationError::ArgumentTypeMismatch {
                rule_label: "AddInt".to_string(),
                position: 1,
                expected: RhoScalarType::Int,
                actual: RhoScalarInvocationLiteralType::Bool,
            }
        );
    }
}
