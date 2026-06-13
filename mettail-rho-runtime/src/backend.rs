//! Gate-preserving Rho backend execution boundary.
//!
//! `run_validated_program*` is intentionally still available for oracle and
//! debug code that needs to inject a shape-validated AST. Generated backend
//! execution should use [`PlannedRhoBackend`]: it can only be built from a
//! `RhoDefaultBackendPlan`, which is the codegen artifact produced after the
//! proof, oracle, coverage, scheduler-fairness, validation, and deadlock gates
//! pass.

use std::collections::{BTreeMap, BTreeSet};

use mettail_rho_codegen::{RhoArtifactKind, RhoDefaultBackendPlan, ValidatedRhoProgram};
#[cfg(feature = "runtime-report")]
use mettail_runtime::{
    RuntimeBackend, RuntimeBackendArtifact, RuntimeBackendReport, RuntimeChannelObservation,
    RuntimeObservationValue,
};
use models::rhoapi::Par;

use crate::run::{
    run_validated_program, run_validated_program_and_read_ints,
    run_validated_program_and_read_strings, run_validated_program_with_call,
    run_validated_program_with_call_and_read_ints,
    run_validated_program_with_call_and_read_strings,
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
        Ok(RuntimeBackendReport::observations(
            RuntimeBackend::RhoMachine,
            artifact,
            vec![RuntimeChannelObservation::new(self.channel, values)],
            evidence_refs,
        ))
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

        assert_eq!(report.backend, RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact, RuntimeBackendArtifact::RhoNormalizedAst);
        assert_eq!(
            report.evidence_refs,
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
