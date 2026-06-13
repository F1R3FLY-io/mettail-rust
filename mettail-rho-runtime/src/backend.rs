//! Gate-preserving Rho backend execution boundary.
//!
//! `run_validated_program*` is intentionally still available for oracle and
//! debug code that needs to inject a shape-validated AST. Generated backend
//! execution should use [`PlannedRhoBackend`]: it can only be built from a
//! `RhoDefaultBackendPlan`, which is the codegen artifact produced after the
//! proof, oracle, coverage, validation, and deadlock gates pass.

use mettail_rho_codegen::{RhoArtifactKind, RhoDefaultBackendPlan, ValidatedRhoProgram};
use models::rhoapi::Par;

use crate::run::{
    run_validated_program, run_validated_program_and_read_ints,
    run_validated_program_and_read_strings, run_validated_program_with_call,
    run_validated_program_with_call_and_read_ints,
    run_validated_program_with_call_and_read_strings,
};

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
}
