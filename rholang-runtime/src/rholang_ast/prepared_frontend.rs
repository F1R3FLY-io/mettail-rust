//! Direct composition with the existing node frontend ABI.
//!
//! This adapter owns no evaluator, registry, or alternate source traversal.
//! It parses the Proc category once, admits the original caller map, and
//! enters the existing Public preparation session. The node remains responsible
//! for provider/matcher enrollment and funded execution of the returned artifact.
//!
//! Preparation limits below govern the existing import and lowering meters.
//! The source-byte limit is not a lexer/WPDA work or allocator/RSS certificate.
//! Public activation additionally requires the enclosing preparation and parser
//! admission gates; implementing this trait alone does not establish those gates.

use super::imports::{CheckedCallerImports, ImportLimits};
use super::*;
use rholang::rust::interpreter::frontend::{
    PreparationError, PreparedProgram, ProgramFrontend, PREPARED_PROGRAM_ABI_V1,
};

/// Explicit host policy; there is no unlimited or implicit default policy.
#[derive(Clone, Copy, Debug)]
pub struct RholangPreparationPolicy {
    pub max_source_bytes: usize,
    pub max_import_entries: usize,
    pub max_import_nodes: usize,
    pub max_import_payload_bytes: usize,
    pub max_preparation_work: u64,
    /// Existing preparation payload units, not physical allocator bytes.
    pub max_preparation_units: usize,
    pub lowering: LoweringOptions,
}

/// A node frontend using the same resolver and declared policy for each request.
///
/// Callers supply only a thread-safe resolver. No opaque authority is created
/// from its names: dynamically installed FLTs retain the existing runtime ports.
pub struct RholangProgramFrontend {
    policy: RholangPreparationPolicy,
    resolver: Arc<dyn FltResolve + Send + Sync>,
    cancelled: Arc<dyn Fn() -> bool + Send + Sync>,
}

impl RholangProgramFrontend {
    pub fn new(
        policy: RholangPreparationPolicy,
        resolver: Arc<dyn FltResolve + Send + Sync>,
    ) -> Self {
        Self {
            policy,
            resolver,
            cancelled: Arc::new(|| false),
        }
    }

    /// Supply the enclosing request/service cancellation signal.
    /// Cancellation never falls back to unmetered preparation.
    pub fn with_cancellation(mut self, cancelled: Arc<dyn Fn() -> bool + Send + Sync>) -> Self {
        self.cancelled = cancelled;
        self
    }

    /// Preserve owned guard diagnostics without extending the node program ABI.
    /// All parser, import, and preparation errors precede artifact publication.
    pub fn prepare_with_report(
        &self,
        source: &str,
        environment: HashMap<String, Par>,
    ) -> Result<(PreparedProgram, GuardDischargeReport), PreparationError> {
        session::ensure_inactive().map_err(lowering_error)?;
        self.check_cancelled()?;
        if source.len() > self.policy.max_source_bytes {
            return Err(PreparationError::new("Rholang source byte limit exceeded"));
        }

        // The existing cache is thread-local. Start each independent source with
        // fresh lexical identities, exactly as the generated language entry does.
        mettail_runtime::clear_var_cache();
        // Reuse the elected-source entrypoint used by the inline-DDL path.
        // Election belongs to the generated parser, not this adapter. Its
        // complete-input checks and errors remain authoritative; this is not
        // exhaustive enumeration or evidence that the source is unambiguous.
        // Do not use parse_structured's display-and-reparse wrapper.
        let proc = Proc::parse_via_wpda(source)
            .map_err(|error| PreparationError::new(error.to_string()))?;
        self.check_cancelled()?;
        self.prepare_process(&proc, environment)
    }

    fn prepare_process(
        &self,
        proc: &Proc,
        environment: HashMap<String, Par>,
    ) -> Result<(PreparedProgram, GuardDischargeReport), PreparationError> {
        let mut cancelled = || (self.cancelled)();
        let imports = CheckedCallerImports::admit(
            environment,
            ImportLimits {
                entries: self.policy.max_import_entries,
                nodes: self.policy.max_import_nodes,
                payload_bytes: self.policy.max_import_payload_bytes,
            },
            &mut cancelled,
        )
        .map_err(|error| PreparationError::new(format!("Caller import admission: {error:?}")))?;
        let resolver: Arc<dyn FltResolve> = self.resolver.clone();
        let context = BoundEnv::empty_with_admission(
            resolver,
            self.policy.lowering,
            SourceAdmissionMode::Public,
        )
        .with_caller_imports(imports);
        let mut work = 0;
        let mut budget = mettail_rholang_codegen::ReflectedCodecBudget::new(
            &mut work,
            self.policy.max_preparation_work,
            self.policy.max_preparation_units,
            &mut cancelled,
        );
        let output = session::lower_public_body_with_budget(proc, context, &mut budget)
            .map_err(lowering_error)?;
        self.check_cancelled()?;
        finish_output(output)
    }

    fn check_cancelled(&self) -> Result<(), PreparationError> {
        if (self.cancelled)() {
            Err(PreparationError::new("Rholang preparation cancelled"))
        } else {
            Ok(())
        }
    }
}

impl ProgramFrontend for RholangProgramFrontend {
    fn abi_version(&self) -> u16 {
        PREPARED_PROGRAM_ABI_V1
    }

    fn prepare(
        &self,
        source: &str,
        environment: HashMap<String, Par>,
    ) -> Result<PreparedProgram, PreparationError> {
        // Reports are diagnostics only; semantic provider requirements are
        // checked by finish_output and never silently discarded here.
        self.prepare_with_report(source, environment)
            .map(|(program, _)| program)
    }
}

fn finish_output(
    output: session::DirectLoweringOutput,
) -> Result<(PreparedProgram, GuardDischargeReport), PreparationError> {
    // No fold constructor belongs to the checked source profile. If the profile
    // grows, this boundary must gain real enrollment before accepting its output.
    if !output.folds.is_empty() {
        return Err(PreparationError::new("Unenrolled fold definitions in prepared Rholang"));
    }
    if output.guard_report.disagreements != 0 {
        return Err(PreparationError::new("Guard discharge disagreement in prepared Rholang"));
    }
    Ok((PreparedProgram::from_normalized(output.par), output.guard_report))
}

fn lowering_error(error: RholangAstLowerError) -> PreparationError {
    PreparationError::new(format!("Rholang preparation: {error:?}"))
}

#[cfg(test)]
#[path = "prepared_frontend_tests.rs"]
mod tests;
