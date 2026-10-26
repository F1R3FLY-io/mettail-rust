//! Direct composition with the existing node frontend ABI.
//!
//! This adapter owns no evaluator, registry, or alternate source traversal.
//! It parses the Proc category once, admits the original caller map, and
//! enters the existing Public preparation session. The node remains responsible
//! for provider/matcher enrollment and funded execution of the returned artifact.
//!
// Changed by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): was
// "Preparation limits below govern the existing import and lowering meters."
//! The limits below govern caller imports and the source size. Lowering has no
//! work or storage-unit ceiling (DR-131 extension to F1R3Lang, user decision 1);
//! its reservation points only poll cancellation.
//! The source-byte limit is not a lexer/WPDA work or allocator/RSS certificate.
//! Public activation additionally requires the enclosing preparation and parser
//! admission gates; implementing this trait alone does not establish those gates.

use super::imports::{CheckedCallerImports, ImportLimits};
use super::*;
use models::rust::rholang::protobuf_encoder;
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
    // Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
    // pub max_preparation_work: u64,
    // /// Existing preparation payload units, not physical allocator bytes.
    // pub max_preparation_units: usize,
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

pub(super) struct ParsedSource<'a> {
    source: &'a str,
    proc: Proc,
}

impl ParsedSource<'_> {
    pub(super) fn proc(&self) -> &Proc {
        &self.proc
    }
}

enum PreparationInput<'a> {
    Source(&'a ParsedSource<'a>),
    #[cfg(test)]
    Tree(&'a Proc),
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

    // Changed by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): was
    // "Cancellation never falls back to unmetered preparation."
    /// Supply the enclosing request/service cancellation signal.
    /// Cancellation refuses preparation; it never publishes a partial artifact.
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
        self.prepare_input(PreparationInput::Source(&ParsedSource { source, proc }), environment)
    }

    #[cfg(test)]
    fn prepare_process(
        &self,
        proc: &Proc,
        environment: HashMap<String, Par>,
    ) -> Result<(PreparedProgram, GuardDischargeReport), PreparationError> {
        self.prepare_input(PreparationInput::Tree(proc), environment)
    }

    fn prepare_input(
        &self,
        input: PreparationInput<'_>,
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
        // Disabled by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16): host work is not metered.
        // let mut work = 0;
        // let mut budget = mettail_rholang_codegen::ReflectedCodecBudget::new(
        //     &mut work,
        //     self.policy.max_preparation_work,
        //     self.policy.max_preparation_units,
        //     &mut cancelled,
        // );
        // Changed by the DR-131 extension to F1R3Lang (user decision 1 of 2026-10-16):
        // lowering keeps its reservation points, but they only poll cancellation.
        // let output = session::lower_public_body_with_budget(proc, context, &mut budget)
        //     .map_err(lowering_error)?;
        let mut reserve = |_work: usize,
                           _units: usize|
         -> Result<(), mettail_rholang_codegen::DynamicReflectionError> {
            if (self.cancelled)() {
                Err(mettail_rholang_codegen::DynamicReflectionError::Cancelled)
            } else {
                Ok(())
            }
        };
        let output = match &input {
            PreparationInput::Source(parsed) => session::lower_public_checked(
                parsed.proc(),
                Some(*parsed),
                context,
                &mut reserve,
            ),
            #[cfg(test)]
            PreparationInput::Tree(proc) => {
                session::lower_public_checked(proc, None, context, &mut reserve)
            },
        }
        .map_err(lowering_error)?;
        self.check_cancelled()?;
        check_output(&output)?;
        match input {
            PreparationInput::Source(parsed) => {
                let identity = self.language_identity().ok_or_else(|| {
                    PreparationError::new("Generated Rholang definition identity is unavailable")
                })?;
                let output_len = protobuf_encoder::encoded_len(&output.par);
                let source = copy_receipt_bytes(parsed.source.as_bytes())?;
                let language = copy_receipt_bytes(identity)?;
                let mut encoded = Vec::new();
                encoded.try_reserve_exact(output_len).map_err(|_| {
                    PreparationError::new("Rholang receipt output allocation failed")
                })?;
                protobuf_encoder::encode_into(&output.par, &mut encoded);
                self.check_cancelled()?;
                let program = PreparedProgram::from_normalized_with_binding(
                    output.par, source, language, encoded,
                )?;
                self.check_cancelled()?;
                Ok((program, output.guard_report))
            },
            #[cfg(test)]
            PreparationInput::Tree(_) => finish_output(output),
        }
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

    fn language_identity(&self) -> Option<&[u8]> {
        RholangLanguage
            .metadata()
            .definition_fingerprint()
            .map(str::as_bytes)
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

#[cfg(test)]
fn finish_output(
    output: session::DirectLoweringOutput,
) -> Result<(PreparedProgram, GuardDischargeReport), PreparationError> {
    check_output(&output)?;
    Ok((PreparedProgram::from_normalized(output.par), output.guard_report))
}

fn check_output(output: &session::DirectLoweringOutput) -> Result<(), PreparationError> {
    // No fold constructor belongs to the checked source profile. If the profile
    // grows, this boundary must gain real enrollment before accepting its output.
    if !output.folds.is_empty() {
        return Err(PreparationError::new("Unenrolled fold definitions in prepared Rholang"));
    }
    if output.guard_report.disagreements != 0 {
        return Err(PreparationError::new("Guard discharge disagreement in prepared Rholang"));
    }
    Ok(())
}

fn copy_receipt_bytes(bytes: &[u8]) -> Result<Vec<u8>, PreparationError> {
    let mut owned = Vec::new();
    owned
        .try_reserve_exact(bytes.len())
        .map_err(|_| PreparationError::new("Rholang receipt identity allocation failed"))?;
    owned.extend_from_slice(bytes);
    Ok(owned)
}

fn lowering_error(error: RholangAstLowerError) -> PreparationError {
    PreparationError::new(format!("Rholang preparation: {error:?}"))
}

#[cfg(test)]
#[path = "prepared_frontend_tests.rs"]
mod tests;
