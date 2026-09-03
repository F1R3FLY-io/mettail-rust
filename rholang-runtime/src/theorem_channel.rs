//! Checked adapter between reflected Rholang FLTs and theorem-indexed channels.
//!
//! A `Par` reaches the source-neutral theorem kernel only after the installed
//! grammar's structural admission automaton has accepted it and computed its
//! canonical hash.  A consume witness is derived by the production spatial
//! matcher from the stored message; callers cannot supply capture values.  The
//! final callback runs inside the kernel's language-epoch and space-epoch read
//! guards, providing the single mutation seam required by a Reified RSpace.

use crate::language_install::{
    grammar_fingerprint_label, LanguageFltConstructionError, LanguageRuntimeError,
    RholangLanguageRuntime,
};
use mettail_grammar_core::{
    AdmissionBudget, AdmissionCertificate, AdmissionChecker, AdmissionTheorem, AdmittedMessage,
    CategoryId, CheckedMatchEvidence, LanguageAccessError, LanguageRight, PreparedConsume,
    PreparedProduce, SpaceRight, SpaceRights, TermHash, TheoremChannelDescriptor,
    TheoremChannelError, TheoremChannelKernel, TypedPatternDescriptor,
};
use mettail_rholang_codegen::DynamicSyntaxAdmission;
use models::rhoapi::{ListParWithRandom, Par};
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rspace_plus_plus::rspace::r#match::Match;
use std::fmt;
use std::sync::Arc;

pub struct RholangTheoremChannel {
    runtime: Arc<RholangLanguageRuntime>,
    handle: mettail_grammar_core::InstalledLanguageHandle,
    category: CategoryId,
    fingerprint: String,
    admission: Arc<DynamicSyntaxAdmission>,
    kernel: TheoremChannelKernel,
}

impl RholangTheoremChannel {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        runtime: Arc<RholangLanguageRuntime>,
        language_token: &Par,
        category_name: &str,
        channel_theorem: AdmissionTheorem,
        space_theorem: AdmissionTheorem,
        space_rights: SpaceRights,
        checker: Arc<dyn AdmissionChecker>,
        admission_budget: AdmissionBudget,
        proof_cache_capacity: usize,
    ) -> Result<Self, RholangTheoremChannelError> {
        if !space_rights.contains(SpaceRight::Produce)
            && !space_rights.contains(SpaceRight::Consume)
        {
            return Err(RholangTheoremChannelError::NoSpaceRights);
        }
        let handle = runtime
            .resolve(language_token, LanguageRight::Check)
            .map_err(|error| RholangTheoremChannelError::Runtime(Box::new(error)))?;
        let table = runtime.service().table();
        let mut required_rights = vec![LanguageRight::Check];
        if space_rights.contains(SpaceRight::Produce) {
            required_rights.push(LanguageRight::Publish);
        }
        if space_rights.contains(SpaceRight::Consume) {
            required_rights.push(LanguageRight::Match);
        }
        let language = table
            .authorize_all(&handle, &required_rights)
            .map_err(RholangTheoremChannelError::LanguageAccess)?;
        let mut categories = language
            .core()
            .categories
            .iter()
            .filter(|category| category.name == category_name);
        let category = categories
            .next()
            .ok_or_else(|| RholangTheoremChannelError::UnknownCategory(category_name.into()))?
            .id;
        if categories.next().is_some() {
            return Err(RholangTheoremChannelError::DuplicateCategory(category_name.into()));
        }
        let admission = runtime
            .admission_for(handle.fingerprint(), language.core())
            .map_err(|error| RholangTheoremChannelError::Construction(Box::new(error)))?;
        let descriptor = TheoremChannelDescriptor::new(
            handle.fingerprint(),
            category,
            channel_theorem,
            space_theorem,
        )
        .map_err(RholangTheoremChannelError::Theorem)?;
        Ok(Self {
            fingerprint: grammar_fingerprint_label(handle.fingerprint()),
            kernel: TheoremChannelKernel::new(
                descriptor,
                space_rights,
                checker,
                admission_budget,
                proof_cache_capacity,
            ),
            runtime,
            handle,
            category,
            admission,
        })
    }

    pub fn descriptor(&self) -> &TheoremChannelDescriptor {
        self.kernel.descriptor()
    }

    pub fn prepare_produce(
        &self,
        value: Par,
    ) -> Result<PreparedRholangProduce, RholangTheoremChannelError> {
        self.prepare_produce_with_certificate(value, None)
    }

    pub fn prepare_produce_with_certificate(
        &self,
        value: Par,
        presented_certificate: Option<&AdmissionCertificate>,
    ) -> Result<PreparedRholangProduce, RholangTheoremChannelError> {
        let term_hash = self.admitted_term_hash(&value, self.category)?;
        let prepared = self
            .kernel
            .prepare_produce_with_certificate(
                self.runtime.service().table(),
                &self.handle,
                term_hash,
                presented_certificate,
            )
            .map_err(RholangTheoremChannelError::Theorem)?;
        Ok(PreparedRholangProduce { prepared, value })
    }

    pub fn commit_produce<R>(
        &self,
        prepared: PreparedRholangProduce,
        commit: impl FnOnce(AdmittedRholangMessage) -> R,
    ) -> Result<R, RholangTheoremChannelError> {
        let PreparedRholangProduce { prepared, value } = prepared;
        self.kernel
            .commit_produce(self.runtime.service().table(), prepared, |evidence| {
                commit(AdmittedRholangMessage { value: Arc::new(value), evidence })
            })
            .map_err(RholangTheoremChannelError::Theorem)
    }

    /// Match `message` with a previously prepared dynamic FLT pattern and
    /// derive its capture telescope.  The capture values are outputs of the
    /// spatial matcher, never caller assertions.
    pub fn prepare_consume(
        &self,
        message: &AdmittedRholangMessage,
        prepared_pattern_token: &Par,
    ) -> Result<PreparedRholangConsume, RholangTheoremChannelError> {
        self.runtime
            .service()
            .table()
            .authorize_all(&self.handle, &[LanguageRight::Match, LanguageRight::Check])
            .map_err(RholangTheoremChannelError::LanguageAccess)?;
        let pattern = self
            .runtime
            .resolve_prepared_pattern(prepared_pattern_token)
            .map_err(|error| RholangTheoremChannelError::Runtime(Box::new(error)))?;
        if pattern.fingerprint_bytes() != self.handle.fingerprint() {
            return Err(RholangTheoremChannelError::ForeignPattern);
        }
        let root_category = pattern.root_category();
        if root_category != self.category {
            return Err(RholangTheoremChannelError::PatternCategoryMismatch);
        }
        let datum = ListParWithRandom {
            pars: vec![message.value().clone()],
            random_state: Vec::new(),
        };
        if !pattern.admits_subject(&datum) {
            return Err(RholangTheoremChannelError::StructuralAdmissionRejected);
        }
        let occurrences = Matcher
            .get(pattern.pattern(), &datum)
            .ok_or(RholangTheoremChannelError::PatternMismatch)?;
        let captures = pattern
            .project_admitted_captures(occurrences)
            .ok_or(RholangTheoremChannelError::CaptureAdmissionRejected)?;
        let mut capture_hashes = Vec::with_capacity(captures.pars.len());
        for (capture, category) in captures.pars.iter().zip(pattern.capture_categories()) {
            let hash = pattern
                .admitted_term_hash(capture, *category)
                .ok_or(RholangTheoremChannelError::CaptureAdmissionRejected)?;
            capture_hashes.push(TermHash(hash));
        }
        let descriptor = TypedPatternDescriptor::new(
            self.handle.fingerprint(),
            self.category,
            pattern.pattern_id(),
            None,
            pattern.capture_categories().to_vec(),
            usize::try_from(self.runtime.service().policy().runtime.max_capture_bindings)
                .unwrap_or(usize::MAX),
        )
        .map_err(RholangTheoremChannelError::Theorem)?;
        let prepared = self
            .kernel
            .prepare_consume(
                self.runtime.service().table(),
                &self.handle,
                message.evidence(),
                &descriptor,
                &capture_hashes,
            )
            .map_err(RholangTheoremChannelError::Theorem)?;
        Ok(PreparedRholangConsume {
            prepared,
            message: message.clone(),
            captures: captures.pars,
        })
    }

    pub fn commit_consume<R>(
        &self,
        prepared: PreparedRholangConsume,
        commit: impl FnOnce(CheckedRholangMatch) -> R,
    ) -> Result<R, RholangTheoremChannelError> {
        let PreparedRholangConsume { prepared, message, captures } = prepared;
        self.kernel
            .commit_consume(self.runtime.service().table(), prepared, |evidence| {
                let message = AdmittedRholangMessage {
                    value: message.value,
                    evidence: evidence.message().clone(),
                };
                commit(CheckedRholangMatch { message, captures, evidence })
            })
            .map_err(RholangTheoremChannelError::Theorem)
    }

    pub fn attenuate_space_rights(
        &self,
        requested: &SpaceRights,
    ) -> Result<u64, RholangTheoremChannelError> {
        self.kernel
            .attenuate_space_rights(requested)
            .map_err(RholangTheoremChannelError::Theorem)
    }

    pub fn revoke(&self) -> Result<u64, RholangTheoremChannelError> {
        self.kernel
            .revoke()
            .map_err(RholangTheoremChannelError::Theorem)
    }

    fn admitted_term_hash(
        &self,
        value: &Par,
        category: CategoryId,
    ) -> Result<TermHash, RholangTheoremChannelError> {
        let hash = self
            .admission
            .admitted_term_hash(value, &self.fingerprint, category)
            .ok_or(RholangTheoremChannelError::StructuralAdmissionRejected)?;
        Ok(TermHash(hash))
    }
}

pub struct PreparedRholangProduce {
    prepared: PreparedProduce,
    value: Par,
}

pub struct PreparedRholangConsume {
    prepared: PreparedConsume,
    message: AdmittedRholangMessage,
    captures: Vec<Par>,
}

#[derive(Clone)]
pub struct AdmittedRholangMessage {
    value: Arc<Par>,
    evidence: AdmittedMessage,
}

impl AdmittedRholangMessage {
    pub fn value(&self) -> &Par {
        &self.value
    }

    pub fn evidence(&self) -> &AdmittedMessage {
        &self.evidence
    }
}

pub struct CheckedRholangMatch {
    message: AdmittedRholangMessage,
    captures: Vec<Par>,
    evidence: CheckedMatchEvidence,
}

impl CheckedRholangMatch {
    pub fn message(&self) -> &AdmittedRholangMessage {
        &self.message
    }

    pub fn captures(&self) -> &[Par] {
        &self.captures
    }

    pub fn evidence(&self) -> &CheckedMatchEvidence {
        &self.evidence
    }
}

#[derive(Debug)]
pub enum RholangTheoremChannelError {
    NoSpaceRights,
    UnknownCategory(String),
    DuplicateCategory(String),
    StructuralAdmissionRejected,
    ForeignPattern,
    PatternCategoryMismatch,
    PatternMismatch,
    CaptureAdmissionRejected,
    Construction(Box<LanguageFltConstructionError>),
    Runtime(Box<LanguageRuntimeError>),
    LanguageAccess(LanguageAccessError),
    Theorem(TheoremChannelError),
}

impl fmt::Display for RholangTheoremChannelError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSpaceRights => formatter.write_str("typed channel has no space rights"),
            Self::UnknownCategory(name) => write!(formatter, "unknown grammar category `{name}`"),
            Self::DuplicateCategory(name) => {
                write!(formatter, "grammar contains duplicate category `{name}`")
            },
            Self::StructuralAdmissionRejected => {
                formatter.write_str("value is not structurally admitted by the channel grammar")
            },
            Self::ForeignPattern => {
                formatter.write_str("prepared pattern belongs to another installed language")
            },
            Self::PatternCategoryMismatch => {
                formatter.write_str("prepared pattern category does not equal channel category")
            },
            Self::PatternMismatch => formatter.write_str("prepared FLT pattern did not match"),
            Self::CaptureAdmissionRejected => {
                formatter.write_str("matched captures do not satisfy their typed telescope")
            },
            Self::Construction(error) => write!(formatter, "FLT construction error: {error}"),
            Self::Runtime(error) => write!(formatter, "language runtime error: {error}"),
            Self::LanguageAccess(error) => write!(formatter, "language access error: {error:?}"),
            Self::Theorem(error) => write!(formatter, "theorem channel error: {error}"),
        }
    }
}

impl std::error::Error for RholangTheoremChannelError {}
