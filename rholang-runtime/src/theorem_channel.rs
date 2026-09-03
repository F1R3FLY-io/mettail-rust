//! Checked adapter between reflected Rholang FLTs and theorem-indexed channels.
//!
//! A `Par` reaches the source-neutral theorem kernel only after the installed
//! grammar's structural admission automaton has accepted it and computed its
//! canonical hash.  A consume witness is derived by the production spatial
//! matcher from the stored message; callers cannot supply capture values.  The
//! final callback runs inside the kernel's language-epoch and space-epoch read
//! guards, providing the single mutation seam required by a Reified RSpace.

use crate::language_install::{
    decode_flt_hole, decode_flt_piece, error_response, exact_expr, exact_list, exact_string,
    grammar_fingerprint_label, map_par, private_name, single_private_name_id_ignoring_cache,
    wire_list, LanguageFltConstructionError, LanguageRuntimeError, NamedRuntimeTemplateHole,
    RholangLanguageRuntime,
};
use mettail_grammar_core::{
    AdmissionBudget, AdmissionCertificate, AdmissionChecker, AdmissionRefutation, AdmissionTheorem,
    AdmissionUndetermined, AdmittedMessage, CategoryId, CheckedMatchEvidence, LanguageAccessError,
    LanguageRight, PreparedConsume, PreparedProduce, SpaceRight, SpaceRights,
    StructuralTheoremChecker, TermHash, TheoremChannelDescriptor, TheoremChannelError,
    TheoremChannelKernel, TypedPatternDescriptor,
};
use mettail_rholang_codegen::{DynamicSyntaxAdmission, THEOREM_CHANNEL_BAND};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{ListParWithRandom, Par};
use models::rust::utils::{new_gbytearray_par, new_gint_par, new_gstring_par};
use rholang::rust::interpreter::contract_call::{ContractCall, Producer};
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::system_processes::Definition;
use rspace_plus_plus::rspace::r#match::Match;
use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::RwLock;

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

pub const THEOREM_CHANNEL_SERVICE_ABI_V1: &str = "mettail-theorem-channel-service/1";
pub const THEOREM_CHANNEL_OPEN_ABI_V1: &str = "mettail-theorem-channel-open/1";
pub const THEOREM_CHANNEL_PREPARE_ABI_V1: &str = "mettail-theorem-channel-prepare/1";
pub const THEOREM_CHANNEL_COMMIT_ABI_V1: &str = "mettail-theorem-channel-commit/1";
pub const THEOREM_CHANNEL_REVOKE_ABI_V1: &str = "mettail-theorem-channel-revoke/1";

pub const THEOREM_CHANNEL_OPEN_URN: &str = "rho:mettail:theorem-channel:open";
pub const THEOREM_CHANNEL_PREPARE_URN: &str = "rho:mettail:theorem-channel:prepare";
pub const THEOREM_CHANNEL_COMMIT_URN: &str = "rho:mettail:theorem-channel:commit";
pub const THEOREM_CHANNEL_REVOKE_URN: &str = "rho:mettail:theorem-channel:revoke";

const THEOREM_CHANNEL_OPEN_INDEX: u8 = 0;
const THEOREM_CHANNEL_PREPARE_INDEX: u8 = 1;
const THEOREM_CHANNEL_COMMIT_INDEX: u8 = 2;
const THEOREM_CHANNEL_REVOKE_INDEX: u8 = 3;
const THEOREM_CHANNEL_TOKEN_DOMAIN_V1: &[u8] = b"mettail-theorem-channel-capability/1\0";
const THEOREM_TRANSACTION_TOKEN_DOMAIN_V1: &[u8] = b"mettail-theorem-transaction-capability/1\0";

/// Host-supplied bounds and authority for the transient theorem transaction
/// service. A Rholang request can attenuate these values but cannot increase
/// them or select the checker implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremServicePolicy {
    pub host_space_rights: SpaceRights,
    pub max_channels: usize,
    pub max_prepared_transactions: usize,
    pub max_work_units: u64,
    pub max_evidence_bytes: u64,
    pub max_proof_cache_entries: usize,
}

impl Default for TheoremServicePolicy {
    fn default() -> Self {
        Self {
            host_space_rights: SpaceRights::all(),
            max_channels: 1_024,
            max_prepared_transactions: 4_096,
            max_work_units: 1_000_000,
            max_evidence_bytes: 16 * 1024 * 1024,
            max_proof_cache_entries: 4_096,
        }
    }
}

#[derive(Clone)]
struct TheoremChannelEntry {
    language_token: Par,
    category: String,
    channel: Arc<RholangTheoremChannel>,
}

struct PreparedExchangeEntry {
    channel: Arc<RholangTheoremChannel>,
    prepared: PreparedRholangConsume,
}

#[derive(Default)]
struct TheoremServiceState {
    next_channel: u64,
    next_transaction: u64,
    channels: BTreeMap<Vec<u8>, TheoremChannelEntry>,
    transactions: BTreeMap<Vec<u8>, PreparedExchangeEntry>,
}

/// Process-local capability router for theorem-channel transactions. It owns
/// neither source parsers nor tuple-space persistence: patterns are compiled
/// through the installed-language runtime, and successful commit returns the
/// matcher-derived capture telescope to the caller.
pub struct RholangTheoremService {
    language_runtime: Arc<RholangLanguageRuntime>,
    checker: Arc<dyn AdmissionChecker>,
    policy: TheoremServicePolicy,
    state: RwLock<TheoremServiceState>,
}

impl RholangTheoremService {
    pub fn new(
        language_runtime: Arc<RholangLanguageRuntime>,
        checker: Arc<dyn AdmissionChecker>,
        policy: TheoremServicePolicy,
    ) -> Self {
        Self {
            language_runtime,
            checker,
            policy,
            state: RwLock::new(Default::default()),
        }
    }

    pub fn structural(language_runtime: Arc<RholangLanguageRuntime>) -> Self {
        Self::new(
            language_runtime,
            Arc::new(StructuralTheoremChecker::default()),
            TheoremServicePolicy::default(),
        )
    }

    fn open(&self, request: OpenTheoremChannelCall) -> Result<Par, TheoremServiceError> {
        if request.budget.max_work_units > self.policy.max_work_units {
            return Err(TheoremServiceError::PolicyLimit("admission work units"));
        }
        if request.budget.max_evidence_bytes > self.policy.max_evidence_bytes {
            return Err(TheoremServiceError::PolicyLimit("admission evidence bytes"));
        }
        if request.proof_cache_capacity > self.policy.max_proof_cache_entries {
            return Err(TheoremServiceError::PolicyLimit("proof-cache entries"));
        }
        let handle = self
            .language_runtime
            .resolve(&request.language_token, LanguageRight::Check)
            .map_err(|error| TheoremServiceError::LanguageRuntime(Box::new(error)))?;
        let language = self
            .language_runtime
            .service()
            .table()
            .authorize(&handle, LanguageRight::Check)
            .map_err(TheoremServiceError::LanguageAccess)?;
        let mut categories = language
            .core()
            .categories
            .iter()
            .filter(|candidate| candidate.name == request.category);
        let category = categories
            .next()
            .ok_or_else(|| TheoremServiceError::UnknownCategory(request.category.clone()))?
            .id;
        if categories.next().is_some() {
            return Err(TheoremServiceError::DuplicateCategory(request.category));
        }
        let channel_theorem = request.channel_theorem.resolve(category);
        let space_theorem = request.space_theorem.resolve(category);
        let effective_rights = self
            .policy
            .host_space_rights
            .attenuate(&request.space_rights);
        let channel = Arc::new(
            RholangTheoremChannel::new(
                self.language_runtime.clone(),
                &request.language_token,
                &request.category,
                channel_theorem,
                space_theorem,
                effective_rights,
                self.checker.clone(),
                request.budget,
                request.proof_cache_capacity,
            )
            .map_err(TheoremServiceError::Channel)?,
        );

        let mut state = self
            .state
            .write()
            .map_err(|_| TheoremServiceError::Poisoned)?;
        if state.channels.len() >= self.policy.max_channels {
            return Err(TheoremServiceError::Capacity("theorem channels"));
        }
        let generation = state.next_channel;
        state.next_channel = generation
            .checked_add(1)
            .ok_or(TheoremServiceError::Generation)?;
        let id = channel_token_id(generation, channel.descriptor().id());
        let previous = state.channels.insert(
            id.clone(),
            TheoremChannelEntry {
                language_token: request.language_token,
                category: request.category,
                channel,
            },
        );
        debug_assert!(previous.is_none(), "monotone channel generations are unique");
        Ok(private_name(id))
    }

    fn prepare(&self, request: PrepareTheoremExchangeCall) -> Result<Par, TheoremServiceError> {
        let channel_id = theorem_token_id(&request.channel_token, THEOREM_CHANNEL_TOKEN_DOMAIN_V1)
            .ok_or(TheoremServiceError::InvalidChannelToken)?;
        let entry = self
            .state
            .read()
            .map_err(|_| TheoremServiceError::Poisoned)?
            .channels
            .get(channel_id)
            .cloned()
            .ok_or(TheoremServiceError::UnknownChannel)?;

        let prepared_pattern = self
            .language_runtime
            .prepare_pattern(
                &entry.language_token,
                &request.pieces,
                &request.holes,
                Some(&entry.category),
            )
            .map_err(|error| TheoremServiceError::Pattern(Box::new(error)))?;
        let admitted = entry
            .channel
            .commit_produce(
                entry
                    .channel
                    .prepare_produce(request.value)
                    .map_err(TheoremServiceError::Channel)?,
                |message| message,
            )
            .map_err(TheoremServiceError::Channel)?;
        let prepared = entry
            .channel
            .prepare_consume(&admitted, &prepared_pattern)
            .map_err(TheoremServiceError::Channel)?;

        let mut state = self
            .state
            .write()
            .map_err(|_| TheoremServiceError::Poisoned)?;
        if state.transactions.len() >= self.policy.max_prepared_transactions {
            return Err(TheoremServiceError::Capacity("prepared theorem transactions"));
        }
        let generation = state.next_transaction;
        state.next_transaction = generation
            .checked_add(1)
            .ok_or(TheoremServiceError::Generation)?;
        let id = transaction_token_id(generation, channel_id);
        let previous = state
            .transactions
            .insert(id.clone(), PreparedExchangeEntry { channel: entry.channel, prepared });
        debug_assert!(previous.is_none(), "monotone transaction generations are unique");
        Ok(private_name(id))
    }

    fn commit(&self, token: &Par) -> Result<CheckedRholangMatch, TheoremServiceError> {
        let id = theorem_token_id(token, THEOREM_TRANSACTION_TOKEN_DOMAIN_V1)
            .ok_or(TheoremServiceError::InvalidTransactionToken)?;
        let transaction = self
            .state
            .write()
            .map_err(|_| TheoremServiceError::Poisoned)?
            .transactions
            .remove(id)
            .ok_or(TheoremServiceError::UnknownTransaction)?;
        transaction
            .channel
            .commit_consume(transaction.prepared, |matched| matched)
            .map_err(TheoremServiceError::Channel)
    }

    fn revoke(&self, token: &Par) -> Result<(), TheoremServiceError> {
        let id = theorem_token_id(token, THEOREM_CHANNEL_TOKEN_DOMAIN_V1)
            .ok_or(TheoremServiceError::InvalidChannelToken)?;
        let mut state = self
            .state
            .write()
            .map_err(|_| TheoremServiceError::Poisoned)?;
        let entry = state
            .channels
            .get(id)
            .ok_or(TheoremServiceError::UnknownChannel)?;
        entry
            .channel
            .revoke()
            .map_err(TheoremServiceError::Channel)?;
        state.channels.remove(id);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TheoremWire {
    Bottom,
    Membership,
    Exact(TermHash),
}

impl TheoremWire {
    fn resolve(self, category: CategoryId) -> AdmissionTheorem {
        match self {
            Self::Bottom => AdmissionTheorem::Bottom,
            Self::Membership => AdmissionTheorem::membership(category),
            Self::Exact(hash) => AdmissionTheorem::exact(category, hash),
        }
    }
}

struct OpenTheoremChannelCall {
    language_token: Par,
    category: String,
    channel_theorem: TheoremWire,
    space_theorem: TheoremWire,
    space_rights: SpaceRights,
    budget: AdmissionBudget,
    proof_cache_capacity: usize,
    reply: Par,
}

struct PrepareTheoremExchangeCall {
    channel_token: Par,
    value: Par,
    pieces: Vec<mettail_grammar_core::RuntimeTemplatePiece>,
    holes: Vec<NamedRuntimeTemplateHole>,
    reply: Par,
}

struct TokenCall {
    token: Par,
    reply: Par,
}

#[derive(Debug)]
enum TheoremServiceWireError {
    Shape(&'static str),
    UnsupportedAbi(String),
    IntegerRange(&'static str),
    UnknownRight(String),
    DuplicateRight(String),
    InvalidTheorem,
    InvalidTermHash,
    Flt(String),
}

#[derive(Debug)]
enum TheoremServiceError {
    PolicyLimit(&'static str),
    Capacity(&'static str),
    Generation,
    InvalidChannelToken,
    UnknownChannel,
    InvalidTransactionToken,
    UnknownTransaction,
    UnknownCategory(String),
    DuplicateCategory(String),
    Pattern(Box<LanguageFltConstructionError>),
    LanguageRuntime(Box<LanguageRuntimeError>),
    LanguageAccess(LanguageAccessError),
    Channel(RholangTheoremChannelError),
    Poisoned,
}

impl fmt::Display for TheoremServiceWireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape(message) => formatter.write_str(message),
            Self::UnsupportedAbi(abi) => {
                write!(formatter, "unsupported theorem service ABI `{abi}`")
            },
            Self::IntegerRange(field) => {
                write!(formatter, "{field} is outside its supported range")
            },
            Self::UnknownRight(right) => {
                write!(formatter, "unknown theorem-channel right `{right}`")
            },
            Self::DuplicateRight(right) => {
                write!(formatter, "duplicate theorem-channel right `{right}`")
            },
            Self::InvalidTheorem => formatter.write_str("invalid theorem descriptor"),
            Self::InvalidTermHash => {
                formatter.write_str("exact theorem hash must contain 32 bytes")
            },
            Self::Flt(error) => formatter.write_str(error),
        }
    }
}

impl fmt::Display for TheoremServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PolicyLimit(resource) => {
                write!(formatter, "requested {resource} exceed host policy")
            },
            Self::Capacity(resource) => write!(formatter, "{resource} capacity is exhausted"),
            Self::Generation => formatter.write_str("theorem capability generation is exhausted"),
            Self::InvalidChannelToken => {
                formatter.write_str("expected a theorem-channel capability")
            },
            Self::UnknownChannel => {
                formatter.write_str("unknown or revoked theorem-channel capability")
            },
            Self::InvalidTransactionToken => {
                formatter.write_str("expected a theorem-transaction capability")
            },
            Self::UnknownTransaction => {
                formatter.write_str("unknown or already-consumed theorem transaction")
            },
            Self::UnknownCategory(category) => {
                write!(formatter, "unknown grammar category `{category}`")
            },
            Self::DuplicateCategory(category) => {
                write!(formatter, "duplicate grammar category `{category}`")
            },
            Self::Pattern(error) => write!(formatter, "FLT pattern preparation failed: {error}"),
            Self::LanguageRuntime(error) => {
                write!(formatter, "language runtime rejected the request: {error}")
            },
            Self::LanguageAccess(error) => {
                write!(formatter, "language authority rejected the request: {error:?}")
            },
            Self::Channel(error) => error.fmt(formatter),
            Self::Poisoned => formatter.write_str("theorem capability directory lock is poisoned"),
        }
    }
}

impl std::error::Error for TheoremServiceWireError {}
impl std::error::Error for TheoremServiceError {}

pub fn theorem_runtime_definitions(service: Arc<RholangTheoremService>) -> Vec<Definition> {
    vec![
        theorem_channel_open_definition(service.clone()),
        theorem_channel_prepare_definition(service.clone()),
        theorem_channel_commit_definition(service.clone()),
        theorem_channel_revoke_definition(service),
    ]
}

fn theorem_channel_open_definition(service: Arc<RholangTheoremService>) -> Definition {
    Definition {
        urn: THEOREM_CHANNEL_OPEN_URN.into(),
        fixed_channel: THEOREM_CHANNEL_BAND
            .channel(THEOREM_CHANNEL_OPEN_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        arity: 1,
        body_ref: THEOREM_CHANNEL_BAND
            .body_ref(THEOREM_CHANNEL_OPEN_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let service = service.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let service = service.clone();
                Box::pin(async move {
                    let (produce, payload) =
                        unapply_single_message(call, args, THEOREM_CHANNEL_OPEN_URN)?;
                    let [datum] = payload.as_slice() else {
                        return Err(request_arity_error(THEOREM_CHANNEL_OPEN_URN, payload.len()));
                    };
                    let request = decode_open_call(datum).map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{THEOREM_CHANNEL_OPEN_URN}: {error}"
                        ))
                    })?;
                    let reply = request.reply.clone();
                    let result = tokio::task::spawn_blocking(move || service.open(request)).await;
                    let response = match result {
                        Ok(Ok(token)) => success_token_response("channel", token),
                        Ok(Err(error)) => theorem_error_response(&error),
                        Err(error) => error_response("TheoremWorkerFailed", &error.to_string()),
                    };
                    let output = vec![response];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

fn theorem_channel_prepare_definition(service: Arc<RholangTheoremService>) -> Definition {
    Definition {
        urn: THEOREM_CHANNEL_PREPARE_URN.into(),
        fixed_channel: THEOREM_CHANNEL_BAND
            .channel(THEOREM_CHANNEL_PREPARE_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        arity: 1,
        body_ref: THEOREM_CHANNEL_BAND
            .body_ref(THEOREM_CHANNEL_PREPARE_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let service = service.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let service = service.clone();
                Box::pin(async move {
                    let (produce, payload) =
                        unapply_single_message(call, args, THEOREM_CHANNEL_PREPARE_URN)?;
                    let [datum] = payload.as_slice() else {
                        return Err(request_arity_error(
                            THEOREM_CHANNEL_PREPARE_URN,
                            payload.len(),
                        ));
                    };
                    let request = decode_prepare_call(datum).map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{THEOREM_CHANNEL_PREPARE_URN}: {error}"
                        ))
                    })?;
                    let reply = request.reply.clone();
                    let result =
                        tokio::task::spawn_blocking(move || service.prepare(request)).await;
                    let response = match result {
                        Ok(Ok(token)) => success_token_response("transaction", token),
                        Ok(Err(error)) => theorem_error_response(&error),
                        Err(error) => error_response("TheoremWorkerFailed", &error.to_string()),
                    };
                    let output = vec![response];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

fn theorem_channel_commit_definition(service: Arc<RholangTheoremService>) -> Definition {
    Definition {
        urn: THEOREM_CHANNEL_COMMIT_URN.into(),
        fixed_channel: THEOREM_CHANNEL_BAND
            .channel(THEOREM_CHANNEL_COMMIT_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        arity: 1,
        body_ref: THEOREM_CHANNEL_BAND
            .body_ref(THEOREM_CHANNEL_COMMIT_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let service = service.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let service = service.clone();
                Box::pin(async move {
                    let (produce, payload) =
                        unapply_single_message(call, args, THEOREM_CHANNEL_COMMIT_URN)?;
                    let [datum] = payload.as_slice() else {
                        return Err(request_arity_error(THEOREM_CHANNEL_COMMIT_URN, payload.len()));
                    };
                    let request = decode_token_call(datum, THEOREM_CHANNEL_COMMIT_ABI_V1)?;
                    let reply = request.reply.clone();
                    let result =
                        tokio::task::spawn_blocking(move || service.commit(&request.token)).await;
                    let response = match result {
                        Ok(Ok(matched)) => checked_match_response(&matched),
                        Ok(Err(error)) => theorem_error_response(&error),
                        Err(error) => error_response("TheoremWorkerFailed", &error.to_string()),
                    };
                    let output = vec![response];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

fn theorem_channel_revoke_definition(service: Arc<RholangTheoremService>) -> Definition {
    Definition {
        urn: THEOREM_CHANNEL_REVOKE_URN.into(),
        fixed_channel: THEOREM_CHANNEL_BAND
            .channel(THEOREM_CHANNEL_REVOKE_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        arity: 1,
        body_ref: THEOREM_CHANNEL_BAND
            .body_ref(THEOREM_CHANNEL_REVOKE_INDEX, THEOREM_CHANNEL_SERVICE_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let service = service.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let service = service.clone();
                Box::pin(async move {
                    let (produce, payload) =
                        unapply_single_message(call, args, THEOREM_CHANNEL_REVOKE_URN)?;
                    let [datum] = payload.as_slice() else {
                        return Err(request_arity_error(THEOREM_CHANNEL_REVOKE_URN, payload.len()));
                    };
                    let request = decode_token_call(datum, THEOREM_CHANNEL_REVOKE_ABI_V1)?;
                    let reply = request.reply.clone();
                    let result =
                        tokio::task::spawn_blocking(move || service.revoke(&request.token)).await;
                    let response = match result {
                        Ok(Ok(())) => map_par([(
                            "ok".into(),
                            map_par([(
                                "status".into(),
                                new_gstring_par("revoked".into(), Vec::new(), false),
                            )]),
                        )]),
                        Ok(Err(error)) => theorem_error_response(&error),
                        Err(error) => error_response("TheoremWorkerFailed", &error.to_string()),
                    };
                    let output = vec![response];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

fn unapply_single_message(
    call: ContractCall,
    args: (Vec<ListParWithRandom>, bool, Vec<Par>),
    urn: &str,
) -> Result<(Producer, Vec<Par>), InterpreterError> {
    let Some((produce, _is_replay, _previous, payload)) = call.unapply(args) else {
        return Err(InterpreterError::IllegalArgumentError(format!(
            "{urn}: not a single-message contract call"
        )));
    };
    Ok((produce, payload))
}

fn request_arity_error(urn: &str, found: usize) -> InterpreterError {
    InterpreterError::IllegalArgumentError(format!(
        "{urn}: expected one request datum, got Rho arity {found}"
    ))
}

fn decode_open_call(datum: &Par) -> Result<OpenTheoremChannelCall, TheoremServiceWireError> {
    let fields = exact_list(datum).ok_or(TheoremServiceWireError::Shape(
        "expected [abi, handle, category, channel-theorem, space-theorem, rights, work, evidence, cache, reply]",
    ))?;
    let [abi, handle, category, channel_theorem, space_theorem, rights, work, evidence, cache, reply] =
        fields
    else {
        return Err(TheoremServiceWireError::Shape(
            "theorem-channel open request must have arity ten",
        ));
    };
    let abi = exact_string(abi)
        .ok_or(TheoremServiceWireError::Shape("theorem-channel ABI must be a string"))?;
    if abi != THEOREM_CHANNEL_OPEN_ABI_V1 {
        return Err(TheoremServiceWireError::UnsupportedAbi(abi.into()));
    }
    Ok(OpenTheoremChannelCall {
        language_token: handle.clone(),
        category: exact_string(category)
            .ok_or(TheoremServiceWireError::Shape("theorem-channel category must be a string"))?
            .into(),
        channel_theorem: decode_theorem(channel_theorem)?,
        space_theorem: decode_theorem(space_theorem)?,
        space_rights: decode_space_rights(rights)?,
        budget: AdmissionBudget::new(
            exact_u64(work, "admission work budget")?,
            exact_u64(evidence, "admission evidence budget")?,
        ),
        proof_cache_capacity: exact_usize(cache, "proof-cache capacity")?,
        reply: reply.clone(),
    })
}

fn decode_prepare_call(datum: &Par) -> Result<PrepareTheoremExchangeCall, TheoremServiceWireError> {
    let fields = exact_list(datum).ok_or(TheoremServiceWireError::Shape(
        "expected [abi, channel, value, pieces, holes, reply]",
    ))?;
    let [abi, channel, value, pieces, holes, reply] = fields else {
        return Err(TheoremServiceWireError::Shape(
            "theorem-channel prepare request must have arity six",
        ));
    };
    let abi = exact_string(abi)
        .ok_or(TheoremServiceWireError::Shape("theorem-channel ABI must be a string"))?;
    if abi != THEOREM_CHANNEL_PREPARE_ABI_V1 {
        return Err(TheoremServiceWireError::UnsupportedAbi(abi.into()));
    }
    let pieces = exact_list(pieces)
        .ok_or(TheoremServiceWireError::Shape("FLT pattern pieces must be a proper list"))?
        .iter()
        .map(decode_flt_piece)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| TheoremServiceWireError::Flt(error.to_string()))?;
    let holes = exact_list(holes)
        .ok_or(TheoremServiceWireError::Shape("FLT pattern holes must be a proper list"))?
        .iter()
        .map(decode_flt_hole)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| TheoremServiceWireError::Flt(error.to_string()))?;
    Ok(PrepareTheoremExchangeCall {
        channel_token: channel.clone(),
        value: value.clone(),
        pieces,
        holes,
        reply: reply.clone(),
    })
}

fn decode_token_call(datum: &Par, expected_abi: &str) -> Result<TokenCall, InterpreterError> {
    let fields = exact_list(datum).ok_or_else(|| {
        InterpreterError::IllegalArgumentError("expected [abi, capability, reply]".into())
    })?;
    let [abi, token, reply] = fields else {
        return Err(InterpreterError::IllegalArgumentError(
            "theorem capability request must have arity three".into(),
        ));
    };
    let abi = exact_string(abi).ok_or_else(|| {
        InterpreterError::IllegalArgumentError("theorem capability ABI must be a string".into())
    })?;
    if abi != expected_abi {
        return Err(InterpreterError::IllegalArgumentError(format!(
            "unsupported theorem service ABI `{abi}`"
        )));
    }
    Ok(TokenCall {
        token: token.clone(),
        reply: reply.clone(),
    })
}

fn decode_theorem(value: &Par) -> Result<TheoremWire, TheoremServiceWireError> {
    let fields = exact_list(value).ok_or(TheoremServiceWireError::InvalidTheorem)?;
    match fields {
        [kind] if exact_string(kind) == Some("bottom") => Ok(TheoremWire::Bottom),
        [kind] if exact_string(kind) == Some("membership") => Ok(TheoremWire::Membership),
        [kind, hash] if exact_string(kind) == Some("exact") => {
            let Some(ExprInstance::GByteArray(bytes)) = exact_expr(hash) else {
                return Err(TheoremServiceWireError::InvalidTermHash);
            };
            let bytes: [u8; 32] = bytes
                .as_slice()
                .try_into()
                .map_err(|_| TheoremServiceWireError::InvalidTermHash)?;
            Ok(TheoremWire::Exact(TermHash(bytes)))
        },
        _ => Err(TheoremServiceWireError::InvalidTheorem),
    }
}

fn decode_space_rights(value: &Par) -> Result<SpaceRights, TheoremServiceWireError> {
    let rights = exact_list(value)
        .ok_or(TheoremServiceWireError::Shape("theorem-channel rights must be a proper list"))?;
    let mut decoded = std::collections::BTreeSet::new();
    for value in rights {
        let name = exact_string(value)
            .ok_or(TheoremServiceWireError::Shape("theorem-channel right must be a string"))?;
        let right = match name {
            "Produce" => SpaceRight::Produce,
            "Consume" => SpaceRight::Consume,
            other => return Err(TheoremServiceWireError::UnknownRight(other.into())),
        };
        if !decoded.insert(right) {
            return Err(TheoremServiceWireError::DuplicateRight(name.into()));
        }
    }
    Ok(SpaceRights::from_rights(decoded))
}

fn exact_u64(value: &Par, field: &'static str) -> Result<u64, TheoremServiceWireError> {
    let Some(ExprInstance::GInt(value)) = exact_expr(value) else {
        return Err(TheoremServiceWireError::Shape("resource bound must be an integer"));
    };
    u64::try_from(*value).map_err(|_| TheoremServiceWireError::IntegerRange(field))
}

fn exact_usize(value: &Par, field: &'static str) -> Result<usize, TheoremServiceWireError> {
    usize::try_from(exact_u64(value, field)?)
        .map_err(|_| TheoremServiceWireError::IntegerRange(field))
}

fn theorem_token_id<'a>(value: &'a Par, domain: &[u8]) -> Option<&'a [u8]> {
    single_private_name_id_ignoring_cache(value).filter(|id| id.starts_with(domain))
}

fn channel_token_id(generation: u64, descriptor: [u8; 32]) -> Vec<u8> {
    let mut id = Vec::with_capacity(THEOREM_CHANNEL_TOKEN_DOMAIN_V1.len() + 8 + 32);
    id.extend_from_slice(THEOREM_CHANNEL_TOKEN_DOMAIN_V1);
    id.extend_from_slice(&generation.to_be_bytes());
    id.extend_from_slice(&descriptor);
    id
}

fn transaction_token_id(generation: u64, channel_id: &[u8]) -> Vec<u8> {
    let mut id =
        Vec::with_capacity(THEOREM_TRANSACTION_TOKEN_DOMAIN_V1.len() + 8 + 8 + channel_id.len());
    id.extend_from_slice(THEOREM_TRANSACTION_TOKEN_DOMAIN_V1);
    id.extend_from_slice(&generation.to_be_bytes());
    id.extend_from_slice(&(channel_id.len() as u64).to_be_bytes());
    id.extend_from_slice(channel_id);
    id
}

fn success_token_response(field: &str, token: Par) -> Par {
    map_par([("ok".into(), map_par([(field.into(), token)]))])
}

fn checked_match_response(matched: &CheckedRholangMatch) -> Par {
    let evidence = matched.evidence();
    let capture_proofs = evidence.captures().iter().map(proof_response).collect();
    map_par([(
        "ok".into(),
        map_par([
            ("status".into(), new_gstring_par("committed".into(), Vec::new(), false)),
            ("captures".into(), wire_list(matched.captures().to_vec())),
            (
                "pattern".into(),
                new_gbytearray_par(evidence.pattern_id().to_vec(), Vec::new(), false),
            ),
            ("message-proof".into(), proof_response(matched.message().evidence().proof())),
            ("capture-proofs".into(), wire_list(capture_proofs)),
        ]),
    )])
}

fn proof_response(proof: &mettail_grammar_core::ProvenAdmission) -> Par {
    let certificate = proof.certificate();
    let term = certificate.term();
    let usage = proof.usage();
    map_par([
        (
            "language".into(),
            new_gbytearray_par(term.language().to_vec(), Vec::new(), false),
        ),
        ("category".into(), new_gint_par(i64::from(term.category().0), Vec::new(), false)),
        (
            "term".into(),
            new_gbytearray_par(term.term_hash().0.to_vec(), Vec::new(), false),
        ),
        (
            "theorem".into(),
            new_gbytearray_par(certificate.theorem_id().0.to_vec(), Vec::new(), false),
        ),
        (
            "checker".into(),
            new_gstring_par(certificate.checker_abi().into(), Vec::new(), false),
        ),
        (
            "limits".into(),
            new_gstring_par(certificate.limit_profile().into(), Vec::new(), false),
        ),
        (
            "evidence".into(),
            new_gbytearray_par(certificate.evidence().to_vec(), Vec::new(), false),
        ),
        (
            "evidence-hash".into(),
            new_gbytearray_par(certificate.evidence_hash().to_vec(), Vec::new(), false),
        ),
        (
            "work".into(),
            new_gint_par(
                i64::try_from(usage.logical_work_units)
                    .expect("checked request budgets originate in nonnegative Rholang integers"),
                Vec::new(),
                false,
            ),
        ),
        (
            "evidence-bytes".into(),
            new_gint_par(
                i64::try_from(usage.evidence_bytes)
                    .expect("checked evidence is bounded by a nonnegative Rholang integer"),
                Vec::new(),
                false,
            ),
        ),
    ])
}

fn theorem_error_response(error: &TheoremServiceError) -> Par {
    error_response(theorem_error_code(error), &error.to_string())
}

fn theorem_error_code(error: &TheoremServiceError) -> &'static str {
    match error {
        TheoremServiceError::PolicyLimit(_) | TheoremServiceError::Capacity(_) => {
            "ResourceExhausted"
        },
        TheoremServiceError::Generation => "GenerationExhausted",
        TheoremServiceError::InvalidChannelToken | TheoremServiceError::InvalidTransactionToken => {
            "InvalidCapability"
        },
        TheoremServiceError::UnknownChannel | TheoremServiceError::UnknownTransaction => {
            "StaleAuthority"
        },
        TheoremServiceError::UnknownCategory(_) => "UnknownCategory",
        TheoremServiceError::DuplicateCategory(_) => "DuplicateCategory",
        TheoremServiceError::Pattern(error)
            if matches!(error.as_ref(), LanguageFltConstructionError::AmbiguousPattern) =>
        {
            "AmbiguousPattern"
        },
        TheoremServiceError::Pattern(_) => "InvalidPattern",
        TheoremServiceError::LanguageRuntime(error)
            if matches!(error.as_ref(), LanguageRuntimeError::UnknownHandle) =>
        {
            "StaleAuthority"
        },
        TheoremServiceError::LanguageAccess(LanguageAccessError::Revoked)
        | TheoremServiceError::Channel(RholangTheoremChannelError::Theorem(
            TheoremChannelError::StaleEpoch,
        )) => "StaleAuthority",
        TheoremServiceError::LanguageRuntime(_) | TheoremServiceError::LanguageAccess(_) => {
            "LanguageAuthorityRejected"
        },
        TheoremServiceError::Channel(RholangTheoremChannelError::StructuralAdmissionRejected)
        | TheoremServiceError::Channel(RholangTheoremChannelError::ForeignPattern)
        | TheoremServiceError::Channel(RholangTheoremChannelError::PatternCategoryMismatch) => {
            "WrongLanguageOrCategory"
        },
        TheoremServiceError::Channel(RholangTheoremChannelError::PatternMismatch)
        | TheoremServiceError::Channel(RholangTheoremChannelError::CaptureAdmissionRejected) => {
            "PatternRejected"
        },
        TheoremServiceError::Channel(RholangTheoremChannelError::Theorem(
            TheoremChannelError::AdmissionRefuted {
                reason: AdmissionRefutation::TheoremDoesNotHold,
                ..
            },
        )) => "TheoremRefuted",
        TheoremServiceError::Channel(RholangTheoremChannelError::Theorem(
            TheoremChannelError::AdmissionRefuted { .. },
        )) => "CertificateRejected",
        TheoremServiceError::Channel(RholangTheoremChannelError::Theorem(
            TheoremChannelError::AdmissionUndetermined {
                reason:
                    AdmissionUndetermined::WorkBudgetExhausted { .. }
                    | AdmissionUndetermined::EvidenceBudgetExhausted { .. },
                ..
            },
        )) => "AdmissionExhausted",
        TheoremServiceError::Channel(RholangTheoremChannelError::Theorem(
            TheoremChannelError::AdmissionUndetermined { .. },
        )) => "AdmissionUndetermined",
        TheoremServiceError::Channel(_) => "TheoremChannelRejected",
        TheoremServiceError::Poisoned => "TheoremServiceUnavailable",
    }
}

#[cfg(test)]
mod service_wire_tests {
    use super::*;

    fn string(value: &str) -> Par {
        new_gstring_par(value.into(), Vec::new(), false)
    }

    fn integer(value: i64) -> Par {
        new_gint_par(value, Vec::new(), false)
    }

    #[test]
    fn open_wire_preserves_explicit_authority_and_resource_requests() {
        let handle = private_name(b"installed-language-test-capability".to_vec());
        let reply = private_name(b"reply".to_vec());
        let datum = wire_list(vec![
            string(THEOREM_CHANNEL_OPEN_ABI_V1),
            handle.clone(),
            string("Expr"),
            wire_list(vec![string("membership")]),
            wire_list(vec![string("bottom")]),
            wire_list(vec![string("Produce"), string("Consume")]),
            integer(17),
            integer(1_024),
            integer(31),
            reply.clone(),
        ]);

        let request = decode_open_call(&datum).expect("canonical open request decodes");
        assert_eq!(request.language_token, handle);
        assert_eq!(request.category, "Expr");
        assert_eq!(request.channel_theorem, TheoremWire::Membership);
        assert_eq!(request.space_theorem, TheoremWire::Bottom);
        assert!(request.space_rights.contains(SpaceRight::Produce));
        assert!(request.space_rights.contains(SpaceRight::Consume));
        assert_eq!(request.budget, AdmissionBudget::new(17, 1_024));
        assert_eq!(request.proof_cache_capacity, 31);
        assert_eq!(request.reply, reply);
    }

    #[test]
    fn open_wire_rejects_implicit_duplicate_and_unknown_space_rights() {
        assert_eq!(
            decode_space_rights(&wire_list(Vec::new())).expect("an explicit empty request decodes"),
            SpaceRights::none(),
        );
        assert!(matches!(
            decode_space_rights(&wire_list(vec![string("Produce"), string("Produce")])),
            Err(TheoremServiceWireError::DuplicateRight(ref right)) if right == "Produce"
        ));
        assert!(matches!(
            decode_space_rights(&wire_list(vec![string("Admin")])),
            Err(TheoremServiceWireError::UnknownRight(ref right)) if right == "Admin"
        ));
    }

    #[test]
    fn channel_and_transaction_capabilities_have_disjoint_framed_domains() {
        let channel_id = channel_token_id(7, [0xA5; 32]);
        let transaction_id = transaction_token_id(11, &channel_id);
        let channel = private_name(channel_id.clone());
        let transaction = private_name(transaction_id.clone());

        assert_eq!(
            theorem_token_id(&channel, THEOREM_CHANNEL_TOKEN_DOMAIN_V1),
            Some(channel_id.as_slice()),
        );
        assert_eq!(
            theorem_token_id(&transaction, THEOREM_TRANSACTION_TOKEN_DOMAIN_V1),
            Some(transaction_id.as_slice()),
        );
        assert!(theorem_token_id(&channel, THEOREM_TRANSACTION_TOKEN_DOMAIN_V1).is_none());
        assert!(theorem_token_id(&transaction, THEOREM_CHANNEL_TOKEN_DOMAIN_V1).is_none());
        assert!(
            theorem_token_id(
                &string("mettail-theorem-channel-capability/1"),
                THEOREM_CHANNEL_TOKEN_DOMAIN_V1
            )
            .is_none(),
            "a public string that resembles a token is not authority",
        );
    }
}
