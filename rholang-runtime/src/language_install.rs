//! Rholang-facing installation boundary for run-time MeTTaIL languages.
//!
//! Greg/Mike `Module` / `Theory` syntax and the ordinary `language/2` value are
//! authoring fronts only. Both are converted to the same canonical value before
//! GrammarCore lowering, parser-image compilation, and the single atomic table
//! commit. Registry access is injected as an immutable snapshot. File references
//! remain recognized but unavailable until a scoped Rholang File I/O capability
//! implements the resolver contract; this module never calls ambient filesystem
//! APIs.

use mettail_dovetail_runtime::{compile_theory_semantic_image, TheoryImageCompileError};
use mettail_elab::canonical::{RhoValue, ValueToCoreError};
use mettail_elab::module::{CanonicalModuleValue, CANONICAL_MODULE_SCHEMA_V1};
use mettail_elab::registry::{
    FinishExecutableRegistryInstallError, InstallExecutableRegistryError, ParserCacheDisposition,
    RegistryLanguageRecord, SemanticCacheDisposition, VersionedLanguageRegistryReader,
};
use mettail_elab::resolve::{
    ModuleRef, RegistryModuleValue, RegistryResolver, VersionedRegistryReader,
};
use mettail_elab::wire::{decode_ddl_value, ParsedDdl};
use mettail_grammar_core::{
    CategoryId, DefaultRuntimeHost, ExecutableLanguageInstall, InstallLanguageError,
    InstalledLanguageHandle, InstalledLanguageTable, InstalledParseError, LanguageAccessError,
    LanguageRevocationAuthority, LanguageRight, LanguageRights, ParserImageAdmissionLimits,
    RuntimeCapabilityError, RuntimeError, RuntimeHost, RuntimePolicy, RuntimeTemplateHole,
    RuntimeTemplatePiece, TheoryImageAdmissionLimits, WeightedParse,
};
use mettail_prattail::runtime_backend::{
    compile_parser_image, RuntimeCompileError, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI,
};
use mettail_rholang_codegen::{
    dynamic_syntax_to_ground_term, dynamic_template_hole_categories, reflect_flt_construction,
    reflect_flt_pattern, DynamicAdmissionCompileError, DynamicReflectionError,
    DynamicSyntaxAdmission, FltHole, FltPatternReflection, FltReflectError,
    LANGUAGE_FLT_CONSTRUCT_BAND, LANGUAGE_FLT_PATTERN_BAND, LANGUAGE_INSTALL_BAND,
    LANGUAGE_PARSE_BAND,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance::GPrivateBody;
use models::rhoapi::{BindPattern, GPrivate, GUnforgeable, ListParWithRandom, Par};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::rholang::par_children::visit_canonical_par_tree;
use models::rust::rholang::protobuf_encoder;
use models::rust::utils::{
    new_elist_par, new_emap_par, new_gint_par, new_gstring_par, new_key_value_pair, union,
};
use rholang::rust::interpreter::contract_call::ContractCall;
use rholang::rust::interpreter::errors::InterpreterError;
use rholang::rust::interpreter::system_processes::Definition;
use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, RwLock};

pub use mettail_elab::wire::DDL_AST_ENVELOPE_V2;

pub const LANGUAGE_CAPABILITY_ABI_V1: &str = "mettail-language-capability/1";
pub const LANGUAGE_CAPABILITY_ABI_V2: &str = "mettail-language-capability/2";
pub const LANGUAGE_CAPABILITY_ABI_CURRENT: &str = LANGUAGE_CAPABILITY_ABI_V2;
pub const LANGUAGE_INSTALL_URN: &str = "rho:mettail:install";
pub const LANGUAGE_PARSE_ABI_V1: &str = "mettail-language-parse/1";
pub const LANGUAGE_PARSE_URN: &str = "rho:mettail:parse";
pub const LANGUAGE_FLT_CONSTRUCT_ABI_V1: &str = "mettail-language-flt-construct/1";
pub const LANGUAGE_FLT_CONSTRUCT_URN: &str = "rho:mettail:flt:construct";
pub const LANGUAGE_FLT_PATTERN_ABI_V1: &str = "mettail-language-flt-pattern/1";
pub const LANGUAGE_FLT_PATTERN_URN: &str = "rho:mettail:flt:pattern";
pub const DYNAMIC_FLT_PATTERN_ENVELOPE_V1: &str = "mettail.dynamic-flt-pattern.v1";
pub const REGISTRY_MODULE_REFERENCE_V1: &str = "mettail-registry-module-ref/1";
pub const REGISTRY_LANGUAGE_REFERENCE_V1: &str = "mettail-registry-language-ref/1";
#[cfg(test)]
const LANGUAGE_HANDLE_DOMAIN_V1: &[u8] = b"mettail-installed-language-handle/1\0";
const LANGUAGE_HANDLE_DOMAIN_V2: &[u8] = b"mettail-installed-language-handle/2\0";
const LANGUAGE_HANDLE_DOMAIN_CURRENT: &[u8] = LANGUAGE_HANDLE_DOMAIN_V2;
const PREPARED_PATTERN_DOMAIN_V1: &[u8] = b"mettail-prepared-flt-pattern/1\0";
const MAX_PUBLIC_ERROR_CHARS: usize = 512;
pub const MAX_INSTALL_CANDIDATE_ENCODED_BYTES: usize = 128 * 1024 * 1024;

/// One immutable view of Registry state used for a complete installation.
///
/// The node adapter must pin the snapshot before calling the installer. The
/// two lookup families are separate because module references resolve signed
/// canonical multi-export records, while canonical `extends` / `includes` /
/// `mixins` edges resolve authoritative single-language records. Neither
/// lookup grants installation authority or licenses source reparsing.
pub trait RegistrySnapshot: Send + Sync {
    fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String>;
    fn lookup_language(&self, name: &str) -> Result<Option<RegistryLanguageRecord>, String>;
    fn verify_module_trust(
        &self,
        uri: &str,
        signed_payload: &[u8],
        signatures: &RhoValue,
    ) -> Result<(), String>;
}

#[derive(Default)]
pub struct EmptyRegistrySnapshot;

impl RegistrySnapshot for EmptyRegistrySnapshot {
    fn lookup_module(&self, _uri: &str) -> Result<Option<RegistryModuleValue>, String> {
        Ok(None)
    }

    fn lookup_language(&self, _name: &str) -> Result<Option<RegistryLanguageRecord>, String> {
        Ok(None)
    }

    fn verify_module_trust(
        &self,
        _uri: &str,
        _signed_payload: &[u8],
        _signatures: &RhoValue,
    ) -> Result<(), String> {
        Err("empty Registry snapshot has no trust authority".into())
    }
}

#[derive(Debug)]
pub enum InstallCandidate {
    Ddl(ParsedDdl),
    DdlWithPrograms {
        declaration: ParsedDdl,
        programs: Vec<StagedModuleProgram>,
    },
    Canonical(RhoValue),
    RegistryModule(String),
    RegistryLanguage(String),
}

/// One ordinary module `Proc`, moved out of the structural DDL envelope before
/// literal-value admission. It is returned only after the whole language batch
/// commits and is never executed by the installer.
#[derive(Debug)]
pub struct StagedModuleProgram {
    pub source_ordinal: usize,
    pub process: Par,
}

/// Host authority and deterministic resource policy for one installer.
/// Specification data can request a subset of `host_grants`; it cannot modify
/// this value or its commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LanguageInstallPolicy {
    pub host_grants: LanguageRights,
    pub runtime: RuntimePolicy,
    pub parser_image: ParserImageAdmissionLimits,
    pub semantic_image: TheoryImageAdmissionLimits,
    pub max_installed_languages: u64,
    pub capability_abi: String,
    pub fingerprint: [u8; 32],
}

impl LanguageInstallPolicy {
    pub fn new(
        host_grants: LanguageRights,
        runtime: RuntimePolicy,
        capability_abi: impl Into<String>,
    ) -> Self {
        Self::with_language_limit(host_grants, runtime, 1_024, capability_abi)
    }

    pub fn with_language_limit(
        host_grants: LanguageRights,
        runtime: RuntimePolicy,
        max_installed_languages: u64,
        capability_abi: impl Into<String>,
    ) -> Self {
        Self::with_language_and_semantic_limits(
            host_grants,
            runtime,
            TheoryImageAdmissionLimits::default(),
            max_installed_languages,
            capability_abi,
        )
    }

    pub fn with_language_and_semantic_limits(
        host_grants: LanguageRights,
        runtime: RuntimePolicy,
        semantic_image: TheoryImageAdmissionLimits,
        max_installed_languages: u64,
        capability_abi: impl Into<String>,
    ) -> Self {
        Self::with_language_and_artifact_limits(
            host_grants,
            runtime,
            ParserImageAdmissionLimits::default(),
            semantic_image,
            max_installed_languages,
            capability_abi,
        )
    }

    pub fn with_language_and_artifact_limits(
        host_grants: LanguageRights,
        runtime: RuntimePolicy,
        parser_image: ParserImageAdmissionLimits,
        semantic_image: TheoryImageAdmissionLimits,
        max_installed_languages: u64,
        capability_abi: impl Into<String>,
    ) -> Self {
        let capability_abi = capability_abi.into();
        let fingerprint = fingerprint_policy(
            &host_grants,
            runtime,
            parser_image,
            semantic_image,
            max_installed_languages,
            &capability_abi,
        );
        Self {
            host_grants,
            runtime,
            parser_image,
            semantic_image,
            max_installed_languages,
            capability_abi,
            fingerprint,
        }
    }
}

impl Default for LanguageInstallPolicy {
    fn default() -> Self {
        Self::new(LanguageRights::all(), RuntimePolicy::default(), LANGUAGE_CAPABILITY_ABI_CURRENT)
    }
}

fn fingerprint_policy(
    grants: &LanguageRights,
    runtime: RuntimePolicy,
    parser_image: ParserImageAdmissionLimits,
    semantic_image: TheoryImageAdmissionLimits,
    max_installed_languages: u64,
    capability_abi: &str,
) -> [u8; 32] {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"mettail-install-policy/5\0");
    for right in grants.iter() {
        bytes.extend_from_slice(right.name().as_bytes());
        bytes.push(0);
    }
    bytes.extend_from_slice(&runtime.max_input_bytes.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_parse_items.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_forest_nodes.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_semantic_results.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_capture_bindings.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_symbolic_template_cache_entries.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_symbolic_template_cache_weight.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_lexer_mode_depth.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_foreign_nesting.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_lexer_states.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_lexer_edges.to_be_bytes());
    bytes.extend_from_slice(&runtime.max_lexer_work.to_be_bytes());
    bytes.extend_from_slice(&parser_image.fingerprint());
    bytes.extend_from_slice(&semantic_image.fingerprint());
    bytes.extend_from_slice(&max_installed_languages.to_be_bytes());
    bytes.extend_from_slice(&(capability_abi.len() as u64).to_be_bytes());
    bytes.extend_from_slice(capability_abi.as_bytes());
    *blake3::hash(&bytes).as_bytes()
}

#[derive(Debug)]
pub struct InstalledLanguageReceipt {
    pub handle: InstalledLanguageHandle,
    pub fingerprint: [u8; 32],
    pub requested_rights: LanguageRights,
    pub granted_rights: LanguageRights,
    pub cache_disposition: ParserCacheDisposition,
    pub semantic_cache_disposition: SemanticCacheDisposition,
}

#[derive(Debug)]
pub struct InstalledLanguageExportReceipt {
    pub name: String,
    pub receipt: InstalledLanguageReceipt,
}

#[derive(Debug)]
pub struct InstalledLanguageBatchReceipt {
    /// Present only when the installed candidate was a Greg/Mike `Module`.
    pub module_name: Option<String>,
    pub exports: Vec<InstalledLanguageExportReceipt>,
    pub programs: Vec<StagedModuleProgram>,
}

struct CanonicalCandidateSet {
    module_name: Option<String>,
    records: Vec<(Option<String>, RegistryLanguageRecord)>,
    programs: Vec<StagedModuleProgram>,
}

pub struct LanguageInstallService {
    registry: Arc<dyn RegistrySnapshot>,
    table: Arc<InstalledLanguageTable>,
    policy: LanguageInstallPolicy,
    revocations: RwLock<BTreeMap<[u8; 32], LanguageRevocationAuthority>>,
}

impl LanguageInstallService {
    pub fn new(registry: Arc<dyn RegistrySnapshot>, policy: LanguageInstallPolicy) -> Self {
        Self {
            registry,
            table: Arc::new(InstalledLanguageTable::new()),
            policy,
            revocations: RwLock::new(BTreeMap::new()),
        }
    }

    pub fn table(&self) -> &Arc<InstalledLanguageTable> {
        &self.table
    }

    pub fn policy(&self) -> &LanguageInstallPolicy {
        &self.policy
    }

    pub fn installed_count(&self) -> Result<usize, InstallServiceError> {
        self.revocations
            .read()
            .map(|entries| entries.len())
            .map_err(|_| InstallServiceError::Poisoned)
    }

    /// Prepare entirely outside the installed table, then perform one atomic
    /// publication. The revocation map lock is acquired before the table commit,
    /// so a poisoned host-control plane cannot leave a published but unmanaged
    /// language.
    pub fn install(
        &self,
        candidate: InstallCandidate,
    ) -> Result<InstalledLanguageReceipt, InstallServiceError> {
        self.install_with_host(candidate, &DefaultRuntimeHost)
    }

    pub fn install_with_host(
        &self,
        candidate: InstallCandidate,
        host: &dyn RuntimeHost,
    ) -> Result<InstalledLanguageReceipt, InstallServiceError> {
        let candidates = self.canonical_records(candidate)?;
        if candidates.records.len() != 1 {
            return Err(InstallServiceError::MultipleExports { count: candidates.records.len() });
        }
        let mut batch = self.install_candidate_set(candidates, host)?;
        Ok(batch
            .exports
            .pop()
            .ok_or(InstallServiceError::EmptyExportSet)?
            .receipt)
    }

    /// Prepare, compile, admit, and atomically publish every language exported
    /// by a module. Single-language candidates use the same path.
    pub fn install_all(
        &self,
        candidate: InstallCandidate,
    ) -> Result<InstalledLanguageBatchReceipt, InstallServiceError> {
        self.install_all_with_host(candidate, &DefaultRuntimeHost)
    }

    pub fn install_all_with_host(
        &self,
        candidate: InstallCandidate,
        host: &dyn RuntimeHost,
    ) -> Result<InstalledLanguageBatchReceipt, InstallServiceError> {
        let candidates = self.canonical_records(candidate)?;
        self.install_candidate_set(candidates, host)
    }

    fn install_candidate_set(
        &self,
        candidates: CanonicalCandidateSet,
        host: &dyn RuntimeHost,
    ) -> Result<InstalledLanguageBatchReceipt, InstallServiceError> {
        let CanonicalCandidateSet { module_name, records, programs } = candidates;
        let reader = RegistryLanguageReader(self.registry.as_ref());
        let mut pending = Vec::with_capacity(records.len());
        let mut requests = Vec::with_capacity(records.len());
        for (expected_name, record) in records {
            let prepared = record
                .prepare_executable_install_with_registry_and_artifact_limits(
                    RUNTIME_COMPILER_ABI,
                    RUNTIME_UNICODE_ABI,
                    self.policy.parser_image,
                    self.policy.semantic_image,
                    &reader,
                )
                .map_err(|error| {
                    InstallServiceError::Canonical(InstallExecutableRegistryError::Prepare(error))
                })?;
            let name = expected_name.unwrap_or_else(|| prepared.language.grammar.name.clone());
            if prepared.language.grammar.name != name {
                return Err(InstallServiceError::ExportNameMismatch {
                    export: name,
                    language: prepared.language.grammar.name,
                });
            }
            if !prepared.language.theory.checker_requirements.is_empty() {
                return Err(InstallServiceError::CheckerRequirementsUnavailable {
                    count: prepared.language.theory.checker_requirements.len(),
                });
            }
            let requested_rights = prepared.requested_rights.clone();
            if let Some(action) = prepared
                .language
                .theory
                .actions
                .iter()
                .find(|action| !action.required_rights.is_subset_of(&requested_rights))
            {
                return Err(InstallServiceError::TheoryRightsNotRequested {
                    action: action.id.clone(),
                });
            }
            let installed = prepared
                .install(
                    RUNTIME_COMPILER_ABI,
                    RUNTIME_UNICODE_ABI,
                    compile_parser_image,
                    compile_theory_semantic_image,
                )
                .map_err(|error| {
                    InstallServiceError::Canonical(match error {
                        FinishExecutableRegistryInstallError::CompileParser(error) => {
                            InstallExecutableRegistryError::CompileParser(error)
                        },
                        FinishExecutableRegistryInstallError::CompileSemantic(error) => {
                            InstallExecutableRegistryError::CompileSemantic(error)
                        },
                        FinishExecutableRegistryInstallError::InvalidParserImage(error) => {
                            InstallExecutableRegistryError::InvalidParserImage(error)
                        },
                        FinishExecutableRegistryInstallError::InvalidSemanticImage(error) => {
                            InstallExecutableRegistryError::InvalidSemanticImage(error)
                        },
                    })
                })?;
            let granted_rights = self.policy.host_grants.attenuate(&requested_rights);
            let fingerprint = installed
                .language
                .fingerprint()
                .map_err(|error| InstallServiceError::Fingerprint(error.to_string()))?;
            pending.push((
                name,
                fingerprint,
                requested_rights,
                granted_rights.clone(),
                installed.parser_cache_disposition,
                installed.semantic_cache_disposition,
            ));
            requests.push(ExecutableLanguageInstall {
                language: installed.language,
                parser_image: installed.parser_image,
                semantic_image: installed.semantic_image,
                granted_rights,
            });
        }
        if requests.is_empty() {
            return Err(InstallServiceError::EmptyExportSet);
        }

        let mut revocations = self
            .revocations
            .write()
            .map_err(|_| InstallServiceError::Poisoned)?;
        let new_fingerprints = pending
            .iter()
            .map(|(_, fingerprint, ..)| *fingerprint)
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .filter(|fingerprint| !revocations.contains_key(fingerprint))
            .count();
        let resulting_count = revocations
            .len()
            .checked_add(new_fingerprints)
            .and_then(|count| u64::try_from(count).ok())
            .ok_or(InstallServiceError::InstalledLanguageLimit {
                limit: self.policy.max_installed_languages,
            })?;
        if resulting_count > self.policy.max_installed_languages {
            return Err(InstallServiceError::InstalledLanguageLimit {
                limit: self.policy.max_installed_languages,
            });
        }
        let grants = self
            .table
            .install_executable_runtime_batch_with_artifact_limits_and_host(
                requests,
                RUNTIME_COMPILER_ABI,
                RUNTIME_UNICODE_ABI,
                &self.policy.capability_abi,
                self.policy.fingerprint,
                self.policy.parser_image,
                self.policy.semantic_image,
                host,
            )
            .map_err(InstallServiceError::Commit)?;
        let exports = pending
            .into_iter()
            .zip(grants)
            .map(
                |(
                    (
                        name,
                        fingerprint,
                        requested_rights,
                        granted_rights,
                        cache_disposition,
                        semantic_cache_disposition,
                    ),
                    grant,
                )| {
                    revocations.insert(fingerprint, grant.revocation);
                    InstalledLanguageExportReceipt {
                        name,
                        receipt: InstalledLanguageReceipt {
                            handle: grant.handle,
                            fingerprint,
                            requested_rights,
                            granted_rights,
                            cache_disposition,
                            semantic_cache_disposition,
                        },
                    }
                },
            )
            .collect();
        Ok(InstalledLanguageBatchReceipt { module_name, exports, programs })
    }

    pub fn parse(
        &self,
        handle: &InstalledLanguageHandle,
        source: &str,
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
    ) -> Result<Vec<WeightedParse>, InstalledParseError> {
        self.table
            .parse(handle, source, category, host, self.policy.runtime)
    }

    pub fn parse_template(
        &self,
        handle: &InstalledLanguageHandle,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        operation: LanguageRight,
        host: &dyn RuntimeHost,
    ) -> Result<Vec<WeightedParse>, InstalledParseError> {
        self.table.parse_template(
            handle,
            pieces,
            holes,
            category,
            host,
            self.policy.runtime,
            operation,
        )
    }

    pub fn revoke(&self, fingerprint: [u8; 32]) -> Result<(), InstallServiceError> {
        let authority = self
            .revocations
            .write()
            .map_err(|_| InstallServiceError::Poisoned)?
            .remove(&fingerprint)
            .ok_or(InstallServiceError::UnknownRevocation(fingerprint))?;
        self.table
            .revoke(authority)
            .map_err(InstallServiceError::Revoke)
    }

    fn canonical_records(
        &self,
        candidate: InstallCandidate,
    ) -> Result<CanonicalCandidateSet, InstallServiceError> {
        let (candidate, staged_programs) = match candidate {
            InstallCandidate::DdlWithPrograms { declaration, programs } => {
                (InstallCandidate::Ddl(declaration), programs)
            },
            candidate => (candidate, Vec::new()),
        };
        match candidate {
            InstallCandidate::Canonical(value)
                if canonical_value_schema(&value) == Some(CANONICAL_MODULE_SCHEMA_V1) =>
            {
                let module = CanonicalModuleValue::from_rho_value(&value)
                    .map_err(InstallServiceError::CanonicalModule)?;
                Ok(CanonicalCandidateSet {
                    module_name: Some(module.name),
                    records: module
                        .exports
                        .into_iter()
                        .map(|export| (Some(export.name), RegistryLanguageRecord::new(export.spec)))
                        .collect(),
                    programs: Vec::new(),
                })
            },
            InstallCandidate::Canonical(value) => Ok(CanonicalCandidateSet {
                module_name: None,
                records: vec![(None, RegistryLanguageRecord::new(value))],
                programs: Vec::new(),
            }),
            InstallCandidate::RegistryLanguage(name) => Ok(CanonicalCandidateSet {
                module_name: None,
                records: vec![(
                    None,
                    self.registry
                        .lookup_language(&name)
                        .map_err(InstallServiceError::Registry)?
                        .ok_or(InstallServiceError::RegistryLanguageNotFound(name))?,
                )],
                programs: Vec::new(),
            }),
            InstallCandidate::RegistryModule(uri) => {
                let record = self
                    .registry
                    .lookup_module(&uri)
                    .map_err(InstallServiceError::Registry)?
                    .ok_or_else(|| InstallServiceError::RegistryModuleNotFound(uri.clone()))?;
                let entry = ModuleRef::parse(&uri).map_err(|error| {
                    InstallServiceError::RegistryModuleReference(error.to_string())
                })?;
                let signed_payload = record
                    .signed_payload()
                    .map_err(InstallServiceError::RegistryModule)?;
                self.registry
                    .verify_module_trust(&uri, &signed_payload, &record.signatures)
                    .map_err(InstallServiceError::RegistryTrust)?;
                let canonical = CanonicalModuleValue::from_rho_value(&record.module)
                    .map_err(InstallServiceError::CanonicalModule)?;
                let pinned = PinnedRegistryReader {
                    registry: self.registry.as_ref(),
                    entry_uri: &uri,
                    entry: &record,
                    entry_signed_payload: &signed_payload,
                };
                let resolver = RegistryResolver::new(pinned);
                mettail_elab::resolve::Program::load(&entry, &resolver)
                    .map_err(InstallServiceError::Surface)?;
                let records = record
                    .export_records()
                    .map_err(InstallServiceError::RegistryModule)?;
                Ok(CanonicalCandidateSet {
                    module_name: Some(canonical.name),
                    records: records
                        .into_iter()
                        .map(|(name, record)| (Some(name), record))
                        .collect(),
                    programs: Vec::new(),
                })
            },
            InstallCandidate::Ddl(ParsedDdl::Theory(theory)) => {
                if !staged_programs.is_empty() {
                    return Err(InstallServiceError::StagedProgramShape(
                        "a standalone Theory cannot carry module programs".into(),
                    ));
                }
                let name = theory.name.clone();
                let elaborated = mettail_elab::elaborate_theory_ast(theory)
                    .map_err(InstallServiceError::Surface)?;
                Ok(CanonicalCandidateSet {
                    module_name: None,
                    records: vec![(
                        Some(name),
                        RegistryLanguageRecord::new(elaborated.canonical_value),
                    )],
                    programs: Vec::new(),
                })
            },
            InstallCandidate::Ddl(ParsedDdl::Module(module)) => {
                validate_staged_programs(&module, &staged_programs)?;
                let resolver =
                    RegistryResolver::new(RegistryLanguageReader(self.registry.as_ref()));
                let module = mettail_elab::elaborate_module_ast(module, &resolver)
                    .map_err(InstallServiceError::Surface)?;
                Ok(CanonicalCandidateSet {
                    module_name: Some(module.name),
                    records: module
                        .exports
                        .into_iter()
                        .map(|export| {
                            (
                                Some(export.name),
                                RegistryLanguageRecord::new(export.language.canonical_value),
                            )
                        })
                        .collect(),
                    programs: staged_programs,
                })
            },
            InstallCandidate::DdlWithPrograms { .. } => {
                unreachable!("staged DDL candidate normalized before elaboration")
            },
        }
    }
}

fn validate_staged_programs(
    module: &mettail_elab::ast::ModuleFile,
    programs: &[StagedModuleProgram],
) -> Result<(), InstallServiceError> {
    let references = module.items.iter().filter_map(|item| match item {
        mettail_elab::ast::ModuleItem::Program(reference) => Some(*reference),
        mettail_elab::ast::ModuleItem::TheoryDecl(_)
        | mettail_elab::ast::ModuleItem::TheoryEntry(_) => None,
    });
    let mut count = 0usize;
    for (slot, reference) in references.enumerate() {
        let Some(program) = programs.get(slot) else {
            return Err(InstallServiceError::StagedProgramShape(format!(
                "module program slot {slot} has no structural process leaf"
            )));
        };
        if reference.slot != slot || reference.source_ordinal != program.source_ordinal {
            return Err(InstallServiceError::StagedProgramShape(format!(
                "module program reference ({}, {}) does not match staged slot ({slot}, {})",
                reference.slot, reference.source_ordinal, program.source_ordinal
            )));
        }
        count = slot + 1;
    }
    if count != programs.len() {
        return Err(InstallServiceError::StagedProgramShape(format!(
            "module has {count} program references but {} structural process leaves",
            programs.len()
        )));
    }
    Ok(())
}

fn canonical_value_schema(value: &RhoValue) -> Option<&str> {
    let RhoValue::Map(record) = value else {
        return None;
    };
    let Some(RhoValue::String(schema)) = record.get("mettail") else {
        return None;
    };
    Some(schema)
}

struct RegistryLanguageReader<'a>(&'a dyn RegistrySnapshot);

/// A one-transaction view that reuses the already fetched root record while
/// delegating every dependency to the same immutable snapshot. This prevents
/// a mutable or equivocating adapter from swapping the entry between trust
/// verification, graph validation, and export installation.
struct PinnedRegistryReader<'a> {
    registry: &'a dyn RegistrySnapshot,
    entry_uri: &'a str,
    entry: &'a RegistryModuleValue,
    entry_signed_payload: &'a [u8],
}

impl VersionedLanguageRegistryReader for RegistryLanguageReader<'_> {
    fn lookup_language(&self, name: &str) -> Result<Option<RegistryLanguageRecord>, String> {
        self.0.lookup_language(name)
    }
}

impl VersionedRegistryReader for RegistryLanguageReader<'_> {
    fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String> {
        self.0.lookup_module(uri)
    }

    fn verify_module_trust(
        &self,
        uri: &str,
        signed_payload: &[u8],
        signatures: &RhoValue,
    ) -> Result<(), String> {
        self.0.verify_module_trust(uri, signed_payload, signatures)
    }
}

impl VersionedRegistryReader for PinnedRegistryReader<'_> {
    fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String> {
        if uri == self.entry_uri {
            Ok(Some(self.entry.clone()))
        } else {
            self.registry.lookup_module(uri)
        }
    }

    fn verify_module_trust(
        &self,
        uri: &str,
        signed_payload: &[u8],
        signatures: &RhoValue,
    ) -> Result<(), String> {
        if uri == self.entry_uri {
            if signed_payload == self.entry_signed_payload && signatures == &self.entry.signatures {
                Ok(())
            } else {
                Err("pinned Registry entry changed during graph validation".into())
            }
        } else {
            self.registry
                .verify_module_trust(uri, signed_payload, signatures)
        }
    }
}

#[derive(Debug)]
pub enum InstallServiceError {
    Surface(mettail_elab::Diag),
    StagedProgramShape(String),
    ExportNameMismatch {
        export: String,
        language: String,
    },
    EmptyExportSet,
    MultipleExports {
        count: usize,
    },
    Registry(String),
    RegistryLanguageNotFound(String),
    RegistryModuleNotFound(String),
    RegistryModuleReference(String),
    RegistryModule(mettail_elab::registry::RegistryModuleError),
    RegistryTrust(String),
    CanonicalModule(mettail_elab::canonical::ValueDecodeError),
    Canonical(
        InstallExecutableRegistryError<
            ValueToCoreError,
            RuntimeCompileError,
            TheoryImageCompileError,
        >,
    ),
    CheckerRequirementsUnavailable {
        count: usize,
    },
    TheoryRightsNotRequested {
        action: String,
    },
    Fingerprint(String),
    Commit(InstallLanguageError),
    Revoke(mettail_grammar_core::LanguageAccessError),
    UnknownRevocation([u8; 32]),
    InstalledLanguageLimit {
        limit: u64,
    },
    Poisoned,
}

impl fmt::Display for InstallServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Surface(error) => write!(formatter, "surface DDL rejected: {error}"),
            Self::StagedProgramShape(error) => {
                write!(formatter, "staged module program rejected: {error}")
            },
            Self::ExportNameMismatch { export, language } => write!(
                formatter,
                "module export name `{export}` differs from canonical language name `{language}`"
            ),
            Self::EmptyExportSet => {
                formatter.write_str("module has no installable language exports")
            },
            Self::MultipleExports { count } => write!(
                formatter,
                "module exports {count} languages; use the atomic multi-export installation result"
            ),
            Self::Registry(error) => write!(formatter, "Registry snapshot failed: {error}"),
            Self::RegistryLanguageNotFound(name) => {
                write!(formatter, "Registry language `{name}` was not found")
            },
            Self::RegistryModuleNotFound(uri) => {
                write!(formatter, "Registry module `{uri}` was not found")
            },
            Self::RegistryModuleReference(error) => {
                write!(formatter, "invalid Registry module reference: {error}")
            },
            Self::RegistryModule(error) => write!(formatter, "Registry module rejected: {error}"),
            Self::RegistryTrust(error) => {
                write!(formatter, "Registry module trust verification failed: {error}")
            },
            Self::CanonicalModule(error) => write!(formatter, "canonical module rejected: {error}"),
            Self::Canonical(error) => write!(formatter, "canonical language rejected: {error:?}"),
            Self::CheckerRequirementsUnavailable { count } => write!(
                formatter,
                "language requests {count} theorem checker bindings, but no checker resolver was supplied"
            ),
            Self::TheoryRightsNotRequested { action } => write!(
                formatter,
                "theory action `{action}` requires a language right absent from the installation request"
            ),
            Self::Fingerprint(error) => write!(formatter, "language identity failed: {error}"),
            Self::Commit(error) => write!(formatter, "atomic installation failed: {error:?}"),
            Self::Revoke(error) => write!(formatter, "revocation failed: {error:?}"),
            Self::UnknownRevocation(fingerprint) => {
                write!(formatter, "no revocation authority for {:02x?}", fingerprint)
            },
            Self::InstalledLanguageLimit { limit } => {
                write!(formatter, "installed-language limit reached ({limit})")
            },
            Self::Poisoned => formatter.write_str("installed-language control lock was poisoned"),
        }
    }
}

impl std::error::Error for InstallServiceError {}

/// Resource bounds for converting normalized Rholang values into the closed
/// `language/2` subset. The traversal is iterative; depth affects the explicit
/// work stack, never the native call stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanonicalValueLimits {
    pub max_nodes: usize,
    pub max_encoded_bytes: usize,
    pub max_depth: usize,
    pub max_collection_items: usize,
    pub max_string_bytes: usize,
    pub max_total_string_bytes: usize,
    pub max_byte_array_bytes: usize,
    pub max_total_byte_array_bytes: usize,
}

impl Default for CanonicalValueLimits {
    fn default() -> Self {
        Self {
            max_nodes: mettail_elab::canonical::MAX_CANONICAL_VALUE_NODES,
            max_encoded_bytes: MAX_INSTALL_CANDIDATE_ENCODED_BYTES,
            max_depth: mettail_elab::parse::MAX_DDL_STRUCTURAL_DEPTH - 1,
            max_collection_items: mettail_elab::canonical::MAX_CANONICAL_COLLECTION_ITEMS,
            max_string_bytes: mettail_elab::canonical::MAX_CANONICAL_STRING_BYTES,
            max_total_string_bytes: mettail_elab::canonical::MAX_CANONICAL_TOTAL_STRING_BYTES,
            max_byte_array_bytes: mettail_elab::canonical::MAX_CANONICAL_BYTE_ARRAY_BYTES,
            max_total_byte_array_bytes:
                mettail_elab::canonical::MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalValueError {
    Shape { path: String, message: String },
    Limit { resource: &'static str, limit: usize },
}

impl fmt::Display for CanonicalValueError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape { path, message } => write!(formatter, "{path}: {message}"),
            Self::Limit { resource, limit } => {
                write!(formatter, "canonical value {resource} limit exceeded ({limit})")
            },
        }
    }
}

impl std::error::Error for CanonicalValueError {}

enum DecodeTask<'a> {
    Visit { par: &'a Par, path: String, depth: usize },
    FinishList(usize),
    FinishMap(usize),
}

/// Decode only literal, closed Rholang values admitted by the `language/2`
/// schema. Computed expressions, free variables, remainders, connectives,
/// process forms, unforgeables, and duplicate map keys fail closed.
pub fn par_to_canonical_value(
    root: &Par,
    limits: CanonicalValueLimits,
) -> Result<RhoValue, CanonicalValueError> {
    let mut tasks = vec![DecodeTask::Visit { par: root, path: "$".into(), depth: 0 }];
    let mut values = Vec::new();
    let mut nodes = 0usize;
    let mut collection_items = 0usize;
    let mut total_string_bytes = 0usize;
    let mut total_byte_array_bytes = 0usize;

    while let Some(task) = tasks.pop() {
        match task {
            DecodeTask::Visit { par, path, depth } => {
                nodes = nodes.checked_add(1).ok_or(CanonicalValueError::Limit {
                    resource: "node",
                    limit: limits.max_nodes,
                })?;
                if nodes > limits.max_nodes {
                    return Err(CanonicalValueError::Limit {
                        resource: "node",
                        limit: limits.max_nodes,
                    });
                }
                if depth > limits.max_depth {
                    return Err(CanonicalValueError::Limit {
                        resource: "depth",
                        limit: limits.max_depth,
                    });
                }
                require_closed_value_par(par, &path)?;
                if par.exprs.is_empty() {
                    values.push(RhoValue::Nil);
                    continue;
                }
                let [expr] = par.exprs.as_slice() else {
                    return shape(path, "expected exactly one literal expression");
                };
                let Some(instance) = expr.expr_instance.as_ref() else {
                    return shape(path, "literal expression has no value");
                };
                match instance {
                    ExprInstance::GString(value) => {
                        account_string(value, &mut total_string_bytes, limits, &path)?;
                        values.push(RhoValue::String(value.clone()));
                    },
                    ExprInstance::GByteArray(value) => {
                        account_byte_array(value, &mut total_byte_array_bytes, limits)?;
                        values.push(RhoValue::Bytes(value.clone()));
                    },
                    ExprInstance::GInt(value) => values.push(RhoValue::Integer((*value).into())),
                    ExprInstance::GBigInt(bytes) => {
                        let value =
                            signed_i128(bytes).ok_or_else(|| CanonicalValueError::Shape {
                                path,
                                message: "integer is outside the canonical signed-128 range".into(),
                            })?;
                        values.push(RhoValue::Integer(value));
                    },
                    ExprInstance::GDouble(bits) => values.push(RhoValue::FloatBits(*bits)),
                    ExprInstance::GBool(value) => values.push(RhoValue::Boolean(*value)),
                    ExprInstance::EListBody(list)
                        if list.remainder.is_none()
                            && !list.connective_used
                            && list.locally_free.is_empty() =>
                    {
                        account_collection(list.ps.len(), &mut collection_items, limits)?;
                        tasks.push(DecodeTask::FinishList(list.ps.len()));
                        for (index, child) in list.ps.iter().enumerate().rev() {
                            tasks.push(DecodeTask::Visit {
                                par: child,
                                path: format!("{path}[{index}]"),
                                depth: depth + 1,
                            });
                        }
                    },
                    ExprInstance::EMapBody(map)
                        if map.remainder.is_none()
                            && !map.connective_used
                            && map.locally_free.is_empty() =>
                    {
                        account_collection(map.kvs.len(), &mut collection_items, limits)?;
                        if !map
                            .kvs
                            .iter()
                            .all(|pair| pair.key.is_some() && pair.value.is_some())
                        {
                            return shape(path, "map entry is missing a key or value");
                        }
                        tasks.push(DecodeTask::FinishMap(map.kvs.len()));
                        for (index, pair) in map.kvs.iter().enumerate().rev() {
                            let key = pair.key.as_ref().expect("validated map key");
                            let value = pair.value.as_ref().expect("validated map value");
                            tasks.push(DecodeTask::Visit {
                                par: value,
                                path: format!("{path}.value[{index}]"),
                                depth: depth + 1,
                            });
                            tasks.push(DecodeTask::Visit {
                                par: key,
                                path: format!("{path}.key[{index}]"),
                                depth: depth + 1,
                            });
                        }
                    },
                    _ => return shape(path, "value is not in the closed language/2 subset"),
                }
            },
            DecodeTask::FinishList(count) => {
                let start = values
                    .len()
                    .checked_sub(count)
                    .expect("decoder scheduled one value per list child");
                let children = values.split_off(start);
                values.push(RhoValue::List(children));
            },
            DecodeTask::FinishMap(count) => {
                let width = count
                    .checked_mul(2)
                    .expect("collection limit bounds the child width");
                let start = values
                    .len()
                    .checked_sub(width)
                    .expect("decoder scheduled two values per map entry");
                let children = values.split_off(start);
                let mut map = BTreeMap::new();
                let mut children = children.into_iter();
                for index in 0..count {
                    let mut key = children.next().expect("validated key position");
                    let value = children.next().expect("validated value position");
                    let RhoValue::String(key_value) = &mut key else {
                        return shape(format!("$.key[{index}]"), "map key must be a string");
                    };
                    let key = std::mem::take(key_value);
                    if map.insert(key.clone(), value).is_some() {
                        return shape(format!("$.key[{index}]"), format!("duplicate key `{key}`"));
                    }
                }
                values.push(RhoValue::Map(map));
            },
        }
    }

    let [value] = values.as_slice() else {
        unreachable!("one root schedules one result")
    };
    Ok(value.clone())
}

fn require_closed_value_par(par: &Par, path: &str) -> Result<(), CanonicalValueError> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
        || !par.unforgeables.is_empty()
        || !par.locally_free.is_empty()
        || par.connective_used
    {
        return shape(path, "expected a closed literal value, not a process or capability");
    }
    Ok(())
}

fn account_collection(
    count: usize,
    total: &mut usize,
    limits: CanonicalValueLimits,
) -> Result<(), CanonicalValueError> {
    *total = total.checked_add(count).ok_or(CanonicalValueError::Limit {
        resource: "collection-item",
        limit: limits.max_collection_items,
    })?;
    if *total > limits.max_collection_items {
        return Err(CanonicalValueError::Limit {
            resource: "collection-item",
            limit: limits.max_collection_items,
        });
    }
    Ok(())
}

fn account_byte_array(
    value: &[u8],
    total: &mut usize,
    limits: CanonicalValueLimits,
) -> Result<(), CanonicalValueError> {
    if value.len() > limits.max_byte_array_bytes {
        return Err(CanonicalValueError::Limit {
            resource: "byte-array byte",
            limit: limits.max_byte_array_bytes,
        });
    }
    *total = total
        .checked_add(value.len())
        .ok_or(CanonicalValueError::Limit {
            resource: "total byte-array byte",
            limit: limits.max_total_byte_array_bytes,
        })?;
    if *total > limits.max_total_byte_array_bytes {
        return Err(CanonicalValueError::Limit {
            resource: "total byte-array byte",
            limit: limits.max_total_byte_array_bytes,
        });
    }
    Ok(())
}

fn account_string(
    value: &str,
    total: &mut usize,
    limits: CanonicalValueLimits,
    path: &str,
) -> Result<(), CanonicalValueError> {
    if value.len() > limits.max_string_bytes {
        return Err(CanonicalValueError::Shape {
            path: path.into(),
            message: format!(
                "string has {} bytes; maximum is {}",
                value.len(),
                limits.max_string_bytes
            ),
        });
    }
    *total = total
        .checked_add(value.len())
        .ok_or(CanonicalValueError::Limit {
            resource: "total-string-byte",
            limit: limits.max_total_string_bytes,
        })?;
    if *total > limits.max_total_string_bytes {
        return Err(CanonicalValueError::Limit {
            resource: "total-string-byte",
            limit: limits.max_total_string_bytes,
        });
    }
    Ok(())
}

fn signed_i128(bytes: &[u8]) -> Option<i128> {
    if bytes.is_empty() {
        return None;
    }
    let negative = bytes[0] & 0x80 != 0;
    let mut first = 0usize;
    while bytes.len() - first > 1 {
        let redundant_zero = bytes[first] == 0 && bytes[first + 1] & 0x80 == 0;
        let redundant_ones = bytes[first] == 0xff && bytes[first + 1] & 0x80 != 0;
        if !(redundant_zero || redundant_ones) {
            break;
        }
        first += 1;
    }
    let bytes = &bytes[first..];
    if bytes.len() > 16 {
        return None;
    }
    let mut encoded = [if negative { 0xff } else { 0 }; 16];
    encoded[16 - bytes.len()..].copy_from_slice(bytes);
    Some(i128::from_be_bytes(encoded))
}

fn shape<T>(path: impl Into<String>, message: impl Into<String>) -> Result<T, CanonicalValueError> {
    Err(CanonicalValueError::Shape {
        path: path.into(),
        message: message.into(),
    })
}

/// Decode the exact structural envelope emitted by nouveau Rholang lowering.
/// The value has already passed the bounded `Par -> RhoValue` admission walk;
/// this step reconstructs the neutral DDL AST and performs no text parsing.
pub fn decode_ddl_envelope(value: RhoValue) -> Result<InstallCandidate, CanonicalValueError> {
    decode_ddl_value(value)
        .map(InstallCandidate::Ddl)
        .map_err(|error| CanonicalValueError::Shape { path: error.path, message: error.message })
}

#[derive(Clone)]
struct CapabilityEntry {
    fingerprint: [u8; 32],
    handle: InstalledLanguageHandle,
}

#[derive(Clone)]
struct PreparedPatternEntry {
    fingerprint: [u8; 32],
    pattern_id: [u8; 32],
    handle: InstalledLanguageHandle,
    pattern: BindPattern,
    root_category: CategoryId,
    capture_plan: PreparedCapturePlan,
    capture_categories: Vec<CategoryId>,
    admission: Arc<DynamicSyntaxAdmission>,
}

/// Matcher-owned projection from raw hole occurrences to the public capture
/// telescope. The reflected pattern binds every occurrence independently so
/// repeated holes can be checked before any capture is published. Public
/// captures are then projected from first occurrences in declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PreparedCapturePlan {
    occurrence_count: usize,
    projection: Vec<usize>,
    repetitions: Vec<(usize, usize)>,
}

impl PreparedCapturePlan {
    fn compile(
        holes: &[NamedRuntimeTemplateHole],
        hole_bindings: &[(String, i32)],
        linearity_guards: &[(i32, i32)],
        free_count: i32,
    ) -> Option<Self> {
        let occurrence_count = usize::try_from(free_count).ok()?;
        if occurrence_count != hole_bindings.len() {
            return None;
        }

        let mut first_occurrence = BTreeMap::<&str, usize>::new();
        let mut projection = Vec::new();
        let mut repetitions = Vec::new();
        let mut first_names = Vec::new();
        for (expected_level, (name, level)) in hole_bindings.iter().enumerate() {
            if usize::try_from(*level).ok() != Some(expected_level) {
                return None;
            }
            match first_occurrence.get(name.as_str()).copied() {
                Some(first) => repetitions.push((first, expected_level)),
                None => {
                    first_occurrence.insert(name, expected_level);
                    first_names.push(name.as_str());
                    projection.push(expected_level);
                },
            }
        }
        if first_names
            .into_iter()
            .ne(holes.iter().map(|hole| hole.name.as_str()))
        {
            return None;
        }
        let reflected_repetitions = linearity_guards
            .iter()
            .map(|(first, repeated)| {
                Some((usize::try_from(*first).ok()?, usize::try_from(*repeated).ok()?))
            })
            .collect::<Option<Vec<_>>>()?;
        if reflected_repetitions != repetitions {
            return None;
        }
        Some(Self {
            occurrence_count,
            projection,
            repetitions,
        })
    }

    fn project(&self, matched: ListParWithRandom) -> Option<ListParWithRandom> {
        if matched.pars.len() != self.occurrence_count {
            return None;
        }
        for &(first, repeated) in &self.repetitions {
            if matched.pars.get(first)? != matched.pars.get(repeated)? {
                return None;
            }
        }
        let pars = self
            .projection
            .iter()
            .map(|&occurrence| matched.pars.get(occurrence).cloned())
            .collect::<Option<Vec<_>>>()?;
        Some(ListParWithRandom { pars, random_state: matched.random_state })
    }
}

#[derive(Clone)]
pub(crate) struct ResolvedPreparedPattern {
    pattern: BindPattern,
    pattern_id: [u8; 32],
    root_category: CategoryId,
    capture_plan: PreparedCapturePlan,
    capture_categories: Vec<CategoryId>,
    fingerprint: String,
    fingerprint_bytes: [u8; 32],
    admission: Arc<DynamicSyntaxAdmission>,
}

impl ResolvedPreparedPattern {
    pub(crate) fn pattern(&self) -> &BindPattern {
        &self.pattern
    }

    pub(crate) fn root_category(&self) -> CategoryId {
        self.root_category
    }

    pub(crate) fn capture_count(&self) -> usize {
        self.capture_categories.len()
    }

    pub(crate) fn pattern_id(&self) -> [u8; 32] {
        self.pattern_id
    }

    pub(crate) fn capture_categories(&self) -> &[CategoryId] {
        &self.capture_categories
    }

    pub(crate) fn fingerprint_bytes(&self) -> [u8; 32] {
        self.fingerprint_bytes
    }

    pub(crate) fn admitted_term_hash(&self, value: &Par, category: CategoryId) -> Option<[u8; 32]> {
        self.admission
            .admitted_term_hash(value, &self.fingerprint, category)
    }

    pub(crate) fn admits_subject(&self, data: &ListParWithRandom) -> bool {
        let [subject] = data.pars.as_slice() else {
            return false;
        };
        self.admission
            .admits_category(subject, &self.fingerprint, self.root_category)
    }

    pub(crate) fn project_admitted_captures(
        &self,
        occurrences: ListParWithRandom,
    ) -> Option<ListParWithRandom> {
        let captures = self.capture_plan.project(occurrences)?;
        self.admission
            .admits_captures(&captures.pars, &self.fingerprint, &self.capture_categories)
            .then_some(captures)
    }
}

#[derive(Default)]
struct CapabilityState {
    generations: BTreeMap<[u8; 32], u64>,
    entries: BTreeMap<Vec<u8>, CapabilityEntry>,
    patterns: BTreeMap<Vec<u8>, PreparedPatternEntry>,
    admissions: BTreeMap<[u8; 32], Arc<DynamicSyntaxAdmission>>,
}

/// Process-local authority directory behind Rholang-visible `GPrivate` values.
///
/// A private-name byte string is only an index: every operation resolves it to
/// the sealed [`InstalledLanguageHandle`] and calls the installed table's
/// authorization check again. Fingerprints, Registry names, and aliases never
/// become authority. Repeated identical installation in one live generation
/// returns the same token; revocation removes every token for that fingerprint
/// and advances the generation, so reinstall cannot revive a stale token.
pub struct RholangLanguageRuntime {
    service: Arc<LanguageInstallService>,
    host: Arc<dyn RuntimeHost>,
    capabilities: RwLock<CapabilityState>,
}

#[derive(Debug)]
pub struct RholangInstalledExport {
    pub name: String,
    pub handle: Par,
}

#[derive(Debug)]
pub struct RholangInstalledBatch {
    pub module_name: Option<String>,
    pub exports: Vec<RholangInstalledExport>,
    pub programs: Vec<StagedModuleProgram>,
}

/// The four observable results of bounded recognition. A parse-only operation
/// intentionally returns no reflected syntax: syntax reflection and FLT
/// construction are independently authorized operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LanguageParseOutcome {
    Accepted,
    Rejected(LanguageParseRejection),
    Ambiguous { alternatives: u32 },
    Exhausted(LanguageParseExhaustion),
}

/// Stable, deterministic reasons that guest text is not in the requested
/// category. Byte positions are UTF-8 byte offsets into the exact guest input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LanguageParseRejection {
    NoParse,
    Lex { byte: u32 },
    LexerModeUnderflow { byte: u32 },
    LexerModeUnclosed { byte: u32, depth: u32 },
    InvalidTokenValue,
    ForeignLanguage { byte: u32 },
}

/// Stable resource boundaries that distinguish fail-closed exhaustion from a
/// negative recognition result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LanguageParseExhaustion {
    InputBytes,
    LexerStates,
    LexerEdges,
    LexerWork,
    LexerModeDepth { byte: u32 },
    ForeignNesting { byte: u32 },
    ParseItems,
    ForestNodes,
    ForestCycle,
    SemanticResults,
    CapabilityCost,
}

impl LanguageParseRejection {
    fn code(&self) -> &'static str {
        match self {
            Self::NoParse => "NoParse",
            Self::Lex { .. } => "Lex",
            Self::LexerModeUnderflow { .. } => "LexerModeUnderflow",
            Self::LexerModeUnclosed { .. } => "LexerModeUnclosed",
            Self::InvalidTokenValue => "InvalidTokenValue",
            Self::ForeignLanguage { .. } => "ForeignLanguage",
        }
    }

    fn byte(&self) -> Option<u32> {
        match self {
            Self::Lex { byte }
            | Self::LexerModeUnderflow { byte }
            | Self::LexerModeUnclosed { byte, .. }
            | Self::ForeignLanguage { byte } => Some(*byte),
            Self::NoParse | Self::InvalidTokenValue => None,
        }
    }

    fn depth(&self) -> Option<u32> {
        match self {
            Self::LexerModeUnclosed { depth, .. } => Some(*depth),
            _ => None,
        }
    }
}

impl LanguageParseExhaustion {
    fn code(&self) -> &'static str {
        match self {
            Self::InputBytes => "InputBytes",
            Self::LexerStates => "LexerStates",
            Self::LexerEdges => "LexerEdges",
            Self::LexerWork => "LexerWork",
            Self::LexerModeDepth { .. } => "LexerModeDepth",
            Self::ForeignNesting { .. } => "ForeignNesting",
            Self::ParseItems => "ParseItems",
            Self::ForestNodes => "ForestNodes",
            Self::ForestCycle => "ForestCycle",
            Self::SemanticResults => "SemanticResults",
            Self::CapabilityCost => "CapabilityCost",
        }
    }

    fn byte(&self) -> Option<u32> {
        match self {
            Self::LexerModeDepth { byte } | Self::ForeignNesting { byte } => Some(*byte),
            _ => None,
        }
    }
}

impl RholangLanguageRuntime {
    pub fn new(service: Arc<LanguageInstallService>) -> Self {
        Self::with_host(service, Arc::new(DefaultRuntimeHost))
    }

    /// Construct a runtime with explicitly injected parser capabilities. This
    /// is the only route by which token decoders, foreign parsers, or future
    /// scoped I/O-backed module resolvers enter run-time parsing; there is no
    /// ambient host or filesystem lookup.
    pub fn with_host(service: Arc<LanguageInstallService>, host: Arc<dyn RuntimeHost>) -> Self {
        Self {
            service,
            host,
            capabilities: RwLock::new(CapabilityState::default()),
        }
    }

    pub fn service(&self) -> &Arc<LanguageInstallService> {
        &self.service
    }

    pub(crate) fn admission_for(
        &self,
        fingerprint: [u8; 32],
        core: &mettail_grammar_core::GrammarCoreV1,
    ) -> Result<Arc<DynamicSyntaxAdmission>, LanguageFltConstructionError> {
        if let Some(admission) = self
            .capabilities
            .read()
            .map_err(|_| LanguageRuntimeError::Poisoned)
            .map_err(LanguageFltConstructionError::Runtime)?
            .admissions
            .get(&fingerprint)
            .cloned()
        {
            return Ok(admission);
        }
        let compiled = Arc::new(
            DynamicSyntaxAdmission::compile(core)
                .map_err(LanguageFltConstructionError::Admission)?,
        );
        let mut state = self
            .capabilities
            .write()
            .map_err(|_| LanguageRuntimeError::Poisoned)
            .map_err(LanguageFltConstructionError::Runtime)?;
        Ok(state
            .admissions
            .entry(fingerprint)
            .or_insert_with(|| compiled.clone())
            .clone())
    }

    pub fn install(&self, candidate: InstallCandidate) -> Result<Par, LanguageRuntimeError> {
        let mut state = self
            .capabilities
            .write()
            .map_err(|_| LanguageRuntimeError::Poisoned)?;
        let receipt = self
            .service
            .install_with_host(candidate, self.host.as_ref())
            .map_err(LanguageRuntimeError::Install)?;
        let generation = *state.generations.entry(receipt.fingerprint).or_insert(0);
        let id = capability_token_id(
            receipt.fingerprint,
            generation,
            &receipt.granted_rights,
            self.service.policy(),
        );
        state.entries.insert(
            id.clone(),
            CapabilityEntry {
                fingerprint: receipt.fingerprint,
                handle: receipt.handle,
            },
        );
        Ok(private_name(id))
    }

    pub fn install_all(
        &self,
        candidate: InstallCandidate,
    ) -> Result<RholangInstalledBatch, LanguageRuntimeError> {
        // This lock deliberately spans the service's atomic commit. Acquiring it
        // first guarantees that a poisoned capability directory cannot leave a
        // newly published language with no Rholang-visible authority token.
        let mut state = self
            .capabilities
            .write()
            .map_err(|_| LanguageRuntimeError::Poisoned)?;
        let batch = self
            .service
            .install_all_with_host(candidate, self.host.as_ref())
            .map_err(LanguageRuntimeError::Install)?;
        let mut exports = Vec::with_capacity(batch.exports.len());
        for export in batch.exports {
            let receipt = export.receipt;
            let generation = *state.generations.entry(receipt.fingerprint).or_insert(0);
            let id = capability_token_id(
                receipt.fingerprint,
                generation,
                &receipt.granted_rights,
                self.service.policy(),
            );
            state.entries.insert(
                id.clone(),
                CapabilityEntry {
                    fingerprint: receipt.fingerprint,
                    handle: receipt.handle,
                },
            );
            exports.push(RholangInstalledExport {
                name: export.name,
                handle: private_name(id),
            });
        }
        Ok(RholangInstalledBatch {
            module_name: batch.module_name,
            exports,
            programs: batch.programs,
        })
    }

    pub fn resolve(
        &self,
        token: &Par,
        required: LanguageRight,
    ) -> Result<InstalledLanguageHandle, LanguageRuntimeError> {
        let id = private_name_id(token).ok_or(LanguageRuntimeError::InvalidHandleShape)?;
        let state = self
            .capabilities
            .read()
            .map_err(|_| LanguageRuntimeError::Poisoned)?;
        let entry = state
            .entries
            .get(id)
            .ok_or(LanguageRuntimeError::UnknownHandle)?;
        self.service
            .table()
            .authorize(&entry.handle, required)
            .map_err(LanguageRuntimeError::Access)?;
        Ok(entry.handle.clone())
    }

    pub fn parse_template(
        &self,
        token: &Par,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        operation: LanguageRight,
        host: &dyn RuntimeHost,
    ) -> Result<Vec<WeightedParse>, LanguageRuntimeError> {
        let handle = self.resolve(token, operation)?;
        self.service
            .parse_template(&handle, pieces, holes, category, operation, host)
            .map_err(LanguageRuntimeError::Parse)
    }

    /// Recognize raw guest text in one explicit category through an opaque
    /// installed-language capability. This is the parse-only public boundary:
    /// it preserves ambiguity, distinguishes resource exhaustion from
    /// rejection, and never grants access to the recognized syntax tree.
    pub fn parse_source(
        &self,
        token: &Par,
        source: &str,
        category: &str,
    ) -> Result<LanguageParseOutcome, LanguageRuntimeError> {
        let handle = self.resolve(token, LanguageRight::Parse)?;
        let language = self
            .service
            .table()
            .authorize(&handle, LanguageRight::Parse)
            .map_err(LanguageRuntimeError::Access)?;
        let category = resolve_required_category(language.core(), category)?;
        match self
            .service
            .parse(&handle, source, Some(category), self.host.as_ref())
        {
            Ok(parses) => match parses.len() {
                0 => Ok(LanguageParseOutcome::Rejected(LanguageParseRejection::NoParse)),
                1 => Ok(LanguageParseOutcome::Accepted),
                alternatives => Ok(LanguageParseOutcome::Ambiguous {
                    alternatives: u32::try_from(alternatives).map_err(|_| {
                        LanguageRuntimeError::AlternativeCountOverflow(alternatives)
                    })?,
                }),
            },
            Err(InstalledParseError::Access(error)) => Err(LanguageRuntimeError::Access(error)),
            Err(InstalledParseError::Parse(error)) => classify_parse_error(error),
        }
    }

    /// Parse one structural FLT template through an installed capability and
    /// reflect every admitted recognition alternative into the common Rho term
    /// algebra. Text and holes remain separate through lexing; fills are spliced
    /// only after recognition, so no fill can become guest source.
    pub fn construct_template(
        &self,
        token: &Par,
        pieces: &[RuntimeTemplatePiece],
        holes: &[NamedRuntimeTemplateHole],
        category: Option<&str>,
        fills: &BTreeMap<String, Par>,
    ) -> Result<Par, LanguageFltConstructionError> {
        let handle = self
            .resolve(token, LanguageRight::Construct)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let language = self
            .service
            .table()
            .authorize(&handle, LanguageRight::Construct)
            .map_err(LanguageRuntimeError::Access)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let core = language.core();
        let capture_limit = usize::try_from(self.service.policy().runtime.max_capture_bindings)
            .unwrap_or(usize::MAX);
        if holes.len() > capture_limit {
            return Err(LanguageFltConstructionError::TemplateHoleLimit {
                limit: capture_limit,
                found: holes.len(),
            });
        }
        let category = resolve_root_category(core, category)?;
        let mut runtime_holes = Vec::with_capacity(holes.len());
        let mut hole_names = BTreeMap::new();
        for (index, hole) in holes.iter().enumerate() {
            if usize::try_from(hole.id).ok() != Some(index) {
                return Err(LanguageFltConstructionError::NonCanonicalHoleId {
                    expected: u32::try_from(index).unwrap_or(u32::MAX),
                    found: hole.id,
                });
            }
            if hole.name.is_empty() || hole_names.insert(hole.id, hole.name.clone()).is_some() {
                return Err(LanguageFltConstructionError::InvalidHoleName(hole.name.clone()));
            }
            runtime_holes.push(RuntimeTemplateHole {
                id: hole.id,
                category: resolve_category(core, hole.category.as_deref())?,
            });
        }
        let declared_names = hole_names
            .values()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>();
        let fill_names = fills
            .keys()
            .cloned()
            .collect::<std::collections::BTreeSet<_>>();
        if declared_names != fill_names {
            return Err(LanguageFltConstructionError::FillSetMismatch {
                declared: declared_names,
                supplied: fill_names,
            });
        }

        let parses = self
            .service
            .parse_template(
                &handle,
                pieces,
                &runtime_holes,
                Some(category),
                LanguageRight::Construct,
                self.host.as_ref(),
            )
            .map_err(LanguageRuntimeError::Parse)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let fingerprint = grammar_fingerprint_label(handle.fingerprint());
        let admission = self.admission_for(handle.fingerprint(), core)?;
        let mut alternatives = Vec::with_capacity(parses.len());
        let mut inferred_categories = None;
        for parse in parses {
            let categories = dynamic_template_hole_categories(&parse.syntax, holes.len())
                .map_err(LanguageFltConstructionError::Reflection)?;
            if inferred_categories
                .as_ref()
                .is_some_and(|inferred| inferred != &categories)
            {
                return Err(LanguageFltConstructionError::AmbiguousHoleCategories);
            }
            inferred_categories.get_or_insert_with(|| categories.clone());
            alternatives.push(
                dynamic_syntax_to_ground_term(&parse.syntax, core, &hole_names)
                    .map_err(LanguageFltConstructionError::Reflection)?,
            );
        }
        let inferred_categories = inferred_categories.unwrap_or_default();
        for (hole, category) in holes.iter().zip(&inferred_categories) {
            let fill = fills
                .get(&hole.name)
                .expect("the fill set was checked against the telescope");
            if !admission.admits_category(fill, &fingerprint, *category) {
                let category = core
                    .categories
                    .get(category.0 as usize)
                    .map_or_else(|| format!("#{}", category.0), |category| category.name.clone());
                return Err(LanguageFltConstructionError::FillCategoryMismatch {
                    hole: hole.name.clone(),
                    category,
                });
            }
        }
        let mut reflected = Par::default();
        for ground in alternatives {
            let alternative = reflect_flt_construction(&ground, fills, &fingerprint)
                .map_err(LanguageFltConstructionError::Construction)?;
            // Preserve every weighted recognition alternative in the same
            // deterministic order returned by GrammarCore. Selecting the first
            // parse here would be an implicit and authority-free disambiguation.
            reflected = reflected.append(alternative);
        }
        Ok(reflected)
    }

    /// Parse and reflect an installed-language receive pattern before the
    /// receive is published. Matching later reauthorizes the originating
    /// handle, so revocation invalidates every derived pattern token.
    pub fn prepare_pattern(
        &self,
        token: &Par,
        pieces: &[RuntimeTemplatePiece],
        holes: &[NamedRuntimeTemplateHole],
        category: Option<&str>,
    ) -> Result<Par, LanguageFltConstructionError> {
        let language_token = private_name_id(token)
            .ok_or(LanguageRuntimeError::InvalidHandleShape)
            .map_err(LanguageFltConstructionError::Runtime)?
            .to_vec();
        let handle = self
            .resolve(token, LanguageRight::Match)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let language = self
            .service
            .table()
            .authorize(&handle, LanguageRight::Match)
            .map_err(LanguageRuntimeError::Access)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let core = language.core();
        let capture_limit = usize::try_from(self.service.policy().runtime.max_capture_bindings)
            .unwrap_or(usize::MAX);
        if holes.len() > capture_limit {
            return Err(LanguageFltConstructionError::TemplateHoleLimit {
                limit: capture_limit,
                found: holes.len(),
            });
        }
        let category = resolve_root_category(core, category)?;
        let mut runtime_holes = Vec::with_capacity(holes.len());
        let mut hole_names = BTreeMap::new();
        let mut reflection_holes = Vec::with_capacity(holes.len());
        for (index, hole) in holes.iter().enumerate() {
            if usize::try_from(hole.id).ok() != Some(index) {
                return Err(LanguageFltConstructionError::NonCanonicalHoleId {
                    expected: u32::try_from(index).unwrap_or(u32::MAX),
                    found: hole.id,
                });
            }
            if hole.name.is_empty() || hole_names.insert(hole.id, hole.name.clone()).is_some() {
                return Err(LanguageFltConstructionError::InvalidHoleName(hole.name.clone()));
            }
            runtime_holes.push(RuntimeTemplateHole {
                id: hole.id,
                category: resolve_category(core, hole.category.as_deref())?,
            });
            reflection_holes.push(match &hole.category {
                Some(category) => FltHole::typed(hole.name.clone(), category.clone()),
                None => FltHole::new(hole.name.clone()),
            });
        }
        let parses = self
            .service
            .parse_template(
                &handle,
                pieces,
                &runtime_holes,
                Some(category),
                LanguageRight::Match,
                self.host.as_ref(),
            )
            .map_err(LanguageRuntimeError::Parse)
            .map_err(LanguageFltConstructionError::Runtime)?;
        let mut recognized = None;
        for parse in parses {
            let categories = dynamic_template_hole_categories(&parse.syntax, holes.len())
                .map_err(LanguageFltConstructionError::Reflection)?;
            let ground = dynamic_syntax_to_ground_term(&parse.syntax, core, &hole_names)
                .map_err(LanguageFltConstructionError::Reflection)?;
            match &recognized {
                Some((first, first_categories))
                    if first != &ground || first_categories != &categories =>
                {
                    return Err(LanguageFltConstructionError::AmbiguousPattern)
                },
                Some(_) => {},
                None => recognized = Some((ground, categories)),
            }
        }
        let (ground, capture_categories) =
            recognized.ok_or(LanguageFltConstructionError::AmbiguousPattern)?;
        let fingerprint = grammar_fingerprint_label(handle.fingerprint());
        let admission = self.admission_for(handle.fingerprint(), core)?;
        let FltPatternReflection {
            pattern,
            free_count,
            mut hole_bindings,
            linearity_guards,
        } = reflect_flt_pattern(&ground, &reflection_holes, &fingerprint)
            .map_err(LanguageFltConstructionError::Construction)?;
        hole_bindings.sort_by_key(|(_, level)| *level);
        let occurrence_count = usize::try_from(free_count)
            .map_err(|_| LanguageFltConstructionError::PatternTelescopeMismatch)?;
        if occurrence_count > capture_limit {
            return Err(LanguageFltConstructionError::TemplateOccurrenceLimit {
                limit: capture_limit,
                found: occurrence_count,
            });
        }
        let capture_plan =
            PreparedCapturePlan::compile(holes, &hole_bindings, &linearity_guards, free_count)
                .ok_or(LanguageFltConstructionError::PatternTelescopeMismatch)?;
        let pattern = BindPattern {
            patterns: vec![pattern],
            remainder: None,
            free_count,
        };
        let id = prepared_pattern_token_id(
            &language_token,
            handle.fingerprint(),
            pieces,
            holes,
            Some(category),
        );
        let pattern_id =
            prepared_pattern_semantic_id(handle.fingerprint(), pieces, holes, Some(category));
        let mut state = self
            .capabilities
            .write()
            .map_err(|_| LanguageRuntimeError::Poisoned)
            .map_err(LanguageFltConstructionError::Runtime)?;
        self.service
            .table()
            .authorize(&handle, LanguageRight::Match)
            .map_err(LanguageRuntimeError::Access)
            .map_err(LanguageFltConstructionError::Runtime)?;
        state.patterns.insert(
            id.clone(),
            PreparedPatternEntry {
                fingerprint: handle.fingerprint(),
                pattern_id,
                handle,
                pattern,
                root_category: category,
                capture_plan,
                capture_categories,
                admission,
            },
        );
        Ok(private_name(id))
    }

    pub(crate) fn resolve_prepared_pattern(
        &self,
        token: &Par,
    ) -> Result<ResolvedPreparedPattern, LanguageRuntimeError> {
        let id = prepared_pattern_name_id(token).ok_or(LanguageRuntimeError::InvalidHandleShape)?;
        let state = self
            .capabilities
            .read()
            .map_err(|_| LanguageRuntimeError::Poisoned)?;
        let entry = state
            .patterns
            .get(id)
            .ok_or(LanguageRuntimeError::UnknownHandle)?;
        self.service
            .table()
            .authorize(&entry.handle, LanguageRight::Match)
            .map_err(LanguageRuntimeError::Access)?;
        Ok(ResolvedPreparedPattern {
            pattern: entry.pattern.clone(),
            pattern_id: entry.pattern_id,
            root_category: entry.root_category,
            capture_plan: entry.capture_plan.clone(),
            capture_categories: entry.capture_categories.clone(),
            fingerprint: grammar_fingerprint_label(entry.fingerprint),
            fingerprint_bytes: entry.fingerprint,
            admission: entry.admission.clone(),
        })
    }

    pub fn revoke(&self, token: &Par) -> Result<(), LanguageRuntimeError> {
        let id = private_name_id(token).ok_or(LanguageRuntimeError::InvalidHandleShape)?;
        let mut state = self
            .capabilities
            .write()
            .map_err(|_| LanguageRuntimeError::Poisoned)?;
        let fingerprint = state
            .entries
            .get(id)
            .ok_or(LanguageRuntimeError::UnknownHandle)?
            .fingerprint;
        let generation = state.generations.get(&fingerprint).copied().unwrap_or(0);
        let next = generation
            .checked_add(1)
            .ok_or(LanguageRuntimeError::GenerationExhausted)?;
        self.service
            .revoke(fingerprint)
            .map_err(LanguageRuntimeError::Install)?;
        state.generations.insert(fingerprint, next);
        state
            .entries
            .retain(|_, entry| entry.fingerprint != fingerprint);
        state
            .patterns
            .retain(|_, entry| entry.fingerprint != fingerprint);
        state.admissions.remove(&fingerprint);
        Ok(())
    }
}

/// One name-bearing FLT telescope declaration at the Rholang system boundary.
/// GrammarCore uses numeric category identifiers internally; names are resolved
/// only through the core authorized by the opaque language handle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedRuntimeTemplateHole {
    pub id: u32,
    pub name: String,
    pub category: Option<String>,
}

#[derive(Debug)]
pub enum LanguageFltConstructionError {
    Runtime(LanguageRuntimeError),
    MissingRootCategory,
    UnknownCategory(String),
    DuplicateCategory(String),
    NonCanonicalHoleId {
        expected: u32,
        found: u32,
    },
    InvalidHoleName(String),
    FillSetMismatch {
        declared: std::collections::BTreeSet<String>,
        supplied: std::collections::BTreeSet<String>,
    },
    Reflection(DynamicReflectionError),
    Admission(DynamicAdmissionCompileError),
    Construction(FltReflectError),
    FillCategoryMismatch {
        hole: String,
        category: String,
    },
    AmbiguousHoleCategories,
    AmbiguousPattern,
    PatternTelescopeMismatch,
    TemplateHoleLimit {
        limit: usize,
        found: usize,
    },
    TemplateOccurrenceLimit {
        limit: usize,
        found: usize,
    },
}

impl fmt::Display for LanguageFltConstructionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Runtime(error) => error.fmt(formatter),
            Self::MissingRootCategory => {
                formatter.write_str("an FLT must select an explicit root category")
            },
            Self::UnknownCategory(name) => write!(formatter, "unknown grammar category `{name}`"),
            Self::DuplicateCategory(name) => {
                write!(formatter, "grammar contains duplicate category `{name}`")
            },
            Self::NonCanonicalHoleId { expected, found } => write!(
                formatter,
                "FLT hole ids must be dense in declaration order: expected {expected}, found {found}",
            ),
            Self::InvalidHoleName(name) => write!(formatter, "invalid or duplicate FLT hole name `{name}`"),
            Self::FillSetMismatch { declared, supplied } => write!(
                formatter,
                "FLT fill names do not equal the declared telescope: declared {declared:?}, supplied {supplied:?}",
            ),
            Self::Reflection(error) => write!(formatter, "dynamic syntax reflection failed: {error}"),
            Self::Admission(error) => write!(formatter, "dynamic syntax admission failed: {error}"),
            Self::Construction(error) => write!(formatter, "FLT construction reflection failed: {error}"),
            Self::FillCategoryMismatch { hole, category } => write!(
                formatter,
                "FLT fill `${{{hole}}}` is not a well-formed term of category `{category}`",
            ),
            Self::AmbiguousHoleCategories => formatter.write_str(
                "FLT template alternatives infer different hole categories",
            ),
            Self::AmbiguousPattern => formatter.write_str(
                "FLT receive pattern has more than one structurally distinct weighted parse",
            ),
            Self::PatternTelescopeMismatch => formatter.write_str(
                "reflected FLT pattern bindings do not equal the declared telescope",
            ),
            Self::TemplateHoleLimit { limit, found } => write!(
                formatter,
                "FLT template declares {found} holes, exceeding the host limit {limit}",
            ),
            Self::TemplateOccurrenceLimit { limit, found } => write!(
                formatter,
                "FLT pattern contains {found} hole occurrences, exceeding the host limit {limit}",
            ),
        }
    }
}

impl std::error::Error for LanguageFltConstructionError {}

fn resolve_category(
    core: &mettail_grammar_core::GrammarCoreV1,
    name: Option<&str>,
) -> Result<Option<CategoryId>, LanguageFltConstructionError> {
    let Some(name) = name else { return Ok(None) };
    let mut matching = core
        .categories
        .iter()
        .filter(|category| category.name == name);
    let Some(category) = matching.next() else {
        return Err(LanguageFltConstructionError::UnknownCategory(name.into()));
    };
    if matching.next().is_some() {
        return Err(LanguageFltConstructionError::DuplicateCategory(name.into()));
    }
    Ok(Some(category.id))
}

fn resolve_root_category(
    core: &mettail_grammar_core::GrammarCoreV1,
    name: Option<&str>,
) -> Result<CategoryId, LanguageFltConstructionError> {
    let name = name.ok_or(LanguageFltConstructionError::MissingRootCategory)?;
    resolve_category(core, Some(name))?.ok_or(LanguageFltConstructionError::MissingRootCategory)
}

fn resolve_required_category(
    core: &mettail_grammar_core::GrammarCoreV1,
    name: &str,
) -> Result<CategoryId, LanguageRuntimeError> {
    let mut matching = core
        .categories
        .iter()
        .filter(|category| category.name == name);
    let Some(category) = matching.next() else {
        return Err(LanguageRuntimeError::UnknownCategory(name.into()));
    };
    if matching.next().is_some() {
        return Err(LanguageRuntimeError::DuplicateCategory(name.into()));
    }
    Ok(category.id)
}

fn classify_parse_error(error: RuntimeError) -> Result<LanguageParseOutcome, LanguageRuntimeError> {
    let outcome = match error {
        RuntimeError::NoParse => LanguageParseOutcome::Rejected(LanguageParseRejection::NoParse),
        RuntimeError::Lex { byte } => LanguageParseOutcome::Rejected(LanguageParseRejection::Lex {
            byte: parse_diagnostic_u32("byte", byte)?,
        }),
        RuntimeError::LexerModeUnderflow { byte } => {
            LanguageParseOutcome::Rejected(LanguageParseRejection::LexerModeUnderflow {
                byte: parse_diagnostic_u32("byte", byte)?,
            })
        },
        RuntimeError::LexerModeUnclosed { byte, depth } => {
            LanguageParseOutcome::Rejected(LanguageParseRejection::LexerModeUnclosed {
                byte: parse_diagnostic_u32("byte", byte)?,
                depth: parse_diagnostic_u32("depth", depth)?,
            })
        },
        RuntimeError::InvalidTokenValue { .. } => {
            LanguageParseOutcome::Rejected(LanguageParseRejection::InvalidTokenValue)
        },
        RuntimeError::ForeignLanguage { byte, .. } => {
            LanguageParseOutcome::Rejected(LanguageParseRejection::ForeignLanguage {
                byte: parse_diagnostic_u32("byte", byte)?,
            })
        },
        RuntimeError::InputTooLarge => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::InputBytes)
        },
        RuntimeError::LexerStateLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerStates)
        },
        RuntimeError::LexerEdgeLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerEdges)
        },
        RuntimeError::LexerWorkLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerWork)
        },
        RuntimeError::LexerModeDepthLimit { byte } => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerModeDepth {
                byte: parse_diagnostic_u32("byte", byte)?,
            })
        },
        RuntimeError::ForeignNestingLimit { byte } => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::ForeignNesting {
                byte: parse_diagnostic_u32("byte", byte)?,
            })
        },
        RuntimeError::ParseItemLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::ParseItems)
        },
        RuntimeError::ForestNodeLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::ForestNodes)
        },
        RuntimeError::ForestCycle => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::ForestCycle)
        },
        RuntimeError::SemanticResultLimit => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::SemanticResults)
        },
        RuntimeError::Capability(RuntimeCapabilityError::CostExceeded(_)) => {
            LanguageParseOutcome::Exhausted(LanguageParseExhaustion::CapabilityCost)
        },
        other => return Err(LanguageRuntimeError::Parse(InstalledParseError::Parse(other))),
    };
    Ok(outcome)
}

fn parse_diagnostic_u32(field: &'static str, value: usize) -> Result<u32, LanguageRuntimeError> {
    u32::try_from(value).map_err(|_| LanguageRuntimeError::ParseDiagnosticOverflow { field, value })
}

pub(crate) fn grammar_fingerprint_label(fingerprint: [u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut label = String::with_capacity("mettail-grammar-core-v1:".len() + 64);
    label.push_str("mettail-grammar-core-v1:");
    for byte in fingerprint {
        write!(&mut label, "{byte:02x}").expect("String writes are infallible");
    }
    label
}

fn prepared_pattern_token_id(
    language_token: &[u8],
    fingerprint: [u8; 32],
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: Option<CategoryId>,
) -> Vec<u8> {
    let semantic_id = prepared_pattern_semantic_id(fingerprint, pieces, holes, category);
    let mut hasher = blake3::Hasher::new();
    hasher.update(PREPARED_PATTERN_DOMAIN_V1);
    hash_pattern_field(&mut hasher, language_token);
    hasher.update(&semantic_id);
    let mut id = Vec::with_capacity(PREPARED_PATTERN_DOMAIN_V1.len() + 32);
    id.extend_from_slice(PREPARED_PATTERN_DOMAIN_V1);
    id.extend_from_slice(hasher.finalize().as_bytes());
    id
}

fn prepared_pattern_semantic_id(
    fingerprint: [u8; 32],
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: Option<CategoryId>,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"mettail-prepared-flt-pattern-semantics/1\0");
    hash_pattern_field(&mut hasher, LANGUAGE_FLT_PATTERN_ABI_V1.as_bytes());
    hasher.update(&fingerprint);
    hasher.update(
        &category
            .map_or(u32::MAX, |category| category.0)
            .to_be_bytes(),
    );
    hasher.update(b"pieces\0");
    hasher.update(&(pieces.len() as u64).to_be_bytes());
    for piece in pieces {
        match piece {
            RuntimeTemplatePiece::Text(text) => {
                hasher.update(&[0]);
                hash_pattern_field(&mut hasher, text.as_bytes());
            },
            RuntimeTemplatePiece::Hole(id) => {
                hasher.update(&[1]);
                hasher.update(&id.to_be_bytes());
            },
        }
    }
    hasher.update(b"holes\0");
    hasher.update(&(holes.len() as u64).to_be_bytes());
    for hole in holes {
        hasher.update(&hole.id.to_be_bytes());
        hash_pattern_field(&mut hasher, hole.name.as_bytes());
        match &hole.category {
            Some(category) => {
                hasher.update(&[1]);
                hash_pattern_field(&mut hasher, category.as_bytes());
            },
            None => {
                hasher.update(&[0]);
            },
        }
    }
    *hasher.finalize().as_bytes()
}

fn hash_pattern_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn capability_token_id(
    fingerprint: [u8; 32],
    generation: u64,
    rights: &LanguageRights,
    policy: &LanguageInstallPolicy,
) -> Vec<u8> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(LANGUAGE_HANDLE_DOMAIN_CURRENT);
    hasher.update(&fingerprint);
    hasher.update(&generation.to_be_bytes());
    hasher.update(&policy.fingerprint);
    for right in rights.iter() {
        hasher.update(right.name().as_bytes());
        hasher.update(&[0]);
    }
    let mut id = Vec::with_capacity(LANGUAGE_HANDLE_DOMAIN_CURRENT.len() + 32);
    id.extend_from_slice(LANGUAGE_HANDLE_DOMAIN_CURRENT);
    id.extend_from_slice(hasher.finalize().as_bytes());
    id
}

pub(crate) fn private_name(id: Vec<u8>) -> Par {
    Par::default().with_unforgeables(vec![GUnforgeable {
        unf_instance: Some(GPrivateBody(GPrivate { id })),
    }])
}

fn private_name_id(value: &Par) -> Option<&[u8]> {
    single_private_name_id(value).filter(|id| id.starts_with(LANGUAGE_HANDLE_DOMAIN_CURRENT))
}

fn prepared_pattern_name_id(value: &Par) -> Option<&[u8]> {
    // A prepared token enters a receive pattern through a `VarRef`. f1r3node's
    // substitution removes that connective structurally but conservatively
    // retains the enclosing `connective_used` cache bit. Capability identity is
    // the sole GPrivate payload, not derived traversal metadata, so accept that
    // conservative cache while retaining the exact structural shape check.
    single_private_name_id_ignoring_cache(value)
        .filter(|id| id.starts_with(PREPARED_PATTERN_DOMAIN_V1))
}

fn single_private_name_id(value: &Par) -> Option<&[u8]> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.exprs.is_empty()
        || !value.matches.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
        || !value.locally_free.is_empty()
        || value.connective_used
    {
        return None;
    }
    single_private_name_id_ignoring_cache(value)
}

pub(crate) fn single_private_name_id_ignoring_cache(value: &Par) -> Option<&[u8]> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.exprs.is_empty()
        || !value.matches.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
    {
        return None;
    }
    let [unforgeable] = value.unforgeables.as_slice() else {
        return None;
    };
    let Some(GPrivateBody(private)) = unforgeable.unf_instance.as_ref() else {
        return None;
    };
    Some(private.id.as_slice())
}

#[derive(Debug)]
pub enum LanguageRuntimeError {
    Install(InstallServiceError),
    Access(LanguageAccessError),
    Parse(InstalledParseError),
    InvalidHandleShape,
    UnknownHandle,
    GenerationExhausted,
    EmptyExportSet,
    MultipleExports { count: usize },
    UnknownCategory(String),
    DuplicateCategory(String),
    AlternativeCountOverflow(usize),
    ParseDiagnosticOverflow { field: &'static str, value: usize },
    Poisoned,
}

impl fmt::Display for LanguageRuntimeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Install(error) => error.fmt(formatter),
            Self::Access(error) => write!(formatter, "language authority rejected: {error:?}"),
            Self::Parse(error) => write!(formatter, "installed language parse rejected: {error:?}"),
            Self::InvalidHandleShape => {
                formatter.write_str("expected one installed-language capability")
            },
            Self::UnknownHandle => formatter.write_str("unknown installed-language capability"),
            Self::GenerationExhausted => {
                formatter.write_str("language capability generation exhausted")
            },
            Self::EmptyExportSet => formatter.write_str("module has no installed exports"),
            Self::MultipleExports { count } => {
                write!(formatter, "module installed {count} exports; use the multi-export result")
            },
            Self::UnknownCategory(name) => write!(formatter, "unknown grammar category `{name}`"),
            Self::DuplicateCategory(name) => {
                write!(formatter, "grammar contains duplicate category `{name}`")
            },
            Self::AlternativeCountOverflow(count) => {
                write!(formatter, "parse produced {count} alternatives, outside the wire range")
            },
            Self::ParseDiagnosticOverflow { field, value } => {
                write!(formatter, "parse diagnostic {field}={value} is outside the wire range")
            },
            Self::Poisoned => {
                formatter.write_str("language capability directory lock was poisoned")
            },
        }
    }
}

impl std::error::Error for LanguageRuntimeError {}

/// The deploy-reachable, non-local installation boundary. Provenance and host
/// grants are captured by `runtime`; they are intentionally absent from the
/// two-argument Rholang protocol `[specification, reply]`.
pub fn language_install_definition(runtime: Arc<RholangLanguageRuntime>) -> Definition {
    Definition {
        urn: LANGUAGE_INSTALL_URN.into(),
        fixed_channel: LANGUAGE_INSTALL_BAND.channel(0, LANGUAGE_CAPABILITY_ABI_CURRENT),
        // Nouveau Rholang has one datum per send.  Its surface
        // `install!(specification, *reply)` is lowered to the canonical arity
        // list `[specification, reply]` inside that datum.
        arity: 1,
        body_ref: LANGUAGE_INSTALL_BAND.body_ref(0, LANGUAGE_CAPABILITY_ABI_CURRENT),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let runtime = runtime.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let runtime = runtime.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = call.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_INSTALL_URN}: not a single-message contract call"
                        )));
                    };
                    if payload.len() != 1 {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_INSTALL_URN}: expected one canonical call datum, got Rho arity {}",
                            payload.len()
                        )));
                    }
                    let call = payload
                        .into_iter()
                        .next()
                        .expect("one install call datum was checked");
                    let Some((specification, reply)) = decode_install_call(call) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_INSTALL_URN}: expected the two-argument call [specification, reply]"
                        )));
                    };
                    let candidate = decode_install_candidate(specification);
                    let response = match candidate {
                        Ok(candidate) => {
                            let installed =
                                tokio::task::spawn_blocking(move || runtime.install_all(candidate))
                                    .await;
                            match installed {
                                Ok(Ok(batch)) => success_batch_response(batch),
                                Ok(Err(error)) => {
                                    error_response(runtime_error_code(&error), &error.to_string())
                                },
                                Err(error) => {
                                    error_response("InstallerTaskFailed", &error.to_string())
                                },
                            }
                        },
                        Err(error) => {
                            error_response("InvalidSpecificationValue", &error.to_string())
                        },
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

/// Parse-only recognition through an installed-language capability.
///
/// The request is the closed list `[abi, handle, source, category, reply]`.
/// `category` is mandatory because guessing among overlapping grammar roots is
/// neither deterministic dispatch nor a usable authority boundary. The reply
/// is a closed result map with one of `accepted`, `rejected`, `ambiguous`, or
/// `exhausted`; reflected syntax is deliberately absent.
pub fn language_parse_definition(runtime: Arc<RholangLanguageRuntime>) -> Definition {
    Definition {
        urn: LANGUAGE_PARSE_URN.into(),
        fixed_channel: LANGUAGE_PARSE_BAND.channel(0, LANGUAGE_PARSE_ABI_V1),
        arity: 1,
        body_ref: LANGUAGE_PARSE_BAND.body_ref(0, LANGUAGE_PARSE_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let runtime = runtime.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let runtime = runtime.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = call.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_PARSE_URN}: not a single-message contract call"
                        )));
                    };
                    let [datum] = payload.as_slice() else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_PARSE_URN}: expected one request datum, got Rho arity {}",
                            payload.len()
                        )));
                    };
                    let request = decode_language_parse_call(datum).map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_PARSE_URN}: {error}"
                        ))
                    })?;
                    let reply = request.reply.clone();
                    let parsed = tokio::task::spawn_blocking(move || {
                        runtime.parse_source(&request.handle, &request.source, &request.category)
                    })
                    .await;
                    let response = match parsed {
                        Ok(Ok(outcome)) => parse_outcome_response(outcome),
                        Ok(Err(error)) => {
                            error_response(runtime_error_code(&error), &error.to_string())
                        },
                        Err(error) => error_response("ParserTaskFailed", &error.to_string()),
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

/// The inseparable installed-language system surface. Both definitions must be
/// built from the same runtime instance: the construction handler resolves the
/// opaque capability minted by the installation handler in that instance's
/// private directory.
pub fn language_runtime_definitions(runtime: Arc<RholangLanguageRuntime>) -> Vec<Definition> {
    language_runtime_definitions_with_theorem_checker(
        runtime,
        Arc::new(mettail_grammar_core::StructuralTheoremChecker::default()),
        crate::theorem_channel::TheoremServicePolicy::default(),
    )
}

/// Build the complete Rholang-facing language surface with a host-injected
/// theorem checker and policy. The theorem service is constructed around the
/// same installed-language runtime as the parser and FLT ports, so a caller
/// cannot accidentally split capability identity across two runtime tables.
/// This is the OSLF/Reified-RSpace integration seam; the default helper above
/// installs only the bounded structural checker.
pub fn language_runtime_definitions_with_theorem_checker(
    runtime: Arc<RholangLanguageRuntime>,
    checker: Arc<dyn mettail_grammar_core::AdmissionChecker>,
    policy: crate::theorem_channel::TheoremServicePolicy,
) -> Vec<Definition> {
    let theorem_service = Arc::new(crate::theorem_channel::RholangTheoremService::new(
        runtime.clone(),
        checker,
        policy,
    ));
    let mut definitions = vec![
        language_install_definition(runtime.clone()),
        language_parse_definition(runtime.clone()),
        language_flt_construct_definition(runtime.clone()),
        language_flt_pattern_definition(runtime),
    ];
    definitions.extend(crate::theorem_channel::theorem_runtime_definitions(theorem_service));
    definitions
}

/// Machine boundary for structural construction through an installed language.
/// The request is one ordinary Rho list datum:
///
/// `[abi, handle, pieces, holes, root-category, fills, reply]`.
///
/// A malformed request or rejected parse aborts the system-process call. This
/// endpoint is compiler-internal and its result is substituted directly into a
/// staged program body, so returning an error *as if it were an FLT value* would
/// violate the structural reflection ABI.
pub fn language_flt_construct_definition(runtime: Arc<RholangLanguageRuntime>) -> Definition {
    Definition {
        urn: LANGUAGE_FLT_CONSTRUCT_URN.into(),
        fixed_channel: LANGUAGE_FLT_CONSTRUCT_BAND.channel(0, LANGUAGE_FLT_CONSTRUCT_ABI_V1),
        arity: 1,
        body_ref: LANGUAGE_FLT_CONSTRUCT_BAND.body_ref(0, LANGUAGE_FLT_CONSTRUCT_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let runtime = runtime.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let runtime = runtime.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = call.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_CONSTRUCT_URN}: not a single-message contract call"
                        )));
                    };
                    let [datum] = payload.as_slice() else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_CONSTRUCT_URN}: expected one request datum, got Rho arity {}",
                            payload.len()
                        )));
                    };
                    let request = decode_flt_construct_call(datum).map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_CONSTRUCT_URN}: {error}"
                        ))
                    })?;
                    let reply = request.reply.clone();
                    let constructed = tokio::task::spawn_blocking(move || {
                        runtime.construct_template(
                            &request.handle,
                            &request.pieces,
                            &request.holes,
                            Some(request.category.as_str()),
                            &request.fills,
                        )
                    })
                    .await
                    .map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_CONSTRUCT_URN}: construction worker failed: {error}"
                        ))
                    })?
                    .map_err(|error| {
                        let message: String = error
                            .to_string()
                            .chars()
                            .take(MAX_PUBLIC_ERROR_CHARS)
                            .collect();
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_CONSTRUCT_URN}: {message}"
                        ))
                    })?;
                    let output = vec![constructed];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

/// Pre-publication FLT receive-pattern preparation. The reply is an opaque
/// pattern token, never a parser object or authority-amplifying language handle.
pub fn language_flt_pattern_definition(runtime: Arc<RholangLanguageRuntime>) -> Definition {
    Definition {
        urn: LANGUAGE_FLT_PATTERN_URN.into(),
        fixed_channel: LANGUAGE_FLT_PATTERN_BAND.channel(0, LANGUAGE_FLT_PATTERN_ABI_V1),
        arity: 1,
        body_ref: LANGUAGE_FLT_PATTERN_BAND.body_ref(0, LANGUAGE_FLT_PATTERN_ABI_V1),
        remainder: None,
        handler: Box::new(move |context| {
            let space = context.space.clone();
            let dispatcher = context.dispatcher.clone();
            let runtime = runtime.clone();
            Box::new(move |args: (Vec<ListParWithRandom>, bool, Vec<Par>)| {
                let call = ContractCall {
                    space: space.clone(),
                    dispatcher: dispatcher.clone(),
                };
                let runtime = runtime.clone();
                Box::pin(async move {
                    let Some((produce, _is_replay, _previous, payload)) = call.unapply(args) else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_PATTERN_URN}: not a single-message contract call"
                        )));
                    };
                    let [datum] = payload.as_slice() else {
                        return Err(InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_PATTERN_URN}: expected one request datum, got Rho arity {}",
                            payload.len()
                        )));
                    };
                    let request = decode_flt_pattern_call(datum).map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_PATTERN_URN}: {error}"
                        ))
                    })?;
                    let reply = request.reply.clone();
                    let prepared = tokio::task::spawn_blocking(move || {
                        runtime.prepare_pattern(
                            &request.handle,
                            &request.pieces,
                            &request.holes,
                            Some(request.category.as_str()),
                        )
                    })
                    .await
                    .map_err(|error| {
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_PATTERN_URN}: pattern worker failed: {error}"
                        ))
                    })?
                    .map_err(|error| {
                        let message: String = error
                            .to_string()
                            .chars()
                            .take(MAX_PUBLIC_ERROR_CHARS)
                            .collect();
                        InterpreterError::IllegalArgumentError(format!(
                            "{LANGUAGE_FLT_PATTERN_URN}: {message}"
                        ))
                    })?;
                    let output = vec![prepared];
                    produce(&output, &reply).await?;
                    Ok(output)
                })
                    as Pin<Box<dyn Future<Output = Result<Vec<Par>, InterpreterError>> + Send>>
            })
        }),
    }
}

struct FltConstructCall {
    handle: Par,
    pieces: Vec<RuntimeTemplatePiece>,
    holes: Vec<NamedRuntimeTemplateHole>,
    category: String,
    fills: BTreeMap<String, Par>,
    reply: Par,
}

struct FltPatternCall {
    handle: Par,
    pieces: Vec<RuntimeTemplatePiece>,
    holes: Vec<NamedRuntimeTemplateHole>,
    category: String,
    reply: Par,
}

struct LanguageParseCall {
    handle: Par,
    source: String,
    category: String,
    reply: Par,
}

/// Encode the compiler-internal request datum consumed by
/// [`language_flt_construct_definition`]. Cached protobuf metadata is derived
/// from every handle/fill/reply child, so de-Bruijn substitution descends into
/// the envelope before the system process sees it.
pub(crate) fn encode_flt_construct_call(
    handle: Par,
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: &str,
    fills: &BTreeMap<String, Par>,
    reply: Par,
) -> Par {
    let pieces = wire_list(
        pieces
            .iter()
            .map(|piece| match piece {
                RuntimeTemplatePiece::Text(text) => wire_list(vec![
                    new_gstring_par("text".into(), Vec::new(), false),
                    new_gstring_par(text.clone(), Vec::new(), false),
                ]),
                RuntimeTemplatePiece::Hole(id) => wire_list(vec![
                    new_gstring_par("hole".into(), Vec::new(), false),
                    new_gint_par(i64::from(*id), Vec::new(), false),
                ]),
            })
            .collect(),
    );
    let holes = wire_list(
        holes
            .iter()
            .map(|hole| {
                wire_list(vec![
                    new_gint_par(i64::from(hole.id), Vec::new(), false),
                    new_gstring_par(hole.name.clone(), Vec::new(), false),
                    optional_string_par(hole.category.as_deref()),
                ])
            })
            .collect(),
    );
    let fills = wire_map(
        fills
            .iter()
            .map(|(name, value)| (new_gstring_par(name.clone(), Vec::new(), false), value.clone()))
            .collect(),
    );
    wire_list(vec![
        new_gstring_par(LANGUAGE_FLT_CONSTRUCT_ABI_V1.into(), Vec::new(), false),
        handle,
        pieces,
        holes,
        new_gstring_par(category.into(), Vec::new(), false),
        fills,
        reply,
    ])
}

pub(crate) fn encode_flt_pattern_call(
    handle: Par,
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: &str,
    reply: Par,
) -> Par {
    let pieces = wire_list(
        pieces
            .iter()
            .map(|piece| match piece {
                RuntimeTemplatePiece::Text(text) => wire_list(vec![
                    new_gstring_par("text".into(), Vec::new(), false),
                    new_gstring_par(text.clone(), Vec::new(), false),
                ]),
                RuntimeTemplatePiece::Hole(id) => wire_list(vec![
                    new_gstring_par("hole".into(), Vec::new(), false),
                    new_gint_par(i64::from(*id), Vec::new(), false),
                ]),
            })
            .collect(),
    );
    let holes = wire_list(
        holes
            .iter()
            .map(|hole| {
                wire_list(vec![
                    new_gint_par(i64::from(hole.id), Vec::new(), false),
                    new_gstring_par(hole.name.clone(), Vec::new(), false),
                    optional_string_par(hole.category.as_deref()),
                ])
            })
            .collect(),
    );
    wire_list(vec![
        new_gstring_par(LANGUAGE_FLT_PATTERN_ABI_V1.into(), Vec::new(), false),
        handle,
        pieces,
        holes,
        new_gstring_par(category.into(), Vec::new(), false),
        reply,
    ])
}

/// Encode the exact closed request consumed by [`language_parse_definition`].
#[cfg(test)]
pub(crate) fn encode_language_parse_call(
    handle: Par,
    source: impl Into<String>,
    category: impl Into<String>,
    reply: Par,
) -> Par {
    wire_list(vec![
        new_gstring_par(LANGUAGE_PARSE_ABI_V1.into(), Vec::new(), false),
        handle,
        new_gstring_par(source.into(), Vec::new(), false),
        new_gstring_par(category.into(), Vec::new(), false),
        reply,
    ])
}

/// Placeholder installed in a receive pattern after preparation but before the
/// outer preparation reply substitutes its token. It is ordinary Rho structure
/// tagged by a reserved private name, so user strings cannot forge the shape.
pub(crate) fn dynamic_flt_pattern_token_pattern(token: Par) -> Par {
    wire_list(vec![
        GPrivateBuilder::new_par_from_string(DYNAMIC_FLT_PATTERN_ENVELOPE_V1.into()),
        token,
    ])
}

pub(crate) fn dynamic_flt_pattern_token(pattern: &BindPattern) -> Option<&Par> {
    if pattern.remainder.is_some() {
        return None;
    }
    let [envelope] = pattern.patterns.as_slice() else {
        return None;
    };
    let [tag, token] = exact_list(envelope)? else {
        return None;
    };
    (tag == &GPrivateBuilder::new_par_from_string(DYNAMIC_FLT_PATTERN_ENVELOPE_V1.into()))
        .then_some(token)
}

fn optional_string_par(value: Option<&str>) -> Par {
    value.map_or_else(Par::default, |value| new_gstring_par(value.into(), Vec::new(), false))
}

pub(crate) fn wire_list(items: Vec<Par>) -> Par {
    let locally_free = items
        .iter()
        .fold(Vec::new(), |acc, item| union(acc, item.locally_free.clone()));
    let connective_used = items.iter().any(|item| item.connective_used);
    new_elist_par(
        items,
        locally_free.clone(),
        connective_used,
        None,
        locally_free,
        connective_used,
    )
}

fn wire_map(entries: Vec<(Par, Par)>) -> Par {
    let locally_free = entries.iter().fold(Vec::new(), |acc, (key, value)| {
        union(acc, union(key.locally_free.clone(), value.locally_free.clone()))
    });
    let connective_used = entries
        .iter()
        .any(|(key, value)| key.connective_used || value.connective_used);
    new_emap_par(
        entries
            .into_iter()
            .map(|(key, value)| new_key_value_pair(key, value))
            .collect(),
        locally_free.clone(),
        connective_used,
        None,
        locally_free,
        connective_used,
    )
}

#[derive(Debug)]
pub(crate) enum FltConstructWireError {
    Shape(&'static str),
    UnsupportedAbi(String),
    IntegerRange,
    DuplicateFill(String),
}

#[derive(Debug, PartialEq, Eq)]
enum LanguageParseWireError {
    Shape(&'static str),
    UnsupportedAbi(String),
}

impl fmt::Display for LanguageParseWireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape(message) => formatter.write_str(message),
            Self::UnsupportedAbi(abi) => {
                write!(formatter, "unsupported language parse ABI `{abi}`")
            },
        }
    }
}

impl fmt::Display for FltConstructWireError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Shape(message) => formatter.write_str(message),
            Self::UnsupportedAbi(abi) => {
                write!(formatter, "unsupported FLT construction ABI `{abi}`")
            },
            Self::IntegerRange => {
                formatter.write_str("FLT hole identifier is outside the u32 range")
            },
            Self::DuplicateFill(name) => write!(formatter, "duplicate FLT fill `{name}`"),
        }
    }
}

fn decode_flt_construct_call(datum: &Par) -> Result<FltConstructCall, FltConstructWireError> {
    let fields = exact_list(datum).ok_or(FltConstructWireError::Shape(
        "expected [abi, handle, pieces, holes, root-category, fills, reply]",
    ))?;
    let [abi, handle, pieces, holes, category, fills, reply] = fields else {
        return Err(FltConstructWireError::Shape(
            "construction request list must have arity seven",
        ));
    };
    let abi = exact_string(abi)
        .ok_or(FltConstructWireError::Shape("construction request ABI must be a string"))?;
    if abi != LANGUAGE_FLT_CONSTRUCT_ABI_V1 {
        return Err(FltConstructWireError::UnsupportedAbi(abi.into()));
    }

    let pieces = exact_list(pieces)
        .ok_or(FltConstructWireError::Shape("FLT pieces must be a proper list"))?
        .iter()
        .map(decode_flt_piece)
        .collect::<Result<Vec<_>, _>>()?;
    let holes = exact_list(holes)
        .ok_or(FltConstructWireError::Shape("FLT holes must be a proper list"))?
        .iter()
        .map(decode_flt_hole)
        .collect::<Result<Vec<_>, _>>()?;
    let category = exact_string(category)
        .ok_or(FltConstructWireError::Shape("root category must be a string"))?;
    if category.is_empty() {
        return Err(FltConstructWireError::Shape("root category must not be empty"));
    }
    let fills = decode_flt_fills(fills)?;
    Ok(FltConstructCall {
        handle: handle.clone(),
        pieces,
        holes,
        category: category.into(),
        fills,
        reply: reply.clone(),
    })
}

fn decode_flt_pattern_call(datum: &Par) -> Result<FltPatternCall, FltConstructWireError> {
    let fields = exact_list(datum).ok_or(FltConstructWireError::Shape(
        "expected [abi, handle, pieces, holes, root-category, reply]",
    ))?;
    let [abi, handle, pieces, holes, category, reply] = fields else {
        return Err(FltConstructWireError::Shape("pattern request list must have arity six"));
    };
    let abi = exact_string(abi)
        .ok_or(FltConstructWireError::Shape("pattern request ABI must be a string"))?;
    if abi != LANGUAGE_FLT_PATTERN_ABI_V1 {
        return Err(FltConstructWireError::UnsupportedAbi(abi.into()));
    }
    let pieces = exact_list(pieces)
        .ok_or(FltConstructWireError::Shape("FLT pieces must be a proper list"))?
        .iter()
        .map(decode_flt_piece)
        .collect::<Result<Vec<_>, _>>()?;
    let holes = exact_list(holes)
        .ok_or(FltConstructWireError::Shape("FLT holes must be a proper list"))?
        .iter()
        .map(decode_flt_hole)
        .collect::<Result<Vec<_>, _>>()?;
    let category = exact_string(category)
        .ok_or(FltConstructWireError::Shape("root category must be a string"))?;
    if category.is_empty() {
        return Err(FltConstructWireError::Shape("root category must not be empty"));
    }
    Ok(FltPatternCall {
        handle: handle.clone(),
        pieces,
        holes,
        category: category.into(),
        reply: reply.clone(),
    })
}

fn decode_language_parse_call(datum: &Par) -> Result<LanguageParseCall, LanguageParseWireError> {
    let fields = exact_list(datum)
        .ok_or(LanguageParseWireError::Shape("expected [abi, handle, source, category, reply]"))?;
    let [abi, handle, source, category, reply] = fields else {
        return Err(LanguageParseWireError::Shape("parse request list must have arity five"));
    };
    let abi = exact_string(abi)
        .ok_or(LanguageParseWireError::Shape("parse request ABI must be a string"))?;
    if abi != LANGUAGE_PARSE_ABI_V1 {
        return Err(LanguageParseWireError::UnsupportedAbi(abi.into()));
    }
    let source = exact_string(source)
        .ok_or(LanguageParseWireError::Shape("parse request source must be a string"))?;
    let category = exact_string(category)
        .ok_or(LanguageParseWireError::Shape("parse request category must be a string"))?;
    if category.is_empty() {
        return Err(LanguageParseWireError::Shape("parse request category must not be empty"));
    }
    Ok(LanguageParseCall {
        handle: handle.clone(),
        source: source.into(),
        category: category.into(),
        reply: reply.clone(),
    })
}

pub(crate) fn decode_flt_piece(value: &Par) -> Result<RuntimeTemplatePiece, FltConstructWireError> {
    let fields =
        exact_list(value).ok_or(FltConstructWireError::Shape("FLT piece must be [kind, value]"))?;
    let [kind, value] = fields else {
        return Err(FltConstructWireError::Shape("FLT piece must have arity two"));
    };
    match exact_string(kind) {
        Some("text") => exact_string(value)
            .map(|text| RuntimeTemplatePiece::Text(text.into()))
            .ok_or(FltConstructWireError::Shape("text piece payload must be a string")),
        Some("hole") => exact_u32(value).map(RuntimeTemplatePiece::Hole),
        _ => Err(FltConstructWireError::Shape("FLT piece kind must be `text` or `hole`")),
    }
}

pub(crate) fn decode_flt_hole(
    value: &Par,
) -> Result<NamedRuntimeTemplateHole, FltConstructWireError> {
    let fields = exact_list(value).ok_or(FltConstructWireError::Shape(
        "FLT hole declaration must be [id, name, category-or-Nil]",
    ))?;
    let [id, name, category] = fields else {
        return Err(FltConstructWireError::Shape("FLT hole declaration must have arity three"));
    };
    Ok(NamedRuntimeTemplateHole {
        id: exact_u32(id)?,
        name: exact_string(name)
            .ok_or(FltConstructWireError::Shape("FLT hole name must be a string"))?
            .into(),
        category: exact_optional_string(category)
            .ok_or(FltConstructWireError::Shape("FLT hole category must be a string or Nil"))?,
    })
}

fn decode_flt_fills(value: &Par) -> Result<BTreeMap<String, Par>, FltConstructWireError> {
    let map =
        exact_map(value).ok_or(FltConstructWireError::Shape("FLT fills must be a proper map"))?;
    let mut fills = BTreeMap::new();
    for pair in map {
        let key = pair
            .key
            .as_ref()
            .and_then(exact_string)
            .ok_or(FltConstructWireError::Shape("FLT fill keys must be strings"))?;
        let fill = pair
            .value
            .as_ref()
            .ok_or(FltConstructWireError::Shape("FLT fill entry has no value"))?;
        if fills.insert(key.into(), fill.clone()).is_some() {
            return Err(FltConstructWireError::DuplicateFill(key.into()));
        }
    }
    Ok(fills)
}

pub(crate) fn exact_list(value: &Par) -> Option<&[Par]> {
    let instance = exact_expr(value)?;
    let ExprInstance::EListBody(list) = instance else {
        return None;
    };
    (list.remainder.is_none()).then_some(list.ps.as_slice())
}

fn exact_map(value: &Par) -> Option<&[models::rhoapi::KeyValuePair]> {
    let instance = exact_expr(value)?;
    let ExprInstance::EMapBody(map) = instance else {
        return None;
    };
    (map.remainder.is_none()).then_some(map.kvs.as_slice())
}

pub(crate) fn exact_string(value: &Par) -> Option<&str> {
    let ExprInstance::GString(value) = exact_expr(value)? else {
        return None;
    };
    Some(value)
}

fn exact_u32(value: &Par) -> Result<u32, FltConstructWireError> {
    let ExprInstance::GInt(value) = exact_expr(value)
        .ok_or(FltConstructWireError::Shape("FLT hole identifier must be an integer"))?
    else {
        return Err(FltConstructWireError::Shape("FLT hole identifier must be an integer"));
    };
    u32::try_from(*value).map_err(|_| FltConstructWireError::IntegerRange)
}

fn exact_optional_string(value: &Par) -> Option<Option<String>> {
    if exact_nil(value) {
        Some(None)
    } else {
        exact_string(value).map(|value| Some(value.into()))
    }
}

fn exact_nil(value: &Par) -> bool {
    value.sends.is_empty()
        && value.receives.is_empty()
        && value.news.is_empty()
        && value.exprs.is_empty()
        && value.matches.is_empty()
        && value.unforgeables.is_empty()
        && value.bundles.is_empty()
        && value.connectives.is_empty()
        && value.conditionals.is_empty()
        && value.locally_free.is_empty()
        && !value.connective_used
}

pub(crate) fn exact_expr(value: &Par) -> Option<&ExprInstance> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.matches.is_empty()
        || !value.unforgeables.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
    {
        return None;
    }
    let [expr] = value.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

fn decode_install_call(mut call: Par) -> Option<(Par, Par)> {
    if !call.sends.is_empty()
        || !call.receives.is_empty()
        || !call.news.is_empty()
        || !call.matches.is_empty()
        || !call.unforgeables.is_empty()
        || !call.bundles.is_empty()
        || !call.connectives.is_empty()
        || !call.conditionals.is_empty()
        || !call.locally_free.is_empty()
        || call.connective_used
    {
        return None;
    }
    if call.exprs.len() != 1 {
        return None;
    }
    let mut expression = call.exprs.pop()?;
    let Some(ExprInstance::EListBody(mut list)) = expression.expr_instance.take() else {
        return None;
    };
    if !list.locally_free.is_empty() || list.connective_used || list.remainder.is_some() {
        return None;
    }
    if list.ps.len() != 2 {
        return None;
    }
    let reply = list.ps.pop()?;
    let specification = list.ps.pop()?;
    Some((specification, reply))
}

fn decode_install_candidate(mut value: Par) -> Result<InstallCandidate, CanonicalValueError> {
    let limits = CanonicalValueLimits::default();
    admit_install_candidate(&value, limits)?;
    let programs = take_staged_module_programs(&mut value)?;
    let value = par_to_canonical_value(&value, limits)?;
    match value {
        RhoValue::Map(ref record)
            if canonical_value_schema(&value) == Some(REGISTRY_MODULE_REFERENCE_V1) =>
        {
            decode_registry_reference(record, REGISTRY_MODULE_REFERENCE_V1)
                .map(InstallCandidate::RegistryModule)
        },
        RhoValue::Map(ref record)
            if canonical_value_schema(&value) == Some(REGISTRY_LANGUAGE_REFERENCE_V1) =>
        {
            decode_registry_reference(record, REGISTRY_LANGUAGE_REFERENCE_V1)
                .map(InstallCandidate::RegistryLanguage)
        },
        RhoValue::Map(_) => Ok(InstallCandidate::Canonical(value)),
        RhoValue::List(_) => {
            let declaration = decode_ddl_value(value).map_err(|error| {
                CanonicalValueError::Shape { path: error.path, message: error.message }
            })?;
            if programs.is_empty() {
                Ok(InstallCandidate::Ddl(declaration))
            } else {
                Ok(InstallCandidate::DdlWithPrograms { declaration, programs })
            }
        },
        _ => shape("$", "expected a canonical language/2 map or DDL envelope"),
    }
}

/// Bound the complete normalized install candidate before any staged process
/// leaf is moved out of its DDL envelope. Both traversals are deterministic
/// heap machines supplied by the Rholang model dependency: the first
/// counts every reachable `Par`, and the second computes the exact protobuf
/// body length in one memoized pass. Neither consumes native stack by input
/// depth, and a staged process cannot escape either charge.
fn admit_install_candidate(
    value: &Par,
    limits: CanonicalValueLimits,
) -> Result<(), CanonicalValueError> {
    let mut nodes = 0usize;
    let mut node_overflow = false;
    visit_canonical_par_tree(value, |_| match nodes.checked_add(1) {
        Some(next) => nodes = next,
        None => node_overflow = true,
    })
    .map_err(|error| CanonicalValueError::Shape {
        path: "$".into(),
        message: format!("install candidate has an invalid canonical PathMap key: {error}"),
    })?;
    if node_overflow || nodes > limits.max_nodes {
        return Err(CanonicalValueError::Limit {
            resource: "install-candidate node",
            limit: limits.max_nodes,
        });
    }

    let encoded_bytes = protobuf_encoder::encoded_len(value);
    if encoded_bytes > limits.max_encoded_bytes {
        return Err(CanonicalValueError::Limit {
            resource: "install-candidate encoded-byte",
            limit: limits.max_encoded_bytes,
        });
    }
    Ok(())
}

/// Move ordinary module processes out of the already-normalized structural
/// envelope and replace them with exact ordinal slots. This is a fixed-depth
/// framing walk; recursive DDL and process structure remain owned by the
/// existing heap-stack lowerer and iterative canonical decoder.
fn take_staged_module_programs(
    value: &mut Par,
) -> Result<Vec<StagedModuleProgram>, CanonicalValueError> {
    let Some(envelope) = exact_closed_list_mut(value) else {
        return Ok(Vec::new());
    };
    if envelope.len() != 2 || exact_string(&envelope[0]) != Some(DDL_AST_ENVELOPE_V2) {
        return Ok(Vec::new());
    }
    let Some(module) = exact_closed_list_mut(&mut envelope[1]) else {
        return Ok(Vec::new());
    };
    if module.len() != 4 || exact_string(&module[0]) != Some("module") {
        return Ok(Vec::new());
    }
    let Some(items) = exact_closed_list_mut(&mut module[3]) else {
        return Ok(Vec::new());
    };
    if items.is_empty() || exact_string(&items[0]) != Some("sequence") {
        return Ok(Vec::new());
    }

    let mut programs = Vec::new();
    for (source_ordinal, item) in items[1..].iter_mut().enumerate() {
        let Some(fields) = exact_closed_list_mut(item) else {
            continue;
        };
        if fields.is_empty() || exact_string(&fields[0]) != Some("module-program") {
            continue;
        }
        if fields.len() != 2 {
            return shape(
                format!("$.module.items[{source_ordinal}]"),
                "module-program requires exactly one process leaf",
            );
        }
        if !fields[1].locally_free.is_empty() {
            return shape(
                format!("$.module.items[{source_ordinal}].program"),
                "staged module process is not closed",
            );
        }
        let slot = programs.len();
        let slot_value = i64::try_from(slot).map_err(|_| CanonicalValueError::Limit {
            resource: "module-program count",
            limit: CanonicalValueLimits::default().max_collection_items,
        })?;
        let process = std::mem::take(&mut fields[1]);
        fields[1] = new_gint_par(slot_value, Vec::new(), false);
        programs.push(StagedModuleProgram { source_ordinal, process });
    }
    Ok(programs)
}

fn exact_closed_list_mut(value: &mut Par) -> Option<&mut Vec<Par>> {
    if !value.sends.is_empty()
        || !value.receives.is_empty()
        || !value.news.is_empty()
        || !value.matches.is_empty()
        || !value.unforgeables.is_empty()
        || !value.bundles.is_empty()
        || !value.connectives.is_empty()
        || !value.conditionals.is_empty()
        || !value.locally_free.is_empty()
        || value.connective_used
    {
        return None;
    }
    let [expression] = value.exprs.as_mut_slice() else {
        return None;
    };
    let Some(ExprInstance::EListBody(list)) = expression.expr_instance.as_mut() else {
        return None;
    };
    if list.remainder.is_some() || !list.locally_free.is_empty() || list.connective_used {
        return None;
    }
    Some(&mut list.ps)
}

fn decode_registry_reference(
    record: &BTreeMap<String, RhoValue>,
    schema: &str,
) -> Result<String, CanonicalValueError> {
    if record.len() != 2 || !record.contains_key("mettail") || !record.contains_key("uri") {
        return shape("$", "a Registry reference requires exactly `mettail` and `uri`");
    }
    let Some(RhoValue::String(uri)) = record.get("uri") else {
        return shape("$.uri", "Registry reference URI must be a string");
    };
    let reference = ModuleRef::parse(uri).map_err(|error| CanonicalValueError::Shape {
        path: "$.uri".into(),
        message: error.to_string(),
    })?;
    if !matches!(reference, ModuleRef::Registry(_)) {
        return shape("$.uri", format!("`{schema}` requires an explicit `rho:` URI"));
    }
    Ok(uri.clone())
}

pub(crate) fn map_par(entries: impl IntoIterator<Item = (String, Par)>) -> Par {
    new_emap_par(
        entries
            .into_iter()
            .map(|(key, value)| new_key_value_pair(new_gstring_par(key, Vec::new(), false), value))
            .collect(),
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    )
}

fn success_response(handle: Par) -> Par {
    map_par([("ok".into(), handle)])
}

fn parse_outcome_response(outcome: LanguageParseOutcome) -> Par {
    let (status, code, alternatives, byte, depth) = match outcome {
        LanguageParseOutcome::Accepted => ("accepted", "Accepted", 1, None, None),
        LanguageParseOutcome::Rejected(reason) => {
            ("rejected", reason.code(), 0, reason.byte(), reason.depth())
        },
        LanguageParseOutcome::Ambiguous { alternatives } => {
            ("ambiguous", "Ambiguous", alternatives, None, None)
        },
        LanguageParseOutcome::Exhausted(resource) => {
            ("exhausted", resource.code(), 0, resource.byte(), None)
        },
    };
    let result = map_par([
        ("status".into(), new_gstring_par(status.into(), Vec::new(), false)),
        ("code".into(), new_gstring_par(code.into(), Vec::new(), false)),
        ("alternatives".into(), new_gint_par(i64::from(alternatives), Vec::new(), false)),
        ("byte".into(), optional_u32_par(byte)),
        ("depth".into(), optional_u32_par(depth)),
    ]);
    map_par([("ok".into(), result)])
}

fn optional_u32_par(value: Option<u32>) -> Par {
    value.map_or_else(Par::default, |value| new_gint_par(i64::from(value), Vec::new(), false))
}

fn success_batch_response(mut batch: RholangInstalledBatch) -> Par {
    if batch.module_name.is_none() && batch.exports.len() == 1 {
        if let Some(export) = batch.exports.pop() {
            return success_response(export.handle);
        }
    }
    let exports = batch
        .exports
        .into_iter()
        .map(|export| {
            map_par([
                ("name".into(), new_gstring_par(export.name, Vec::new(), false)),
                ("handle".into(), export.handle),
            ])
        })
        .collect();
    let programs = batch
        .programs
        .into_iter()
        .map(|program| {
            let ordinal = i64::try_from(program.source_ordinal)
                .expect("canonical DDL collection limits fit a Rholang integer");
            map_par([
                ("ordinal".into(), new_gint_par(ordinal, Vec::new(), false)),
                // A normalized process is also the Rholang representation of
                // its quoted name. The caller must explicitly dereference it;
                // this response never schedules it.
                ("program".into(), program.process),
            ])
        })
        .collect();
    let module = map_par([
        (
            "module".into(),
            batch
                .module_name
                .map_or_else(Par::default, |name| new_gstring_par(name, Vec::new(), false)),
        ),
        ("exports".into(), wire_list(exports)),
        ("programs".into(), wire_list(programs)),
    ]);
    map_par([("ok".into(), module)])
}

pub(crate) fn error_response(code: &str, message: &str) -> Par {
    let message: String = message.chars().take(MAX_PUBLIC_ERROR_CHARS).collect();
    let error = map_par([
        ("code".into(), new_gstring_par(code.into(), Vec::new(), false)),
        ("message".into(), new_gstring_par(message, Vec::new(), false)),
    ]);
    map_par([("error".into(), error)])
}

fn runtime_error_code(error: &LanguageRuntimeError) -> &'static str {
    match error {
        LanguageRuntimeError::Install(InstallServiceError::Surface(_)) => "InvalidSurfaceDdl",
        LanguageRuntimeError::Install(InstallServiceError::StagedProgramShape(_)) => {
            "InvalidStagedProgram"
        },
        LanguageRuntimeError::Install(InstallServiceError::ExportNameMismatch { .. }) => {
            "DeclarationNameMismatch"
        },
        LanguageRuntimeError::Install(InstallServiceError::EmptyExportSet)
        | LanguageRuntimeError::EmptyExportSet => "EmptyExportSet",
        LanguageRuntimeError::Install(InstallServiceError::MultipleExports { .. })
        | LanguageRuntimeError::MultipleExports { .. } => "MultipleExports",
        LanguageRuntimeError::Install(InstallServiceError::Registry(_)) => "RegistryUnavailable",
        LanguageRuntimeError::Install(InstallServiceError::RegistryLanguageNotFound(_)) => {
            "RegistryLanguageNotFound"
        },
        LanguageRuntimeError::Install(InstallServiceError::RegistryModuleNotFound(_)) => {
            "RegistryModuleNotFound"
        },
        LanguageRuntimeError::Install(InstallServiceError::RegistryModuleReference(_)) => {
            "InvalidRegistryModuleReference"
        },
        LanguageRuntimeError::Install(InstallServiceError::RegistryModule(_)) => {
            "InvalidRegistryModule"
        },
        LanguageRuntimeError::Install(InstallServiceError::RegistryTrust(_)) => {
            "RegistryTrustFailure"
        },
        LanguageRuntimeError::Install(InstallServiceError::CanonicalModule(_)) => {
            "InvalidCanonicalModule"
        },
        LanguageRuntimeError::Install(InstallServiceError::Canonical(_)) => {
            "InvalidCanonicalLanguage"
        },
        LanguageRuntimeError::Install(InstallServiceError::CheckerRequirementsUnavailable {
            ..
        }) => "CheckerRequirementsUnavailable",
        LanguageRuntimeError::Install(InstallServiceError::TheoryRightsNotRequested { .. }) => {
            "TheoryRightsNotRequested"
        },
        LanguageRuntimeError::Install(InstallServiceError::Fingerprint(_)) => "FingerprintFailure",
        LanguageRuntimeError::Install(InstallServiceError::Commit(_)) => "InstallConflict",
        LanguageRuntimeError::Install(InstallServiceError::Revoke(_)) => "RevocationFailure",
        LanguageRuntimeError::Install(InstallServiceError::UnknownRevocation(_)) => {
            "UnknownRevocation"
        },
        LanguageRuntimeError::Install(InstallServiceError::InstalledLanguageLimit { .. }) => {
            "InstalledLanguageLimit"
        },
        LanguageRuntimeError::Install(InstallServiceError::Poisoned)
        | LanguageRuntimeError::Poisoned => "ControlPlaneUnavailable",
        LanguageRuntimeError::Access(_) => "AuthorityDenied",
        LanguageRuntimeError::Parse(_) => "LanguageParseFailed",
        LanguageRuntimeError::InvalidHandleShape => "InvalidHandle",
        LanguageRuntimeError::UnknownHandle => "UnknownHandle",
        LanguageRuntimeError::GenerationExhausted => "GenerationExhausted",
        LanguageRuntimeError::UnknownCategory(_) => "UnknownCategory",
        LanguageRuntimeError::DuplicateCategory(_) => "DuplicateCategory",
        LanguageRuntimeError::AlternativeCountOverflow(_) => "AlternativeCountOverflow",
        LanguageRuntimeError::ParseDiagnosticOverflow { .. } => "ParseDiagnosticOverflow",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{
        AdmissionBudget, AdmissionRefutation, AdmissionTheorem, DefaultRuntimeHost, DynamicValue,
        LanguageRight, RuntimeTemplateHole, RuntimeTemplatePiece, SpaceRight, SpaceRights,
        StructuralTheoremChecker,
    };
    use mettail_languages::rholang::Proc;
    use models::rust::utils::{
        new_elist_par, new_emap_par, new_gbytearray_par, new_gint_par, new_gstring_par,
        new_key_value_pair, new_send_par,
    };
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Default)]
    struct MemoryRegistry {
        modules: HashMap<String, RegistryModuleValue>,
        languages: HashMap<String, RegistryLanguageRecord>,
        trust_error: Option<String>,
    }

    impl RegistrySnapshot for MemoryRegistry {
        fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String> {
            Ok(self.modules.get(uri).cloned())
        }

        fn lookup_language(&self, name: &str) -> Result<Option<RegistryLanguageRecord>, String> {
            Ok(self.languages.get(name).cloned())
        }

        fn verify_module_trust(
            &self,
            _uri: &str,
            _signed_payload: &[u8],
            _signatures: &RhoValue,
        ) -> Result<(), String> {
            self.trust_error.clone().map_or(Ok(()), Err)
        }
    }

    struct AlternatingEntryRegistry {
        uri: String,
        first: RegistryModuleValue,
        second: RegistryModuleValue,
        lookups: AtomicUsize,
    }

    impl RegistrySnapshot for AlternatingEntryRegistry {
        fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String> {
            if uri != self.uri {
                return Ok(None);
            }
            let index = self.lookups.fetch_add(1, Ordering::SeqCst);
            Ok(Some(if index == 0 {
                self.first.clone()
            } else {
                self.second.clone()
            }))
        }

        fn lookup_language(&self, _name: &str) -> Result<Option<RegistryLanguageRecord>, String> {
            Ok(None)
        }

        fn verify_module_trust(
            &self,
            _uri: &str,
            _signed_payload: &[u8],
            _signatures: &RhoValue,
        ) -> Result<(), String> {
            Ok(())
        }
    }

    fn s(value: &str) -> RhoValue {
        RhoValue::String(value.into())
    }

    fn map_entry<'a>(value: &'a Par, key: &str) -> Option<&'a Par> {
        exact_map(value)?.iter().find_map(|pair| {
            (pair.key.as_ref().and_then(exact_string) == Some(key))
                .then(|| pair.value.as_ref())
                .flatten()
        })
    }

    fn l(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
        RhoValue::List(values.into_iter().collect())
    }

    fn m(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
        RhoValue::Map(
            values
                .into_iter()
                .map(|(key, value)| (key.into(), value))
                .collect(),
        )
    }

    fn tiny_value(name: &str, rights: RhoValue) -> RhoValue {
        m([
            ("mettail", s("language/2")),
            ("name", s(name)),
            ("rights", rights),
            ("types", l([s("Expr")])),
            (
                "terms",
                l([m([
                    ("label", s("Zero")),
                    ("category", s("Expr")),
                    ("syntax", l([l([s("lit"), s("0")])])),
                ])]),
            ),
        ])
    }

    fn literal_value(name: &str, category: &str, literal: &str, rights: RhoValue) -> RhoValue {
        m([
            ("mettail", s("language/2")),
            ("name", s(name)),
            ("rights", rights),
            ("types", l([s(category)])),
            (
                "terms",
                l([m([
                    ("label", s("Literal")),
                    ("category", s(category)),
                    ("syntax", l([l([s("lit"), s(literal)])])),
                ])]),
            ),
        ])
    }

    fn ambiguous_value(name: &str, rights: RhoValue) -> RhoValue {
        m([
            ("mettail", s("language/2")),
            ("name", s(name)),
            ("rights", rights),
            ("types", l([s("Expr")])),
            (
                "terms",
                l([
                    m([
                        ("label", s("First")),
                        ("category", s("Expr")),
                        ("syntax", l([l([s("lit"), s("0")])])),
                    ]),
                    m([
                        ("label", s("Second")),
                        ("category", s("Expr")),
                        ("syntax", l([l([s("lit"), s("0")])])),
                    ]),
                ]),
            ),
        ])
    }

    fn pair_value(name: &str, rights: RhoValue) -> RhoValue {
        m([
            ("mettail", s("language/2")),
            ("name", s(name)),
            ("rights", rights),
            ("types", l([s("Expr")])),
            (
                "terms",
                l([
                    m([
                        ("label", s("Zero")),
                        ("category", s("Expr")),
                        ("syntax", l([l([s("lit"), s("0")])])),
                    ]),
                    m([
                        ("label", s("One")),
                        ("category", s("Expr")),
                        ("syntax", l([l([s("lit"), s("1")])])),
                    ]),
                    m([
                        ("label", s("Pair")),
                        ("category", s("Expr")),
                        (
                            "context",
                            l([
                                l([s("param"), s("left"), s("Expr")]),
                                l([s("param"), s("right"), s("Expr")]),
                            ]),
                        ),
                        (
                            "syntax",
                            l([
                                l([s("lit"), s("(")]),
                                s("left"),
                                l([s("lit"), s(",")]),
                                s("right"),
                                l([s("lit"), s(")")]),
                            ]),
                        ),
                    ]),
                ]),
            ),
        ])
    }

    fn two_category_value(name: &str, rights: RhoValue) -> RhoValue {
        m([
            ("mettail", s("language/2")),
            ("name", s(name)),
            ("rights", rights),
            ("types", l([s("Expr"), s("Other")])),
            (
                "terms",
                l([
                    m([
                        ("label", s("ExprZero")),
                        ("category", s("Expr")),
                        ("syntax", l([l([s("lit"), s("0")])])),
                    ]),
                    m([
                        ("label", s("OtherZero")),
                        ("category", s("Other")),
                        ("syntax", l([l([s("lit"), s("other")])])),
                    ]),
                ]),
            ),
        ])
    }

    fn registry_module(source: &str) -> RegistryModuleValue {
        let reference = ModuleRef::Registry("rho:test:registry-record".into());
        let resolver =
            mettail_elab::resolve::MemResolver::new().with(&reference.external_form(), source);
        let elaborated = mettail_elab::elaborate_module_languages(&reference, &resolver)
            .expect("test Registry module elaborates");
        let canonical = CanonicalModuleValue::from_rho_value(&elaborated.canonical_value)
            .expect("elaborator emits module/1");
        RegistryModuleValue::new(source, canonical, RhoValue::Nil)
    }

    fn registry_module_with_images(source: &str) -> RegistryModuleValue {
        let mut record = registry_module(source);
        for spec in record.exports.values() {
            let language = mettail_elab::canonical::value_to_language_core(spec)
                .expect("test Registry export lowers");
            let grammar_fingerprint = language
                .grammar_fingerprint()
                .expect("test grammar fingerprints");
            let language_fingerprint = language.fingerprint().expect("test language fingerprints");
            let image = compile_parser_image(&language.grammar)
                .expect("test parser image compiles")
                .encode()
                .expect("test parser image encodes");
            record.images.insert(grammar_fingerprint, image);
            let semantic =
                compile_theory_semantic_image(&language, TheoryImageAdmissionLimits::default())
                    .expect("test semantic image compiles")
                    .encode(&language, TheoryImageAdmissionLimits::default())
                    .expect("test semantic image encodes");
            record
                .semantic_images
                .insert(language_fingerprint, semantic);
        }
        record
    }

    /// Exercise the production inline-DDL path used by Rholang applications:
    /// the generated nouveau-Rholang parser constructs the typed DDL AST, the
    /// iterative lowerer encodes that AST as a closed value, and the installer
    /// decodes the value structurally. No DDL source parser is invoked after the
    /// Rholang parse.
    fn rholang_ddl_par(source: &str) -> Par {
        mettail_runtime::clear_var_cache();
        let proc = Proc::parse_via_wpda(source).expect("nouveau Rholang parses inline DDL");
        crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("typed inline DDL lowers to a closed structural value")
    }

    fn rholang_ddl_candidate(source: &str) -> InstallCandidate {
        let par = rholang_ddl_par(source);
        decode_install_candidate(par).unwrap_or_else(|error| {
            panic!("lowered DDL value satisfies structural admission: {error:?}")
        })
    }

    const SCOPED_MODULE_SOURCE: &str = r#"Module Scoped {
        Theory Left() { Types { Expr; } Terms { L . |- "l" : Expr; } }
        Theory Right() { Types { Expr; } Terms { R . |- "r" : Expr; } }
        Theory Pick(left:Left, right:Right) { let left = right in (left) }
        theory Pick(Left(), Right())
        theory Right()
    }"#;

    const REGEX_EXTENSION_MODULE_SOURCE: &str =
        include_str!("../tests/fixtures/regex_extension.rho");

    fn installed_regex_binding_fixture() -> Arc<mettail_grammar_core::InstalledLanguage> {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let batch = service
            .install_all(rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE))
            .expect("the actual inline Regex module installs");
        service
            .table()
            .authorize(&batch.exports[0].receipt.handle, LanguageRight::Construct)
            .expect("the fixture has an admitted immutable pair")
    }

    fn install_binding_core(
        language: &mettail_grammar_core::LanguageCoreV1,
    ) -> Arc<mettail_grammar_core::InstalledLanguage> {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let value = mettail_elab::core_value::language_core_to_value(language)
            .expect("fixture edit retains a valid canonical language value");
        let receipt = service
            .install(InstallCandidate::Canonical(value))
            .expect("installation must succeed before the adapter representability test");
        service
            .table()
            .authorize(&receipt.handle, LanguageRight::Construct)
            .expect("the modified fixture supplies an admitted pair")
    }

    fn assert_installed_binding_correspondence(
        installed: &mettail_grammar_core::InstalledLanguage,
    ) {
        use crate::installed_flt::{InstalledFltBindings, InstalledFltSort};
        use mettail_grammar_core::{TheoryConstructorId, TheoryLiteralCarrierV1, TheorySortId};
        use mettail_rholang_codegen::ReflectedCodecBudget;

        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        let bindings = InstalledFltBindings::new(installed, &mut budget).expect("binding roster");
        let image = installed.semantic_image().expect("admitted semantic image");
        assert!(std::ptr::eq(bindings.image(), image));
        for (signature, source) in image
            .constructors
            .iter()
            .zip(&installed.language_core().theory.constructors)
        {
            let reverse = bindings
                .constructor_by_id(signature.id, &mut budget)
                .expect("bounded reverse lookup")
                .expect("every image constructor is retained");
            assert!(std::ptr::eq(reverse.signature, signature));
            assert_eq!(reverse.label, source.name);
            assert_eq!(reverse.label.as_ptr(), source.name.as_ptr());
            let forward = bindings
                .constructor(signature.codomain, &source.name, &mut budget)
                .expect("bounded forward lookup")
                .expect("the same complete binding is present");
            assert!(std::ptr::eq(forward.signature, reverse.signature));
            assert_eq!(forward.label, reverse.label);
            assert_eq!(
                bindings
                    .sort_for_category(
                        signature.grammar.expect("exact grammar pair").category,
                        &mut budget
                    )
                    .expect("category mapping"),
                Some(signature.codomain)
            );
        }
        let sort_named = |name: &str| {
            let index = installed
                .language_core()
                .theory
                .sorts
                .iter()
                .position(|sort| sort.name == name)
                .expect("fixture declares requested sort");
            image.sorts[index].id
        };
        for category in &installed.core().categories {
            let sort = bindings
                .sort_for_category(category.id, &mut budget)
                .expect("bounded category lookup")
                .expect("every Regex grammar category has a syntax sort");
            assert_eq!(sort, sort_named(&category.name));
            let Some(InstalledFltSort::Syntax { category: reverse, literal }) = bindings
                .sort(sort, &mut budget)
                .expect("bounded sort lookup")
            else {
                panic!("grammar categories map to syntax sorts");
            };
            assert!(std::ptr::eq(reverse, category));
            let expected = match category.name.as_str() {
                "Scalar" | "Text" => Some(&TheoryLiteralCarrierV1::String),
                "Nat" | "Grade" => Some(&TheoryLiteralCarrierV1::Integer),
                "Bool" => Some(&TheoryLiteralCarrierV1::Boolean),
                _ => None,
            };
            assert_eq!(literal, expected, "exact admitted {} carrier", category.name);
        }
        let pattern = sort_named("Pattern");
        let scalar = sort_named("Scalar");
        let literal = bindings
            .constructor(pattern, "PLiteral", &mut budget)
            .expect("literal lookup")
            .expect("literal constructor");
        assert_eq!(literal.signature.domain, [scalar]);
        let concat = bindings
            .constructor(pattern, "PConcat", &mut budget)
            .expect("concat lookup")
            .expect("concat constructor");
        assert_eq!(concat.signature.domain, [pattern, pattern]);
        for label in ["BFalse", "BTrue"] {
            assert!(bindings
                .constructor(sort_named("Bool"), label, &mut budget)
                .expect("Boolean constructors coexist with the native carrier")
                .is_some());
        }
        assert!(bindings
            .constructor(scalar, "PLiteral", &mut budget)
            .expect("wrong sort")
            .is_none());
        assert!(bindings
            .constructor(pattern, "Missing", &mut budget)
            .expect("missing label")
            .is_none());
        assert!(bindings
            .constructor_by_id(TheoryConstructorId(u32::MAX), &mut budget)
            .expect("bad ID")
            .is_none());
        assert!(bindings
            .sort(TheorySortId(u32::MAX), &mut budget)
            .expect("bad sort")
            .is_none());
        assert_eq!(
            bindings
                .sort_for_category(CategoryId(u32::MAX), &mut budget)
                .expect("bad category"),
            None
        );
    }

    #[test]
    fn installed_flt_bindings_retain_actual_regex_signatures_and_native_sorts() {
        let installed = installed_regex_binding_fixture();
        assert_installed_binding_correspondence(&installed);
    }

    #[test]
    fn installed_flt_bindings_join_names_after_sort_reordering() {
        let original = installed_regex_binding_fixture();
        let mut language = original.language_core().clone();
        language.theory.sorts.reverse();
        let installed = install_binding_core(&language);
        assert_ne!(
            installed.language_core().theory.sorts[0].name,
            installed.core().categories[0].name,
            "fixture must expose ordinal coincidence"
        );
        assert_installed_binding_correspondence(&installed);
    }

    #[test]
    fn installed_flt_bindings_allow_repeated_productions_without_duplicate_entries() {
        let original = installed_regex_binding_fixture();
        let mut language = original.language_core().clone();
        let mut repeated = language.grammar.productions[0].clone();
        repeated.id = mettail_grammar_core::ProductionId(
            u32::try_from(language.grammar.productions.len()).expect("small fixture"),
        );
        language.grammar.productions.push(repeated);
        let installed = install_binding_core(&language);
        assert_eq!(
            installed
                .semantic_image()
                .expect("image")
                .constructors
                .len(),
            original
                .semantic_image()
                .expect("original image")
                .constructors
                .len()
        );
        assert_installed_binding_correspondence(&installed);
    }

    #[test]
    fn installed_flt_bindings_reject_global_grammar_constructor_aliases() {
        use crate::installed_flt::{InstalledFltBindingError, InstalledFltBindings};
        use mettail_rholang_codegen::ReflectedCodecBudget;

        let original = installed_regex_binding_fixture();
        let mut language = original.language_core().clone();
        let shared = language.grammar.productions[0].constructor;
        let mut production = language.grammar.productions[0].clone();
        let mut constructor = language
            .theory
            .constructors
            .iter()
            .find(|entry| entry.name == production.label)
            .expect("paired declaration")
            .clone();
        production.id = mettail_grammar_core::ProductionId(
            u32::try_from(language.grammar.productions.len()).expect("small fixture"),
        );
        production.label = "ConflictingAlias".into();
        constructor.name = production.label.clone();
        // Keep the original dense constructor roster and matching reduction;
        // the added label is the only new representability violation.
        language.grammar.productions.push(production);
        language.theory.constructors.push(constructor);
        let installed = install_binding_core(&language);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        assert!(matches!(
            InstalledFltBindings::new(&installed, &mut budget),
            Err(InstalledFltBindingError::ConflictingGrammarLabel(id)) if id == shared
        ));
    }

    #[test]
    fn installed_flt_bindings_reject_reserved_constructor_namespace() {
        use crate::installed_flt::{InstalledFltBindingError, InstalledFltBindings};
        use mettail_rholang_codegen::ReflectedCodecBudget;

        let original = installed_regex_binding_fixture();
        let mut language = original.language_core().clone();
        // Add a valid ordinary theory constructor; do not corrupt a rule term
        // or image fingerprint to manufacture a pre-installation rejection.
        let mut production = language.grammar.productions[0].clone();
        let mut constructor = language
            .theory
            .constructors
            .iter()
            .find(|entry| entry.name == production.label)
            .expect("paired constructor")
            .clone();
        production.id = mettail_grammar_core::ProductionId(
            u32::try_from(language.grammar.productions.len()).expect("small fixture"),
        );
        production.constructor = mettail_grammar_core::ConstructorId(
            language
                .grammar
                .productions
                .iter()
                .map(|entry| entry.constructor.0)
                .max()
                .expect("constructors")
                + 1,
        );
        production.label = "^dynamic-text:61".into();
        constructor.name = production.label.clone();
        let mut reduction = language.grammar.reductions[production.reduction as usize].clone();
        reduction.constructor = production.constructor;
        production.reduction =
            u32::try_from(language.grammar.reductions.len()).expect("small fixture");
        language.grammar.reductions.push(reduction);
        language.grammar.productions.push(production);
        language.theory.constructors.push(constructor);
        let installed = install_binding_core(&language);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        assert!(matches!(
            InstalledFltBindings::new(&installed, &mut budget),
            Err(InstalledFltBindingError::ReservedConstructorLabel(_))
        ));
    }

    #[test]
    fn installed_flt_bindings_preserve_theory_only_sort_as_unsupported() {
        use crate::installed_flt::{InstalledFltBindings, InstalledFltSort};
        use mettail_grammar_core::{TheorySortKindImageV1, TheorySortKindV1, TheorySortV1};
        use mettail_rholang_codegen::ReflectedCodecBudget;

        let original = installed_regex_binding_fixture();
        let mut language = original.language_core().clone();
        language.theory.sorts.push(TheorySortV1 {
            name: "PrivateRuntimeState".into(),
            kind: TheorySortKindV1::Opaque { abi: "fixture-only/1".into() },
        });
        let installed = install_binding_core(&language);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        let bindings = InstalledFltBindings::new(&installed, &mut budget)
            .expect("non-Syntax sort is not a blanket rejection");
        let sort = installed
            .semantic_image()
            .expect("image")
            .sorts
            .last()
            .expect("extra sort");
        let Some(InstalledFltSort::Unsupported(shape)) =
            bindings.sort(sort.id, &mut budget).expect("sort lookup")
        else {
            panic!("theory-only opaque sort must not be fabricated as syntax");
        };
        assert!(std::ptr::eq(shape, &sort.kind));
        assert!(matches!(shape, TheorySortKindImageV1::Opaque { abi } if abi == "fixture-only/1"));
        assert_installed_binding_correspondence(&installed);
    }

    #[test]
    fn installed_flt_bindings_charge_setup_and_lookup_without_resetting_work() {
        use crate::installed_flt::{InstalledFltBindingError, InstalledFltBindings};
        use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};

        let installed = installed_regex_binding_fixture();
        let mut work = 7;
        let mut calls = 0;
        let mut cancelled = || {
            calls += 1;
            false
        };
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        let bindings = InstalledFltBindings::new(&installed, &mut budget).expect("bounded setup");
        let setup_work = budget.work_used();
        let remaining = budget.finish();
        let setup_calls = calls;
        let image = installed.semantic_image().expect("image");
        let exact_payload = 13 * installed.core().categories.len()
            + 5 * image.sorts.len()
            + 8 * installed.core().productions.len()
            + 20 * image.constructors.len();
        assert_eq!(1_000_000 - remaining, exact_payload, "fixed logical coordinate-slot schedule");
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, setup_work, remaining, &mut cancelled);
        assert!(matches!(
            bindings.constructor_by_id(bindings.image().constructors[0].id, &mut budget),
            Err(InstalledFltBindingError::Resource(DynamicReflectionError::WorkLimit))
        ));
        assert_eq!(budget.work_used(), setup_work);
        budget.finish();
        for cancel_at in 1..=setup_calls {
            let mut calls = 0;
            let mut cancelled = || {
                calls += 1;
                calls == cancel_at
            };
            let mut work = 7;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
            assert!(
                matches!(
                    InstalledFltBindings::new(&installed, &mut budget),
                    Err(InstalledFltBindingError::Resource(DynamicReflectionError::Cancelled))
                ),
                "cancel at {cancel_at}"
            );
            assert!(budget.work_used() >= 7);
            assert!(budget.work_used() <= setup_work);
        }
        let mut work = 7;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 0, &mut cancelled);
        assert!(matches!(
            InstalledFltBindings::new(&installed, &mut budget),
            Err(InstalledFltBindingError::Resource(DynamicReflectionError::PayloadByteLimit))
        ));
        assert_eq!(
            budget.work_used(),
            8,
            "allocation fails after only the initial operation charge"
        );
        budget.finish();
        for allowance in [exact_payload - 1, exact_payload] {
            let mut work = 7;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 1_000_000, allowance, &mut cancelled);
            match (allowance == exact_payload, InstalledFltBindings::new(&installed, &mut budget)) {
                (true, Ok(_)) => assert_eq!(budget.remaining_bytes(), 0),
                (
                    false,
                    Err(InstalledFltBindingError::Resource(
                        DynamicReflectionError::PayloadByteLimit,
                    )),
                ) => {
                    assert_eq!(
                        budget.remaining_bytes(),
                        12 * image.constructors.len() - 1,
                        "failed final reservation does not consume a partial slot allowance"
                    );
                },
                _ => panic!("exact index payload boundary"),
            }
        }
    }

    #[test]
    fn installed_flt_bindings_do_not_invent_a_missing_semantic_image() {
        use crate::installed_flt::{InstalledFltBindingError, InstalledFltBindings};
        use mettail_rholang_codegen::ReflectedCodecBudget;

        // The executable LanguageInstallService intentionally installs both
        // images even for a theory without actions. Use the existing parser-only
        // table API to exercise its genuine no-semantic-image case.
        let core =
            mettail_elab::canonical::value_to_core(&tiny_value("SyntaxOnly", l([s("Construct")])))
                .expect("structural core");
        let parser_image = compile_parser_image(&core).expect("parser image");
        let table = InstalledLanguageTable::new();
        let grant = table
            .install_runtime(
                core,
                parser_image,
                LanguageRights::from_rights([LanguageRight::Construct]),
                RUNTIME_COMPILER_ABI,
                RUNTIME_UNICODE_ABI,
                LANGUAGE_CAPABILITY_ABI_V1,
                [0; 32],
            )
            .expect("parser-only installation");
        let installed = table
            .authorize(&grant.handle, LanguageRight::Construct)
            .expect("installed language");
        assert!(installed.semantic_image().is_none());
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, 0, &mut cancelled);
        assert!(matches!(
            InstalledFltBindings::new(&installed, &mut budget),
            Err(InstalledFltBindingError::MissingSemanticImage)
        ));
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (1, 0));
    }

    #[test]
    fn canonical_install_intersects_requests_with_host_authority() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let service = LanguageInstallService::new(Arc::new(MemoryRegistry::default()), policy);
        let receipt = service
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse"), s("Bridge")]))))
            .expect("valid language installs");
        assert!(receipt.requested_rights.contains(LanguageRight::Bridge));
        assert!(receipt.granted_rights.contains(LanguageRight::Parse));
        assert!(!receipt.granted_rights.contains(LanguageRight::Bridge));
        let parses = service
            .parse(&receipt.handle, "0", None, &DefaultRuntimeHost)
            .expect("granted parse works");
        assert_eq!(parses.len(), 1);
    }

    #[test]
    fn greg_surface_and_canonical_value_share_the_installed_identity() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let surface = r#"Module Tiny {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let from_surface = service
            .install(rholang_ddl_candidate(surface))
            .expect("surface installs");
        let from_value = service
            .install(InstallCandidate::Canonical(tiny_value(
                "T",
                l([
                    s("Parse"),
                    s("Construct"),
                    s("Match"),
                    s("Observe"),
                    s("ReflectAst"),
                    s("Reduce"),
                ]),
            )))
            .expect("canonical value installs");
        assert_eq!(from_surface.fingerprint, from_value.fingerprint);
        assert_eq!(service.installed_count().unwrap(), 1);
    }

    #[test]
    fn greg_surface_and_canonical_value_lower_to_the_exact_same_language_core() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let surface = r#"Module Tiny {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let canonical = tiny_value(
            "T",
            l([
                s("Parse"),
                s("Construct"),
                s("Match"),
                s("Observe"),
                s("ReflectAst"),
                s("Reduce"),
            ]),
        );

        let mut surface_records = service
            .canonical_records(rholang_ddl_candidate(surface))
            .expect("Greg surface elaborates to one canonical record")
            .records;
        let mut value_records = service
            .canonical_records(InstallCandidate::Canonical(canonical))
            .expect("language/2 value supplies one canonical record")
            .records;
        assert_eq!(surface_records.len(), 1);
        assert_eq!(value_records.len(), 1);
        let surface_spec = surface_records.pop().expect("one surface record").1.spec;
        let value_spec = value_records.pop().expect("one value record").1.spec;
        let surface_core = mettail_elab::canonical::value_to_language_core(&surface_spec)
            .expect("surface canonical value lowers to LanguageCore");
        let value_core = mettail_elab::canonical::value_to_language_core(&value_spec)
            .expect("programmatic canonical value lowers to LanguageCore");

        assert_eq!(surface_core, value_core, "L0 and L1 must lower to the same complete core");
        let surface_bytes = mettail_elab::core_value::language_core_to_data_fragment(&surface_core)
            .expect("surface core has a closed canonical value")
            .canonical_bytes();
        let value_bytes = mettail_elab::core_value::language_core_to_data_fragment(&value_core)
            .expect("programmatic core has a closed canonical value")
            .canonical_bytes();
        assert_eq!(surface_bytes, value_bytes, "L0/L1 canonical bytes must be identical");
    }

    #[test]
    fn generated_root_parser_accepts_only_complete_module_derivations() {
        let _service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );

        fn is_named_module(term: &Proc, expected: &str) -> bool {
            matches!(term, Proc::DdlModule(name, _) if name == expected)
                || matches!(term, Proc::DdlModuleImported(_, name, _) if name == expected)
        }

        let cases = [
            ("complete-cold", SCOPED_MODULE_SOURCE),
            ("empty", "Module Scoped { }"),
            (
                "one-declaration",
                r#"Module Scoped {
                    Theory Left() { Types { Expr; } Terms { L . |- "l" : Expr; } }
                }"#,
            ),
            (
                "two-declarations",
                r#"Module Scoped {
                    Theory Left() { Types { Expr; } Terms { L . |- "l" : Expr; } }
                    Theory Right() { Types { Expr; } Terms { R . |- "r" : Expr; } }
                }"#,
            ),
            (
                "parameterized-declaration",
                r#"Module Scoped {
                    Theory Left() { Types { Expr; } Terms { L . |- "l" : Expr; } }
                    Theory Right() { Types { Expr; } Terms { R . |- "r" : Expr; } }
                    Theory Pick(left:Left, right:Right) { let left = right in (left) }
                }"#,
            ),
        ];

        let mut failures = Vec::new();
        for (label, source) in cases {
            mettail_runtime::clear_var_cache();
            let best = Proc::parse_via_wpda(source);
            mettail_runtime::clear_var_cache();
            let all = Proc::parse_via_wpda_all_with_weights(source);

            let best_is_complete = best
                .as_ref()
                .is_ok_and(|term| is_named_module(term, "Scoped"));
            let all_are_complete = all.as_ref().is_ok_and(|(terms, _)| {
                !terms.is_empty() && terms.iter().all(|term| is_named_module(term, "Scoped"))
            });
            if !best_is_complete || !all_are_complete {
                failures.push(format!("{label}: best={best:?}; all={all:?}",));
            }
        }

        assert!(
            failures.is_empty(),
            "root parser elected or exposed an incomplete derivation:\n{}",
            failures.join("\n"),
        );
    }

    #[test]
    fn theory_parameters_and_let_bindings_are_lexical_and_shadow_correctly() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let records = service
            .canonical_records(rholang_ddl_candidate(SCOPED_MODULE_SOURCE))
            .expect("well-scoped parameters and lexical shadowing elaborate")
            .records;
        assert_eq!(records.len(), 2);
        let picked = mettail_elab::canonical::value_to_language_core(&records[0].1.spec)
            .expect("selected theory lowers");
        let right = mettail_elab::canonical::value_to_language_core(&records[1].1.spec)
            .expect("reference theory lowers");
        assert_eq!(picked.grammar.name, "Pick");
        assert_eq!(right.grammar.name, "Right");

        fn erase_export_name(
            mut language: mettail_grammar_core::LanguageCoreV1,
        ) -> mettail_grammar_core::LanguageCoreV1 {
            language.grammar.name.clear();
            language
        }

        assert_eq!(
            erase_export_name(picked),
            erase_export_name(right),
            "the derived `Pick` artifact must retain its own export name while every semantic field denotes the lexically bound `right` value",
        );

        let leaking = r#"Module Leaking {
            Theory Base() { Types { Expr; } Terms { X . |- "x" : Expr; } }
            Theory Bad() { (let local = Base() in (local)) /\ local }
            theory Bad()
        }"#;
        let error = match service.canonical_records(rholang_ddl_candidate(leaking)) {
            Ok(_) => panic!("a let-bound theory name must not escape its lexical body"),
            Err(error) => error,
        };
        assert!(
            matches!(
                error,
                InstallServiceError::Surface(mettail_elab::Diag {
                    kind: mettail_elab::DiagKind::Resolution,
                    ..
                })
            ),
            "out-of-scope reference must fail as a resolution error, got {error:?}",
        );
    }

    #[test]
    fn generated_rholang_entrypoint_installs_exact_core_data_without_reparse() {
        let rights = l([
            s("Parse"),
            s("Construct"),
            s("Match"),
            s("Observe"),
            s("ReflectAst"),
            s("Reduce"),
        ]);
        let canonical = tiny_value("Tiny", rights);
        let expected = mettail_elab::canonical::value_to_language_core(&canonical)
            .expect("test language lowers to LanguageCore");
        let fragment = mettail_elab::core_value::language_core_to_data_fragment(&expected)
            .expect("LanguageCore has a closed Data fragment");
        let literal = mettail_elab::rholang_literal::render_rholang_value_literal(&fragment)
            .expect("Data fragment has a canonical Rholang spelling");
        let surface = format!("Theory Tiny() {{ Data({literal}) }}");
        let candidate = rholang_ddl_candidate(&surface);

        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let from_surface = service
            .install(candidate)
            .expect("generated-entrypoint exact Data theory installs");
        let from_value = service
            .install(InstallCandidate::Canonical(canonical))
            .expect("canonical presentation installs");

        assert_eq!(from_surface.fingerprint, from_value.fingerprint);
        assert_eq!(from_surface.fingerprint, expected.fingerprint().unwrap());
        assert_eq!(service.installed_count().unwrap(), 1);
    }

    #[test]
    fn module_exports_install_atomically_as_distinct_language_capabilities() {
        let surface = r#"Module Pair {
            Theory Left() { Types { L; } Terms { L0 . |- "l" : L; } }
            Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
            theory Left()
            theory Right()
        }"#;
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let batch = service
            .install_all(rholang_ddl_candidate(surface))
            .expect("both exports install");

        assert_eq!(batch.module_name.as_deref(), Some("Pair"));
        assert_eq!(
            batch
                .exports
                .iter()
                .map(|export| export.name.as_str())
                .collect::<Vec<_>>(),
            ["Left", "Right"]
        );
        assert_eq!(service.installed_count().expect("count"), 2);
        assert_eq!(
            service
                .parse(&batch.exports[0].receipt.handle, "l", None, &DefaultRuntimeHost)
                .expect("left parser")
                .len(),
            1
        );
        assert_eq!(
            service
                .parse(&batch.exports[1].receipt.handle, "r", None, &DefaultRuntimeHost)
                .expect("right parser")
                .len(),
            1
        );

        let rejecting = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        assert!(matches!(
            rejecting.install(rholang_ddl_candidate(surface)),
            Err(InstallServiceError::MultipleExports { count: 2 })
        ));
        assert_eq!(rejecting.installed_count().expect("count"), 0);
    }

    #[test]
    fn regex_gslt_module_compiles_and_installs_both_runtime_images_atomically() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );

        let candidate = rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE);
        let canonical = service
            .canonical_records(candidate)
            .expect("the generated Rholang entrypoint elaborates the composed Regex module");
        assert_eq!(canonical.module_name.as_deref(), Some("RegexExtension"));
        assert_eq!(canonical.records.len(), 1);
        let language =
            mettail_elab::canonical::value_to_language_core(&canonical.records[0].1.spec)
                .expect("the Regex export lowers to one complete LanguageCore");
        assert_eq!(language.grammar.name, "Regex");
        assert_eq!(language.theory.profile, mettail_grammar_core::TheoryProfileV1::Oslf);
        assert_eq!(language.theory.equations.len(), 9);
        assert_eq!(language.theory.rewrites.len(), 3);
        assert_eq!(language.theory.actions.len(), 3);
        assert_eq!(language.theory.judgments.len(), 1);
        assert!(language.grammar.semantic_program.equations.is_empty());
        assert!(language.grammar.semantic_program.rewrites.is_empty());

        let binding_power = |label: &str| {
            language
                .grammar
                .productions
                .iter()
                .find(|production| production.label == label)
                .and_then(|production| production.precedence.binding_power)
        };
        assert_eq!(binding_power("PAlt"), Some(10));
        assert_eq!(binding_power("PConcat"), Some(20));
        assert_eq!(binding_power("PStar"), Some(30));
        assert_eq!(binding_power("PPlus"), Some(30));
        assert_eq!(binding_power("POptional"), Some(30));

        let batch = service
            .install_all(rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE))
            .expect("Regex parser and semantic images compile, verify, and commit together");
        assert_eq!(batch.module_name.as_deref(), Some("RegexExtension"));
        assert_eq!(batch.exports.len(), 1);
        let receipt = &batch.exports[0].receipt;
        assert_eq!(batch.exports[0].name, "Regex");
        assert_eq!(receipt.cache_disposition, ParserCacheDisposition::CompiledMissing);
        assert_eq!(receipt.semantic_cache_disposition, SemanticCacheDisposition::CompiledMissing);
        assert_eq!(service.table().installed_count().expect("table readable"), 1);
        assert_eq!(service.installed_count().expect("revocations readable"), 1);

        let installed = service
            .table()
            .authorize(&receipt.handle, LanguageRight::Parse)
            .expect("the opaque Regex handle authorizes parsing");
        assert_eq!(installed.language_core(), &language);
        let parser_image = installed
            .parser_image()
            .expect("runtime parser image is installed");
        let semantic_image = installed
            .semantic_image()
            .expect("semantic image is installed");
        assert_eq!(parser_image.core_fingerprint, language.grammar_fingerprint().unwrap());
        assert_eq!(semantic_image.language_fingerprint, language.fingerprint().unwrap());
        assert_eq!(semantic_image.grammar_fingerprint, language.grammar_fingerprint().unwrap());
        assert_eq!(semantic_image.theory_fingerprint, language.theory_fingerprint().unwrap());
        assert_eq!(semantic_image.actions.len(), 3);
        assert_eq!(semantic_image.judgments.len(), 1);
        assert_eq!(
            installed.commitment().parser_limits_fingerprint,
            Some(service.policy().parser_image.fingerprint())
        );
        assert_eq!(
            installed.commitment().semantic_limits_fingerprint,
            Some(service.policy().semantic_image.fingerprint())
        );

        let pattern_category = installed
            .core()
            .categories
            .iter()
            .find(|category| category.name == "Pattern")
            .expect("Regex declares its Pattern entrypoint")
            .id;
        let scalar_category = installed
            .core()
            .categories
            .iter()
            .find(|category| category.name == "Scalar")
            .expect("Regex declares its Scalar literal category")
            .id;
        let scalar_rules = parser_image.engine.rules_for(scalar_category.0);
        assert_eq!(scalar_rules.len(), 1);
        assert_eq!(scalar_rules[0].semantic, mettail_grammar_core::RuntimeRuleSemantic::TokenValue);
        assert_eq!(scalar_rules[0].production, None);
        let scalar = service
            .parse(&receipt.handle, "a", Some(scalar_category), &DefaultRuntimeHost)
            .expect("declared literal inhabits Scalar without an invented constructor");
        assert_eq!(scalar.len(), 1);
        assert_eq!(scalar[0].value, mettail_grammar_core::DynamicValue::Text("a".into()));
        assert_eq!(scalar[0].syntax, scalar[0].value);
        let epsilon = service
            .parse(&receipt.handle, "eps", Some(pattern_category), &DefaultRuntimeHost)
            .expect("the explicit epsilon constructor still parses");
        let pattern_parses: Vec<_> = ["a", "a*", "a+", "a?", "ab", "a|b", "(a|b)*"]
            .into_iter()
            .map(|source| {
                (
                    source,
                    service.parse(
                        &receipt.handle,
                        source,
                        Some(pattern_category),
                        &DefaultRuntimeHost,
                    ),
                )
            })
            .collect();
        // The declared literal `eps` overlaps three Scalar literals. Both
        // meanings survive; only the association forbidden by Left/20 is
        // rejected. Token priority is ranking, not authority to erase either.
        let term = |label: &str, start, end, fields| {
            let production = language
                .grammar
                .productions
                .iter()
                .find(|production| production.label == label)
                .expect("declared constructor");
            mettail_grammar_core::DynamicValue::Term(Box::new(mettail_grammar_core::DynamicTerm {
                category: production.result,
                constructor: production.constructor,
                fields,
                span: mettail_grammar_core::SourceSpan { start, end },
            }))
        };
        let literal = |text: &str, start| {
            term(
                "PLiteral",
                start,
                start + 1,
                vec![mettail_grammar_core::DynamicValue::Text(text.into())],
            )
        };
        let left_associated = |a: &str, b: &str, c: &str| {
            term(
                "PConcat",
                0,
                3,
                vec![term("PConcat", 0, 2, vec![literal(a, 0), literal(b, 1)]), literal(c, 2)],
            )
        };
        assert_eq!(epsilon.len(), 2, "epsilon candidates: {epsilon:#?}");
        assert_eq!(epsilon[0].syntax, term("PEpsilon", 0, 3, vec![]));
        assert_eq!(epsilon[1].syntax, left_associated("e", "p", "s"));
        for candidate in &epsilon {
            assert_eq!(candidate.syntax, candidate.value);
        }
        let abc = service
            .parse(&receipt.handle, "abc", Some(pattern_category), &DefaultRuntimeHost)
            .expect("three literals obey declared concatenation associativity");
        assert_eq!(abc.len(), 1);
        assert_eq!(abc[0].syntax, left_associated("a", "b", "c"));
        for (source, result) in pattern_parses {
            let parses =
                result.unwrap_or_else(|error| panic!("Regex `{source}` parses: {error:?}"));
            assert_eq!(parses.len(), 1, "Regex `{source}` has one precedence-resolved parse");
        }
    }

    fn assert_installed_regex_literal_fill(category: &str, admits_variables: bool) {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let batch = runtime
            .install_all(rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE))
            .expect("the real inline Regex module installs");
        let token = &batch
            .exports
            .iter()
            .find(|export| export.name == "Regex")
            .expect("the module exports its Regex theory")
            .handle;
        let fill = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Text("a".into())],
                &[],
                Some(category),
                &BTreeMap::new(),
            )
            .expect("the installed parser and reflector construct the literal-bearing value");
        let handle = runtime
            .resolve(token, LanguageRight::Construct)
            .expect("the installed handle grants construction");
        let installed = runtime
            .service
            .table()
            .authorize(&handle, LanguageRight::Construct)
            .expect("the same language remains installed");
        let category_definition = installed
            .core()
            .categories
            .iter()
            .find(|definition| definition.name == category)
            .expect("the requested category is declared");
        assert_eq!(
            category_definition.admits_variables, admits_variables,
            "the regression must preserve the declared {category} hole policy"
        );
        let admission = DynamicSyntaxAdmission::compile(installed.core())
            .expect("the installed grammar's structural automaton compiles");
        assert!(
            admission.admits_category(
                &fill,
                &grammar_fingerprint_label(handle.fingerprint()),
                category_definition.id,
            ),
            "the installed {category} category must admit its parsed reflected value",
        );
        // Scalar deliberately forbids template variables. Test its membership
        // without bypassing that policy; Pattern also exercises actual filling.
        if !admits_variables {
            return;
        }
        let constructed = runtime
            .construct_template(
                token,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "literal".into(),
                    category: Some(category.into()),
                }],
                Some(category),
                &BTreeMap::from([("literal".into(), fill.clone())]),
            )
            .expect("the same installed category admits its parsed structural fill");
        assert_eq!(constructed, fill, "a typed fill must preserve the existing reflected value");
    }

    #[test]
    fn installed_regex_literal_fill_preserves_direct_scalar_category() {
        assert_installed_regex_literal_fill("Scalar", false);
    }

    #[test]
    fn installed_regex_literal_fill_preserves_nested_pattern_category() {
        assert_installed_regex_literal_fill("Pattern", true);
    }

    #[test]
    fn installed_regex_boolean_carrier_admits_computed_values_without_lexical_tokens() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let batch = runtime
            .install_all(rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE))
            .expect("the inline Regex module installs");
        let token = &batch
            .exports
            .iter()
            .find(|export| export.name == "Regex")
            .expect("Regex is exported")
            .handle;
        let handle = runtime
            .resolve(token, LanguageRight::Construct)
            .expect("the installed handle grants construction");
        let installed = runtime
            .service
            .table()
            .authorize(&handle, LanguageRight::Construct)
            .expect("the language remains installed");
        let core = installed.core();
        let category = core
            .categories
            .iter()
            .find(|category| category.name == "Bool")
            .expect("the theory declares the Boolean result category");
        assert_eq!(
            category.carrier,
            mettail_grammar_core::Carrier::Builtin(mettail_grammar_core::BuiltinCarrier::Boolean)
        );
        assert!(
            core.tokens
                .iter()
                .all(|token| token.category != Some(category.id)),
            "this regression requires a carrier without a lexical token"
        );
        let admission = DynamicSyntaxAdmission::compile(core).expect("the automaton compiles");
        let fingerprint = grammar_fingerprint_label(handle.fingerprint());
        for value in [false, true] {
            let ground = dynamic_syntax_to_ground_term(
                &mettail_grammar_core::DynamicValue::Boolean(value),
                core,
                &BTreeMap::new(),
            )
            .expect("the existing reflector encodes native Boolean results");
            let reflected = mettail_rholang_codegen::reflect_ground_term_par(&ground, &fingerprint);
            assert!(admission.admits_category(&reflected, &fingerprint, category.id));
        }
    }

    #[test]
    fn module_programs_stage_in_source_order_and_release_only_after_commit() {
        let source = r#"Module Programmed {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            @"first"!(0)
            theory T()
            @"second"!(0)
        }"#;
        let candidate = rholang_ddl_candidate(source);
        let InstallCandidate::DdlWithPrograms { declaration, programs } = candidate else {
            panic!("ordinary module Proc items must use the staged structural path")
        };
        assert_eq!(
            programs
                .iter()
                .map(|program| program.source_ordinal)
                .collect::<Vec<_>>(),
            [1, 3]
        );
        assert!(programs
            .iter()
            .all(|program| program.process.sends.len() == 1));

        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let batch = service
            .install_all(InstallCandidate::DdlWithPrograms { declaration, programs })
            .expect("the language batch commits before staged programs are released");
        assert_eq!(batch.exports.len(), 1);
        assert_eq!(
            batch
                .programs
                .iter()
                .map(|program| program.source_ordinal)
                .collect::<Vec<_>>(),
            [1, 3]
        );
        assert_eq!(service.installed_count().expect("count"), 1);
    }

    #[test]
    fn staged_module_program_is_charged_before_extraction() {
        let source = r#"Module Programmed {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            @"first"!(0)
            theory T()
        }"#;
        let candidate = rholang_ddl_par(source);
        let mut stripped = candidate.clone();
        let programs = take_staged_module_programs(&mut stripped)
            .expect("well-formed module process staging succeeds");
        assert_eq!(programs.len(), 1);

        let count_nodes = |value: &Par| {
            let mut nodes = 0usize;
            visit_canonical_par_tree(value, |_| nodes += 1)
                .expect("generated Rholang values have canonical PathMap keys");
            nodes
        };
        let candidate_nodes = count_nodes(&candidate);
        let stripped_nodes = count_nodes(&stripped);
        assert!(
            candidate_nodes > stripped_nodes,
            "the process leaf must contribute to whole-candidate admission"
        );

        let node_limited = CanonicalValueLimits {
            max_nodes: stripped_nodes,
            ..CanonicalValueLimits::default()
        };
        assert!(matches!(
            admit_install_candidate(&candidate, node_limited),
            Err(CanonicalValueError::Limit { resource: "install-candidate node", .. })
        ));
        admit_install_candidate(&stripped, node_limited)
            .expect("the same node limit admits the envelope after extraction");

        let candidate_bytes = protobuf_encoder::encoded_len(&candidate);
        let byte_limited = CanonicalValueLimits {
            max_encoded_bytes: candidate_bytes - 1,
            ..CanonicalValueLimits::default()
        };
        assert!(matches!(
            admit_install_candidate(&candidate, byte_limited),
            Err(CanonicalValueError::Limit {
                resource: "install-candidate encoded-byte",
                ..
            })
        ));
    }

    #[test]
    fn staged_program_reference_mismatch_fails_before_installation() {
        let source = r#"Module Programmed {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            @"first"!(0)
            theory T()
        }"#;
        let InstallCandidate::DdlWithPrograms { declaration, mut programs } =
            rholang_ddl_candidate(source)
        else {
            panic!("expected a staged module program")
        };
        programs[0].source_ordinal += 1;
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        assert!(matches!(
            service.install_all(InstallCandidate::DdlWithPrograms { declaration, programs }),
            Err(InstallServiceError::StagedProgramShape(_))
        ));
        assert_eq!(service.installed_count().expect("count"), 0);
    }

    #[test]
    fn rholang_module_result_preserves_source_order_and_opaque_handles() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let source = r#"Module Pair {
            Theory Left() { Types { L; } Terms { L0 . |- "l" : L; } }
            Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
            theory Left()
            theory Right()
        }"#;
        let batch = runtime
            .install_all(rholang_ddl_candidate(source))
            .expect("module installs");

        assert_eq!(batch.module_name.as_deref(), Some("Pair"));
        assert_eq!(
            batch
                .exports
                .iter()
                .map(|export| export.name.as_str())
                .collect::<Vec<_>>(),
            ["Left", "Right"]
        );
        for export in batch.exports {
            assert!(private_name_id(&export.handle).is_some());
            assert!(runtime
                .resolve(&export.handle, LanguageRight::Parse)
                .is_ok());
        }
    }

    #[test]
    fn parse_source_is_scoped_to_one_opaque_handle_and_explicit_category() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let left = runtime
            .install(InstallCandidate::Canonical(literal_value(
                "Left",
                "LeftExpr",
                "l",
                l([s("Parse")]),
            )))
            .expect("left language installs");
        let right = runtime
            .install(InstallCandidate::Canonical(literal_value(
                "Right",
                "RightExpr",
                "r",
                l([s("Parse")]),
            )))
            .expect("right language installs");

        assert!(matches!(
            runtime.parse_source(&left, "l", "LeftExpr"),
            Ok(LanguageParseOutcome::Accepted)
        ));
        assert!(matches!(
            runtime.parse_source(&right, "r", "RightExpr"),
            Ok(LanguageParseOutcome::Accepted)
        ));
        assert!(matches!(
            runtime.parse_source(&left, "r", "LeftExpr"),
            Ok(LanguageParseOutcome::Rejected(_))
        ));
        assert!(matches!(
            runtime.parse_source(&right, "l", "RightExpr"),
            Ok(LanguageParseOutcome::Rejected(_))
        ));
        assert!(matches!(
            runtime.parse_source(&left, "l", "RightExpr"),
            Err(LanguageRuntimeError::UnknownCategory(name)) if name == "RightExpr"
        ));
    }

    #[test]
    fn parse_source_distinguishes_ambiguity_exhaustion_and_rejection() {
        let ambiguous = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let handle = ambiguous
            .install(InstallCandidate::Canonical(ambiguous_value("Ambiguous", l([s("Parse")]))))
            .expect("ambiguous grammar installs");
        assert!(matches!(
            ambiguous.parse_source(&handle, "0", "Expr"),
            Ok(LanguageParseOutcome::Ambiguous { alternatives: 2 })
        ));
        assert!(matches!(
            ambiguous.parse_source(&handle, "1", "Expr"),
            Ok(LanguageParseOutcome::Rejected(LanguageParseRejection::Lex { byte: 0 }))
        ));

        let policy = LanguageInstallPolicy::new(
            LanguageRights::all(),
            RuntimePolicy {
                max_input_bytes: 0,
                ..RuntimePolicy::default()
            },
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let exhausted = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let handle = exhausted
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse")]))))
            .expect("bounded grammar installs");
        assert!(matches!(
            exhausted.parse_source(&handle, "0", "Expr"),
            Ok(LanguageParseOutcome::Exhausted(LanguageParseExhaustion::InputBytes))
        ));
    }

    #[test]
    fn pattern_preparation_rejects_ambiguous_structural_meanings() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let handle = runtime
            .install(InstallCandidate::Canonical(ambiguous_value(
                "Ambiguous",
                l([s("Parse"), s("Match")]),
            )))
            .expect("ambiguous grammar installs");
        let result = runtime.prepare_pattern(
            &handle,
            &[RuntimeTemplatePiece::Text("0".into())],
            &[],
            Some("Expr"),
        );
        assert!(
            matches!(result, Err(LanguageFltConstructionError::AmbiguousPattern)),
            "unexpected pattern-preparation result: {result:?}",
        );
    }

    #[test]
    fn parse_source_rejects_attenuated_revoked_and_non_handle_values() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Construct]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let attenuated = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let token = attenuated
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse")]))))
            .expect("the specification cannot amplify host grants");
        assert!(matches!(
            attenuated.parse_source(&token, "0", "Expr"),
            Err(LanguageRuntimeError::Access(LanguageAccessError::MissingRight(
                LanguageRight::Parse
            )))
        ));

        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value("Revocable", l([s("Parse")]))))
            .expect("language installs");
        runtime.revoke(&token).expect("language revokes");
        assert!(matches!(
            runtime.parse_source(&token, "0", "Expr"),
            Err(LanguageRuntimeError::UnknownHandle)
        ));

        for non_handle in ["Tiny", "rho:registry:Tiny", "mettail-grammar-core-v1:deadbeef"] {
            let value = new_gstring_par(non_handle.into(), Vec::new(), false);
            assert!(matches!(
                runtime.parse_source(&value, "0", "Expr"),
                Err(LanguageRuntimeError::InvalidHandleShape)
            ));
        }
        let legacy_private = private_name([LANGUAGE_HANDLE_DOMAIN_V1, b"legacy"].concat());
        assert!(matches!(
            runtime.parse_source(&legacy_private, "0", "Expr"),
            Err(LanguageRuntimeError::InvalidHandleShape)
        ));
        let unknown_private = private_name([LANGUAGE_HANDLE_DOMAIN_CURRENT, b"unknown"].concat());
        assert!(matches!(
            runtime.parse_source(&unknown_private, "0", "Expr"),
            Err(LanguageRuntimeError::UnknownHandle)
        ));
    }

    #[test]
    fn surface_imports_resolve_only_through_the_registry_snapshot() {
        let base = r#"Module Base {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let main = r#"import "rho:base" as b
            Module Main { theory b.T() }"#;
        let registry = MemoryRegistry {
            modules: HashMap::from([("rho:base".into(), registry_module(base))]),
            languages: HashMap::new(),
            trust_error: None,
        };
        let service =
            LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
        service
            .install(rholang_ddl_candidate(main))
            .expect("registry import installs");

        let file_import = r#"import "file:base.module" as b
            Module Main { theory b.T() }"#;
        let error = service
            .install(rholang_ddl_candidate(file_import))
            .expect_err("ambient filesystem access stays unavailable");
        assert!(error
            .to_string()
            .contains("future Rholang File I/O capability"));
    }

    #[test]
    fn failed_installation_publishes_nothing() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let error = service
            .install(InstallCandidate::Canonical(m([
                ("mettail", s("language/2")),
                ("name", s("Broken")),
                ("types", l([s("Expr")])),
                (
                    "terms",
                    l([m([
                        ("label", s("Bad")),
                        ("category", s("Missing")),
                        ("syntax", l([l([s("lit"), s("x")])])),
                    ])]),
                ),
            ])))
            .expect_err("invalid grammar must fail");
        assert!(error.to_string().contains("canonical language rejected"));
        assert_eq!(service.installed_count().unwrap(), 0);
    }

    #[test]
    fn identical_grammar_with_distinct_theories_installs_distinct_full_language_handles() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let source = |effect: &str| {
            format!(
                r#"Theory T() {{
                    Types {{ Expr; }}
                    Terms {{ Zero . |- "0" : Expr; }}
                    Data({{
                      "oslf": {{
                        "effects": [{{"name":"{effect}","requires":[],"emits":[]}}]
                      }}
                    }})
                }}"#,
            )
        };
        let left = service
            .install(rholang_ddl_candidate(&source("LeftEffect")))
            .expect("first full language installs");
        let right = service
            .install(rholang_ddl_candidate(&source("RightEffect")))
            .expect("same grammar with a distinct theory also installs");

        assert_ne!(left.fingerprint, right.fingerprint);
        assert_eq!(service.table().installed_count().expect("table readable"), 2);
        let left_language = service
            .table()
            .authorize(&left.handle, LanguageRight::Parse)
            .expect("left handle authorizes");
        let right_language = service
            .table()
            .authorize(&right.handle, LanguageRight::Parse)
            .expect("right handle authorizes");
        assert_eq!(left_language.core(), right_language.core());
        assert_ne!(left_language.language_core().theory, right_language.language_core().theory,);
        assert!(left_language.semantic_image().is_some());
        assert!(right_language.semantic_image().is_some());
        assert_eq!(
            left_language.commitment().parser_limits_fingerprint,
            Some(service.policy().parser_image.fingerprint()),
        );
    }

    #[test]
    fn theory_actions_cannot_amplify_the_installation_manifest() {
        let service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let source = r#"Theory Attenuated() {
            Types { Expr; Grade; }
            Terms { Zero . |- "0" : Expr; }
            Data({
              "rights": ["Parse"],
              "oslf": {
                "effects": [{"name":"Pure","requires":[],"emits":[]}],
                "actions": [{
                  "id":"step", "domain":["Expr"], "codomain":"Expr",
                  "transition":["handler","mtl:test:step/1"],
                  "effect":"Pure", "effect_class":"pure",
                  "required_rights":["Reduce"], "grade":"Grade",
                  "execution":"one_step"
                }]
              }
            })
        }"#;
        let result = service.install(rholang_ddl_candidate(source));
        assert!(
            matches!(
                &result,
                Err(InstallServiceError::TheoryRightsNotRequested { ref action })
                    if action == "step"
            ),
            "unexpected installation result: {result:?}"
        );
        assert_eq!(service.table().installed_count().expect("table readable"), 0);
        assert_eq!(service.installed_count().expect("revocations readable"), 0);
    }

    #[test]
    fn parser_and_semantic_artifacts_are_admitted_before_atomic_publication() {
        let language = mettail_elab::elaborate_theory_language(
            r#"Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }"#,
        )
        .expect("test language elaborates")
        .language_core;
        let parser_image = compile_parser_image(&language.grammar).expect("parser compiles");
        let semantic_limits = TheoryImageAdmissionLimits::default();
        let semantic_image = compile_theory_semantic_image(&language, semantic_limits)
            .expect("semantic image compiles");

        #[derive(Clone, Copy, Debug)]
        enum StaleAbi {
            Parser,
            ParserCompiler,
            Unicode,
            Semantic,
            SemanticCompiler,
            PrimitiveSubstrate,
        }
        for stale in [
            StaleAbi::Parser,
            StaleAbi::ParserCompiler,
            StaleAbi::Unicode,
            StaleAbi::Semantic,
            StaleAbi::SemanticCompiler,
            StaleAbi::PrimitiveSubstrate,
        ] {
            let table = InstalledLanguageTable::new();
            let valid = ExecutableLanguageInstall {
                language: language.clone(),
                parser_image: parser_image.clone(),
                semantic_image: semantic_image.clone(),
                granted_rights: LanguageRights::all(),
            };
            let mut invalid = ExecutableLanguageInstall {
                language: language.clone(),
                parser_image: parser_image.clone(),
                semantic_image: semantic_image.clone(),
                granted_rights: LanguageRights::all(),
            };
            match stale {
                StaleAbi::Parser => invalid.parser_image.abi = 0,
                StaleAbi::ParserCompiler => invalid.parser_image.compiler_abi = "stale".into(),
                StaleAbi::Unicode => invalid.parser_image.unicode_version = "stale".into(),
                StaleAbi::Semantic => invalid.semantic_image.abi = 0,
                StaleAbi::SemanticCompiler => invalid.semantic_image.compiler_abi = 0,
                StaleAbi::PrimitiveSubstrate => invalid.semantic_image.primitive_substrate_abi = 0,
            }
            let result = table.install_executable_runtime_batch(
                vec![valid, invalid],
                RUNTIME_COMPILER_ABI,
                RUNTIME_UNICODE_ABI,
                LANGUAGE_CAPABILITY_ABI_CURRENT,
                [0; 32],
                semantic_limits,
            );
            use mettail_grammar_core::{ImageError, TheoryImageError};
            assert!(
                matches!(
                    (stale, &result),
                    (
                        StaleAbi::Parser,
                        Err(InstallLanguageError::InvalidImage(ImageError::UnsupportedAbi(0)))
                    ) | (
                        StaleAbi::ParserCompiler,
                        Err(InstallLanguageError::InvalidImage(ImageError::CompilerAbiMismatch))
                    ) | (
                        StaleAbi::Unicode,
                        Err(InstallLanguageError::InvalidImage(ImageError::UnicodeVersionMismatch))
                    ) | (
                        StaleAbi::Semantic,
                        Err(InstallLanguageError::InvalidTheoryImage(
                            TheoryImageError::UnsupportedAbi(0)
                        ))
                    ) | (
                        StaleAbi::SemanticCompiler,
                        Err(InstallLanguageError::InvalidTheoryImage(
                            TheoryImageError::UnsupportedCompilerAbi(0)
                        ))
                    ) | (
                        StaleAbi::PrimitiveSubstrate,
                        Err(InstallLanguageError::InvalidTheoryImage(
                            TheoryImageError::UnsupportedPrimitiveSubstrateAbi(0)
                        ))
                    )
                ),
                "{stale:?} must reject the batch before publishing its valid prefix: {:?}",
                result.as_ref().err()
            );
            assert_eq!(table.installed_count().expect("table readable"), 0);
        }

        let table = InstalledLanguageTable::new();
        let mut bad_semantic = semantic_image.clone();
        bad_semantic.language_fingerprint = [0xff; 32];
        let semantic_result = table.install_executable_runtime_batch(
            vec![
                ExecutableLanguageInstall {
                    language: language.clone(),
                    parser_image: parser_image.clone(),
                    semantic_image: semantic_image.clone(),
                    granted_rights: LanguageRights::all(),
                },
                ExecutableLanguageInstall {
                    language: language.clone(),
                    parser_image: parser_image.clone(),
                    semantic_image: bad_semantic,
                    granted_rights: LanguageRights::all(),
                },
            ],
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            LANGUAGE_CAPABILITY_ABI_V1,
            [0; 32],
            semantic_limits,
        );
        assert!(matches!(semantic_result, Err(InstallLanguageError::InvalidTheoryImage(_))));
        assert_eq!(table.installed_count().expect("table readable"), 0);

        let table = InstalledLanguageTable::new();
        let parser_limits = ParserImageAdmissionLimits {
            max_runtime_rules: 0,
            ..ParserImageAdmissionLimits::default()
        };
        let parser_limit_result = table
            .install_executable_runtime_batch_with_artifact_limits_and_host(
                vec![ExecutableLanguageInstall {
                    language: language.clone(),
                    parser_image: parser_image.clone(),
                    semantic_image: semantic_image.clone(),
                    granted_rights: LanguageRights::all(),
                }],
                RUNTIME_COMPILER_ABI,
                RUNTIME_UNICODE_ABI,
                LANGUAGE_CAPABILITY_ABI_CURRENT,
                [0; 32],
                parser_limits,
                semantic_limits,
                &DefaultRuntimeHost,
            );
        assert!(matches!(
            parser_limit_result,
            Err(InstallLanguageError::InvalidImage(
                mettail_grammar_core::ImageError::ImageLimitExceeded("runtime rules")
            ))
        ));
        assert_eq!(table.installed_count().expect("table readable"), 0);

        let table = InstalledLanguageTable::new();
        let mut bad_parser = parser_image.clone();
        bad_parser.core_fingerprint = [0xff; 32];
        let parser_result = table.install_executable_runtime_batch(
            vec![
                ExecutableLanguageInstall {
                    language: language.clone(),
                    parser_image,
                    semantic_image: semantic_image.clone(),
                    granted_rights: LanguageRights::all(),
                },
                ExecutableLanguageInstall {
                    language,
                    parser_image: bad_parser,
                    semantic_image,
                    granted_rights: LanguageRights::all(),
                },
            ],
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            LANGUAGE_CAPABILITY_ABI_V1,
            [0; 32],
            semantic_limits,
        );
        assert!(matches!(parser_result, Err(InstallLanguageError::InvalidImage(_))));
        assert_eq!(table.installed_count().expect("table readable"), 0);
    }

    #[test]
    fn semantic_artifact_budget_rejection_preserves_both_installation_tables() {
        for seed_existing in [false, true] {
            let policy = LanguageInstallPolicy::with_language_and_semantic_limits(
                LanguageRights::all(),
                RuntimePolicy::default(),
                TheoryImageAdmissionLimits {
                    max_actions: 0,
                    ..TheoryImageAdmissionLimits::default()
                },
                1_024,
                LANGUAGE_CAPABILITY_ABI_CURRENT,
            );
            let service = LanguageInstallService::new(Arc::new(MemoryRegistry::default()), policy);
            let existing = seed_existing.then(|| {
                service
                    .install(InstallCandidate::Canonical(tiny_value("Existing", l([s("Parse")]))))
                    .expect("a structural language fits the zero-action budget")
            });
            let before = usize::from(seed_existing);
            assert_eq!(service.table().installed_count().expect("table readable"), before);
            assert_eq!(service.installed_count().expect("revocations readable"), before);
            let result = service.install_all(rholang_ddl_candidate(REGEX_EXTENSION_MODULE_SOURCE));
            assert!(
                matches!(
                    &result,
                    Err(InstallServiceError::Canonical(
                        InstallExecutableRegistryError::CompileSemantic(
                            TheoryImageCompileError::Image(
                                mettail_grammar_core::TheoryImageError::LimitExceeded("actions")
                            )
                        )
                    ))
                ),
                "the real Regex action image must exceed the zero-action budget: {result:?}"
            );
            assert_eq!(service.table().installed_count().expect("table readable"), before);
            assert_eq!(service.installed_count().expect("revocations readable"), before);
            if let Some(existing) = existing {
                assert!(service
                    .table()
                    .authorize(&existing.handle, LanguageRight::Parse)
                    .is_ok());
            }
        }
    }

    #[test]
    fn installed_language_limit_rejection_preserves_both_installation_tables() {
        for limit in [0_u64, 1] {
            let policy = LanguageInstallPolicy::with_language_limit(
                LanguageRights::all(),
                RuntimePolicy::default(),
                limit,
                LANGUAGE_CAPABILITY_ABI_CURRENT,
            );
            let service = LanguageInstallService::new(Arc::new(MemoryRegistry::default()), policy);
            let existing = (limit == 1).then(|| {
                service
                    .install(InstallCandidate::Canonical(tiny_value("Existing", l([s("Parse")]))))
                    .expect("the first language fits the one-language limit")
            });
            let before = usize::try_from(limit).expect("small test limit");
            assert_eq!(service.table().installed_count().expect("table readable"), before);
            assert_eq!(service.installed_count().expect("revocations readable"), before);
            let result =
                service.install(InstallCandidate::Canonical(tiny_value("Excess", l([s("Parse")]))));
            assert!(
                matches!(
                    &result,
                    Err(InstallServiceError::InstalledLanguageLimit { limit: actual })
                        if *actual == limit
                ),
                "the language-count limit must reject before publishing: {result:?}"
            );
            assert_eq!(service.table().installed_count().expect("table readable"), before);
            assert_eq!(service.installed_count().expect("revocations readable"), before);
            if let Some(existing) = existing {
                assert!(service
                    .table()
                    .authorize(&existing.handle, LanguageRight::Parse)
                    .is_ok());
            }
        }
    }

    #[test]
    fn canonical_module_value_and_surface_module_have_identical_exports() {
        let source = r#"Module Pair {
            Theory Left() { Types { L; } Terms { L0 . |- "l" : L; } }
            Theory Right() { Types { R; } Terms { R0 . |- "r" : R; } }
            theory Left()
            theory Right()
        }"#;
        let reference = ModuleRef::Registry("rho:test:canonical-parity".into());
        let resolver =
            mettail_elab::resolve::MemResolver::new().with(&reference.external_form(), source);
        let canonical = mettail_elab::elaborate_module_languages(&reference, &resolver)
            .expect("surface module elaborates")
            .canonical_value;

        let surface_service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let surface = surface_service
            .install_all(rholang_ddl_candidate(source))
            .expect("surface module installs");
        let canonical_service = LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        );
        let direct = canonical_service
            .install_all(InstallCandidate::Canonical(canonical))
            .expect("canonical module installs");

        assert_eq!(surface.module_name, direct.module_name);
        assert_eq!(
            surface
                .exports
                .iter()
                .map(|export| (&export.name, export.receipt.fingerprint))
                .collect::<Vec<_>>(),
            direct
                .exports
                .iter()
                .map(|export| (&export.name, export.receipt.fingerprint))
                .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn registry_module_reference_reuses_only_fingerprint_selected_images() {
        let source = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let registry = MemoryRegistry {
            modules: HashMap::from([("rho:stored".into(), registry_module_with_images(source))]),
            ..MemoryRegistry::default()
        };
        let service =
            LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
        let batch = service
            .install_all(InstallCandidate::RegistryModule("rho:stored".into()))
            .expect("trusted Registry module installs");
        assert_eq!(batch.module_name.as_deref(), Some("Stored"));
        assert_eq!(batch.exports.len(), 1);
        assert_eq!(batch.exports[0].name, "T");
        assert_eq!(
            batch.exports[0].receipt.cache_disposition,
            ParserCacheDisposition::ReusedVerified,
        );
        assert_eq!(
            batch.exports[0].receipt.semantic_cache_disposition,
            SemanticCacheDisposition::ReusedVerified,
        );
    }

    #[test]
    fn registry_module_recompiles_an_invalid_selected_unsigned_cache() {
        let source = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let mut record = registry_module(source);
        let module =
            CanonicalModuleValue::from_rho_value(&record.module).expect("test module is canonical");
        let core = mettail_elab::canonical::value_to_core(&module.exports[0].spec)
            .expect("test export lowers");
        let fingerprint = core.fingerprint().expect("test export fingerprints");
        record.images.insert(fingerprint, Vec::new());
        let registry = MemoryRegistry {
            modules: HashMap::from([("rho:stored".into(), record)]),
            ..MemoryRegistry::default()
        };
        let service =
            LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
        let batch = service
            .install_all(InstallCandidate::RegistryModule("rho:stored".into()))
            .expect("invalid unsigned cache is discarded and deterministically recompiled");
        assert_eq!(batch.exports.len(), 1);
        assert!(matches!(
            batch.exports[0].receipt.cache_disposition,
            ParserCacheDisposition::RecompiledRejected { .. }
        ));
        assert_eq!(service.installed_count().expect("table readable"), 1);
    }

    #[test]
    fn registry_entry_is_fetched_once_per_installation_snapshot() {
        let first_source = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let second_source = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { One . |- "1" : Expr; } }
            theory T()
        }"#;
        let registry = Arc::new(AlternatingEntryRegistry {
            uri: "rho:stored".into(),
            first: registry_module(first_source),
            second: registry_module(second_source),
            lookups: AtomicUsize::new(0),
        });
        let service =
            LanguageInstallService::new(registry.clone(), LanguageInstallPolicy::default());
        let batch = service
            .install_all(InstallCandidate::RegistryModule("rho:stored".into()))
            .expect("one pinned entry record must drive verification, elaboration, and install");
        assert_eq!(batch.exports.len(), 1);
        assert_eq!(registry.lookups.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn registry_trust_failure_prevents_every_export_from_becoming_visible() {
        let source = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let registry = MemoryRegistry {
            modules: HashMap::from([("rho:stored".into(), registry_module(source))]),
            trust_error: Some("signature threshold not met".into()),
            ..MemoryRegistry::default()
        };
        let service =
            LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
        let error = service
            .install_all(InstallCandidate::RegistryModule("rho:stored".into()))
            .expect_err("untrusted module fails closed");
        assert!(matches!(error, InstallServiceError::RegistryTrust(_)));
        assert_eq!(service.installed_count().expect("control plane readable"), 0);
        assert_eq!(service.table().installed_count().expect("table readable"), 0);
    }

    #[test]
    fn registry_source_oracle_cannot_override_signed_canonical_content() {
        let authoritative = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        let substituted = r#"Module Stored {
            Theory T() { Types { Expr; } Terms { One . |- "1" : Expr; } }
            theory T()
        }"#;
        let mut record = registry_module(authoritative);
        record.source = substituted.into();
        record.source_commitment = *blake3::hash(substituted.as_bytes()).as_bytes();
        record
            .validate_source_oracle()
            .expect("the substituted source is internally committed but remains non-authoritative");
        let registry = MemoryRegistry {
            modules: HashMap::from([("rho:stored".into(), record)]),
            ..MemoryRegistry::default()
        };
        let service =
            LanguageInstallService::new(Arc::new(registry), LanguageInstallPolicy::default());
        let batch = service
            .install_all(InstallCandidate::RegistryModule("rho:stored".into()))
            .expect("signed canonical module installs without parsing the source oracle");
        let handle = &batch.exports[0].receipt.handle;
        assert_eq!(
            service
                .parse(handle, "0", None, &DefaultRuntimeHost)
                .expect("canonical parser accepts its own source")
                .len(),
            1,
        );
        assert!(
            service
                .parse(handle, "1", None, &DefaultRuntimeHost)
                .is_err(),
            "source-oracle grammar is not installed",
        );
    }

    #[test]
    fn registry_reference_values_require_an_explicit_rho_uri() {
        let valid = BTreeMap::from([
            ("mettail".into(), RhoValue::String(REGISTRY_MODULE_REFERENCE_V1.into())),
            ("uri".into(), RhoValue::String("rho:stored".into())),
        ]);
        assert_eq!(
            decode_registry_reference(&valid, REGISTRY_MODULE_REFERENCE_V1),
            Ok("rho:stored".into()),
        );
        let invalid = BTreeMap::from([
            ("mettail".into(), RhoValue::String(REGISTRY_MODULE_REFERENCE_V1.into())),
            ("uri".into(), RhoValue::String("file:stored.module".into())),
        ]);
        assert!(decode_registry_reference(&invalid, REGISTRY_MODULE_REFERENCE_V1).is_err());
    }

    #[test]
    fn par_decoder_is_closed_and_preserves_numeric_kinds() {
        let key = new_gstring_par("answer".into(), Vec::new(), false);
        let value = new_gint_par(42, Vec::new(), false);
        let par = new_emap_par(
            vec![new_key_value_pair(key, value)],
            Vec::new(),
            false,
            None,
            Vec::new(),
            false,
        );
        assert_eq!(
            par_to_canonical_value(&par, CanonicalValueLimits::default()).unwrap(),
            m([("answer", RhoValue::Integer(42))])
        );
    }

    #[test]
    fn par_decoder_preserves_byte_arrays_and_bounds_them_before_cloning() {
        let bytes = new_gbytearray_par(vec![0xde, 0xad], Vec::new(), false);
        assert_eq!(
            par_to_canonical_value(&bytes, CanonicalValueLimits::default()).unwrap(),
            RhoValue::Bytes(vec![0xde, 0xad]),
        );
        let limits = CanonicalValueLimits {
            max_byte_array_bytes: 1,
            ..CanonicalValueLimits::default()
        };
        assert!(matches!(
            par_to_canonical_value(&bytes, limits),
            Err(CanonicalValueError::Limit { resource: "byte-array byte", limit: 1 })
        ));
    }

    #[test]
    fn nouveau_rholang_theory_lowers_to_the_structural_installer_envelope() {
        assert!(matches!(
            rholang_ddl_candidate("Theory T() { Empty }"),
            InstallCandidate::Ddl(ParsedDdl::Theory(ref theory)) if theory.name == "T"
        ));
    }

    #[test]
    fn nouveau_rholang_module_lowers_to_the_structural_installer_envelope() {
        let source = r#"Module Tiny {
            Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
            theory T()
        }"#;
        assert!(matches!(
            rholang_ddl_candidate(source),
            InstallCandidate::Ddl(ParsedDdl::Module(ref module)) if module.name == "Tiny"
        ));
    }

    #[test]
    fn official_uri_binder_lowers_to_the_installer_system_channel() {
        mettail_runtime::clear_var_cache();
        let proc = Proc::parse_via_wpda("new install(`rho:mettail:install`) in { install!(Nil) }")
            .expect("nouveau Rholang parses the official URI binder");
        let par = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("the URI-bound installer call lowers");
        assert_eq!(par.news.len(), 1, "one URI binder produces one New");
        let new = &par.news[0];
        assert_eq!(new.bind_count, 1);
        assert_eq!(new.uri, [LANGUAGE_INSTALL_URN]);
        let body = new.p.as_ref().expect("New retains its body");
        assert_eq!(body.sends.len(), 1, "the body retains the installer send");
        assert_eq!(
            body.sends[0].chan.as_ref().expect("send channel").exprs[0].expr_instance,
            Some(ExprInstance::EVarBody(models::rhoapi::EVar {
                v: Some(models::rhoapi::Var {
                    var_instance: Some(models::rhoapi::var::VarInstance::BoundVar(0)),
                }),
            })),
            "the URI declaration binds the send channel at de-Bruijn level zero",
        );
    }

    #[tokio::test]
    async fn rholang_program_installs_ddl_through_the_uri_capability() {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let language_runtime = Arc::new(RholangLanguageRuntime::new(service.clone()));
        let source = r#"
            new install(`rho:mettail:install`) in {
              new ret in {
                install!(
                  Module Tiny {
                    Theory T() { Types { Expr; } Terms { Zero . |- "0" : Expr; } }
                    theory T()
                  },
                  *ret
                ) |
                for(@result <- ret) { @"OUT"!(result) }
              }
            }
        "#;
        let proc = Proc::parse_via_wpda(source).expect("complete installer program parses");
        let par = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("complete installer program lowers");
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &par,
            vec![language_install_definition(language_runtime)],
            &["OUT"],
        )
        .await
        .expect("installer definition executes");
        assert_eq!(service.installed_count().unwrap(), 1, "installer handler commits");
        let out = outputs.get("OUT").expect("OUT channel was requested");
        assert_eq!(out.len(), 1, "the installer replies exactly once");
        let ExprInstance::EMapBody(map) = out[0]
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
            .expect("installer reply is a map")
        else {
            panic!("installer reply must be an EMap");
        };
        assert_eq!(map.kvs.len(), 1);
        let installed_module = map_entry(&out[0], "ok").expect("success payload exists");
        assert_eq!(map_entry(installed_module, "module").and_then(exact_string), Some("Tiny"),);
        let exports = map_entry(installed_module, "exports")
            .and_then(exact_list)
            .expect("module exports are a proper list");
        assert_eq!(exports.len(), 1);
        assert_eq!(map_entry(&exports[0], "name").and_then(exact_string), Some("T"));
        assert!(matches!(
            map_entry(&exports[0], "handle")
                .and_then(|value| value.unforgeables.first())
                .and_then(|unforgeable| unforgeable.unf_instance.as_ref()),
            Some(GPrivateBody(_)),
        ));
    }

    #[tokio::test]
    async fn rholang_program_parses_guest_text_through_its_lexical_handle() {
        mettail_runtime::clear_var_cache();
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ))));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse")]))))
            .expect("language installs");
        let source = r#"
            for(language <- @"HANDLE") {
              new parse(`rho:mettail:parse`) in {
                new ret in {
                  parse!(["mettail-language-parse/1", *language, "0", "Expr", *ret]) |
                  for(@result <- ret) { @"OUT"!(result) }
                }
              }
            }
        "#;
        let proc = Proc::parse_via_wpda(source).expect("parse-capability program parses");
        let par =
            crate::rholang_ast::lower_rholang_proc(&proc).expect("parse-capability program lowers");
        let handle_send = new_send_par(
            new_gstring_par("HANDLE".into(), Vec::new(), false),
            vec![handle],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &par.append(handle_send),
            language_runtime_definitions(runtime),
            &["OUT"],
        )
        .await
        .expect("parse definition executes");
        let [response] = outputs.get("OUT").expect("OUT was requested").as_slice() else {
            panic!("the parser replies exactly once")
        };
        let result = map_entry(response, "ok").expect("parse operation succeeds");
        assert_eq!(map_entry(result, "status").and_then(exact_string), Some("accepted"));
        assert_eq!(map_entry(result, "code").and_then(exact_string), Some("Accepted"));
    }

    #[tokio::test]
    async fn rholang_parse_errors_are_stable_data_not_forged_authority() {
        mettail_runtime::clear_var_cache();
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ))));
        let source = r#"
            new parse(`rho:mettail:parse`) in {
              new ret in {
                parse!(["mettail-language-parse/1", "Tiny", "0", "Expr", *ret]) |
                for(@result <- ret) { @"OUT"!(result) }
              }
            }
        "#;
        let proc = Proc::parse_via_wpda(source).expect("forged-handle program parses");
        let par =
            crate::rholang_ast::lower_rholang_proc(&proc).expect("forged-handle program lowers");
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &par,
            language_runtime_definitions(runtime),
            &["OUT"],
        )
        .await
        .expect("authority refusal is returned as data");
        let [response] = outputs.get("OUT").expect("OUT was requested").as_slice() else {
            panic!("the parser replies exactly once")
        };
        let error = map_entry(response, "error").expect("forged string is rejected");
        assert_eq!(map_entry(error, "code").and_then(exact_string), Some("InvalidHandle"));
    }

    #[test]
    fn capability_tokens_are_reused_then_invalidated_across_revocation() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = RholangLanguageRuntime::new(service);
        let candidate = || {
            InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([
                    s("Parse"),
                    s("Construct"),
                    s("Match"),
                    s("Observe"),
                    s("ReflectAst"),
                    s("Reduce"),
                ]),
            ))
        };

        let first = runtime.install(candidate()).expect("first install");
        let replay = runtime.install(candidate()).expect("identical install");
        assert_eq!(private_name_id(&first), private_name_id(&replay));
        runtime
            .resolve(&first, LanguageRight::Parse)
            .expect("live capability authorizes parse");

        runtime.revoke(&first).expect("revocation succeeds");
        assert!(matches!(
            runtime.resolve(&first, LanguageRight::Parse),
            Err(LanguageRuntimeError::UnknownHandle)
        ));

        let reinstalled = runtime
            .install(candidate())
            .expect("fresh generation installs");
        assert_ne!(private_name_id(&first), private_name_id(&reinstalled));
        runtime
            .resolve(&reinstalled, LanguageRight::Parse)
            .expect("fresh capability authorizes parse");
    }

    #[test]
    fn capability_resolution_rechecks_each_required_right() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse"), s("Bridge")]))))
            .expect("language installs");
        runtime
            .resolve(&token, LanguageRight::Parse)
            .expect("granted right succeeds");
        assert!(matches!(
            runtime.resolve(&token, LanguageRight::Bridge),
            Err(LanguageRuntimeError::Access(LanguageAccessError::MissingRight(
                LanguageRight::Bridge
            )))
        ));
    }

    #[test]
    fn capability_scoped_template_parse_checks_construct_and_preserves_holes() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse, LanguageRight::Construct]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct")]),
            )))
            .expect("language installs");
        let parsed = runtime
            .parse_template(
                &token,
                &[RuntimeTemplatePiece::Hole(0)],
                &[RuntimeTemplateHole { id: 0, category: Some(CategoryId(0)) }],
                Some(CategoryId(0)),
                LanguageRight::Construct,
                &DefaultRuntimeHost,
            )
            .expect("capability-authorized structural parse");
        assert_eq!(parsed[0].value, DynamicValue::TemplateHole { id: 0, category: CategoryId(0) });
    }

    #[test]
    fn installed_language_constructs_a_structural_hole_without_source_interpolation() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse, LanguageRight::Construct]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct")]),
            )))
            .expect("language installs");
        assert!(matches!(
            runtime.construct_template(
                &token,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
                &BTreeMap::from([("x".into(), new_gint_par(73, Vec::new(), false))]),
            ),
            Err(LanguageFltConstructionError::FillCategoryMismatch { .. })
        ));
        let fill = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("a category-valid fill is constructed structurally");
        let constructed = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
                &BTreeMap::from([("x".into(), fill.clone())]),
            )
            .expect("authorized structural construction");
        assert_eq!(constructed, fill, "the fill is spliced as Rho structure, never guest text");
    }

    #[test]
    fn construction_rechecks_construct_authority() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse")]))))
            .expect("parse-only language installs");
        assert!(matches!(
            runtime.construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            ),
            Err(LanguageFltConstructionError::Runtime(LanguageRuntimeError::Access(
                LanguageAccessError::MissingRight(LanguageRight::Construct)
            )))
        ));
    }

    #[test]
    fn prepared_pattern_tokens_preserve_holes_and_are_revocation_linked() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = RholangLanguageRuntime::new(service);
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse"), s("Match")]))))
            .expect("Match-authorized language installs");
        let prepared = runtime
            .prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
            )
            .expect("structural pattern is prepared before publication");
        let resolved = runtime
            .resolve_prepared_pattern(&prepared)
            .expect("live prepared token resolves");
        assert_eq!(resolved.pattern().free_count, 1);
        assert_eq!(resolved.pattern().patterns.len(), 1);
        assert!(
            resolved
                .project_admitted_captures(ListParWithRandom {
                    pars: vec![new_gint_par(73, Vec::new(), false)],
                    random_state: Vec::new(),
                })
                .is_none(),
            "a raw Rho integer is not a forged Expr AST capture",
        );

        runtime
            .revoke(&handle)
            .expect("language capability revokes");
        assert!(matches!(
            runtime.resolve_prepared_pattern(&prepared),
            Err(LanguageRuntimeError::UnknownHandle)
        ));
    }

    #[test]
    fn prepared_capture_plan_enforces_repetitions_before_projecting_the_telescope() {
        let holes = [
            NamedRuntimeTemplateHole {
                id: 0,
                name: "x".into(),
                category: Some("Expr".into()),
            },
            NamedRuntimeTemplateHole {
                id: 1,
                name: "y".into(),
                category: Some("Expr".into()),
            },
        ];
        let plan = PreparedCapturePlan::compile(
            &holes,
            &[("x".into(), 0), ("x".into(), 1), ("y".into(), 2)],
            &[(0, 1)],
            3,
        )
        .expect("the reflector's dense occurrence plan is admitted");
        assert_eq!(plan.projection, vec![0, 2]);
        assert_eq!(plan.repetitions, vec![(0, 1)]);

        let x = new_gint_par(7, Vec::new(), false);
        let y = new_gint_par(9, Vec::new(), false);
        let projected = plan
            .project(ListParWithRandom {
                pars: vec![x.clone(), x.clone(), y.clone()],
                random_state: vec![4, 2],
            })
            .expect("equal normalized occurrences satisfy the repeated hole");
        assert_eq!(projected.pars, vec![x.clone(), y]);
        assert_eq!(projected.random_state, vec![4, 2]);
        assert!(
            plan.project(ListParWithRandom {
                pars: vec![x.clone(), new_gint_par(8, Vec::new(), false), x],
                random_state: Vec::new(),
            })
            .is_none(),
            "a mismatch must publish no partial telescope",
        );
    }

    #[test]
    fn construction_and_pattern_preparation_require_an_explicit_root_category() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("language installs");
        assert!(matches!(
            runtime.construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                None,
                &BTreeMap::new(),
            ),
            Err(LanguageFltConstructionError::MissingRootCategory)
        ));
        assert!(matches!(
            runtime.prepare_pattern(&handle, &[RuntimeTemplatePiece::Text("0".into())], &[], None,),
            Err(LanguageFltConstructionError::MissingRootCategory)
        ));
    }

    #[test]
    fn prepared_pattern_root_admission_rejects_another_category() {
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        )));
        let handle = runtime
            .install(InstallCandidate::Canonical(two_category_value(
                "TwoCategory",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("two-category language installs");
        let pattern = runtime
            .prepare_pattern(&handle, &[RuntimeTemplatePiece::Text("0".into())], &[], Some("Expr"))
            .expect("Expr pattern prepares");
        let prepared = runtime
            .resolve_prepared_pattern(&pattern)
            .expect("prepared pattern resolves");
        let other = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("other".into())],
                &[],
                Some("Other"),
                &BTreeMap::new(),
            )
            .expect("Other term constructs");
        assert!(!prepared.admits_subject(&ListParWithRandom {
            pars: vec![other],
            random_state: Vec::new(),
        }));
    }

    #[test]
    fn pattern_preparation_rechecks_match_authority() {
        let policy = LanguageInstallPolicy::new(
            LanguageRights::from_rights([LanguageRight::Parse]),
            RuntimePolicy::default(),
            LANGUAGE_CAPABILITY_ABI_V1,
        );
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            policy,
        )));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value("Tiny", l([s("Parse"), s("Match")]))))
            .expect("language installs with authority intersection");
        assert!(matches!(
            runtime.prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
            ),
            Err(LanguageFltConstructionError::Runtime(LanguageRuntimeError::Access(
                LanguageAccessError::MissingRight(LanguageRight::Match)
            )))
        ));
    }

    #[test]
    fn install_definition_uses_the_reserved_nonlocal_abi() {
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ))));
        let definition = language_install_definition(runtime);
        assert_eq!(definition.urn, LANGUAGE_INSTALL_URN);
        assert_eq!(definition.arity, 1, "nouveau Rholang carries one canonical arity list");
        assert_eq!(definition.remainder, None);
        assert_eq!(
            definition.fixed_channel,
            LANGUAGE_INSTALL_BAND.channel(0, LANGUAGE_CAPABILITY_ABI_CURRENT)
        );
        assert_eq!(
            definition.body_ref,
            LANGUAGE_INSTALL_BAND.body_ref(0, LANGUAGE_CAPABILITY_ABI_CURRENT)
        );
    }

    #[test]
    fn parse_definition_and_wire_use_the_reserved_nonlocal_abi() {
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ))));
        let definition = language_parse_definition(runtime);
        assert_eq!(definition.urn, LANGUAGE_PARSE_URN);
        assert_eq!(definition.arity, 1);
        assert_eq!(definition.remainder, None);
        assert_eq!(definition.fixed_channel, LANGUAGE_PARSE_BAND.channel(0, LANGUAGE_PARSE_ABI_V1));
        assert_eq!(definition.body_ref, LANGUAGE_PARSE_BAND.body_ref(0, LANGUAGE_PARSE_ABI_V1));

        let handle = private_name([LANGUAGE_HANDLE_DOMAIN_CURRENT, b"wire"].concat());
        let reply = new_gstring_par("reply".into(), Vec::new(), false);
        let encoded = encode_language_parse_call(handle.clone(), "0", "Expr", reply.clone());
        let decoded = decode_language_parse_call(&encoded).expect("canonical request decodes");
        assert_eq!(decoded.handle, handle);
        assert_eq!(decoded.source, "0");
        assert_eq!(decoded.category, "Expr");
        assert_eq!(decoded.reply, reply);

        let wrong_abi = wire_list(vec![
            new_gstring_par("mettail-language-parse/2".into(), Vec::new(), false),
            private_name([LANGUAGE_HANDLE_DOMAIN_CURRENT, b"wire"].concat()),
            new_gstring_par("0".into(), Vec::new(), false),
            new_gstring_par("Expr".into(), Vec::new(), false),
            new_gstring_par("reply".into(), Vec::new(), false),
        ]);
        assert!(matches!(
            decode_language_parse_call(&wrong_abi),
            Err(LanguageParseWireError::UnsupportedAbi(abi))
                if abi == "mettail-language-parse/2"
        ));
    }

    #[test]
    fn parse_outcome_wire_is_total_stable_and_non_reflective() {
        let cases = [
            (LanguageParseOutcome::Accepted, "accepted", "Accepted", 1, None, None),
            (
                LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerStates),
                "exhausted",
                "LexerStates",
                0,
                None,
                None,
            ),
            (
                LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerEdges),
                "exhausted",
                "LexerEdges",
                0,
                None,
                None,
            ),
            (
                LanguageParseOutcome::Exhausted(LanguageParseExhaustion::LexerWork),
                "exhausted",
                "LexerWork",
                0,
                None,
                None,
            ),
            (
                LanguageParseOutcome::Rejected(LanguageParseRejection::NoParse),
                "rejected",
                "NoParse",
                0,
                None,
                None,
            ),
            (
                LanguageParseOutcome::Rejected(LanguageParseRejection::LexerModeUnclosed {
                    byte: 9,
                    depth: 3,
                }),
                "rejected",
                "LexerModeUnclosed",
                0,
                Some(9),
                Some(3),
            ),
            (
                LanguageParseOutcome::Ambiguous { alternatives: 2 },
                "ambiguous",
                "Ambiguous",
                2,
                None,
                None,
            ),
            (
                LanguageParseOutcome::Exhausted(LanguageParseExhaustion::ForeignNesting {
                    byte: 7,
                }),
                "exhausted",
                "ForeignNesting",
                0,
                Some(7),
                None,
            ),
        ];
        for (outcome, status, code, alternatives, byte, depth) in cases {
            let response = parse_outcome_response(outcome);
            let result = map_entry(&response, "ok").expect("result is wrapped in ok");
            let fields = exact_map(result).expect("result is a closed map");
            assert_eq!(fields.len(), 5, "parse-only results expose no reflected syntax");
            assert_eq!(map_entry(result, "status").and_then(exact_string), Some(status));
            assert_eq!(map_entry(result, "code").and_then(exact_string), Some(code));
            let ExprInstance::GInt(actual_alternatives) =
                exact_expr(map_entry(result, "alternatives").expect("alternatives field exists"))
                    .expect("alternatives is one integer")
            else {
                panic!("alternatives must be an integer")
            };
            assert_eq!(*actual_alternatives, alternatives);
            for (field, expected) in [("byte", byte), ("depth", depth)] {
                let value = map_entry(result, field).expect("fixed result field exists");
                match expected {
                    Some(expected) => {
                        let ExprInstance::GInt(actual) = exact_expr(value).expect("integer detail")
                        else {
                            panic!("{field} must be an integer when present")
                        };
                        assert_eq!(*actual, expected);
                    },
                    None => assert!(exact_nil(value), "{field} must be Nil when absent"),
                }
            }
        }
    }

    #[test]
    fn lexical_limits_have_distinct_install_commitments_and_exhaustion_outcomes() {
        let mut fingerprints = std::collections::BTreeSet::new();
        for mask in 0..8 {
            let mut runtime = RuntimePolicy::default();
            runtime.max_lexer_states -= mask & 1;
            runtime.max_lexer_edges -= (mask >> 1) & 1;
            runtime.max_lexer_work -= u64::from((mask >> 2) & 1);
            let policy = LanguageInstallPolicy::new(
                LanguageRights::from_rights([LanguageRight::Parse]),
                runtime,
                LANGUAGE_CAPABILITY_ABI_V1,
            );
            assert!(
                fingerprints.insert(policy.fingerprint),
                "mask {mask} commits a distinct policy"
            );
        }
        for (error, exhaustion) in [
            (RuntimeError::LexerStateLimit, LanguageParseExhaustion::LexerStates),
            (RuntimeError::LexerEdgeLimit, LanguageParseExhaustion::LexerEdges),
            (RuntimeError::LexerWorkLimit, LanguageParseExhaustion::LexerWork),
        ] {
            assert_eq!(
                classify_parse_error(error).expect("total bounded outcome"),
                LanguageParseOutcome::Exhausted(exhaustion)
            );
        }
    }

    #[test]
    fn language_definitions_are_distinct_but_share_one_runtime() {
        let runtime = Arc::new(RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ))));
        let definitions = language_runtime_definitions(runtime);
        assert_eq!(definitions.len(), 8);
        assert_eq!(definitions[0].urn, LANGUAGE_INSTALL_URN);
        assert_eq!(definitions[1].urn, LANGUAGE_PARSE_URN);
        assert_eq!(definitions[2].urn, LANGUAGE_FLT_CONSTRUCT_URN);
        assert_eq!(definitions[3].urn, LANGUAGE_FLT_PATTERN_URN);
        assert_eq!(definitions[4].urn, crate::theorem_channel::THEOREM_CHANNEL_OPEN_URN);
        assert_eq!(definitions[5].urn, crate::theorem_channel::THEOREM_CHANNEL_PREPARE_URN);
        assert_eq!(definitions[6].urn, crate::theorem_channel::THEOREM_CHANNEL_COMMIT_URN);
        assert_eq!(definitions[7].urn, crate::theorem_channel::THEOREM_CHANNEL_REVOKE_URN);
        for left in 0..definitions.len() {
            for right in left + 1..definitions.len() {
                assert_ne!(definitions[left].fixed_channel, definitions[right].fixed_channel);
                assert_ne!(definitions[left].body_ref, definitions[right].body_ref);
            }
        }
        assert_eq!(definitions[1].arity, 1);
        assert_eq!(definitions[2].arity, 1);
        assert_eq!(definitions[3].arity, 1);
    }

    #[tokio::test]
    async fn lexical_handle_constructs_an_flt_end_to_end() {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let token = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct")]),
            )))
            .expect("language installs");
        let proc = Proc::parse_via_wpda(r#"for(lambda <- @"HANDLE"){ @"OUT"!(lambda:Expr`0`) }"#)
            .expect("lexically selected FLT parses");
        let lowered = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("bound selector stages without a static resolver");
        let handle_send = new_send_par(
            new_gstring_par("HANDLE".into(), Vec::new(), false),
            vec![token],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let outputs = crate::run::run_normalized_par_with_definitions_and_read_par_channels(
            &lowered.append(handle_send),
            language_runtime_definitions(runtime),
            &["OUT"],
        )
        .await
        .expect("installed parser construction executes");
        let out = outputs.get("OUT").expect("OUT was requested");
        assert_eq!(out.len(), 1);
        let ExprInstance::EListBody(reflected) = out[0]
            .exprs
            .first()
            .and_then(|expr| expr.expr_instance.as_ref())
            .expect("constructed FLT is a reflected list")
        else {
            panic!("constructed FLT must use the structural reflected-term ABI")
        };
        assert!(matches!(
            reflected
                .ps
                .first()
                .and_then(|tag| tag.unforgeables.first())
                .and_then(|unforgeable| unforgeable.unf_instance.as_ref()),
            Some(GPrivateBody(_)),
        ));
    }

    #[tokio::test]
    async fn lexical_handle_prepares_and_matches_an_flt_hole_end_to_end() {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("language installs");
        let reflected_zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero is reflected through the installed grammar");
        let proc = Proc::parse_via_wpda(
            r#"for(lambda <- @"HANDLE"){
                 for(@lambda:Expr`${x:Expr}` <- @"IN"){ @"OUT"!(x) }
               }"#,
        )
        .expect("lexically selected FLT receive pattern parses");
        let lowered = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("bound selector stages pattern preparation before receive publication");
        let handle_send = new_send_par(
            new_gstring_par("HANDLE".into(), Vec::new(), false),
            vec![handle],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let data_send = new_send_par(
            new_gstring_par("IN".into(), Vec::new(), false),
            vec![reflected_zero.clone()],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let outputs = crate::run::run_normalized_par_with_language_runtime_and_read_par_channels(
            &lowered.append(handle_send).append(data_send),
            runtime.clone(),
            &["OUT", "IN"],
        )
        .await
        .expect("prepared dynamic FLT pattern executes through the shared matcher");
        assert_eq!(
            runtime
                .capabilities
                .read()
                .expect("capability state")
                .patterns
                .len(),
            1,
            "the pre-publication system service must prepare exactly one pattern",
        );
        assert_eq!(
            outputs.get("IN"),
            Some(&Vec::new()),
            "the reflected datum must be consumed by the prepared receive",
        );
        assert_eq!(
            outputs.get("OUT"),
            Some(&vec![reflected_zero]),
            "the process hole binds the structurally matched reflected term",
        );
    }

    #[tokio::test]
    async fn repeated_flt_hole_matches_once_and_rejects_unequal_occurrences_atomically() {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(pair_value(
                "Pairs",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("pair language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero term");
        let equal_pair = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("(0,0)".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("equal pair");
        let unequal_pair = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("(0,1)".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("unequal pair");
        let proc = Proc::parse_via_wpda(
            r#"for(language <- @"HANDLE"){
                 for(@language:Expr`(${x:Expr},${x:Expr})` <- @"IN"){
                   @"OUT"!(x)
                 }
               }"#,
        )
        .expect("repeated-hole FLT receive parses");
        let lowered = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("the repeated-hole plan stages through the installed matcher");

        let run = |datum: Par| {
            let runtime = runtime.clone();
            let program = lowered
                .clone()
                .append(new_send_par(
                    new_gstring_par("HANDLE".into(), Vec::new(), false),
                    vec![handle.clone()],
                    false,
                    Vec::new(),
                    false,
                    Vec::new(),
                    false,
                ))
                .append(new_send_par(
                    new_gstring_par("IN".into(), Vec::new(), false),
                    vec![datum],
                    false,
                    Vec::new(),
                    false,
                    Vec::new(),
                    false,
                ));
            async move {
                crate::run::run_normalized_par_with_language_runtime_and_read_par_channels(
                    &program,
                    runtime,
                    &["OUT", "IN"],
                )
                .await
                .expect("installed repeated-hole matcher executes")
            }
        };

        let equal_outputs = run(equal_pair).await;
        assert_eq!(equal_outputs.get("OUT"), Some(&vec![zero]));
        assert_eq!(equal_outputs.get("IN"), Some(&Vec::new()));

        let unequal_outputs = run(unequal_pair.clone()).await;
        assert_eq!(unequal_outputs.get("OUT"), Some(&Vec::new()));
        assert_eq!(
            unequal_outputs.get("IN"),
            Some(&vec![unequal_pair]),
            "failed equality must leave the datum available and publish no captures",
        );
    }

    #[tokio::test]
    async fn joined_dynamic_flt_patterns_preserve_each_preparation_scope() {
        mettail_runtime::clear_var_cache();
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("language installs");
        let reflected_zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero is reflected through the installed grammar");
        let proc = Proc::parse_via_wpda(
            r#"for(lambda <- @"HANDLE"){
                 for(@lambda:Expr`${x:Expr}` <- @"LEFT" & @lambda:Expr`${y:Expr}` <- @"RIGHT"){
                   @"OUT"!(x, y)
                 }
               }"#,
        )
        .expect("joined lexically selected FLT patterns parse");
        let lowered = crate::rholang_ast::lower_rholang_proc(&proc)
            .expect("both dynamic patterns stage before the atomic join is published");
        let handle_send = new_send_par(
            new_gstring_par("HANDLE".into(), Vec::new(), false),
            vec![handle],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let left_send = new_send_par(
            new_gstring_par("LEFT".into(), Vec::new(), false),
            vec![reflected_zero.clone()],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let right_send = new_send_par(
            new_gstring_par("RIGHT".into(), Vec::new(), false),
            vec![reflected_zero.clone()],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        let outputs = crate::run::run_normalized_par_with_language_runtime_and_read_par_channels(
            &lowered
                .append(handle_send)
                .append(left_send)
                .append(right_send),
            runtime.clone(),
            &["OUT", "LEFT", "RIGHT"],
        )
        .await
        .expect("both prepared patterns participate in one atomic RSpace join");
        assert_eq!(
            runtime
                .capabilities
                .read()
                .expect("capability state")
                .patterns
                .len(),
            2,
        );
        assert_eq!(outputs.get("LEFT"), Some(&Vec::new()));
        assert_eq!(outputs.get("RIGHT"), Some(&Vec::new()));
        let joined_payload = new_elist_par(
            vec![reflected_zero.clone(), reflected_zero],
            Vec::new(),
            false,
            None,
            Vec::new(),
            false,
        );
        assert_eq!(
            outputs.get("OUT"),
            Some(&vec![joined_payload]),
            "each process hole binds the datum from its own join position",
        );
    }

    #[test]
    fn public_install_errors_are_typed_and_bounded() {
        let response = error_response("InvalidSpecificationValue", &"x".repeat(1_000));
        let value = par_to_canonical_value(&response, CanonicalValueLimits::default())
            .expect("error response is closed data");
        let RhoValue::Map(ref outer) = value else {
            panic!("response must be a map")
        };
        let Some(RhoValue::Map(error)) = outer.get("error") else {
            panic!("response must contain an error map")
        };
        assert_eq!(error.get("code"), Some(&RhoValue::String("InvalidSpecificationValue".into())));
        let Some(RhoValue::String(message)) = error.get("message") else {
            panic!("error must contain a message")
        };
        assert_eq!(message.chars().count(), MAX_PUBLIC_ERROR_CHARS);
    }

    #[test]
    fn theorem_channel_admits_and_extracts_only_structurally_checked_flts() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            32,
        )
        .expect("typed channel");

        assert!(matches!(
            channel.prepare_produce(new_gint_par(7, Vec::new(), false)),
            Err(crate::theorem_channel::RholangTheoremChannelError::StructuralAdmissionRejected)
        ));
        let prepared = channel
            .prepare_produce(zero.clone())
            .expect("admitted produce");
        let message = channel
            .commit_produce(prepared, |message| message)
            .expect("atomic produce");
        let pattern = runtime
            .prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
            )
            .expect("prepared dynamic pattern");
        let prepared = channel
            .prepare_consume(&message, &pattern)
            .expect("checked match witness");
        let matched = channel
            .commit_consume(prepared, |matched| matched)
            .expect("atomic consume");
        assert_eq!(matched.message().value(), &zero);
        assert_eq!(matched.captures(), &[zero]);
        assert_eq!(matched.evidence().captures().len(), 1);
    }

    #[test]
    fn theorem_channel_creation_requires_explicit_check_authority() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match"), s("Publish")]),
            )))
            .expect("language installs without theorem-check authority");
        let membership = AdmissionTheorem::membership(CategoryId(0));

        assert!(matches!(
            crate::theorem_channel::RholangTheoremChannel::new(
                runtime,
                &handle,
                "Expr",
                membership,
                membership,
                SpaceRights::all(),
                Arc::new(StructuralTheoremChecker::default()),
                AdmissionBudget::structural(),
                32,
            ),
            Err(crate::theorem_channel::RholangTheoremChannelError::Runtime(error))
                if matches!(
                    error.as_ref(),
                    LanguageRuntimeError::Access(LanguageAccessError::MissingRight(
                        LanguageRight::Check
                    ))
                )
        ));
    }

    #[test]
    fn theorem_channel_budget_exhaustion_fails_closed_before_rspace_mutation() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime,
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::from_rights([SpaceRight::Produce]),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::new(0, 0),
            32,
        )
        .expect("bounded typed channel");

        assert!(matches!(
            channel.prepare_produce(zero),
            Err(crate::theorem_channel::RholangTheoremChannelError::Theorem(
                mettail_grammar_core::TheoremChannelError::AdmissionUndetermined {
                    reason: mettail_grammar_core::AdmissionUndetermined::WorkBudgetExhausted {
                        required: 1,
                        available: 0,
                    },
                    ..
                }
            ))
        ));
    }

    #[test]
    fn theorem_channel_rejects_a_mismatched_presented_certificate() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime,
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::from_rights([SpaceRight::Produce]),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            32,
        )
        .expect("typed channel");
        let message = channel
            .commit_produce(
                channel
                    .prepare_produce(zero.clone())
                    .expect("prepare proof"),
                |message| message,
            )
            .expect("commit admitted message");
        let mismatched = mettail_grammar_core::AdmissionCertificate::from_checked_evidence(
            message.evidence().term(),
            membership,
            "different-checker/1",
            "different-limits/1",
            Vec::new(),
        );

        assert!(matches!(
            channel.prepare_produce_with_certificate(zero, Some(&mismatched)),
            Err(crate::theorem_channel::RholangTheoremChannelError::Theorem(
                mettail_grammar_core::TheoremChannelError::AdmissionRefuted {
                    reason: AdmissionRefutation::CertificateMismatch,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn theorem_channel_language_revocation_prevents_a_prepared_commit() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            32,
        )
        .expect("typed channel");
        let prepared = channel
            .prepare_produce(zero)
            .expect("prepare before revocation");
        runtime.revoke(&handle).expect("revoke installed language");
        let mut called = false;
        assert!(channel.commit_produce(prepared, |_| called = true).is_err());
        assert!(!called, "revoked authority must reject before mutation");
    }

    #[test]
    fn theorem_channel_space_revocation_prevents_prepared_produce_and_consume() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));

        let produce_channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            0,
        )
        .expect("produce channel");
        let prepared = produce_channel
            .prepare_produce(zero.clone())
            .expect("prepare produce");
        produce_channel.revoke().expect("revoke space");
        let mut produce_called = false;
        assert!(produce_channel
            .commit_produce(prepared, |_| produce_called = true)
            .is_err());
        assert!(!produce_called, "revoked produce must not reach mutation");

        let consume_channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            0,
        )
        .expect("consume channel");
        let message = consume_channel
            .commit_produce(
                consume_channel
                    .prepare_produce(zero)
                    .expect("prepare stored message"),
                |message| message,
            )
            .expect("commit stored message");
        let pattern = runtime
            .prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
            )
            .expect("prepared pattern");
        let prepared = consume_channel
            .prepare_consume(&message, &pattern)
            .expect("prepare consume");
        consume_channel
            .attenuate_space_rights(&SpaceRights::from_rights([SpaceRight::Produce]))
            .expect("remove consume right");
        let mut consume_called = false;
        assert!(consume_channel
            .commit_consume(prepared, |_| consume_called = true)
            .is_err());
        assert!(!consume_called, "revoked consume must not reach mutation");
    }

    #[test]
    fn theorem_channel_rejects_a_prepared_pattern_from_another_language() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let rights = || l([s("Parse"), s("Construct"), s("Match"), s("Publish"), s("Check")]);
        let left = runtime
            .install(InstallCandidate::Canonical(tiny_value("LeftTiny", rights())))
            .expect("left language");
        let right = runtime
            .install(InstallCandidate::Canonical(tiny_value("RightTiny", rights())))
            .expect("right language");
        let zero = runtime
            .construct_template(
                &left,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("left zero");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let channel = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &left,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            8,
        )
        .expect("left channel");
        let message = channel
            .commit_produce(
                channel.prepare_produce(zero).expect("prepare left message"),
                |message| message,
            )
            .expect("commit left message");
        let foreign_pattern = runtime
            .prepare_pattern(
                &right,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
            )
            .expect("right pattern");
        assert!(matches!(
            channel.prepare_consume(&message, &foreign_pattern),
            Err(crate::theorem_channel::RholangTheoremChannelError::ForeignPattern)
        ));
    }

    #[test]
    fn prepared_pattern_identity_is_framed_and_binds_compiler_input() {
        let hole_x = NamedRuntimeTemplateHole {
            id: 0,
            name: "x".into(),
            category: Some("Expr".into()),
        };
        let hole_y = NamedRuntimeTemplateHole { name: "y".into(), ..hole_x.clone() };
        let fingerprint = [42; 32];
        let x = prepared_pattern_semantic_id(
            fingerprint,
            &[RuntimeTemplatePiece::Hole(0)],
            &[hole_x],
            Some(CategoryId(0)),
        );
        let y = prepared_pattern_semantic_id(
            fingerprint,
            &[RuntimeTemplatePiece::Hole(0)],
            &[hole_y],
            Some(CategoryId(0)),
        );
        let text = prepared_pattern_semantic_id(
            fingerprint,
            &[RuntimeTemplatePiece::Text("0".into())],
            &[],
            Some(CategoryId(0)),
        );
        assert_ne!(x, y, "capture-telescope identity includes binder labels");
        assert_ne!(x, text, "piece and telescope sections cannot collide");
    }

    #[test]
    fn theorem_channel_reindexes_an_admitted_flt_into_an_exact_theorem() {
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::default(),
        ));
        let runtime = Arc::new(RholangLanguageRuntime::new(service));
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match"), s("Publish"), s("Check")]),
            )))
            .expect("language installs");
        let zero = runtime
            .construct_template(
                &handle,
                &[RuntimeTemplatePiece::Text("0".into())],
                &[],
                Some("Expr"),
                &BTreeMap::new(),
            )
            .expect("zero FLT");
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let source = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            membership,
            membership,
            SpaceRights::all(),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            4,
        )
        .expect("membership channel");
        let message = source
            .commit_produce(
                source
                    .prepare_produce(zero)
                    .expect("prepare membership message"),
                |message| message,
            )
            .expect("commit membership message");
        let term_hash = message.evidence().term().term_hash();
        let exact = AdmissionTheorem::exact(CategoryId(0), term_hash);
        let target = crate::theorem_channel::RholangTheoremChannel::new(
            runtime.clone(),
            &handle,
            "Expr",
            exact,
            membership,
            SpaceRights::from_rights([SpaceRight::Consume]),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            4,
        )
        .expect("exact theorem channel");
        let pattern = runtime
            .prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &[NamedRuntimeTemplateHole {
                    id: 0,
                    name: "x".into(),
                    category: Some("Expr".into()),
                }],
                Some("Expr"),
            )
            .expect("prepared pattern");
        let checked = target
            .commit_consume(
                target
                    .prepare_consume(&message, &pattern)
                    .expect("exact predicate holds"),
                |checked| checked,
            )
            .expect("exact reindexing commits");
        assert_eq!(checked.message().evidence().certificate().theorem(), exact);
        assert_eq!(checked.evidence().message().certificate().theorem(), exact);

        let rejecting = crate::theorem_channel::RholangTheoremChannel::new(
            runtime,
            &handle,
            "Expr",
            AdmissionTheorem::exact(CategoryId(0), mettail_grammar_core::TermHash([99; 32])),
            membership,
            SpaceRights::from_rights([SpaceRight::Consume]),
            Arc::new(StructuralTheoremChecker::default()),
            AdmissionBudget::structural(),
            4,
        )
        .expect("different exact theorem channel");
        assert!(matches!(
            rejecting.prepare_consume(&message, &pattern),
            Err(crate::theorem_channel::RholangTheoremChannelError::Theorem(
                mettail_grammar_core::TheoremChannelError::AdmissionRefuted {
                    reason: AdmissionRefutation::TheoremDoesNotHold,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn host_capture_budget_bounds_construction_and_pattern_preparation() {
        let mut runtime_policy = RuntimePolicy::default();
        runtime_policy.max_capture_bindings = 0;
        let service = Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::new(
                LanguageRights::all(),
                runtime_policy,
                LANGUAGE_CAPABILITY_ABI_V1,
            ),
        ));
        let runtime = RholangLanguageRuntime::new(service);
        let handle = runtime
            .install(InstallCandidate::Canonical(tiny_value(
                "Tiny",
                l([s("Parse"), s("Construct"), s("Match")]),
            )))
            .expect("language installs");
        let holes = [NamedRuntimeTemplateHole {
            id: 0,
            name: "x".into(),
            category: Some("Expr".into()),
        }];
        assert!(matches!(
            runtime.prepare_pattern(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &holes,
                Some("Expr"),
            ),
            Err(LanguageFltConstructionError::TemplateHoleLimit { limit: 0, found: 1 })
        ));
        assert!(matches!(
            runtime.construct_template(
                &handle,
                &[RuntimeTemplatePiece::Hole(0)],
                &holes,
                Some("Expr"),
                &BTreeMap::new(),
            ),
            Err(LanguageFltConstructionError::TemplateHoleLimit { limit: 0, found: 1 })
        ));
    }

    #[test]
    fn host_capture_budget_counts_repeated_pattern_occurrences() {
        let mut runtime_policy = RuntimePolicy::default();
        runtime_policy.max_capture_bindings = 1;
        let runtime = RholangLanguageRuntime::new(Arc::new(LanguageInstallService::new(
            Arc::new(MemoryRegistry::default()),
            LanguageInstallPolicy::new(
                LanguageRights::all(),
                runtime_policy,
                LANGUAGE_CAPABILITY_ABI_V1,
            ),
        )));
        let handle = runtime
            .install(InstallCandidate::Canonical(pair_value("Pairs", l([s("Parse"), s("Match")]))))
            .expect("pair grammar installs");
        let holes = [NamedRuntimeTemplateHole {
            id: 0,
            name: "x".into(),
            category: Some("Expr".into()),
        }];
        let pieces = [
            RuntimeTemplatePiece::Text("(".into()),
            RuntimeTemplatePiece::Hole(0),
            RuntimeTemplatePiece::Text(",".into()),
            RuntimeTemplatePiece::Hole(0),
            RuntimeTemplatePiece::Text(")".into()),
        ];
        let result = runtime.prepare_pattern(&handle, &pieces, &holes, Some("Expr"));
        assert!(
            matches!(
                result,
                Err(LanguageFltConstructionError::TemplateOccurrenceLimit { limit: 1, found: 2 })
            ),
            "unexpected repeated-hole limit result: {result:?}",
        );
    }
}
