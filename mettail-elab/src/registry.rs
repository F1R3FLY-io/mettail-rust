//! Versioned Registry language records and parser-image cache validation.
//!
//! The canonical `language/2` value is always authoritative. The optional
//! parser image is derived, untrusted cache data and is accepted only after the
//! caller has lowered the value to `GrammarCoreV1` and every cache contract
//! field has been verified against that result.

use crate::canonical::{LanguageValueResolver, RhoValue, ValueToCoreError};
use crate::module::{CanonicalModuleDependency, CanonicalModuleValue};
use mettail_grammar_core::{
    GrammarCoreV1, ImageError, InstallLanguageError, InstalledLanguageGrant,
    InstalledLanguageTable, LanguageRights, ParserImageV1,
};
use std::collections::BTreeMap;
use std::sync::Arc;

pub const REGISTRY_LANGUAGE_SCHEMA_V1: &str = "mettail-registry-language/1";
pub const REGISTRY_MODULE_SCHEMA_V1: &str = "mettail-registry-module/1";
const REGISTRY_MODULE_CONTENT_DOMAIN_V1: &[u8] = b"mettail-registry-module-content/1\0";

/// One immutable Versioned Registry module record.
///
/// `module`, `exports`, and `dependencies` are authoritative and deliberately
/// redundant: validation requires all three projections to agree exactly.
/// Parser images are untrusted caches. `signatures` is opaque to the
/// elaborator; the injected Versioned Registry capability verifies it before
/// returning a pinned snapshot record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryModuleRecord {
    pub schema: String,
    pub source: String,
    pub source_commitment: [u8; 32],
    pub module: RhoValue,
    pub exports: BTreeMap<String, RhoValue>,
    pub dependencies: Vec<CanonicalModuleDependency>,
    pub images: BTreeMap<[u8; 32], Vec<u8>>,
    pub signatures: RhoValue,
}

impl RegistryModuleRecord {
    pub fn new(
        source: impl Into<String>,
        module: CanonicalModuleValue,
        signatures: RhoValue,
    ) -> Self {
        let source = source.into();
        let exports = module
            .exports
            .iter()
            .map(|export| (export.name.clone(), export.spec.clone()))
            .collect();
        let dependencies = module.dependencies.clone();
        Self {
            schema: REGISTRY_MODULE_SCHEMA_V1.into(),
            source_commitment: *blake3::hash(source.as_bytes()).as_bytes(),
            source,
            module: module.to_rho_value(),
            exports,
            dependencies,
            images: BTreeMap::new(),
            signatures,
        }
    }

    /// Validate every authority-bearing canonical projection. The source and
    /// its commitment are retained as a development oracle, but source bytes
    /// do not participate in production semantic admission.
    pub fn validate_structure(&self) -> Result<CanonicalModuleValue, RegistryModuleError> {
        if self.schema != REGISTRY_MODULE_SCHEMA_V1 {
            return Err(RegistryModuleError::UnsupportedSchema(self.schema.clone()));
        }
        crate::canonical::admit_canonical_value(&self.signatures)
            .map_err(RegistryModuleError::SignatureMetadata)?;
        let module = CanonicalModuleValue::from_rho_value(&self.module)
            .map_err(RegistryModuleError::CanonicalModule)?;
        if module.dependencies != self.dependencies {
            return Err(RegistryModuleError::DependencyProjectionMismatch);
        }
        let projected_exports: BTreeMap<_, _> = module
            .exports
            .iter()
            .map(|export| (export.name.clone(), export.spec.clone()))
            .collect();
        if projected_exports != self.exports {
            return Err(RegistryModuleError::ExportProjectionMismatch);
        }
        Ok(module)
    }

    /// Check the optional source oracle without promoting it to production
    /// authority. Developer tooling may call this to compare a source artifact
    /// with its separately committed bytes; installers never need to parse it.
    pub fn validate_source_oracle(&self) -> Result<(), RegistryModuleError> {
        let actual = *blake3::hash(self.source.as_bytes()).as_bytes();
        if actual != self.source_commitment {
            return Err(RegistryModuleError::SourceCommitmentMismatch);
        }
        Ok(())
    }

    /// Canonical bytes covered by Registry trust verification. Images are
    /// excluded because they are explicitly untrusted, replaceable caches.
    pub fn signed_payload(&self) -> Result<Vec<u8>, RegistryModuleError> {
        self.validate_structure()?;
        let dependencies = RhoValue::List(
            self.dependencies
                .iter()
                .map(|dependency| {
                    RhoValue::Map(BTreeMap::from([
                        ("uri".into(), RhoValue::String(dependency.reference.external_form())),
                        ("commitment".into(), RhoValue::Bytes(dependency.commitment.to_vec())),
                    ]))
                })
                .collect(),
        );
        Ok(RhoValue::Map(BTreeMap::from([
            ("schema".into(), RhoValue::String(self.schema.clone())),
            ("source_commitment".into(), RhoValue::Bytes(self.source_commitment.to_vec())),
            ("module".into(), self.module.clone()),
            ("exports".into(), RhoValue::Map(self.exports.clone())),
            ("dependencies".into(), dependencies),
        ]))
        .canonical_bytes())
    }

    /// Exact commitment used by dependency edges. It commits the signed
    /// canonical record projection, including its source-provenance
    /// commitment, but excludes the optional source bytes and every untrusted
    /// parser-image cache.
    pub fn content_commitment(&self) -> Result<[u8; 32], RegistryModuleError> {
        let payload = self.signed_payload()?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(REGISTRY_MODULE_CONTENT_DOMAIN_V1);
        hasher.update(&(payload.len() as u64).to_be_bytes());
        hasher.update(&payload);
        Ok(*hasher.finalize().as_bytes())
    }

    /// Export records in canonical module source order. Every export shares
    /// one immutable image map; authoritative lowering selects at most the
    /// image keyed by that export's computed GrammarCore fingerprint.
    pub fn export_records(
        &self,
    ) -> Result<Vec<(String, RegistryLanguageRecord)>, RegistryModuleError> {
        let module = self.validate_structure()?;
        let images = Arc::new(self.images.clone());
        Ok(module
            .exports
            .into_iter()
            .map(|export| {
                (
                    export.name,
                    RegistryLanguageRecord::with_parser_images(export.spec, images.clone()),
                )
            })
            .collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistryModuleError {
    UnsupportedSchema(String),
    SourceCommitmentMismatch,
    SignatureMetadata(crate::canonical::ValueDecodeError),
    CanonicalModule(crate::canonical::ValueDecodeError),
    DependencyProjectionMismatch,
    ExportProjectionMismatch,
}

impl std::fmt::Display for RegistryModuleError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedSchema(schema) => {
                write!(formatter, "unsupported Registry module schema `{schema}`")
            },
            Self::SourceCommitmentMismatch => {
                formatter.write_str("Registry module source commitment does not match its bytes")
            },
            Self::SignatureMetadata(error) => {
                write!(formatter, "invalid Registry signature metadata: {error}")
            },
            Self::CanonicalModule(error) => write!(formatter, "invalid module/1 value: {error}"),
            Self::DependencyProjectionMismatch => formatter
                .write_str("Registry dependencies differ from the canonical module projection"),
            Self::ExportProjectionMismatch => {
                formatter.write_str("Registry exports differ from the canonical module projection")
            },
        }
    }
}

impl std::error::Error for RegistryModuleError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryLanguageRecord {
    pub schema: String,
    pub spec: RhoValue,
    pub parser_image: Option<Vec<u8>>,
    /// Content-addressed image set used by module records. Selection happens
    /// only after authoritative lowering computes the language fingerprint.
    pub parser_images: Arc<BTreeMap<[u8; 32], Vec<u8>>>,
}

impl RegistryLanguageRecord {
    pub fn new(spec: RhoValue) -> Self {
        Self {
            schema: REGISTRY_LANGUAGE_SCHEMA_V1.into(),
            spec,
            parser_image: None,
            parser_images: Arc::new(BTreeMap::new()),
        }
    }

    pub fn with_parser_images(
        spec: RhoValue,
        parser_images: Arc<BTreeMap<[u8; 32], Vec<u8>>>,
    ) -> Self {
        Self {
            schema: REGISTRY_LANGUAGE_SCHEMA_V1.into(),
            spec,
            parser_image: None,
            parser_images,
        }
    }

    /// Prepare installation by lowering the authoritative value first, then
    /// probing the optional cache against the resulting core.
    pub fn prepare_install<E>(
        &self,
        compiler_abi: &str,
        unicode_version: &str,
        lower: impl FnOnce(&RhoValue) -> Result<GrammarCoreV1, E>,
    ) -> Result<PreparedRegistryLanguage, PrepareRegistryError<E>> {
        if self.schema != REGISTRY_LANGUAGE_SCHEMA_V1 {
            return Err(PrepareRegistryError::UnsupportedSchema(self.schema.clone()));
        }
        let core = lower(&self.spec).map_err(PrepareRegistryError::Lowering)?;
        core.validate()
            .map_err(PrepareRegistryError::InvalidGrammar)?;
        let fingerprint = core
            .fingerprint()
            .map_err(|error| PrepareRegistryError::Fingerprint(format!("{error:?}")))?;
        let selected_image = self
            .parser_images
            .get(&fingerprint)
            .or(self.parser_image.as_ref());
        let cache = match selected_image {
            None => ParserCache::Missing,
            Some(bytes) => match ParserImageV1::decode_executable_verified(
                bytes,
                &core,
                compiler_abi,
                unicode_version,
            ) {
                Ok(image) => ParserCache::Verified(Box::new(image)),
                Err(error) => ParserCache::Rejected(format!("{error:?}")),
            },
        };
        Ok(PreparedRegistryLanguage {
            authoritative_spec: self.spec.clone(),
            core,
            cache,
        })
    }

    pub fn prepare_install_with_registry(
        &self,
        compiler_abi: &str,
        unicode_version: &str,
        registry: &dyn VersionedLanguageRegistryReader,
    ) -> Result<PreparedRegistryLanguage, PrepareRegistryError<ValueToCoreError>> {
        let resolver = RegistryLanguageResolver { registry };
        self.prepare_install(compiler_abi, unicode_version, |value| {
            crate::canonical::value_to_core_with_resolver(value, &resolver)
        })
    }

    pub fn install<E, C>(
        &self,
        compiler_abi: &str,
        unicode_version: &str,
        lower: impl FnOnce(&RhoValue) -> Result<GrammarCoreV1, E>,
        compile: impl FnOnce(&GrammarCoreV1) -> Result<ParserImageV1, C>,
    ) -> Result<InstalledRegistryLanguage, InstallRegistryError<E, C>> {
        let prepared = self
            .prepare_install(compiler_abi, unicode_version, lower)
            .map_err(InstallRegistryError::Prepare)?;
        prepared
            .install(compiler_abi, unicode_version, compile)
            .map_err(|error| match error {
                FinishRegistryInstallError::Compile(error) => InstallRegistryError::Compile(error),
                FinishRegistryInstallError::InvalidCompilerImage(error) => {
                    InstallRegistryError::InvalidCompilerImage(error)
                },
            })
    }

    pub fn install_with_registry<C>(
        &self,
        compiler_abi: &str,
        unicode_version: &str,
        registry: &dyn VersionedLanguageRegistryReader,
        compile: impl FnOnce(&GrammarCoreV1) -> Result<ParserImageV1, C>,
    ) -> Result<InstalledRegistryLanguage, InstallRegistryError<ValueToCoreError, C>> {
        let resolver = RegistryLanguageResolver { registry };
        self.install(
            compiler_abi,
            unicode_version,
            |value| crate::canonical::value_to_core_with_resolver(value, &resolver),
            compile,
        )
    }
}

pub trait VersionedLanguageRegistryReader {
    fn lookup_language(&self, name: &str) -> Result<Option<RegistryLanguageRecord>, String>;
}

struct RegistryLanguageResolver<'a> {
    registry: &'a dyn VersionedLanguageRegistryReader,
}

impl LanguageValueResolver for RegistryLanguageResolver<'_> {
    fn resolve_language(&self, name: &str) -> Result<Option<RhoValue>, String> {
        self.registry.lookup_language(name).and_then(|record| {
            record
                .map(|record| {
                    if record.schema != REGISTRY_LANGUAGE_SCHEMA_V1 {
                        Err(format!(
                            "language `{name}` has unsupported registry schema `{}`",
                            record.schema
                        ))
                    } else {
                        Ok(record.spec)
                    }
                })
                .transpose()
        })
    }
}

pub struct PreparedRegistryLanguage {
    pub authoritative_spec: RhoValue,
    pub core: GrammarCoreV1,
    pub cache: ParserCache,
}

impl PreparedRegistryLanguage {
    pub fn install<C>(
        self,
        compiler_abi: &str,
        unicode_version: &str,
        compile: impl FnOnce(&GrammarCoreV1) -> Result<ParserImageV1, C>,
    ) -> Result<InstalledRegistryLanguage, FinishRegistryInstallError<C>> {
        let (parser_image, cache_disposition) = match self.cache {
            ParserCache::Verified(image) => (*image, ParserCacheDisposition::ReusedVerified),
            ParserCache::Missing => {
                let image = compile(&self.core).map_err(FinishRegistryInstallError::Compile)?;
                image
                    .verify_executable(&self.core, compiler_abi, unicode_version)
                    .map_err(FinishRegistryInstallError::InvalidCompilerImage)?;
                (image, ParserCacheDisposition::CompiledMissing)
            },
            ParserCache::Rejected(reason) => {
                let image = compile(&self.core).map_err(FinishRegistryInstallError::Compile)?;
                image
                    .verify_executable(&self.core, compiler_abi, unicode_version)
                    .map_err(FinishRegistryInstallError::InvalidCompilerImage)?;
                (image, ParserCacheDisposition::RecompiledRejected { reason })
            },
        };
        Ok(InstalledRegistryLanguage {
            authoritative_spec: self.authoritative_spec,
            core: self.core,
            parser_image,
            cache_disposition,
        })
    }
}

pub struct InstalledRegistryLanguage {
    pub authoritative_spec: RhoValue,
    pub core: GrammarCoreV1,
    pub parser_image: ParserImageV1,
    pub cache_disposition: ParserCacheDisposition,
}

impl InstalledRegistryLanguage {
    /// Atomically publish this fully prepared Registry record into the neutral
    /// installed-language capability table. The canonical Registry value was
    /// authoritative during lowering; the image is re-admitted by the table
    /// immediately before the single publication commit.
    #[allow(clippy::too_many_arguments)]
    pub fn commit(
        self,
        table: &InstalledLanguageTable,
        granted_rights: LanguageRights,
        compiler_abi: &str,
        unicode_version: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
    ) -> Result<InstalledLanguageGrant, InstallLanguageError> {
        table.install_runtime(
            self.core,
            self.parser_image,
            granted_rights,
            compiler_abi,
            unicode_version,
            capability_abi,
            policy_fingerprint,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParserCacheDisposition {
    ReusedVerified,
    CompiledMissing,
    RecompiledRejected { reason: String },
}

pub enum ParserCache {
    Missing,
    Verified(Box<ParserImageV1>),
    /// The cache is discarded and the installation transaction compiles a
    /// fresh image from `PreparedRegistryLanguage::core`.
    Rejected(String),
}

#[derive(Debug)]
pub enum PrepareRegistryError<E> {
    UnsupportedSchema(String),
    Lowering(E),
    InvalidGrammar(Vec<mettail_grammar_core::ValidationError>),
    Fingerprint(String),
}

#[derive(Debug)]
pub enum InstallRegistryError<E, C> {
    Prepare(PrepareRegistryError<E>),
    Compile(C),
    InvalidCompilerImage(ImageError),
}

#[derive(Debug)]
pub enum FinishRegistryInstallError<C> {
    Compile(C),
    InvalidCompilerImage(ImageError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module::{CanonicalModuleExport, CanonicalModuleValue};
    use crate::resolve::ModuleRef;
    use mettail_grammar_core::{
        normalize_runtime_engine, Carrier, Category, CategoryId, IndexWidth, LanguageAccessError,
        LanguageRight, LexerImage, LexerState, ParserImageKind, PARSER_IMAGE_ABI_V1,
        PARSER_IMAGE_MAGIC,
    };

    fn core(name: &str) -> GrammarCoreV1 {
        let mut core = GrammarCoreV1::new(name);
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        core
    }

    fn canonical_module() -> CanonicalModuleValue {
        CanonicalModuleValue {
            name: "Pair".into(),
            dependencies: vec![CanonicalModuleDependency {
                reference: ModuleRef::Registry("rho:base".into()),
                commitment: [0x31; 32],
            }],
            exports: vec![CanonicalModuleExport {
                name: "Only".into(),
                spec: RhoValue::String("authoritative".into()),
            }],
        }
    }

    #[test]
    fn registry_module_projections_and_signed_payload_are_exact() {
        let mut record =
            RegistryModuleRecord::new("Module Pair {}", canonical_module(), RhoValue::Nil);
        let payload = record.signed_payload().expect("record validates");
        record.images.insert([0x44; 32], vec![1, 2, 3]);
        assert_eq!(
            record
                .signed_payload()
                .expect("cache remains non-authoritative"),
            payload,
            "untrusted parser caches are excluded from signed semantic content",
        );
        let exports = record.export_records().expect("exports project");
        assert_eq!(exports.len(), 1);
        assert_eq!(exports[0].0, "Only");
        assert_eq!(exports[0].1.parser_images.len(), 1);
    }

    #[test]
    fn registry_module_redundancy_detects_tampering() {
        let mut record =
            RegistryModuleRecord::new("Module Pair {}", canonical_module(), RhoValue::Nil);
        record.exports.insert("Injected".into(), RhoValue::Nil);
        assert!(matches!(
            record.validate_structure(),
            Err(RegistryModuleError::ExportProjectionMismatch)
        ));
    }

    #[test]
    fn source_oracle_is_checked_only_when_developer_tooling_requests_it() {
        let mut record =
            RegistryModuleRecord::new("Module Pair {}", canonical_module(), RhoValue::Nil);
        record.source.push(' ');
        assert!(record.validate_structure().is_ok());
        assert!(matches!(
            record.validate_source_oracle(),
            Err(RegistryModuleError::SourceCommitmentMismatch)
        ));
    }

    #[test]
    fn content_commitment_excludes_source_oracle_bytes_and_parser_images() {
        let mut record =
            RegistryModuleRecord::new("Module Pair {}", canonical_module(), RhoValue::Nil);
        let commitment = record.content_commitment().expect("record validates");
        record.source = "not even valid MeTTaIL source".into();
        record.images.insert([0x44; 32], vec![1, 2, 3]);
        assert_eq!(
            record
                .content_commitment()
                .expect("canonical record still validates"),
            commitment
        );
    }

    #[test]
    fn unsigned_invalid_cache_cannot_veto_signed_canonical_content() {
        let mut record =
            RegistryModuleRecord::new("Module Pair {}", canonical_module(), RhoValue::Nil);
        let payload = record.signed_payload().expect("canonical record validates");
        record.images.insert([0x44; 32], Vec::new());
        assert_eq!(
            record
                .signed_payload()
                .expect("an unsigned cache cannot invalidate canonical content"),
            payload,
        );
        assert_eq!(
            record
                .export_records()
                .expect("cache validation is deferred until fingerprint selection")
                .len(),
            1,
        );
    }

    fn executable(core: &GrammarCoreV1, compiler: &str, unicode: &str) -> ParserImageV1 {
        let engine = normalize_runtime_engine(core).expect("normalize");
        ParserImageV1 {
            magic: PARSER_IMAGE_MAGIC,
            abi: PARSER_IMAGE_ABI_V1,
            compiler_abi: compiler.into(),
            unicode_version: unicode.into(),
            core_fingerprint: core.fingerprint().expect("fingerprint"),
            kind: ParserImageKind::Executable,
            index_width: IndexWidth::for_max(
                core.categories
                    .len()
                    .max(core.tokens.len())
                    .max(core.productions.len())
                    .max(engine.nonterminal_count as usize),
            ),
            exact: true,
            lexer: LexerImage {
                mode_starts: vec![0],
                states: vec![LexerState {
                    transition_start: 0,
                    transition_len: 0,
                    accept: Vec::new(),
                }],
                transitions: Vec::new(),
            },
            reductions: core.reductions.clone(),
            engine,
            limits: core.limits,
        }
    }

    #[test]
    fn metadata_cache_is_rejected_after_authoritative_lowering() {
        let spec = RhoValue::String("authority".into());
        let authoritative_core = core("A");
        let metadata = ParserImageV1::metadata_only(&authoritative_core, "compiler/1", "15.1")
            .expect("valid metadata")
            .encode()
            .expect("encodable metadata");
        let mut record = RegistryLanguageRecord::new(spec.clone());
        record.parser_image = Some(metadata);
        let prepared = record
            .prepare_install("compiler/1", "15.1", |value| {
                assert_eq!(value, &spec);
                Ok::<_, ()>(authoritative_core.clone())
            })
            .expect("valid authoritative spec");
        assert!(matches!(prepared.cache, ParserCache::Rejected(_)));
        assert_eq!(prepared.authoritative_spec, spec);
    }

    #[test]
    fn mismatched_cache_is_discarded_not_promoted_to_authority() {
        let spec = RhoValue::String("authority".into());
        let cached_core = core("cached");
        let authoritative_core = core("authoritative");
        let mut metadata = ParserImageV1::metadata_only(&cached_core, "compiler/1", "15.1")
            .expect("valid metadata");
        metadata.kind = mettail_grammar_core::ParserImageKind::Executable;
        let mut record = RegistryLanguageRecord::new(spec);
        record.parser_image = Some(metadata.encode().expect("encodable image"));
        let prepared = record
            .prepare_install("compiler/1", "15.1", |_| Ok::<_, ()>(authoritative_core.clone()))
            .expect("valid authoritative spec");
        assert!(matches!(prepared.cache, ParserCache::Rejected(_)));
        assert_eq!(prepared.core.name, "authoritative");
    }

    #[test]
    fn missing_cache_is_compiled_and_verified_in_the_install_transaction() {
        let record = RegistryLanguageRecord::new(RhoValue::String("authority".into()));
        let authoritative = core("authoritative");
        let installed = record
            .install(
                "compiler/1",
                "15.1",
                |_| Ok::<_, ()>(authoritative.clone()),
                |core| Ok::<_, ()>(executable(core, "compiler/1", "15.1")),
            )
            .expect("install");
        assert_eq!(installed.core, authoritative);
        assert_eq!(installed.cache_disposition, ParserCacheDisposition::CompiledMissing);
    }

    #[test]
    fn verified_cache_is_reused_without_invoking_the_compiler() {
        let authoritative = core("authoritative");
        let mut record = RegistryLanguageRecord::new(RhoValue::String("authority".into()));
        record.parser_image = Some(
            executable(&authoritative, "compiler/1", "15.1")
                .encode()
                .expect("encode"),
        );
        let installed = record
            .install(
                "compiler/1",
                "15.1",
                |_| Ok::<_, ()>(authoritative.clone()),
                |_| -> Result<ParserImageV1, ()> { panic!("verified cache must be reused") },
            )
            .expect("install");
        assert_eq!(installed.cache_disposition, ParserCacheDisposition::ReusedVerified);
    }

    #[test]
    fn rejected_cache_is_recompiled_and_the_rejection_is_retained() {
        let authoritative = core("authoritative");
        let mut record = RegistryLanguageRecord::new(RhoValue::String("authority".into()));
        record.parser_image = Some(
            ParserImageV1::metadata_only(&authoritative, "compiler/1", "15.1")
                .expect("metadata")
                .encode()
                .expect("encode"),
        );
        let installed = record
            .install(
                "compiler/1",
                "15.1",
                |_| Ok::<_, ()>(authoritative.clone()),
                |core| Ok::<_, ()>(executable(core, "compiler/1", "15.1")),
            )
            .expect("install");
        assert!(matches!(
            installed.cache_disposition,
            ParserCacheDisposition::RecompiledRejected { .. }
        ));
    }

    #[test]
    fn compiler_output_is_independently_admitted_before_installation() {
        let authoritative = core("authoritative");
        let record = RegistryLanguageRecord::new(RhoValue::String("authority".into()));
        let result = record.install(
            "compiler/1",
            "15.1",
            |_| Ok::<_, ()>(authoritative.clone()),
            |core| Ok::<_, ()>(ParserImageV1::metadata_only(core, "compiler/1", "15.1").unwrap()),
        );
        assert!(matches!(
            result,
            Err(InstallRegistryError::InvalidCompilerImage(ImageError::NotExecutable))
        ));
    }

    #[test]
    fn registry_install_commits_only_explicitly_granted_rights() {
        let authoritative = core("authoritative");
        let record = RegistryLanguageRecord::new(RhoValue::String("authority".into()));
        let installed = record
            .install(
                "compiler/1",
                "15.1",
                |_| Ok::<_, ()>(authoritative.clone()),
                |core| Ok::<_, ()>(executable(core, "compiler/1", "15.1")),
            )
            .expect("prepare and compile");
        let table = InstalledLanguageTable::new();
        let grant = installed
            .commit(
                &table,
                LanguageRights::from_rights([LanguageRight::Parse]),
                "compiler/1",
                "15.1",
                "caps/1",
                [0; 32],
            )
            .expect("atomic publication");
        assert!(table.authorize(&grant.handle, LanguageRight::Parse).is_ok());
        assert!(matches!(
            table.authorize(&grant.handle, LanguageRight::Bridge),
            Err(LanguageAccessError::MissingRight(LanguageRight::Bridge))
        ));
    }
}
