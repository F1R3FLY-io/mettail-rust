//! Module and import resolution.
//!
//! Production imports resolve through Rholang's Versioned Registry. `file:` is
//! recognized but deliberately unavailable until the File I/O FIPS lands.
//! The trait boundary accepts a future capability-backed filesystem resolver
//! without giving this crate ambient filesystem authority.

use crate::ast::*;
use crate::diag::{Diag, DiagKind};
use crate::lex::Span;
use crate::parse::parse_module;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ModuleRef {
    Registry(String),
    File(String),
}

impl ModuleRef {
    pub fn parse(value: &str) -> Result<Self, ResolveError> {
        if let Some(name) = value.strip_prefix("rho:") {
            if name.is_empty() {
                return Err(ResolveError::InvalidReference(value.to_string()));
            }
            return Ok(Self::Registry(format!("rho:{name}")));
        }
        if let Some(path) = value.strip_prefix("file:") {
            if path.is_empty() {
                return Err(ResolveError::InvalidReference(value.to_string()));
            }
            return Ok(Self::File(path.to_string()));
        }
        if value.contains(':') {
            return Err(ResolveError::UnsupportedScheme(value.to_string()));
        }
        if value.is_empty() {
            return Err(ResolveError::InvalidReference(value.to_string()));
        }
        Ok(Self::File(value.to_string()))
    }

    pub fn external_form(&self) -> String {
        match self {
            Self::Registry(uri) => uri.clone(),
            Self::File(path) => format!("file:{path}"),
        }
    }
}

impl fmt::Display for ModuleRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.external_form())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedModule {
    pub canonical_ref: ModuleRef,
    pub source: String,
    pub content_hash: Option<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveError {
    InvalidReference(String),
    UnsupportedScheme(String),
    NotFound(ModuleRef),
    Registry(String),
    FileIoUnavailable { reference: ModuleRef },
    IntegrityMismatch { reference: ModuleRef },
    LimitExceeded { resource: &'static str, limit: usize },
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidReference(value) => {
                write!(formatter, "invalid module reference `{value}`")
            },
            Self::UnsupportedScheme(value) => {
                write!(formatter, "unsupported module scheme in `{value}`")
            },
            Self::NotFound(reference) => write!(formatter, "module `{reference}` was not found"),
            Self::Registry(message) => {
                write!(formatter, "Rholang registry lookup failed: {message}")
            },
            Self::FileIoUnavailable { reference } => write!(
                formatter,
                "module `{reference}` requires the future Rholang File I/O capability"
            ),
            Self::IntegrityMismatch { reference } => {
                write!(formatter, "content commitment mismatch for module `{reference}`")
            },
            Self::LimitExceeded { resource, limit } => {
                write!(formatter, "module {resource} limit exceeded (maximum {limit})")
            },
        }
    }
}

/// Bounds applied before and while parsing an untrusted module graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolveLimits {
    pub max_modules: usize,
    pub max_module_source_bytes: usize,
    pub max_total_source_bytes: usize,
    pub max_imports_per_module: usize,
}

impl Default for ResolveLimits {
    fn default() -> Self {
        Self {
            max_modules: 256,
            max_module_source_bytes: 4 * 1024 * 1024,
            max_total_source_bytes: 16 * 1024 * 1024,
            max_imports_per_module: 256,
        }
    }
}

pub trait Resolver {
    fn fetch(&self, reference: &ModuleRef) -> Result<ResolvedModule, ResolveError>;

    fn join(&self, base: &ModuleRef, child: &str) -> Result<ModuleRef, ResolveError> {
        if child.starts_with("rho:") || child.starts_with("file:") || child.contains(':') {
            return ModuleRef::parse(child);
        }
        match base {
            ModuleRef::Registry(_) => Err(ResolveError::InvalidReference(child.to_string())),
            ModuleRef::File(path) => {
                let joined = match path.rfind('/') {
                    Some(index) => format!("{}{}", &path[..=index], child),
                    None => child.to_string(),
                };
                Ok(ModuleRef::File(joined))
            },
        }
    }
}

/// Adapter to the approved Rholang Versioned Registry implementation.
///
/// The node supplies this interface from its registry system process. Keeping
/// the dependency inverted lets the elaborator remain deterministic and easy
/// to test; it also avoids manufacturing a second registry in this crate.
pub trait VersionedRegistryReader {
    fn lookup_module(&self, uri: &str) -> Result<Option<RegistryModuleValue>, String>;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryModuleValue {
    pub source: String,
    pub content_hash: Option<[u8; 32]>,
}

pub struct RegistryResolver<R> {
    reader: R,
}

impl<R> RegistryResolver<R> {
    pub fn new(reader: R) -> Self {
        Self { reader }
    }
}

impl<R: VersionedRegistryReader> Resolver for RegistryResolver<R> {
    fn fetch(&self, reference: &ModuleRef) -> Result<ResolvedModule, ResolveError> {
        match reference {
            ModuleRef::Registry(uri) => {
                let value = self
                    .reader
                    .lookup_module(uri)
                    .map_err(ResolveError::Registry)?
                    .ok_or_else(|| ResolveError::NotFound(reference.clone()))?;
                Ok(ResolvedModule {
                    canonical_ref: reference.clone(),
                    source: value.source,
                    content_hash: value.content_hash,
                })
            },
            ModuleRef::File(_) => {
                Err(ResolveError::FileIoUnavailable { reference: reference.clone() })
            },
        }
    }
}

/// In-memory resolver: the test and embedded-corpus case.
#[derive(Default)]
pub struct MemResolver {
    pub modules: HashMap<ModuleRef, RegistryModuleValue>,
}

impl MemResolver {
    pub fn new() -> MemResolver {
        MemResolver::default()
    }
    pub fn with(mut self, reference: &str, source: &str) -> MemResolver {
        let reference = ModuleRef::parse(reference).expect("test module reference is valid");
        self.modules.insert(
            reference,
            RegistryModuleValue {
                source: source.to_string(),
                content_hash: None,
            },
        );
        self
    }

    pub fn with_commitment(
        mut self,
        reference: &str,
        source: &str,
        content_hash: [u8; 32],
    ) -> MemResolver {
        let reference = ModuleRef::parse(reference).expect("test module reference is valid");
        self.modules.insert(
            reference,
            RegistryModuleValue {
                source: source.to_string(),
                content_hash: Some(content_hash),
            },
        );
        self
    }
}

impl Resolver for MemResolver {
    fn fetch(&self, reference: &ModuleRef) -> Result<ResolvedModule, ResolveError> {
        let value = self
            .modules
            .get(reference)
            .cloned()
            .ok_or_else(|| ResolveError::NotFound(reference.clone()))?;
        Ok(ResolvedModule {
            canonical_ref: reference.clone(),
            source: value.source,
            content_hash: value.content_hash,
        })
    }
}

/// A resolved import graph plus the entry module.
pub struct Program {
    entry: ModuleRef,
    modules: HashMap<ModuleRef, ModuleFile>,
    commitments: HashMap<ModuleRef, Option<[u8; 32]>>,
}

impl Program {
    pub fn load(entry: &ModuleRef, resolver: &dyn Resolver) -> Result<Program, Diag> {
        Self::load_with_limits(entry, resolver, ResolveLimits::default())
    }

    pub fn load_with_limits(
        entry: &ModuleRef,
        resolver: &dyn Resolver,
        limits: ResolveLimits,
    ) -> Result<Program, Diag> {
        let mut modules = HashMap::new();
        let mut commitments = HashMap::new();
        let mut total_source_bytes = 0usize;
        let mut stack = vec![(entry.clone(), vec![entry.clone()])];

        while let Some((reference, chain)) = stack.pop() {
            if modules.contains_key(&reference) {
                continue;
            }
            if modules.len() >= limits.max_modules {
                return Err(resolve_diag(
                    ResolveError::LimitExceeded {
                        resource: "count",
                        limit: limits.max_modules,
                    },
                    Span { line: 0, col: 0 },
                    &chain,
                ));
            }
            let resolved = resolver
                .fetch(&reference)
                .map_err(|error| resolve_diag(error, Span { line: 0, col: 0 }, &chain))?;
            if resolved.source.len() > limits.max_module_source_bytes {
                return Err(resolve_diag(
                    ResolveError::LimitExceeded {
                        resource: "source-byte",
                        limit: limits.max_module_source_bytes,
                    },
                    Span { line: 0, col: 0 },
                    &chain,
                ));
            }
            total_source_bytes = total_source_bytes
                .checked_add(resolved.source.len())
                .ok_or_else(|| {
                    resolve_diag(
                        ResolveError::LimitExceeded {
                            resource: "total-source-byte",
                            limit: limits.max_total_source_bytes,
                        },
                        Span { line: 0, col: 0 },
                        &chain,
                    )
                })?;
            if total_source_bytes > limits.max_total_source_bytes {
                return Err(resolve_diag(
                    ResolveError::LimitExceeded {
                        resource: "total-source-byte",
                        limit: limits.max_total_source_bytes,
                    },
                    Span { line: 0, col: 0 },
                    &chain,
                ));
            }
            if let Some(expected) = resolved.content_hash {
                let actual = *blake3::hash(resolved.source.as_bytes()).as_bytes();
                if actual != expected {
                    return Err(resolve_diag(
                        ResolveError::IntegrityMismatch {
                            reference: resolved.canonical_ref.clone(),
                        },
                        Span { line: 0, col: 0 },
                        &chain,
                    ));
                }
            }
            let module = parse_module(&resolved.source).map_err(|mut error| {
                error.msg = format!("{}; import chain: {}", error.msg, format_chain(&chain));
                error
            })?;
            if module.imports.len() > limits.max_imports_per_module {
                return Err(resolve_diag(
                    ResolveError::LimitExceeded {
                        resource: "imports-per-module",
                        limit: limits.max_imports_per_module,
                    },
                    Span { line: 0, col: 0 },
                    &chain,
                ));
            }
            for import in &module.imports {
                let child = resolver
                    .join(&resolved.canonical_ref, import.url())
                    .map_err(|error| resolve_diag(error, import.span(), &chain))?;
                if !modules.contains_key(&child) {
                    let mut child_chain = chain.clone();
                    child_chain.push(child.clone());
                    stack.push((child, child_chain));
                }
            }
            commitments.insert(resolved.canonical_ref.clone(), resolved.content_hash);
            modules.insert(resolved.canonical_ref, module);
        }

        detect_cycle(entry, &modules, resolver)?;

        Ok(Program {
            entry: entry.clone(),
            modules,
            commitments,
        })
    }

    pub fn entry_url(&self) -> &ModuleRef {
        &self.entry
    }
    pub fn entry_module(&self) -> &ModuleFile {
        &self.modules[&self.entry]
    }
    pub fn module(&self, reference: &ModuleRef) -> Option<&ModuleFile> {
        self.modules.get(reference)
    }

    /// Plan 9.1: what a reproducible build would record.
    pub fn lockfile(&self) -> Vec<(ModuleRef, Option<[u8; 32]>)> {
        let mut v: Vec<_> = self
            .commitments
            .iter()
            .map(|(reference, hash)| (reference.clone(), *hash))
            .collect();
        v.sort();
        v
    }

    /// Resolve a dotted path to a theory declaration and the url of the module
    /// that owns it.
    pub fn lookup(
        &self,
        path: &DottedPath,
        here: &ModuleRef,
        span: Span,
    ) -> Result<(TheoryDecl, ModuleRef), Diag> {
        let m = self.modules.get(here).ok_or_else(|| {
            Diag::new(DiagKind::Resolution, format!("unknown module {here}"), span)
        })?;

        if path.is_simple() {
            let name = path.last();
            if let Some(d) = m.decls.iter().find(|d| d.name == name) {
                return Ok((d.clone(), here.clone()));
            }
            // `import Name from "<url>"`
            for imp in &m.imports {
                if let Import::FromModule { name: n, url, .. } = imp {
                    if n == name {
                        let child = self.child_ref(here, url)?;
                        if let Some(cm) = self.modules.get(&child) {
                            if let Some(d) = cm.decls.iter().find(|d| d.name == name) {
                                return Ok((d.clone(), child));
                            }
                        }
                    }
                }
            }
            return Err(Diag::new(
                DiagKind::Resolution,
                format!("no theory named `{name}` in scope"),
                span,
            ));
        }

        // Qualified: alias . Name
        let alias = &path.0[0];
        let rest = path.0[1..].join(".");
        for imp in &m.imports {
            if let Import::ModuleAs { url, alias: a, .. } = imp {
                if a == alias {
                    let child = self.child_ref(here, url)?;
                    let cm = self.modules.get(&child).ok_or_else(|| {
                        Diag::new(
                            DiagKind::Resolution,
                            format!("module {child} was not loaded"),
                            span,
                        )
                    })?;
                    if let Some(d) = cm.decls.iter().find(|d| d.name == rest) {
                        return Ok((d.clone(), child));
                    }
                    return Err(Diag::new(
                        DiagKind::Resolution,
                        format!("module `{alias}` has no theory `{rest}`"),
                        span,
                    ));
                }
            }
        }
        Err(Diag::new(DiagKind::Resolution, format!("no import aliased `{alias}`"), span))
    }

    fn child_ref(&self, base: &ModuleRef, value: &str) -> Result<ModuleRef, Diag> {
        if let Ok(reference) = ModuleRef::parse(value) {
            if self.modules.contains_key(&reference) {
                return Ok(reference);
            }
        }
        match base {
            ModuleRef::File(path) => {
                let joined = match path.rfind('/') {
                    Some(index) => ModuleRef::File(format!("{}{}", &path[..=index], value)),
                    None => ModuleRef::File(value.to_string()),
                };
                Ok(joined)
            },
            ModuleRef::Registry(_) => Err(Diag::new(
                DiagKind::Resolution,
                format!("registry module imports must use an explicit `rho:` reference: `{value}`"),
                Span { line: 0, col: 0 },
            )),
        }
    }
}

fn format_chain(chain: &[ModuleRef]) -> String {
    chain
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" -> ")
}

fn resolve_diag(error: ResolveError, span: Span, chain: &[ModuleRef]) -> Diag {
    Diag::new(
        DiagKind::Resolution,
        format!("{error}; import chain: {}", format_chain(chain)),
        span,
    )
}

fn detect_cycle(
    entry: &ModuleRef,
    modules: &HashMap<ModuleRef, ModuleFile>,
    resolver: &dyn Resolver,
) -> Result<(), Diag> {
    fn go(
        reference: &ModuleRef,
        modules: &HashMap<ModuleRef, ModuleFile>,
        resolver: &dyn Resolver,
        path: &mut Vec<ModuleRef>,
        done: &mut Vec<ModuleRef>,
    ) -> Result<(), Diag> {
        if done.contains(reference) {
            return Ok(());
        }
        if path.contains(reference) {
            return Err(Diag::new(
                DiagKind::Resolution,
                format!(
                    "import cycle: {} -> {reference}",
                    path.iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" -> ")
                ),
                Span { line: 0, col: 0 },
            ));
        }
        path.push(reference.clone());
        if let Some(m) = modules.get(reference) {
            for imp in &m.imports {
                let child = resolver.join(reference, imp.url()).map_err(|error| {
                    Diag::new(DiagKind::Resolution, error.to_string(), imp.span())
                })?;
                go(&child, modules, resolver, path, done)?;
            }
        }
        path.pop();
        done.push(reference.clone());
        Ok(())
    }
    let mut path = Vec::new();
    let mut done = Vec::new();
    go(entry, modules, resolver, &mut path, &mut done)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EmptyRegistry;

    impl VersionedRegistryReader for EmptyRegistry {
        fn lookup_module(&self, _uri: &str) -> Result<Option<RegistryModuleValue>, String> {
            Ok(None)
        }
    }

    #[test]
    fn bare_paths_are_future_file_references() {
        assert_eq!(
            ModuleRef::parse("grammars/a.module"),
            Ok(ModuleRef::File("grammars/a.module".into()))
        );
    }

    #[test]
    fn production_resolver_refuses_file_until_capability_exists() {
        let resolver = RegistryResolver::new(EmptyRegistry);
        let reference = ModuleRef::parse("file:grammar.module").expect("valid reference");
        assert!(matches!(
            resolver.fetch(&reference),
            Err(ResolveError::FileIoUnavailable { .. })
        ));
    }

    #[test]
    fn program_rejects_a_mismatched_registry_commitment_before_parsing() {
        let reference = ModuleRef::parse("rho:test").expect("valid reference");
        let source = "Module Test { Theory T() { Empty } theory T() }";
        let resolver = MemResolver::new().with_commitment("rho:test", source, [0x55; 32]);
        let error = match Program::load(&reference, &resolver) {
            Ok(_) => panic!("commitment must be checked"),
            Err(error) => error,
        };
        assert!(error.msg.contains("content commitment mismatch"), "{error}");
    }

    #[test]
    fn program_accepts_a_matching_registry_commitment() {
        let reference = ModuleRef::parse("rho:test").expect("valid reference");
        let source = "Module Test { Theory T() { Empty } theory T() }";
        let hash = *blake3::hash(source.as_bytes()).as_bytes();
        let resolver = MemResolver::new().with_commitment("rho:test", source, hash);
        Program::load(&reference, &resolver).expect("matching commitment is accepted");
    }

    #[test]
    fn missing_registry_module_reports_the_complete_import_chain() {
        let resolver = MemResolver::new()
            .with(
                "rho:a",
                r#"import "rho:b" as b
                   Module A { Theory T() { Empty } theory T() }"#,
            )
            .with(
                "rho:b",
                r#"import "rho:missing" as missing
                   Module B { Theory T() { Empty } theory T() }"#,
            );
        let entry = ModuleRef::parse("rho:a").expect("valid reference");
        let error = match Program::load(&entry, &resolver) {
            Ok(_) => panic!("missing import must fail"),
            Err(error) => error,
        };

        assert!(error.msg.contains("rho:a -> rho:b -> rho:missing"), "{error}");
    }

    #[test]
    fn module_source_limit_is_enforced_before_parsing() {
        let source = "Module Test { Theory T() { Empty } theory T() }";
        let resolver = MemResolver::new().with("rho:test", source);
        let entry = ModuleRef::parse("rho:test").expect("valid reference");
        let limits = ResolveLimits {
            max_module_source_bytes: source.len() - 1,
            ..ResolveLimits::default()
        };
        let error = match Program::load_with_limits(&entry, &resolver, limits) {
            Ok(_) => panic!("oversized source must fail"),
            Err(error) => error,
        };

        assert!(error.msg.contains("source-byte limit exceeded"), "{error}");
        assert!(error.msg.contains("import chain: rho:test"), "{error}");
    }
}
