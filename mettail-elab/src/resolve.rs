//! Module and import resolution.
//!
//! Production imports resolve through Rholang's Versioned Registry. `file:` is
//! recognized but deliberately unavailable until the File I/O FIPS lands.
//! The trait boundary accepts a future capability-backed filesystem resolver
//! without giving this crate ambient filesystem authority.

use crate::ast::*;
use crate::diag::{Diag, DiagKind, SourceProvenance};
use crate::lex::Span;
use crate::parse::parse_module;
pub use crate::registry::RegistryModuleRecord as RegistryModuleValue;
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
    /// Exact BLAKE3 commitment supplied by the resolver authority.
    pub content_hash: [u8; 32],
    /// Signed Registry `module/1` projection for parity checking. Inline and
    /// future capability-backed filesystem sources carry no Registry value.
    pub canonical_module: Option<crate::canonical::RhoValue>,
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
    fn verify_module_trust(
        &self,
        uri: &str,
        signed_payload: &[u8],
        signatures: &crate::canonical::RhoValue,
    ) -> Result<(), String>;
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
                let signed_payload = value
                    .signed_payload()
                    .map_err(|error| ResolveError::Registry(error.to_string()))?;
                self.reader
                    .verify_module_trust(uri, &signed_payload, &value.signatures)
                    .map_err(ResolveError::Registry)?;
                Ok(ResolvedModule {
                    canonical_ref: reference.clone(),
                    canonical_module: Some(value.module),
                    source: value.source,
                    content_hash: value.source_commitment,
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
    pub modules: HashMap<ModuleRef, ResolvedModule>,
}

impl MemResolver {
    pub fn new() -> MemResolver {
        MemResolver::default()
    }
    pub fn with(mut self, reference: &str, source: &str) -> MemResolver {
        let reference = ModuleRef::parse(reference).expect("test module reference is valid");
        self.modules.insert(
            reference.clone(),
            ResolvedModule {
                canonical_ref: reference,
                source: source.to_string(),
                content_hash: *blake3::hash(source.as_bytes()).as_bytes(),
                canonical_module: None,
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
            reference.clone(),
            ResolvedModule {
                canonical_ref: reference,
                source: source.to_string(),
                content_hash,
                canonical_module: None,
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
        Ok(value)
    }
}

/// A resolved import graph plus the entry module.
pub struct Program {
    entry: ModuleRef,
    modules: HashMap<ModuleRef, ModuleFile>,
    declaration_indices: HashMap<ModuleRef, HashMap<String, usize>>,
    commitments: HashMap<ModuleRef, [u8; 32]>,
    resolution_order: Vec<ModuleRef>,
    adjacency: HashMap<ModuleRef, Vec<ModuleRef>>,
    registry_modules: HashMap<ModuleRef, crate::canonical::RhoValue>,
}

impl Program {
    pub(crate) fn from_single_module(
        entry: ModuleRef,
        module: ModuleFile,
    ) -> Result<Program, Diag> {
        validate_module_structure(&module)?;
        let mut modules = HashMap::new();
        modules.insert(entry.clone(), module);
        let declaration_indices = index_declarations(&modules);
        Ok(Program {
            entry,
            modules,
            declaration_indices,
            commitments: HashMap::new(),
            resolution_order: Vec::new(),
            adjacency: HashMap::new(),
            registry_modules: HashMap::new(),
        })
    }

    pub fn load(entry: &ModuleRef, resolver: &dyn Resolver) -> Result<Program, Diag> {
        Self::load_with_limits(entry, resolver, ResolveLimits::default())
    }

    pub fn load_with_limits(
        entry: &ModuleRef,
        resolver: &dyn Resolver,
        limits: ResolveLimits,
    ) -> Result<Program, Diag> {
        Self::load_graph(entry, None, resolver, limits)
    }

    /// Resolve imports around an entry module that the host Rholang parser has
    /// already produced structurally. Only imported Registry/File-I/O records
    /// cross the resolver; the entry is never rendered and parsed again.
    pub fn load_from_ast(
        entry: &ModuleRef,
        module: ModuleFile,
        resolver: &dyn Resolver,
    ) -> Result<Program, Diag> {
        Self::load_from_ast_with_limits(entry, module, resolver, ResolveLimits::default())
    }

    pub fn load_from_ast_with_limits(
        entry: &ModuleRef,
        module: ModuleFile,
        resolver: &dyn Resolver,
        limits: ResolveLimits,
    ) -> Result<Program, Diag> {
        Self::load_graph(entry, Some(module), resolver, limits)
    }

    fn load_graph(
        entry: &ModuleRef,
        entry_module: Option<ModuleFile>,
        resolver: &dyn Resolver,
        limits: ResolveLimits,
    ) -> Result<Program, Diag> {
        let mut modules = HashMap::new();
        let mut commitments = HashMap::new();
        let mut resolution_order = Vec::new();
        let mut adjacency = HashMap::new();
        let mut registry_modules = HashMap::new();
        let mut total_source_bytes = 0usize;
        let mut stack = vec![(entry.clone(), vec![entry.clone()], entry_module)];

        while let Some((reference, chain, parsed_entry)) = stack.pop() {
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
            let (canonical_ref, module, content_hash, canonical_module) = match parsed_entry {
                Some(module) => (reference.clone(), module, None, None),
                None => {
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
                    let actual = *blake3::hash(resolved.source.as_bytes()).as_bytes();
                    if actual != resolved.content_hash {
                        return Err(resolve_diag(
                            ResolveError::IntegrityMismatch {
                                reference: resolved.canonical_ref.clone(),
                            },
                            Span { line: 0, col: 0 },
                            &chain,
                        ));
                    }
                    let module = parse_module(&resolved.source).map_err(|mut error| {
                        error.msg =
                            format!("{}; import chain: {}", error.msg, format_chain(&chain));
                        error.attach_provenance(SourceProvenance {
                            reference: resolved.canonical_ref.external_form(),
                            content_commitment: Some(resolved.content_hash),
                            import_chain: chain.iter().map(ModuleRef::external_form).collect(),
                        });
                        error
                    })?;
                    (
                        resolved.canonical_ref,
                        module,
                        Some(resolved.content_hash),
                        resolved.canonical_module,
                    )
                },
            };
            validate_module_structure(&module).map_err(|mut error| {
                error.attach_provenance(SourceProvenance {
                    reference: canonical_ref.external_form(),
                    content_commitment: content_hash,
                    import_chain: chain.iter().map(ModuleRef::external_form).collect(),
                });
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
            let mut children = Vec::with_capacity(module.imports.len());
            for import in &module.imports {
                children.push(
                    resolver
                        .join(&canonical_ref, import.url())
                        .map_err(|error| resolve_diag(error, import.span(), &chain))?,
                );
            }
            // Push in reverse because this is a LIFO worklist. The resulting
            // first-visit order is deterministic depth-first source order.
            for child in children.iter().rev() {
                if !modules.contains_key(child) {
                    let mut child_chain = chain.clone();
                    child_chain.push(child.clone());
                    stack.push((child.clone(), child_chain, None));
                }
            }
            adjacency.insert(canonical_ref.clone(), children);
            if let Some(canonical_module) = canonical_module {
                registry_modules.insert(canonical_ref.clone(), canonical_module);
            }
            if let Some(content_hash) = content_hash {
                commitments.insert(canonical_ref.clone(), content_hash);
            }
            resolution_order.push(canonical_ref.clone());
            modules.insert(canonical_ref, module);
        }

        detect_cycle(entry, &modules, resolver)?;
        let declaration_indices = index_declarations(&modules);

        Ok(Program {
            entry: entry.clone(),
            modules,
            declaration_indices,
            commitments,
            resolution_order,
            adjacency,
            registry_modules,
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
    pub fn commitment(&self, reference: &ModuleRef) -> Option<[u8; 32]> {
        self.commitments.get(reference).copied()
    }

    /// Plan 9.1: what a reproducible build would record.
    pub fn lockfile(&self) -> Vec<(ModuleRef, [u8; 32])> {
        self.resolution_order
            .iter()
            .map(|reference| {
                (
                    reference.clone(),
                    *self
                        .commitments
                        .get(reference)
                        .expect("every resolved module has an exact commitment"),
                )
            })
            .collect()
    }

    /// Canonical module dependencies in deterministic first-use source order.
    /// The entry module is content being described, not its own dependency.
    pub fn dependency_lockfile(&self) -> Vec<(ModuleRef, [u8; 32])> {
        self.dependency_lockfile_from(&self.entry)
    }

    /// Transitive dependencies of an arbitrary loaded module in deterministic
    /// depth-first, first-use source order.
    pub fn dependency_lockfile_from(&self, root: &ModuleRef) -> Vec<(ModuleRef, [u8; 32])> {
        let mut seen = std::collections::HashSet::from([root.clone()]);
        let mut output = Vec::new();
        let mut work = self
            .adjacency
            .get(root)
            .into_iter()
            .flatten()
            .rev()
            .cloned()
            .collect::<Vec<_>>();
        while let Some(reference) = work.pop() {
            if !seen.insert(reference.clone()) {
                continue;
            }
            output.push((
                reference.clone(),
                *self
                    .commitments
                    .get(&reference)
                    .expect("every dependency has an exact commitment"),
            ));
            if let Some(children) = self.adjacency.get(&reference) {
                work.extend(children.iter().rev().cloned());
            }
        }
        output
    }

    pub(crate) fn registry_module_expectations(
        &self,
    ) -> impl Iterator<Item = (&ModuleRef, &crate::canonical::RhoValue)> {
        self.resolution_order.iter().filter_map(|reference| {
            self.registry_modules
                .get(reference)
                .map(|module| (reference, module))
        })
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
            if let Some(d) = self.declaration(here, name) {
                return Ok((d.clone(), here.clone()));
            }
            // `import Name from "<url>"`
            for imp in &m.imports {
                if let Import::FromModule { name: n, url, .. } = imp {
                    if n == name {
                        let child = self.child_ref(here, url)?;
                        if self.modules.contains_key(&child) {
                            if let Some(d) = self.declaration(&child, name) {
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
                    self.modules.get(&child).ok_or_else(|| {
                        Diag::new(
                            DiagKind::Resolution,
                            format!("module {child} was not loaded"),
                            span,
                        )
                    })?;
                    if let Some(d) = self.declaration(&child, &rest) {
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

    fn declaration(&self, module: &ModuleRef, name: &str) -> Option<&TheoryDecl> {
        let index = *self.declaration_indices.get(module)?.get(name)?;
        self.modules.get(module)?.declarations().nth(index)
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

/// Validate invariants that must hold for both textual modules and the neutral
/// AST supplied by nouveau Rholang. Keeping this check at the resolved-program
/// boundary prevents a forged structural value from bypassing parser-only
/// duplicate checks.
fn validate_module_structure(module: &ModuleFile) -> Result<(), Diag> {
    let mut declarations = std::collections::BTreeMap::<&str, Span>::new();
    for declaration in module.declarations() {
        if declarations
            .insert(&declaration.name, declaration.span)
            .is_some()
        {
            return Err(Diag::new(
                DiagKind::DuplicateTheory,
                format!("theory `{}` is declared more than once in module", declaration.name),
                declaration.span,
            ));
        }
    }

    let mut imports = std::collections::BTreeMap::<&str, Span>::new();
    for import in &module.imports {
        let (binding, span) = match import {
            Import::ModuleAs { alias, span, .. } => (alias.as_str(), *span),
            Import::FromModule { name, span, .. } => (name.as_str(), *span),
        };
        if imports.insert(binding, span).is_some() || declarations.contains_key(binding) {
            return Err(Diag::new(
                DiagKind::DuplicateImport,
                format!("module-scope import binding `{binding}` is not unique"),
                span,
            ));
        }
    }
    validate_module_reference_order(module)
}

/// Greg/Mike modules are lexical and source ordered.  The declaration index is
/// intentionally still global after validation so lookup remains constant
/// time, but no expression may use that index to observe a later declaration.
fn validate_module_reference_order(module: &ModuleFile) -> Result<(), Diag> {
    use crate::ast::ModuleItem;

    let all_declarations = module
        .declarations()
        .map(|declaration| declaration.name.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let mut available = std::collections::BTreeSet::<String>::new();

    for item in &module.items {
        match item {
            ModuleItem::TheoryDecl(declaration) => {
                validate_expression_reference_order(
                    &declaration.body,
                    declaration
                        .params
                        .iter()
                        .map(|parameter| parameter.name.as_str()),
                    &all_declarations,
                    &available,
                )?;
                available.insert(declaration.name.clone());
            },
            ModuleItem::TheoryEntry(expression) => {
                validate_expression_reference_order(
                    expression,
                    std::iter::empty(),
                    &all_declarations,
                    &available,
                )?;
            },
            ModuleItem::Program(_) => {},
        }
    }
    Ok(())
}

fn validate_expression_reference_order<'a>(
    root: &'a crate::ast::TheoryExpr,
    initially_bound: impl Iterator<Item = &'a str>,
    all_declarations: &std::collections::BTreeSet<String>,
    available: &std::collections::BTreeSet<String>,
) -> Result<(), Diag> {
    use crate::ast::TheoryExpr;

    enum Job<'a> {
        Expression(&'a TheoryExpr),
        Bind(&'a str),
        Unbind(&'a str),
    }

    let mut bound = std::collections::BTreeMap::<&str, usize>::new();
    for name in initially_bound {
        *bound.entry(name).or_default() += 1;
    }
    let mut jobs = vec![Job::Expression(root)];
    while let Some(job) = jobs.pop() {
        match job {
            Job::Bind(name) => *bound.entry(name).or_default() += 1,
            Job::Unbind(name) => {
                let count = bound
                    .get_mut(name)
                    .expect("theory reference validator unbinds an active name");
                *count -= 1;
                if *count == 0 {
                    bound.remove(name);
                }
            },
            Job::Expression(expression) => match expression {
                TheoryExpr::Empty(_) => {},
                TheoryExpr::Free(path, span) => {
                    reject_forward_local_reference(path, *span, all_declarations, available)?;
                },
                TheoryExpr::Apply { head, args, span } => {
                    let is_bound_value =
                        head.is_simple() && args.is_empty() && bound.contains_key(head.last());
                    if !is_bound_value {
                        reject_forward_local_reference(head, *span, all_declarations, available)?;
                    }
                    jobs.extend(args.iter().rev().map(Job::Expression));
                },
                TheoryExpr::Let { name, bound: value, body, .. } => {
                    jobs.push(Job::Unbind(name));
                    jobs.push(Job::Expression(body));
                    jobs.push(Job::Bind(name));
                    jobs.push(Job::Expression(value));
                },
                TheoryExpr::Build { base, .. } => jobs.push(Job::Expression(base)),
                TheoryExpr::Meet(left, right, _)
                | TheoryExpr::Join(left, right, _)
                | TheoryExpr::Diff(left, right, _) => {
                    jobs.push(Job::Expression(right));
                    jobs.push(Job::Expression(left));
                },
            },
        }
    }
    Ok(())
}

fn reject_forward_local_reference(
    path: &crate::ast::DottedPath,
    span: Span,
    all_declarations: &std::collections::BTreeSet<String>,
    available: &std::collections::BTreeSet<String>,
) -> Result<(), Diag> {
    if path.is_simple()
        && all_declarations.contains(path.last())
        && !available.contains(path.last())
    {
        return Err(Diag::new(
            DiagKind::ForwardReference,
            format!(
                "theory `{}` is referenced before its declaration in module source order",
                path.last()
            ),
            span,
        ));
    }
    Ok(())
}

fn index_declarations(
    modules: &HashMap<ModuleRef, ModuleFile>,
) -> HashMap<ModuleRef, HashMap<String, usize>> {
    modules
        .iter()
        .map(|(reference, module)| {
            let declarations = module
                .declarations()
                .enumerate()
                .map(|(index, declaration)| (declaration.name.clone(), index))
                .collect();
            (reference.clone(), declarations)
        })
        .collect()
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
    .with_provenance(SourceProvenance {
        reference: chain
            .last()
            .map(ModuleRef::external_form)
            .unwrap_or_else(|| "<unknown>".into()),
        content_commitment: None,
        import_chain: chain.iter().map(ModuleRef::external_form).collect(),
    })
}

fn detect_cycle(
    entry: &ModuleRef,
    modules: &HashMap<ModuleRef, ModuleFile>,
    resolver: &dyn Resolver,
) -> Result<(), Diag> {
    let mut adjacency = HashMap::<ModuleRef, Vec<ModuleRef>>::new();
    for (reference, module) in modules {
        let mut children = Vec::with_capacity(module.imports.len());
        for import in &module.imports {
            children.push(resolver.join(reference, import.url()).map_err(|error| {
                Diag::new(DiagKind::Resolution, error.to_string(), import.span())
            })?);
        }
        adjacency.insert(reference.clone(), children);
    }

    // White is absent, gray is 1, black is 2. Keeping the active path and the
    // next-child cursor in explicit vectors makes cycle checking independent
    // of the native call stack.
    let mut colors = HashMap::<ModuleRef, u8>::new();
    let mut path = vec![entry.clone()];
    let mut stack = vec![(entry.clone(), 0usize)];
    colors.insert(entry.clone(), 1);

    while let Some((reference, next_child)) = stack.last_mut() {
        let children = adjacency.get(reference).map(Vec::as_slice).unwrap_or(&[]);
        if *next_child == children.len() {
            let completed = reference.clone();
            stack.pop();
            path.pop();
            colors.insert(completed, 2);
            continue;
        }

        let child = children[*next_child].clone();
        *next_child += 1;
        match colors.get(&child).copied() {
            Some(2) => {},
            Some(1) => {
                let start = path.iter().position(|item| item == &child).unwrap_or(0);
                let mut cycle = path[start..].to_vec();
                cycle.push(child);
                return Err(Diag::new(
                    DiagKind::Resolution,
                    format!("import cycle: {}", format_chain(&cycle)),
                    Span { line: 0, col: 0 },
                ));
            },
            None => {
                colors.insert(child.clone(), 1);
                path.push(child.clone());
                stack.push((child, 0));
            },
            Some(_) => unreachable!("cycle detector uses only gray and black states"),
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EmptyRegistry;

    impl VersionedRegistryReader for EmptyRegistry {
        fn lookup_module(&self, _uri: &str) -> Result<Option<RegistryModuleValue>, String> {
            Ok(None)
        }

        fn verify_module_trust(
            &self,
            _uri: &str,
            _signed_payload: &[u8],
            _signatures: &crate::canonical::RhoValue,
        ) -> Result<(), String> {
            Err("empty Registry has no trust authority".into())
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
    fn dependency_lock_is_depth_first_source_order_and_excludes_the_entry() {
        let resolver = MemResolver::new()
            .with(
                "rho:a",
                r#"import "rho:b" as b
                   import "rho:c" as c
                   Module A { Theory T() { Empty } theory T() }"#,
            )
            .with(
                "rho:b",
                r#"import "rho:d" as d
                   Module B { Theory T() { Empty } theory T() }"#,
            )
            .with("rho:c", "Module C { Theory T() { Empty } theory T() }")
            .with("rho:d", "Module D { Theory T() { Empty } theory T() }");
        let entry = ModuleRef::parse("rho:a").expect("valid reference");
        let program = Program::load(&entry, &resolver).expect("graph loads");
        assert_eq!(
            program
                .dependency_lockfile()
                .into_iter()
                .map(|(reference, _)| reference.external_form())
                .collect::<Vec<_>>(),
            ["rho:b", "rho:d", "rho:c"],
        );
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
        let provenance = error
            .provenance
            .expect("resolution provenance is structured");
        assert_eq!(provenance.reference, "rho:missing");
        assert_eq!(provenance.import_chain, ["rho:a", "rho:b", "rho:missing"]);
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
