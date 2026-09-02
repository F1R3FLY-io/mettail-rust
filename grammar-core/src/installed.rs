use crate::{
    runtime_capability_requirements, CategoryId, DefaultRuntimeHost, GrammarCoreV1, ImageError,
    ParserImageV1, RuntimeCapabilityBindings, RuntimeCapabilityError, RuntimeEffect, RuntimeError,
    RuntimeHost, RuntimeParser, RuntimePolicy, RuntimeTemplateHole, RuntimeTemplatePiece,
    SyntaxItem, TokenDecoder, WeightedParse,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, RwLock};
use std::thread::ThreadId;

static NEXT_REGISTRY_ID: AtomicU64 = AtomicU64::new(1);

/// Independently attenuable authority over one installed language.
///
/// Proof search, live-space administration, and factory administration are
/// intentionally absent: possessing grammar authority must not imply any of
/// those authorities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum LanguageRight {
    Parse,
    Construct,
    Match,
    Observe,
    ReflectAst,
    Reduce,
    Bridge,
    Publish,
    Introspect,
    Check,
    SearchProof,
    Spend,
}

impl LanguageRight {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Parse => "Parse",
            Self::Construct => "Construct",
            Self::Match => "Match",
            Self::Observe => "Observe",
            Self::ReflectAst => "ReflectAst",
            Self::Reduce => "Reduce",
            Self::Bridge => "Bridge",
            Self::Publish => "Publish",
            Self::Introspect => "Introspect",
            Self::Check => "Check",
            Self::SearchProof => "SearchProof",
            Self::Spend => "Spend",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "Parse" => Self::Parse,
            "Construct" => Self::Construct,
            "Match" => Self::Match,
            "Observe" => Self::Observe,
            "ReflectAst" => Self::ReflectAst,
            "Reduce" => Self::Reduce,
            "Bridge" => Self::Bridge,
            "Publish" => Self::Publish,
            "Introspect" => Self::Introspect,
            "Check" => Self::Check,
            "SearchProof" => Self::SearchProof,
            "Spend" => Self::Spend,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LanguageRights(BTreeSet<LanguageRight>);

impl LanguageRights {
    pub fn none() -> Self {
        Self::default()
    }

    pub fn all() -> Self {
        Self(
            [
                LanguageRight::Parse,
                LanguageRight::Construct,
                LanguageRight::Match,
                LanguageRight::Observe,
                LanguageRight::ReflectAst,
                LanguageRight::Reduce,
                LanguageRight::Bridge,
                LanguageRight::Publish,
                LanguageRight::Introspect,
                LanguageRight::Check,
                LanguageRight::SearchProof,
                LanguageRight::Spend,
            ]
            .into_iter()
            .collect(),
        )
    }

    /// Useful-by-default native FLT request profile. These are requests only:
    /// installation still intersects them with authority supplied by the host.
    /// Bridge, publication, and raw introspection remain explicit opt-ins.
    pub fn native_flt_default() -> Self {
        Self::from_rights([
            LanguageRight::Parse,
            LanguageRight::Construct,
            LanguageRight::Match,
            LanguageRight::Observe,
            LanguageRight::ReflectAst,
            LanguageRight::Reduce,
        ])
    }

    pub fn from_rights(rights: impl IntoIterator<Item = LanguageRight>) -> Self {
        Self(rights.into_iter().collect())
    }

    pub fn contains(&self, right: LanguageRight) -> bool {
        self.0.contains(&right)
    }

    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    pub fn attenuate(&self, requested: &Self) -> Self {
        Self(self.0.intersection(&requested.0).copied().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = LanguageRight> + '_ {
        self.0.iter().copied()
    }

    fn extend(&mut self, additional: &Self) {
        self.0.extend(additional.0.iter().copied());
    }
}

struct HandleSeal;

/// An unforgeable, process-local capability. Semantic fingerprints and aliases
/// are deliberately insufficient to construct this value.
#[derive(Clone)]
pub struct InstalledLanguageHandle {
    registry_id: u64,
    entry_id: u64,
    epoch: u64,
    fingerprint: [u8; 32],
    rights: LanguageRights,
    seal: Arc<HandleSeal>,
}

impl InstalledLanguageHandle {
    pub fn fingerprint(&self) -> [u8; 32] {
        self.fingerprint
    }

    pub fn rights(&self) -> &LanguageRights {
        &self.rights
    }

    /// Attenuation is intersection, so it can never invent authority.
    pub fn attenuate(&self, requested: &LanguageRights) -> Self {
        let mut output = self.clone();
        output.rights = self.rights.attenuate(requested);
        output
    }
}

impl fmt::Debug for InstalledLanguageHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("InstalledLanguageHandle")
            .field("fingerprint", &self.fingerprint)
            .field("rights", &self.rights)
            .finish_non_exhaustive()
    }
}

impl PartialEq for InstalledLanguageHandle {
    fn eq(&self, other: &Self) -> bool {
        self.registry_id == other.registry_id
            && self.entry_id == other.entry_id
            && self.epoch == other.epoch
            && self.fingerprint == other.fingerprint
            && self.rights == other.rights
            && Arc::ptr_eq(&self.seal, &other.seal)
    }
}

impl Eq for InstalledLanguageHandle {}

/// Separate revocation authority. It is never conveyed by attenuation or by
/// any [`LanguageRight`].
pub struct LanguageRevocationAuthority {
    registry_id: u64,
    entry_id: u64,
    fingerprint: [u8; 32],
    seal: Arc<HandleSeal>,
}

impl fmt::Debug for LanguageRevocationAuthority {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LanguageRevocationAuthority")
            .field("fingerprint", &self.fingerprint)
            .finish_non_exhaustive()
    }
}

pub struct InstalledLanguageGrant {
    pub handle: InstalledLanguageHandle,
    pub revocation: LanguageRevocationAuthority,
}

/// One fully prepared run-time language submitted to an atomic table commit.
/// Validation and parser-image admission still happen before the table lock.
pub struct RuntimeLanguageInstall {
    pub core: GrammarCoreV1,
    pub image: ParserImageV1,
    pub granted_rights: LanguageRights,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstalledParserKind {
    RuntimeImage,
    StaticTyped { adapter_abi: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstallCommitment {
    pub core_fingerprint: [u8; 32],
    pub parser_kind: InstalledParserKind,
    pub compiler_abi: String,
    pub unicode_abi: String,
    pub capability_abi: String,
    /// Exact code/ABI/effect/cost manifests selected from injected host
    /// authority for this fingerprint-scoped runtime language.
    pub capability_manifest_fingerprint: [u8; 32],
    pub policy_fingerprint: [u8; 32],
    /// Conservative effects that must be authorized before parser execution.
    pub effect_rights: LanguageRights,
}

/// Adapter used by compile-time grammars. Implementations may call their
/// generated typed parser directly; registration adds no branch to that hot
/// path. The dynamic adapter is provided internally by the table.
pub trait StaticParserAdapter: Send + Sync {
    fn parse(
        &self,
        source: &str,
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError>;

    fn parse_template(
        &self,
        _pieces: &[RuntimeTemplatePiece],
        _holes: &[RuntimeTemplateHole],
        _category: Option<CategoryId>,
        _host: &dyn RuntimeHost,
        _policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        Err(RuntimeError::InvalidTemplate(
            "static parser adapter does not expose structural template parsing",
        ))
    }

    /// Opt in to symbolic-template memoization with a stable semantic epoch.
    /// The value must change before equal inputs can produce different parses.
    /// Stateful or effectful adapters should retain the safe default of `None`.
    fn template_cache_commitment(&self) -> Option<[u8; 32]> {
        None
    }

    /// Rights induced by host callbacks reachable from this trusted static
    /// adapter. Generated pure parsers keep the empty default; adapters that
    /// evaluate or delegate must declare `Reduce` and/or `Bridge`.
    fn required_effect_rights(&self) -> LanguageRights {
        LanguageRights::none()
    }
}

enum InstalledParser {
    Runtime(Arc<ParserImageV1>),
    Static(Arc<dyn StaticParserAdapter>),
}

type SymbolicTemplateCacheKey = [u8; 32];

struct CachedSymbolicTemplate {
    parses: Arc<Vec<WeightedParse>>,
    weight: usize,
}

#[derive(Default)]
struct SymbolicTemplateCacheState {
    entries: BTreeMap<SymbolicTemplateCacheKey, CachedSymbolicTemplate>,
    oldest_first: VecDeque<SymbolicTemplateCacheKey>,
    retained_weight: usize,
    flights: BTreeMap<SymbolicTemplateCacheKey, Arc<SymbolicTemplateFlight>>,
}

impl SymbolicTemplateCacheState {
    fn evict_oldest(&mut self) {
        let Some(key) = self.oldest_first.pop_front() else {
            self.entries.clear();
            self.retained_weight = 0;
            return;
        };
        if let Some(entry) = self.entries.remove(&key) {
            self.retained_weight = self.retained_weight.saturating_sub(entry.weight);
        }
    }

    fn trim_to(&mut self, capacity: usize, max_weight: usize) {
        while self.entries.len() > capacity || self.retained_weight > max_weight {
            self.evict_oldest();
        }
    }

    fn insert(
        &mut self,
        key: SymbolicTemplateCacheKey,
        parses: Arc<Vec<WeightedParse>>,
        weight: usize,
        capacity: usize,
        max_weight: usize,
    ) {
        if capacity == 0 || weight > max_weight || self.entries.contains_key(&key) {
            return;
        }
        while self.entries.len() >= capacity
            || self.retained_weight.saturating_add(weight) > max_weight
        {
            if self.entries.is_empty() {
                return;
            }
            self.evict_oldest();
        }
        self.retained_weight = self.retained_weight.saturating_add(weight);
        self.oldest_first.push_back(key);
        self.entries
            .insert(key, CachedSymbolicTemplate { parses, weight });
    }
}

#[derive(Default)]
struct SymbolicTemplateCache {
    state: Mutex<SymbolicTemplateCacheState>,
}

enum SymbolicTemplateCacheProbe {
    Hit(Arc<Vec<WeightedParse>>),
    Flight(Arc<SymbolicTemplateFlight>),
    Bypass,
}

impl SymbolicTemplateCache {
    fn probe(
        &self,
        key: SymbolicTemplateCacheKey,
        capacity: usize,
        max_weight: usize,
    ) -> SymbolicTemplateCacheProbe {
        let mut state = recover_lock(&self.state);
        state.trim_to(capacity, max_weight);
        if let Some(entry) = state.entries.get(&key) {
            return SymbolicTemplateCacheProbe::Hit(entry.parses.clone());
        }
        if let Some(flight) = state.flights.get(&key) {
            return SymbolicTemplateCacheProbe::Flight(flight.clone());
        }
        if capacity == 0 || max_weight == 0 || state.flights.len() >= capacity {
            return SymbolicTemplateCacheProbe::Bypass;
        }
        let flight = Arc::new(SymbolicTemplateFlight::new());
        state.flights.insert(key, flight.clone());
        SymbolicTemplateCacheProbe::Flight(flight)
    }

    fn retain_success(
        &self,
        key: SymbolicTemplateCacheKey,
        parses: Arc<Vec<WeightedParse>>,
        capacity: usize,
        max_weight: usize,
    ) {
        let weight = symbolic_template_weight(&parses);
        recover_lock(&self.state).insert(key, parses, weight, capacity, max_weight);
    }

    fn remove_flight(&self, key: SymbolicTemplateCacheKey, flight: &Arc<SymbolicTemplateFlight>) {
        let mut state = recover_lock(&self.state);
        if state
            .flights
            .get(&key)
            .is_some_and(|current| Arc::ptr_eq(current, flight))
        {
            state.flights.remove(&key);
        }
    }
}

struct SymbolicTemplateFlight {
    state: Mutex<SymbolicTemplateFlightState>,
    ready: Condvar,
}

impl SymbolicTemplateFlight {
    fn new() -> Self {
        Self {
            state: Mutex::new(SymbolicTemplateFlightState::Idle),
            ready: Condvar::new(),
        }
    }
}

enum SymbolicTemplateFlightState {
    Idle,
    Running(ThreadId),
    Complete(SymbolicTemplateFlightOutcome),
}

enum SymbolicTemplateFlightOutcome {
    Stable(Result<Arc<Vec<WeightedParse>>, RuntimeError>),
    RetryUncached,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct TemplateSemanticCommitments {
    parser: [u8; 32],
    host: [u8; 32],
}

fn recover_lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn symbolic_template_weight(parses: &Vec<WeightedParse>) -> usize {
    let mut weight = parses
        .capacity()
        .saturating_mul(std::mem::size_of::<WeightedParse>());
    for parse in parses {
        weight = weight
            .saturating_add(parse.syntax.retained_heap_weight())
            .saturating_add(parse.value.retained_heap_weight())
            .saturating_add(parse.rank.retained_heap_weight());
    }
    weight
}

pub struct InstalledLanguage {
    core: Arc<GrammarCoreV1>,
    parser: InstalledParser,
    commitment: InstallCommitment,
    effect_rights: LanguageRights,
    capability_bindings: RuntimeCapabilityBindings,
    symbolic_template_cache: SymbolicTemplateCache,
}

impl InstalledLanguage {
    pub fn core(&self) -> &GrammarCoreV1 {
        &self.core
    }

    pub fn commitment(&self) -> &InstallCommitment {
        &self.commitment
    }

    pub fn parser_image(&self) -> Option<&ParserImageV1> {
        match &self.parser {
            InstalledParser::Runtime(image) => Some(image),
            InstalledParser::Static(_) => None,
        }
    }

    fn operation_rights(&self, base: &[LanguageRight]) -> Vec<LanguageRight> {
        let mut rights = Vec::with_capacity(base.len() + self.effect_rights.0.len());
        for right in base.iter().copied().chain(self.effect_rights.iter()) {
            if !rights.contains(&right) {
                rights.push(right);
            }
        }
        rights
    }

    fn parse(
        &self,
        source: &str,
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        match &self.parser {
            InstalledParser::Runtime(image) => {
                let parser = RuntimeParser::new_with_policy_and_bindings(
                    &self.core,
                    image,
                    &self.commitment.compiler_abi,
                    &self.commitment.unicode_abi,
                    host,
                    policy,
                    self.capability_bindings.clone(),
                )?;
                match category {
                    Some(category) => parser.parse_category(source, category),
                    None => parser.parse(source),
                }
            },
            InstalledParser::Static(adapter) => adapter.parse(source, category, host, policy),
        }
    }

    fn parse_template_uncached(
        &self,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        match &self.parser {
            InstalledParser::Runtime(image) => RuntimeParser::new_with_policy_and_bindings(
                &self.core,
                image,
                &self.commitment.compiler_abi,
                &self.commitment.unicode_abi,
                host,
                policy,
                self.capability_bindings.clone(),
            )?
            .parse_template(pieces, holes, category),
            InstalledParser::Static(adapter) => {
                adapter.parse_template(pieces, holes, category, host, policy)
            },
        }
    }

    fn template_semantic_commitments(
        &self,
        host: &dyn RuntimeHost,
    ) -> Option<TemplateSemanticCommitments> {
        let parser = match &self.parser {
            InstalledParser::Runtime(_) => {
                *blake3::hash(b"mettail-runtime-image-symbolic-template/1").as_bytes()
            },
            InstalledParser::Static(adapter) => adapter.template_cache_commitment()?,
        };
        Some(TemplateSemanticCommitments {
            parser,
            host: host.semantic_cache_commitment()?,
        })
    }

    fn parse_template(
        &self,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        let Some(commitments) = self.template_semantic_commitments(host) else {
            return self.parse_template_uncached(pieces, holes, category, host, policy);
        };
        let capacity =
            usize::try_from(policy.max_symbolic_template_cache_entries).unwrap_or(usize::MAX);
        let max_weight =
            usize::try_from(policy.max_symbolic_template_cache_weight).unwrap_or(usize::MAX);
        if capacity == 0 || max_weight == 0 {
            return self.parse_template_uncached(pieces, holes, category, host, policy);
        }
        let key = self.symbolic_template_cache_key(commitments, pieces, holes, category, policy);
        match self
            .symbolic_template_cache
            .probe(key, capacity, max_weight)
        {
            SymbolicTemplateCacheProbe::Hit(parses) => {
                if self.template_semantic_commitments(host) == Some(commitments) {
                    Ok(parses.as_ref().clone())
                } else {
                    self.parse_template_uncached(pieces, holes, category, host, policy)
                }
            },
            SymbolicTemplateCacheProbe::Bypass => {
                self.parse_template_uncached(pieces, holes, category, host, policy)
            },
            SymbolicTemplateCacheProbe::Flight(flight) => self.run_template_flight(
                key,
                flight,
                commitments,
                pieces,
                holes,
                category,
                host,
                policy,
                capacity,
                max_weight,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run_template_flight(
        &self,
        key: SymbolicTemplateCacheKey,
        flight: Arc<SymbolicTemplateFlight>,
        commitments: TemplateSemanticCommitments,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
        capacity: usize,
        max_weight: usize,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        let requester = std::thread::current().id();
        loop {
            let mut state = recover_lock(&flight.state);
            match &*state {
                SymbolicTemplateFlightState::Idle => {
                    *state = SymbolicTemplateFlightState::Running(requester);
                    drop(state);
                    break;
                },
                SymbolicTemplateFlightState::Running(owner) if *owner == requester => {
                    return Err(RuntimeError::TemplateCacheCycle);
                },
                SymbolicTemplateFlightState::Running(_) => {
                    state = flight
                        .ready
                        .wait(state)
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    drop(state);
                },
                SymbolicTemplateFlightState::Complete(outcome) => {
                    if self.template_semantic_commitments(host) != Some(commitments) {
                        drop(state);
                        return self.parse_template_uncached(pieces, holes, category, host, policy);
                    }
                    return match outcome {
                        SymbolicTemplateFlightOutcome::Stable(result) => result
                            .as_ref()
                            .map(|parses| parses.as_ref().clone())
                            .map_err(Clone::clone),
                        SymbolicTemplateFlightOutcome::RetryUncached => {
                            drop(state);
                            self.parse_template_uncached(pieces, holes, category, host, policy)
                        },
                    };
                },
            }
        }

        let parsed = self
            .parse_template_uncached(pieces, holes, category, host, policy)
            .map(Arc::new);
        let stable = self.template_semantic_commitments(host) == Some(commitments);
        if stable {
            if let Ok(parses) = &parsed {
                self.symbolic_template_cache.retain_success(
                    key,
                    parses.clone(),
                    capacity,
                    max_weight,
                );
            }
        }
        {
            let mut state = recover_lock(&flight.state);
            *state = SymbolicTemplateFlightState::Complete(if stable {
                SymbolicTemplateFlightOutcome::Stable(parsed.clone())
            } else {
                SymbolicTemplateFlightOutcome::RetryUncached
            });
            flight.ready.notify_all();
        }
        self.symbolic_template_cache.remove_flight(key, &flight);
        parsed.map(|parses| parses.as_ref().clone())
    }

    fn symbolic_template_cache_key(
        &self,
        commitments: TemplateSemanticCommitments,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        policy: RuntimePolicy,
    ) -> SymbolicTemplateCacheKey {
        let mut hasher = blake3::Hasher::new();
        hash_cache_field(&mut hasher, b"mettail-symbolic-template-cache-key/1");
        hash_cache_field(&mut hasher, &self.commitment.core_fingerprint);
        match &self.commitment.parser_kind {
            InstalledParserKind::RuntimeImage => hash_cache_field(&mut hasher, b"runtime"),
            InstalledParserKind::StaticTyped { adapter_abi } => {
                hash_cache_field(&mut hasher, b"static");
                hash_cache_field(&mut hasher, adapter_abi.as_bytes());
            },
        }
        hash_cache_field(&mut hasher, self.commitment.compiler_abi.as_bytes());
        hash_cache_field(&mut hasher, self.commitment.unicode_abi.as_bytes());
        hash_cache_field(&mut hasher, self.commitment.capability_abi.as_bytes());
        hash_cache_field(&mut hasher, &self.commitment.capability_manifest_fingerprint);
        hash_cache_field(&mut hasher, &self.commitment.policy_fingerprint);
        for right in self.commitment.effect_rights.iter() {
            hash_cache_field(&mut hasher, right.name().as_bytes());
        }
        hash_cache_field(&mut hasher, &commitments.parser);
        hash_cache_field(&mut hasher, &commitments.host);
        hash_cache_field(&mut hasher, &policy.max_input_bytes.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_parse_items.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_forest_nodes.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_semantic_results.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_capture_bindings.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_symbolic_template_cache_entries.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_symbolic_template_cache_weight.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_lexer_mode_depth.to_be_bytes());
        hash_cache_field(&mut hasher, &policy.max_foreign_nesting.to_be_bytes());
        match category {
            Some(category) => {
                hash_cache_field(&mut hasher, b"category");
                hash_cache_field(&mut hasher, &category.0.to_be_bytes());
            },
            None => hash_cache_field(&mut hasher, b"default-category"),
        }
        hash_cache_field(&mut hasher, &(pieces.len() as u64).to_be_bytes());
        for piece in pieces {
            match piece {
                RuntimeTemplatePiece::Text(text) => {
                    hash_cache_field(&mut hasher, b"text");
                    hash_cache_field(&mut hasher, text.as_bytes());
                },
                RuntimeTemplatePiece::Hole(id) => {
                    hash_cache_field(&mut hasher, b"hole");
                    hash_cache_field(&mut hasher, &id.to_be_bytes());
                },
            }
        }
        hash_cache_field(&mut hasher, &(holes.len() as u64).to_be_bytes());
        for hole in holes {
            hash_cache_field(&mut hasher, &hole.id.to_be_bytes());
            match hole.category {
                Some(category) => {
                    hash_cache_field(&mut hasher, b"typed");
                    hash_cache_field(&mut hasher, &category.0.to_be_bytes());
                },
                None => hash_cache_field(&mut hasher, b"inferred"),
            }
        }
        *hasher.finalize().as_bytes()
    }
}

fn hash_cache_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

struct InstalledEntry {
    id: u64,
    epoch: u64,
    revoked: bool,
    maximum_rights: LanguageRights,
    seal: Arc<HandleSeal>,
    language: Arc<InstalledLanguage>,
}

#[derive(Default)]
struct InstalledState {
    next_entry_id: u64,
    entries: BTreeMap<[u8; 32], InstalledEntry>,
}

/// Fingerprint-indexed table shared by dynamic and compile-time grammars.
/// Validation and compilation occur before the write lock; the final duplicate
/// check and publication are one atomic commit.
pub struct InstalledLanguageTable {
    registry_id: u64,
    state: RwLock<InstalledState>,
}

impl Default for InstalledLanguageTable {
    fn default() -> Self {
        Self::new()
    }
}

impl InstalledLanguageTable {
    pub fn new() -> Self {
        let registry_id = NEXT_REGISTRY_ID.fetch_add(1, Ordering::Relaxed);
        assert!(registry_id != 0, "installed-language registry identifier exhausted");
        Self {
            registry_id,
            state: RwLock::new(InstalledState::default()),
        }
    }

    pub fn installed_count(&self) -> Result<usize, LanguageAccessError> {
        self.state
            .read()
            .map(|state| {
                state
                    .entries
                    .values()
                    .filter(|entry| !entry.revoked)
                    .count()
            })
            .map_err(|_| LanguageAccessError::Poisoned)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn install_runtime(
        &self,
        core: GrammarCoreV1,
        image: ParserImageV1,
        granted_rights: LanguageRights,
        compiler_abi: &str,
        unicode_abi: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
    ) -> Result<InstalledLanguageGrant, InstallLanguageError> {
        self.install_runtime_batch(
            vec![RuntimeLanguageInstall { core, image, granted_rights }],
            compiler_abi,
            unicode_abi,
            capability_abi,
            policy_fingerprint,
        )?
        .into_iter()
        .next()
        .ok_or(InstallLanguageError::EmptyBatch)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn install_runtime_with_host(
        &self,
        core: GrammarCoreV1,
        image: ParserImageV1,
        granted_rights: LanguageRights,
        compiler_abi: &str,
        unicode_abi: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
        host: &dyn RuntimeHost,
    ) -> Result<InstalledLanguageGrant, InstallLanguageError> {
        self.install_runtime_batch_with_host(
            vec![RuntimeLanguageInstall { core, image, granted_rights }],
            compiler_abi,
            unicode_abi,
            capability_abi,
            policy_fingerprint,
            host,
        )?
        .into_iter()
        .next()
        .ok_or(InstallLanguageError::EmptyBatch)
    }

    /// Admit every image before acquiring the table lock, then publish the
    /// entire set in one commit. A conflict, malformed image, or identifier
    /// exhaustion leaves both new entries and rights ceilings unchanged.
    pub fn install_runtime_batch(
        &self,
        requests: Vec<RuntimeLanguageInstall>,
        compiler_abi: &str,
        unicode_abi: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
    ) -> Result<Vec<InstalledLanguageGrant>, InstallLanguageError> {
        self.install_runtime_batch_with_host(
            requests,
            compiler_abi,
            unicode_abi,
            capability_abi,
            policy_fingerprint,
            &DefaultRuntimeHost,
        )
    }

    /// Resolve and revalidate every external callback manifest before taking
    /// the table lock. The full batch either publishes with exact bindings or
    /// leaves the table unchanged.
    pub fn install_runtime_batch_with_host(
        &self,
        requests: Vec<RuntimeLanguageInstall>,
        compiler_abi: &str,
        unicode_abi: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
        host: &dyn RuntimeHost,
    ) -> Result<Vec<InstalledLanguageGrant>, InstallLanguageError> {
        if requests.is_empty() {
            return Err(InstallLanguageError::EmptyBatch);
        }
        let mut prepared = Vec::with_capacity(requests.len());
        for request in requests {
            request
                .core
                .validate()
                .map_err(InstallLanguageError::InvalidGrammar)?;
            reject_runtime_source(&request.core)?;
            request
                .image
                .verify_executable(&request.core, compiler_abi, unicode_abi)
                .map_err(InstallLanguageError::InvalidImage)?;
            let core_fingerprint = request
                .core
                .fingerprint()
                .map_err(InstallLanguageError::EncodeCore)?;
            let requirements = runtime_capability_requirements(&request.core, core_fingerprint)
                .map_err(InstallLanguageError::Capability)?;
            let capability_bindings =
                RuntimeCapabilityBindings::bind(&requirements, |key| host.capability_manifest(key))
                    .map_err(InstallLanguageError::Capability)?;
            let capability_manifest_fingerprint = capability_bindings
                .commitment()
                .map_err(InstallLanguageError::Capability)?;
            let effect_rights = runtime_effect_rights(&request.core, &capability_bindings);
            let commitment = InstallCommitment {
                core_fingerprint,
                parser_kind: InstalledParserKind::RuntimeImage,
                compiler_abi: compiler_abi.into(),
                unicode_abi: unicode_abi.into(),
                capability_abi: capability_abi.into(),
                capability_manifest_fingerprint,
                policy_fingerprint,
                effect_rights: effect_rights.clone(),
            };
            prepared.push((
                core_fingerprint,
                request.granted_rights,
                InstalledLanguage {
                    core: Arc::new(request.core),
                    parser: InstalledParser::Runtime(Arc::new(request.image)),
                    commitment,
                    effect_rights,
                    capability_bindings,
                    symbolic_template_cache: SymbolicTemplateCache::default(),
                },
            ));
        }
        self.commit_batch(prepared)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn install_static(
        &self,
        core: GrammarCoreV1,
        adapter: Arc<dyn StaticParserAdapter>,
        adapter_abi: &str,
        granted_rights: LanguageRights,
        compiler_abi: &str,
        unicode_abi: &str,
        capability_abi: &str,
        policy_fingerprint: [u8; 32],
    ) -> Result<InstalledLanguageGrant, InstallLanguageError> {
        core.validate()
            .map_err(InstallLanguageError::InvalidGrammar)?;
        let core_fingerprint = core
            .fingerprint()
            .map_err(InstallLanguageError::EncodeCore)?;
        let effect_rights = adapter.required_effect_rights();
        let capability_bindings = RuntimeCapabilityBindings::default();
        let commitment = InstallCommitment {
            core_fingerprint,
            parser_kind: InstalledParserKind::StaticTyped { adapter_abi: adapter_abi.into() },
            compiler_abi: compiler_abi.into(),
            unicode_abi: unicode_abi.into(),
            capability_abi: capability_abi.into(),
            capability_manifest_fingerprint: capability_bindings
                .commitment()
                .map_err(InstallLanguageError::Capability)?,
            policy_fingerprint,
            effect_rights: effect_rights.clone(),
        };
        self.commit(
            core_fingerprint,
            granted_rights,
            InstalledLanguage {
                core: Arc::new(core),
                parser: InstalledParser::Static(adapter),
                commitment,
                effect_rights,
                capability_bindings,
                symbolic_template_cache: SymbolicTemplateCache::default(),
            },
        )
    }

    fn commit(
        &self,
        fingerprint: [u8; 32],
        granted_rights: LanguageRights,
        language: InstalledLanguage,
    ) -> Result<InstalledLanguageGrant, InstallLanguageError> {
        self.commit_batch(vec![(fingerprint, granted_rights, language)])?
            .into_iter()
            .next()
            .ok_or(InstallLanguageError::EmptyBatch)
    }

    fn commit_batch(
        &self,
        requests: Vec<([u8; 32], LanguageRights, InstalledLanguage)>,
    ) -> Result<Vec<InstalledLanguageGrant>, InstallLanguageError> {
        if requests.is_empty() {
            return Err(InstallLanguageError::EmptyBatch);
        }
        let mut state = self
            .state
            .write()
            .map_err(|_| InstallLanguageError::Poisoned)?;

        // Validate the complete transaction before mutating either an entry or
        // an existing entry's maximum-rights ceiling.
        let mut unique = BTreeMap::<[u8; 32], usize>::new();
        for (index, (fingerprint, _, language)) in requests.iter().enumerate() {
            if let Some(previous) = unique.insert(*fingerprint, index) {
                let previous_language = &requests[previous].2;
                if previous_language.core != language.core
                    || previous_language.commitment != language.commitment
                {
                    return Err(InstallLanguageError::ConflictingInstallation(*fingerprint));
                }
            }
            if let Some(entry) = state
                .entries
                .get(fingerprint)
                .filter(|entry| !entry.revoked)
            {
                if entry.language.core != language.core
                    || entry.language.commitment != language.commitment
                {
                    return Err(InstallLanguageError::ConflictingInstallation(*fingerprint));
                }
            }
        }
        let fresh_count = unique
            .keys()
            .filter(|fingerprint| {
                state
                    .entries
                    .get(*fingerprint)
                    .is_none_or(|entry| entry.revoked)
            })
            .count();
        let fresh_count =
            u64::try_from(fresh_count).map_err(|_| InstallLanguageError::EntryIdExhausted)?;
        state
            .next_entry_id
            .checked_add(fresh_count)
            .ok_or(InstallLanguageError::EntryIdExhausted)?;

        let mut grants = Vec::with_capacity(requests.len());
        for (fingerprint, granted_rights, language) in requests {
            if let Some(entry) = state
                .entries
                .get_mut(&fingerprint)
                .filter(|entry| !entry.revoked)
            {
                // An identical verified commitment reuses the sealed entry.
                // Rights stay on returned handles; extending this host-controlled
                // ceiling does not amplify any handle already in circulation.
                entry.maximum_rights.extend(&granted_rights);
                grants.push(InstalledLanguageGrant {
                    handle: InstalledLanguageHandle {
                        registry_id: self.registry_id,
                        entry_id: entry.id,
                        epoch: entry.epoch,
                        fingerprint,
                        rights: granted_rights,
                        seal: entry.seal.clone(),
                    },
                    revocation: LanguageRevocationAuthority {
                        registry_id: self.registry_id,
                        entry_id: entry.id,
                        fingerprint,
                        seal: entry.seal.clone(),
                    },
                });
                continue;
            }

            state.next_entry_id += 1;
            let id = state.next_entry_id;
            let seal = Arc::new(HandleSeal);
            let epoch = 0;
            state.entries.insert(
                fingerprint,
                InstalledEntry {
                    id,
                    epoch,
                    revoked: false,
                    maximum_rights: granted_rights.clone(),
                    seal: seal.clone(),
                    language: Arc::new(language),
                },
            );
            grants.push(InstalledLanguageGrant {
                handle: InstalledLanguageHandle {
                    registry_id: self.registry_id,
                    entry_id: id,
                    epoch,
                    fingerprint,
                    rights: granted_rights,
                    seal: seal.clone(),
                },
                revocation: LanguageRevocationAuthority {
                    registry_id: self.registry_id,
                    entry_id: id,
                    fingerprint,
                    seal,
                },
            });
        }
        Ok(grants)
    }

    pub fn authorize(
        &self,
        handle: &InstalledLanguageHandle,
        right: LanguageRight,
    ) -> Result<Arc<InstalledLanguage>, LanguageAccessError> {
        self.authorize_all(handle, &[right])
    }

    /// Authorize every independent right against one immutable registry
    /// snapshot. This prevents a multi-right operation from observing rights
    /// from different revocation generations.
    pub fn authorize_all(
        &self,
        handle: &InstalledLanguageHandle,
        rights: &[LanguageRight],
    ) -> Result<Arc<InstalledLanguage>, LanguageAccessError> {
        let state = self
            .state
            .read()
            .map_err(|_| LanguageAccessError::Poisoned)?;
        let entry = self.valid_entry(&state, handle)?;
        for right in rights {
            if !handle.rights.contains(*right) {
                return Err(LanguageAccessError::MissingRight(*right));
            }
        }
        Ok(entry.language.clone())
    }

    /// Run `operation` while the installed-language read guard remains live.
    /// Revocation therefore cannot interleave between authorization and an
    /// adapter's atomic state commit.
    pub fn with_authorized<R>(
        &self,
        handle: &InstalledLanguageHandle,
        right: LanguageRight,
        operation: impl FnOnce(&InstalledLanguage) -> R,
    ) -> Result<R, LanguageAccessError> {
        let state = self
            .state
            .read()
            .map_err(|_| LanguageAccessError::Poisoned)?;
        let entry = self.authorized_entry(&state, handle, right)?;
        Ok(operation(&entry.language))
    }

    fn authorized_entry<'a>(
        &self,
        state: &'a InstalledState,
        handle: &InstalledLanguageHandle,
        right: LanguageRight,
    ) -> Result<&'a InstalledEntry, LanguageAccessError> {
        let entry = self.valid_entry(state, handle)?;
        if !handle.rights.contains(right) {
            return Err(LanguageAccessError::MissingRight(right));
        }
        Ok(entry)
    }

    fn valid_entry<'a>(
        &self,
        state: &'a InstalledState,
        handle: &InstalledLanguageHandle,
    ) -> Result<&'a InstalledEntry, LanguageAccessError> {
        if handle.registry_id != self.registry_id {
            return Err(LanguageAccessError::WrongRegistry);
        }
        let entry = state
            .entries
            .get(&handle.fingerprint)
            .ok_or(LanguageAccessError::UnknownLanguage)?;
        if entry.id != handle.entry_id
            || entry.epoch != handle.epoch
            || !Arc::ptr_eq(&entry.seal, &handle.seal)
        {
            return Err(LanguageAccessError::StaleHandle);
        }
        if entry.revoked {
            return Err(LanguageAccessError::Revoked);
        }
        if !handle.rights.is_subset_of(&entry.maximum_rights) {
            return Err(LanguageAccessError::AmplifiedHandle);
        }
        Ok(entry)
    }

    pub fn parse(
        &self,
        handle: &InstalledLanguageHandle,
        source: &str,
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, InstalledParseError> {
        let language = self
            .authorize(handle, LanguageRight::Parse)
            .map_err(InstalledParseError::Access)?;
        let rights = language.operation_rights(&[LanguageRight::Parse]);
        let language = self
            .authorize_all(handle, &rights)
            .map_err(InstalledParseError::Access)?;
        let parsed = language.parse(source, category, host, policy);
        // Parsing may call injected host capabilities, so do not hold the
        // registry lock across it. Revalidate the same sealed epoch before any
        // result becomes observable; revocation during parsing fails closed.
        self.authorize_all(handle, &rights)
            .map_err(InstalledParseError::Access)?;
        parsed.map_err(InstalledParseError::Parse)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn parse_template(
        &self,
        handle: &InstalledLanguageHandle,
        pieces: &[RuntimeTemplatePiece],
        holes: &[RuntimeTemplateHole],
        category: Option<CategoryId>,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
        operation: LanguageRight,
    ) -> Result<Vec<WeightedParse>, InstalledParseError> {
        let language = self
            .authorize(handle, LanguageRight::Parse)
            .map_err(InstalledParseError::Access)?;
        let rights = language.operation_rights(&[LanguageRight::Parse, operation]);
        let language = self
            .authorize_all(handle, &rights)
            .map_err(InstalledParseError::Access)?;
        let parsed = language.parse_template(pieces, holes, category, host, policy);
        self.authorize_all(handle, &rights)
            .map_err(InstalledParseError::Access)?;
        parsed.map_err(InstalledParseError::Parse)
    }

    pub fn revoke(
        &self,
        authority: LanguageRevocationAuthority,
    ) -> Result<(), LanguageAccessError> {
        if authority.registry_id != self.registry_id {
            return Err(LanguageAccessError::WrongRegistry);
        }
        let mut state = self
            .state
            .write()
            .map_err(|_| LanguageAccessError::Poisoned)?;
        let entry = state
            .entries
            .get_mut(&authority.fingerprint)
            .ok_or(LanguageAccessError::UnknownLanguage)?;
        if entry.id != authority.entry_id || !Arc::ptr_eq(&entry.seal, &authority.seal) {
            return Err(LanguageAccessError::StaleHandle);
        }
        if entry.revoked {
            return Err(LanguageAccessError::Revoked);
        }
        entry.revoked = true;
        entry.epoch = entry
            .epoch
            .checked_add(1)
            .ok_or(LanguageAccessError::EpochExhausted)?;
        Ok(())
    }
}

/// Compute the effect row once during installation. Nested syntax is scanned
/// with an explicit worklist; parser operations later check only the resulting
/// fixed-size right set.
fn runtime_effect_rights(
    core: &GrammarCoreV1,
    capability_bindings: &RuntimeCapabilityBindings,
) -> LanguageRights {
    let reduce = core.tokens.iter().any(|token| {
        matches!(token.decoder, TokenDecoder::Capability(_)) || token.evaluation.is_some()
    }) || core
        .reductions
        .iter()
        .any(|reduction| reduction.evaluation.is_some());
    let mut bridge = false;
    let mut pending = Vec::new();
    for production in core.productions.iter().rev() {
        pending.extend(production.syntax.iter().rev());
    }
    while let Some(item) = pending.pop() {
        match item {
            SyntaxItem::ForeignLanguage { .. } => bridge = true,
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Sequence(body)
            | SyntaxItem::Zip { body, .. }
            | SyntaxItem::Optional(body) => pending.extend(body.iter().rev()),
            SyntaxItem::Separated { source, .. } => pending.push(source),
            SyntaxItem::Mapped { source, body, .. } => {
                pending.push(source);
                pending.extend(body.iter().rev());
            },
            SyntaxItem::Token(_)
            | SyntaxItem::Category { .. }
            | SyntaxItem::CaptureIdent { .. }
            | SyntaxItem::CaptureToken { .. }
            | SyntaxItem::Binder { .. }
            | SyntaxItem::Collection { .. }
            | SyntaxItem::Guard { .. } => {},
        }
        if reduce && bridge {
            break;
        }
    }
    let mut rights = Vec::with_capacity(2);
    if reduce {
        rights.push(LanguageRight::Reduce);
    }
    if bridge {
        rights.push(LanguageRight::Bridge);
    }
    for manifest in capability_bindings.iter() {
        for effect in &manifest.effects {
            let right = match effect {
                RuntimeEffect::Reduce => LanguageRight::Reduce,
                RuntimeEffect::Bridge => LanguageRight::Bridge,
                RuntimeEffect::Reflect => LanguageRight::ReflectAst,
            };
            if !rights.contains(&right) {
                rights.push(right);
            }
        }
    }
    LanguageRights::from_rights(rights)
}

fn reject_runtime_source(core: &GrammarCoreV1) -> Result<(), InstallLanguageError> {
    let token = core
        .tokens
        .iter()
        .find(|token| matches!(token.evaluation, Some(crate::NativeEvaluation::Source { .. })));
    if let Some(token) = token {
        return Err(InstallLanguageError::NativeSourceForbidden(format!("token `{}`", token.name)));
    }
    if let Some((index, _)) = core.reductions.iter().enumerate().find(|(_, reduction)| {
        matches!(reduction.evaluation, Some(crate::NativeEvaluation::Source { .. }))
    }) {
        return Err(InstallLanguageError::NativeSourceForbidden(format!("reduction {index}")));
    }
    Ok(())
}

/// Lexical aliases are deliberately outside the installed table. Resolving an
/// alias only returns a capability already placed in this scope.
#[derive(Default)]
pub struct LanguageAliasScope {
    aliases: BTreeMap<String, InstalledLanguageHandle>,
}

impl LanguageAliasScope {
    pub fn bind(
        &mut self,
        alias: impl Into<String>,
        handle: InstalledLanguageHandle,
    ) -> Result<(), AliasError> {
        let alias = alias.into();
        if alias.is_empty() {
            return Err(AliasError::Empty);
        }
        if self.aliases.contains_key(&alias) {
            return Err(AliasError::Duplicate(alias));
        }
        self.aliases.insert(alias, handle);
        Ok(())
    }

    pub fn resolve(&self, alias: &str) -> Option<InstalledLanguageHandle> {
        self.aliases.get(alias).cloned()
    }
}

#[derive(Debug)]
pub enum InstallLanguageError {
    InvalidGrammar(Vec<crate::ValidationError>),
    NativeSourceForbidden(String),
    InvalidImage(ImageError),
    EncodeCore(postcard::Error),
    Capability(RuntimeCapabilityError),
    ConflictingInstallation([u8; 32]),
    EntryIdExhausted,
    EmptyBatch,
    Poisoned,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LanguageAccessError {
    WrongRegistry,
    UnknownLanguage,
    StaleHandle,
    Revoked,
    MissingRight(LanguageRight),
    AmplifiedHandle,
    EpochExhausted,
    Poisoned,
}

#[derive(Debug)]
pub enum InstalledParseError {
    Access(LanguageAccessError),
    Parse(RuntimeError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AliasError {
    Empty,
    Duplicate(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        normalize_runtime_engine, AdmissionTheorem, Carrier, Category, IndexWidth, LexerImage,
        LexerState, ParserImageKind, SpaceRight, SpaceRights, StructuralTheoremChecker, TermHash,
        TheoremChannelDescriptor, TheoremChannelError, TheoremChannelKernel,
        TypedPatternDescriptor, PARSER_IMAGE_ABI_V1, PARSER_IMAGE_MAGIC,
    };

    const COMPILER: &str = "registry-test/1";
    const UNICODE: &str = "unicode-test/1";

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

    fn image(core: &GrammarCoreV1) -> ParserImageV1 {
        let engine = normalize_runtime_engine(core).expect("normalize");
        ParserImageV1 {
            magic: PARSER_IMAGE_MAGIC,
            abi: PARSER_IMAGE_ABI_V1,
            compiler_abi: COMPILER.into(),
            unicode_version: UNICODE.into(),
            core_fingerprint: core.fingerprint().expect("fingerprint"),
            kind: ParserImageKind::Executable,
            index_width: IndexWidth::for_max(engine.nonterminal_count as usize),
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
            reductions: Vec::new(),
            engine,
            limits: core.limits,
        }
    }

    fn install(table: &InstalledLanguageTable, rights: LanguageRights) -> InstalledLanguageGrant {
        let core = core("T");
        let image = image(&core);
        table
            .install_runtime(core, image, rights, COMPILER, UNICODE, "caps/1", [7; 32])
            .expect("install")
    }

    struct ManifestHost {
        code_commitment: [u8; 32],
    }

    impl RuntimeHost for ManifestHost {
        fn capability_manifest(
            &self,
            key: &crate::RuntimeCapabilityKey,
        ) -> Option<crate::RuntimeCapabilityManifest> {
            Some(crate::RuntimeCapabilityManifest {
                key: key.clone(),
                code_commitment: self.code_commitment,
                abi: "installed-manifest-test/1".into(),
                effects: [RuntimeEffect::Reduce].into_iter().collect(),
                cost: crate::RuntimeLogicalCost {
                    base: 1,
                    per_input_byte: 1,
                    per_value: 0,
                    maximum: 1_024,
                },
            })
        }
    }

    fn capability_core() -> GrammarCoreV1 {
        let mut grammar = core("CapabilityBound");
        grammar
            .capabilities
            .insert(crate::Capability::TokenDecoder("test/decoder".into()));
        grammar.tokens.push(crate::TokenDefinition {
            id: crate::TokenId(0),
            name: "external".into(),
            pattern: crate::TokenPattern::Literal("x".into()),
            category: None,
            evaluation: None,
            priority: 0,
            mode: crate::ModeId(0),
            channel: "main".into(),
            transition: crate::ModeTransition::default(),
            decoder: crate::TokenDecoder::Capability("test/decoder".into()),
            reservation: crate::Reservation::None,
        });
        grammar.modes[0].token_ids.push(crate::TokenId(0));
        grammar
    }

    #[test]
    fn runtime_installation_binds_exact_host_manifests_atomically() {
        let table = InstalledLanguageTable::new();
        let grammar = capability_core();
        let mut parser_image = image(&grammar);
        parser_image.lexer.states = vec![
            LexerState {
                transition_start: 0,
                transition_len: 1,
                accept: Vec::new(),
            },
            LexerState {
                transition_start: 1,
                transition_len: 0,
                accept: vec![crate::TokenId(0)],
            },
        ];
        parser_image.lexer.transitions =
            vec![crate::LexerTransition { start: b'x', end: b'x', target: 1 }];
        assert!(matches!(
            table.install_runtime(
                grammar.clone(),
                parser_image.clone(),
                LanguageRights::all(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            ),
            Err(InstallLanguageError::Capability(RuntimeCapabilityError::Missing(_)))
        ));
        assert_eq!(table.installed_count().expect("count"), 0);

        let first_host = ManifestHost { code_commitment: [1; 32] };
        let first = table
            .install_runtime_with_host(
                grammar.clone(),
                parser_image.clone(),
                LanguageRights::all(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
                &first_host,
            )
            .expect("bind first manifest");
        let changed_host = ManifestHost { code_commitment: [2; 32] };
        assert!(matches!(
            table.install_runtime_with_host(
                grammar,
                parser_image,
                LanguageRights::all(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
                &changed_host,
            ),
            Err(InstallLanguageError::ConflictingInstallation(_))
        ));
        assert_eq!(table.installed_count().expect("count"), 1);
        assert!(table.authorize(&first.handle, LanguageRight::Parse).is_ok());
    }

    #[test]
    fn attenuation_cannot_amplify_or_invent_rights() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Parse, LanguageRight::Match]),
        );
        let requested = LanguageRights::from_rights([
            LanguageRight::Parse,
            LanguageRight::Reduce,
            LanguageRight::Publish,
        ]);
        let attenuated = grant.handle.attenuate(&requested);
        assert!(attenuated.rights().contains(LanguageRight::Parse));
        assert!(!attenuated.rights().contains(LanguageRight::Match));
        assert!(!attenuated.rights().contains(LanguageRight::Reduce));
        assert!(!attenuated.rights().contains(LanguageRight::Publish));
        assert!(table.authorize(&attenuated, LanguageRight::Parse).is_ok());
        assert!(matches!(
            table.authorize(&attenuated, LanguageRight::Reduce),
            Err(LanguageAccessError::MissingRight(LanguageRight::Reduce))
        ));
    }

    #[test]
    fn revocation_invalidates_every_preexisting_handle_epoch() {
        let table = InstalledLanguageTable::new();
        let grant = install(&table, LanguageRights::all());
        let clone = grant.handle.clone();
        table.revoke(grant.revocation).expect("revoke");
        assert!(matches!(
            table.authorize(&clone, LanguageRight::Parse),
            Err(LanguageAccessError::StaleHandle)
        ));
    }

    #[test]
    fn identical_install_is_single_flight_with_per_request_rights() {
        let table = InstalledLanguageTable::new();
        let semantic_core = core("T");
        let parser_image = image(&semantic_core);
        let first = table
            .install_runtime(
                semantic_core.clone(),
                parser_image.clone(),
                LanguageRights::all(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("first install");
        let replay = table
            .install_runtime(
                semantic_core,
                parser_image,
                LanguageRights::none(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("identical replay reuses the installed entry");
        assert!(!replay.handle.rights().contains(LanguageRight::Parse));
        assert!(matches!(
            table.authorize(&replay.handle, LanguageRight::Parse),
            Err(LanguageAccessError::MissingRight(LanguageRight::Parse))
        ));
        assert!(table.authorize(&first.handle, LanguageRight::Parse).is_ok());
        table
            .revoke(replay.revocation)
            .expect("shared entry revokes once");
        assert!(matches!(
            table.authorize(&first.handle, LanguageRight::Parse),
            Err(LanguageAccessError::StaleHandle)
        ));
    }

    #[test]
    fn conflicting_policy_commitment_cannot_replace_an_installed_entry() {
        let table = InstalledLanguageTable::new();
        let semantic_core = core("T");
        let parser_image = image(&semantic_core);
        let first = table
            .install_runtime(
                semantic_core.clone(),
                parser_image.clone(),
                LanguageRights::all(),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("first install");
        let conflict = table.install_runtime(
            semantic_core,
            parser_image,
            LanguageRights::all(),
            COMPILER,
            UNICODE,
            "caps/1",
            [8; 32],
        );
        assert!(matches!(conflict, Err(InstallLanguageError::ConflictingInstallation(_))));
        assert!(table.authorize(&first.handle, LanguageRight::Parse).is_ok());
    }

    #[test]
    fn runtime_batch_publishes_every_language_in_one_commit() {
        let table = InstalledLanguageTable::new();
        let left = core("Left");
        let right = core("Right");
        let grants = table
            .install_runtime_batch(
                vec![
                    RuntimeLanguageInstall {
                        image: image(&left),
                        core: left,
                        granted_rights: LanguageRights::from_rights([LanguageRight::Parse]),
                    },
                    RuntimeLanguageInstall {
                        image: image(&right),
                        core: right,
                        granted_rights: LanguageRights::from_rights([LanguageRight::Parse]),
                    },
                ],
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("batch install");

        assert_eq!(grants.len(), 2);
        assert_eq!(table.installed_count().expect("count"), 2);
        assert!(grants
            .iter()
            .all(|grant| table.authorize(&grant.handle, LanguageRight::Parse).is_ok()));
    }

    #[test]
    fn runtime_batch_with_a_late_invalid_image_publishes_no_prefix() {
        let table = InstalledLanguageTable::new();
        let left = core("Left");
        let right = core("Right");
        let mut invalid_right_image = image(&right);
        invalid_right_image.core_fingerprint = [0xff; 32];

        let result = table.install_runtime_batch(
            vec![
                RuntimeLanguageInstall {
                    image: image(&left),
                    core: left,
                    granted_rights: LanguageRights::all(),
                },
                RuntimeLanguageInstall {
                    image: invalid_right_image,
                    core: right,
                    granted_rights: LanguageRights::all(),
                },
            ],
            COMPILER,
            UNICODE,
            "caps/1",
            [7; 32],
        );

        assert!(matches!(result, Err(InstallLanguageError::InvalidImage(_))));
        assert_eq!(table.installed_count().expect("count"), 0);
    }

    #[test]
    fn runtime_batch_conflict_publishes_nothing_and_changes_no_rights() {
        let table = InstalledLanguageTable::new();
        let existing_core = core("Existing");
        let existing = table
            .install_runtime(
                existing_core.clone(),
                image(&existing_core),
                LanguageRights::from_rights([LanguageRight::Parse]),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("existing install");
        let fresh = core("Fresh");
        let result = table.install_runtime_batch(
            vec![
                RuntimeLanguageInstall {
                    image: image(&fresh),
                    core: fresh,
                    granted_rights: LanguageRights::all(),
                },
                RuntimeLanguageInstall {
                    image: image(&existing_core),
                    core: existing_core,
                    granted_rights: LanguageRights::all(),
                },
            ],
            COMPILER,
            UNICODE,
            "caps/1",
            [8; 32],
        );

        assert!(matches!(result, Err(InstallLanguageError::ConflictingInstallation(_))));
        assert_eq!(table.installed_count().expect("count"), 1);
        assert!(table
            .authorize(&existing.handle, LanguageRight::Parse)
            .is_ok());
        assert!(matches!(
            table.authorize(&existing.handle, LanguageRight::Bridge),
            Err(LanguageAccessError::MissingRight(LanguageRight::Bridge))
        ));
    }

    #[test]
    fn revoked_language_can_be_reinstalled_with_a_fresh_seal() {
        let table = InstalledLanguageTable::new();
        let first = install(&table, LanguageRights::all());
        let stale = first.handle.clone();
        table
            .revoke(first.revocation)
            .expect("revoke first generation");

        let second = install(&table, LanguageRights::all());
        assert_ne!(stale, second.handle);
        assert!(matches!(
            table.authorize(&stale, LanguageRight::Parse),
            Err(LanguageAccessError::StaleHandle)
        ));
        assert!(table
            .authorize(&second.handle, LanguageRight::Parse)
            .is_ok());
    }

    #[test]
    fn aliases_are_lexical_capability_bindings_not_fingerprint_lookups() {
        let table = InstalledLanguageTable::new();
        let grant = install(&table, LanguageRights::all());
        let mut scope = LanguageAliasScope::default();
        scope.bind("calc", grant.handle.clone()).expect("bind");
        assert_eq!(scope.resolve("calc"), Some(grant.handle));
        assert!(scope.resolve("unknown").is_none());
    }

    struct StaticAdapter;

    impl StaticParserAdapter for StaticAdapter {
        fn parse(
            &self,
            _source: &str,
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            Ok(vec![WeightedParse {
                syntax: crate::DynamicValue::Unit,
                value: crate::DynamicValue::Unit,
                cost: crate::ExactParseCost::default(),
                rank: crate::DerivationRank::default(),
                production: Some(crate::ProductionId(0)),
            }])
        }
    }

    #[test]
    fn static_adapter_uses_the_same_capability_table() {
        let table = InstalledLanguageTable::new();
        let grant = table
            .install_static(
                core("Static"),
                Arc::new(StaticAdapter),
                "typed-test/1",
                LanguageRights::from_rights([LanguageRight::Parse]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [0; 32],
            )
            .expect("install static");
        let parsed = table
            .parse(
                &grant.handle,
                "anything",
                None,
                &crate::DefaultRuntimeHost,
                RuntimePolicy::default(),
            )
            .expect("parse through typed adapter");
        assert_eq!(parsed[0].value, crate::DynamicValue::Unit);
    }

    struct EffectfulStaticAdapter {
        calls: std::sync::atomic::AtomicUsize,
    }

    impl StaticParserAdapter for EffectfulStaticAdapter {
        fn parse(
            &self,
            _source: &str,
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            Ok(vec![unit_weighted_parse()])
        }

        fn required_effect_rights(&self) -> LanguageRights {
            LanguageRights::from_rights([LanguageRight::Reduce, LanguageRight::Bridge])
        }
    }

    #[test]
    fn parser_effects_are_authorized_before_static_adapter_execution() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(EffectfulStaticAdapter {
            calls: std::sync::atomic::AtomicUsize::new(0),
        });
        let grant = table
            .install_static(
                core("EffectfulStatic"),
                adapter.clone(),
                "typed-effect-test/1",
                LanguageRights::from_rights([LanguageRight::Parse]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [31; 32],
            )
            .expect("install effectful adapter");
        assert!(matches!(
            table.parse(
                &grant.handle,
                "anything",
                None,
                &crate::DefaultRuntimeHost,
                RuntimePolicy::default(),
            ),
            Err(InstalledParseError::Access(LanguageAccessError::MissingRight(
                LanguageRight::Reduce
            )))
        ));
        assert_eq!(adapter.calls.load(Ordering::SeqCst), 0);

        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(EffectfulStaticAdapter {
            calls: std::sync::atomic::AtomicUsize::new(0),
        });
        let grant = table
            .install_static(
                core("EffectfulStatic"),
                adapter.clone(),
                "typed-effect-test/1",
                LanguageRights::from_rights([LanguageRight::Parse, LanguageRight::Reduce]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [31; 32],
            )
            .expect("install adapter without bridge right");
        assert!(matches!(
            table.parse(
                &grant.handle,
                "anything",
                None,
                &crate::DefaultRuntimeHost,
                RuntimePolicy::default(),
            ),
            Err(InstalledParseError::Access(LanguageAccessError::MissingRight(
                LanguageRight::Bridge
            )))
        ));
        assert_eq!(adapter.calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn runtime_effect_profile_scans_nested_syntax_iteratively() {
        let mut grammar = core("EffectProfile");
        grammar.tokens.push(crate::TokenDefinition {
            id: crate::TokenId(0),
            name: "effectful".into(),
            pattern: crate::TokenPattern::Literal("x".into()),
            category: Some(CategoryId(0)),
            evaluation: Some(crate::NativeEvaluation::Operator("neg".into())),
            priority: 0,
            mode: crate::ModeId(0),
            channel: "main".into(),
            transition: crate::ModeTransition::default(),
            decoder: crate::TokenDecoder::Text,
            reservation: crate::Reservation::None,
        });
        let mut nested = SyntaxItem::ForeignLanguage {
            slot: "guest".into(),
            open: "{{".into(),
            close: "}}".into(),
        };
        for _ in 0..2_000 {
            nested = SyntaxItem::Optional(vec![nested]);
        }
        grammar.productions.push(crate::Production {
            id: crate::ProductionId(0),
            constructor: crate::ConstructorId(0),
            label: "NestedForeign".into(),
            result: CategoryId(0),
            syntax: vec![nested],
            precedence: crate::Precedence::default(),
            classification: crate::ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });

        let rights = runtime_effect_rights(&grammar, &RuntimeCapabilityBindings::default());
        assert!(rights.contains(LanguageRight::Reduce));
        assert!(rights.contains(LanguageRight::Bridge));
        std::mem::forget(grammar);
    }

    fn unit_weighted_parse() -> WeightedParse {
        WeightedParse {
            syntax: crate::DynamicValue::Unit,
            value: crate::DynamicValue::Unit,
            cost: crate::ExactParseCost::default(),
            rank: crate::DerivationRank::default(),
            production: Some(crate::ProductionId(0)),
        }
    }

    struct CountingTemplateAdapter {
        calls: std::sync::atomic::AtomicUsize,
        commitment: Option<[u8; 32]>,
        release: Option<Arc<(Mutex<bool>, Condvar)>>,
    }

    impl CountingTemplateAdapter {
        fn committed() -> Self {
            Self {
                calls: std::sync::atomic::AtomicUsize::new(0),
                commitment: Some([17; 32]),
                release: None,
            }
        }

        fn calls(&self) -> usize {
            self.calls.load(Ordering::SeqCst)
        }
    }

    impl StaticParserAdapter for CountingTemplateAdapter {
        fn parse(
            &self,
            _source: &str,
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            Ok(vec![unit_weighted_parse()])
        }

        fn parse_template(
            &self,
            _pieces: &[RuntimeTemplatePiece],
            _holes: &[RuntimeTemplateHole],
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            if let Some(release) = &self.release {
                let (lock, ready) = release.as_ref();
                let mut released = recover_lock(lock);
                while !*released {
                    released = ready
                        .wait(released)
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                }
            }
            Ok(vec![unit_weighted_parse()])
        }

        fn template_cache_commitment(&self) -> Option<[u8; 32]> {
            self.commitment
        }
    }

    fn install_template_adapter(
        table: &InstalledLanguageTable,
        adapter: Arc<CountingTemplateAdapter>,
    ) -> InstalledLanguageGrant {
        table
            .install_static(
                core("CachedStatic"),
                adapter,
                "typed-template-test/1",
                LanguageRights::from_rights([
                    LanguageRight::Parse,
                    LanguageRight::Construct,
                    LanguageRight::Match,
                ]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [19; 32],
            )
            .expect("install template adapter")
    }

    fn parse_static_template(
        table: &InstalledLanguageTable,
        handle: &InstalledLanguageHandle,
        text: &str,
        host: &dyn RuntimeHost,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, InstalledParseError> {
        table.parse_template(
            handle,
            &[RuntimeTemplatePiece::Text(text.into())],
            &[],
            None,
            host,
            policy,
            LanguageRight::Construct,
        )
    }

    #[test]
    fn identical_symbolic_templates_are_memoized_once() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter::committed());
        let grant = install_template_adapter(&table, adapter.clone());
        let policy = RuntimePolicy::default();

        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("first template parse");
        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("cached template parse");

        assert_eq!(adapter.calls(), 1);
    }

    #[test]
    fn symbolic_template_cache_is_fifo_bounded_and_zero_disables_it() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter::committed());
        let grant = install_template_adapter(&table, adapter.clone());
        let one_entry = RuntimePolicy {
            max_symbolic_template_cache_entries: 1,
            ..RuntimePolicy::default()
        };

        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, one_entry)
            .expect("cache x");
        parse_static_template(&table, &grant.handle, "y", &crate::DefaultRuntimeHost, one_entry)
            .expect("cache y and evict x");
        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, one_entry)
            .expect("reparse evicted x");
        assert_eq!(adapter.calls(), 3);

        let mut disabled = one_entry;
        disabled.max_symbolic_template_cache_entries = 0;
        parse_static_template(&table, &grant.handle, "z", &crate::DefaultRuntimeHost, disabled)
            .expect("uncached z");
        parse_static_template(&table, &grant.handle, "z", &crate::DefaultRuntimeHost, disabled)
            .expect("uncached z again");
        assert_eq!(adapter.calls(), 5);
    }

    #[test]
    fn symbolic_template_cache_rejects_results_over_its_weight_budget() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter::committed());
        let grant = install_template_adapter(&table, adapter.clone());
        let policy = RuntimePolicy {
            max_symbolic_template_cache_weight: 1,
            ..RuntimePolicy::default()
        };

        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("oversize parse");
        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("oversize parse is not retained");
        assert_eq!(adapter.calls(), 2);
    }

    struct UncommittedHost;

    impl RuntimeHost for UncommittedHost {}

    #[test]
    fn uncommitted_host_or_adapter_bypasses_symbolic_memoization() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter::committed());
        let grant = install_template_adapter(&table, adapter.clone());
        let policy = RuntimePolicy::default();
        parse_static_template(&table, &grant.handle, "x", &UncommittedHost, policy)
            .expect("uncommitted host parse");
        parse_static_template(&table, &grant.handle, "x", &UncommittedHost, policy)
            .expect("uncommitted host parse again");
        assert_eq!(adapter.calls(), 2);

        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter {
            calls: std::sync::atomic::AtomicUsize::new(0),
            commitment: None,
            release: None,
        });
        let grant = install_template_adapter(&table, adapter.clone());
        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("uncommitted adapter parse");
        parse_static_template(&table, &grant.handle, "x", &crate::DefaultRuntimeHost, policy)
            .expect("uncommitted adapter parse again");
        assert_eq!(adapter.calls(), 2);
    }

    struct CountingCommittedHost {
        commitment_reads: std::sync::atomic::AtomicUsize,
        epoch: AtomicU64,
    }

    impl RuntimeHost for CountingCommittedHost {
        fn semantic_cache_commitment(&self) -> Option<[u8; 32]> {
            self.commitment_reads.fetch_add(1, Ordering::SeqCst);
            let mut commitment = [0; 32];
            commitment[..8].copy_from_slice(&self.epoch.load(Ordering::SeqCst).to_be_bytes());
            Some(commitment)
        }
    }

    #[test]
    fn concurrent_identical_templates_share_one_in_flight_parse() {
        let table = Arc::new(InstalledLanguageTable::new());
        let release = Arc::new((Mutex::new(false), Condvar::new()));
        let adapter = Arc::new(CountingTemplateAdapter {
            calls: std::sync::atomic::AtomicUsize::new(0),
            commitment: Some([17; 32]),
            release: Some(release.clone()),
        });
        let grant = install_template_adapter(&table, adapter.clone());
        let host = Arc::new(CountingCommittedHost {
            commitment_reads: std::sync::atomic::AtomicUsize::new(0),
            epoch: AtomicU64::new(1),
        });
        let first_table = table.clone();
        let first_handle = grant.handle.clone();
        let first_host = host.clone();
        let first = std::thread::spawn(move || {
            parse_static_template(
                &first_table,
                &first_handle,
                "x",
                first_host.as_ref(),
                RuntimePolicy::default(),
            )
        });
        while adapter.calls() == 0 {
            std::thread::yield_now();
        }

        let second_table = table.clone();
        let second_handle = grant.handle.clone();
        let second_host = host.clone();
        let second = std::thread::spawn(move || {
            parse_static_template(
                &second_table,
                &second_handle,
                "x",
                second_host.as_ref(),
                RuntimePolicy::default(),
            )
        });
        while host.commitment_reads.load(Ordering::SeqCst) < 2 {
            std::thread::yield_now();
        }
        assert_eq!(adapter.calls(), 1);
        {
            let (lock, ready) = release.as_ref();
            *recover_lock(lock) = true;
            ready.notify_all();
        }
        first.join().expect("first worker").expect("first parse");
        second.join().expect("second worker").expect("second parse");
        assert_eq!(adapter.calls(), 1);
    }

    #[test]
    fn changing_the_host_semantic_epoch_invalidates_the_cache_key() {
        let table = InstalledLanguageTable::new();
        let adapter = Arc::new(CountingTemplateAdapter::committed());
        let grant = install_template_adapter(&table, adapter.clone());
        let host = CountingCommittedHost {
            commitment_reads: std::sync::atomic::AtomicUsize::new(0),
            epoch: AtomicU64::new(1),
        };
        let policy = RuntimePolicy::default();

        parse_static_template(&table, &grant.handle, "x", &host, policy).expect("epoch one parse");
        parse_static_template(&table, &grant.handle, "x", &host, policy)
            .expect("epoch one cache hit");
        host.epoch.store(2, Ordering::SeqCst);
        parse_static_template(&table, &grant.handle, "x", &host, policy).expect("epoch two parse");

        assert_eq!(adapter.calls(), 2);
    }

    struct ReentrantTemplateAdapter {
        table: Arc<InstalledLanguageTable>,
        handle: Mutex<Option<InstalledLanguageHandle>>,
    }

    impl StaticParserAdapter for ReentrantTemplateAdapter {
        fn parse(
            &self,
            _source: &str,
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            Ok(vec![unit_weighted_parse()])
        }

        fn parse_template(
            &self,
            pieces: &[RuntimeTemplatePiece],
            holes: &[RuntimeTemplateHole],
            category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            let handle = recover_lock(&self.handle)
                .clone()
                .expect("test handle installed before parsing");
            match self.table.parse_template(
                &handle,
                pieces,
                holes,
                category,
                &crate::DefaultRuntimeHost,
                policy,
                LanguageRight::Construct,
            ) {
                Err(InstalledParseError::Parse(error)) => Err(error),
                Err(InstalledParseError::Access(error)) => {
                    Err(RuntimeError::Reduction(format!("unexpected access error: {error:?}")))
                },
                Ok(_) => Err(RuntimeError::Reduction(
                    "reentrant template parse unexpectedly succeeded".into(),
                )),
            }
        }

        fn template_cache_commitment(&self) -> Option<[u8; 32]> {
            Some([23; 32])
        }
    }

    #[test]
    fn same_thread_same_key_reentry_is_rejected_without_recursion() {
        let table = Arc::new(InstalledLanguageTable::new());
        let adapter = Arc::new(ReentrantTemplateAdapter {
            table: table.clone(),
            handle: Mutex::new(None),
        });
        let grant = table
            .install_static(
                core("ReentrantStatic"),
                adapter.clone(),
                "typed-template-reentrant-test/1",
                LanguageRights::from_rights([LanguageRight::Parse, LanguageRight::Construct]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [29; 32],
            )
            .expect("install reentrant adapter");
        *recover_lock(&adapter.handle) = Some(grant.handle.clone());

        assert!(matches!(
            parse_static_template(
                &table,
                &grant.handle,
                "x",
                &crate::DefaultRuntimeHost,
                RuntimePolicy::default(),
            ),
            Err(InstalledParseError::Parse(RuntimeError::TemplateCacheCycle))
        ));
    }

    struct RevokeDuringParseAdapter {
        table: Arc<InstalledLanguageTable>,
        authority: std::sync::Mutex<Option<LanguageRevocationAuthority>>,
    }

    impl StaticParserAdapter for RevokeDuringParseAdapter {
        fn parse(
            &self,
            _source: &str,
            _category: Option<CategoryId>,
            _host: &dyn RuntimeHost,
            _policy: RuntimePolicy,
        ) -> Result<Vec<WeightedParse>, RuntimeError> {
            let authority = self
                .authority
                .lock()
                .expect("test revocation slot")
                .take()
                .expect("test installs revocation authority before parsing");
            self.table
                .revoke(authority)
                .expect("revocation during parse");
            Ok(vec![WeightedParse {
                syntax: crate::DynamicValue::Unit,
                value: crate::DynamicValue::Unit,
                cost: crate::ExactParseCost::default(),
                rank: crate::DerivationRank::default(),
                production: Some(crate::ProductionId(0)),
            }])
        }
    }

    #[test]
    fn revocation_during_parse_discards_the_unpublishable_result() {
        let table = Arc::new(InstalledLanguageTable::new());
        let adapter = Arc::new(RevokeDuringParseAdapter {
            table: table.clone(),
            authority: std::sync::Mutex::new(None),
        });
        let grant = table
            .install_static(
                core("RevocationRace"),
                adapter.clone(),
                "typed-test/1",
                LanguageRights::from_rights([LanguageRight::Parse]),
                "compile-time/1",
                UNICODE,
                "caps/1",
                [0; 32],
            )
            .expect("install revocation-race adapter");
        *adapter.authority.lock().expect("test revocation slot") = Some(grant.revocation);

        assert!(matches!(
            table.parse(
                &grant.handle,
                "anything",
                None,
                &crate::DefaultRuntimeHost,
                RuntimePolicy::default(),
            ),
            Err(InstalledParseError::Access(LanguageAccessError::StaleHandle))
        ));
    }

    fn theorem_kernel(language: [u8; 32], rights: SpaceRights) -> TheoremChannelKernel {
        let membership = AdmissionTheorem::membership(CategoryId(0));
        theorem_kernel_with(language, membership, membership, rights, 16)
    }

    fn theorem_kernel_with(
        language: [u8; 32],
        channel_theorem: AdmissionTheorem,
        space_theorem: AdmissionTheorem,
        rights: SpaceRights,
        proof_cache_capacity: usize,
    ) -> TheoremChannelKernel {
        TheoremChannelKernel::new(
            TheoremChannelDescriptor::new(language, CategoryId(0), channel_theorem, space_theorem)
                .expect("channel descriptor"),
            rights,
            StructuralTheoremChecker::default(),
            proof_cache_capacity,
        )
    }

    #[test]
    fn theorem_channel_revalidates_space_epoch_before_mutation() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let kernel = theorem_kernel(grant.handle.fingerprint(), SpaceRights::all());
        let prepared = kernel
            .prepare_produce(&table, &grant.handle, TermHash([4; 32]))
            .expect("prepare admitted produce");
        kernel.revoke().expect("revoke channel authority");
        let mut called = false;
        assert!(matches!(
            kernel.commit_produce(&table, prepared, |_| called = true),
            Err(TheoremChannelError::StaleEpoch)
        ));
        assert!(!called, "rejection must not invoke the mutation callback");
    }

    #[test]
    fn proof_cache_hit_cannot_bypass_language_revocation() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let kernel = theorem_kernel(grant.handle.fingerprint(), SpaceRights::all());
        let prepared = kernel
            .prepare_produce(&table, &grant.handle, TermHash([5; 32]))
            .expect("prepare fills the proof cache");
        table
            .revoke(grant.revocation)
            .expect("revoke installed language");
        let mut called = false;
        assert!(matches!(
            kernel.commit_produce(&table, prepared, |_| called = true),
            Err(TheoremChannelError::LanguageAccess(LanguageAccessError::StaleHandle))
        ));
        assert!(!called, "cached proof truth is not live authority");
    }

    #[test]
    fn theorem_channel_rejects_a_capable_handle_for_another_language() {
        let table = InstalledLanguageTable::new();
        let channel_language = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let other_core = core("OtherLanguage");
        let other_language = table
            .install_runtime(
                other_core.clone(),
                image(&other_core),
                LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
                COMPILER,
                UNICODE,
                "caps/1",
                [7; 32],
            )
            .expect("install other language");
        let kernel = theorem_kernel(channel_language.handle.fingerprint(), SpaceRights::all());
        assert!(matches!(
            kernel.prepare_produce(&table, &other_language.handle, TermHash([42; 32])),
            Err(TheoremChannelError::LanguageMismatch)
        ));

        let message = kernel
            .commit_produce(
                &table,
                kernel
                    .prepare_produce(&table, &channel_language.handle, TermHash([43; 32]))
                    .expect("prepare channel message"),
                |message| message,
            )
            .expect("commit channel message");
        let pattern = TypedPatternDescriptor::new(
            channel_language.handle.fingerprint(),
            CategoryId(0),
            [44; 32],
            None,
            Vec::new(),
            0,
        )
        .expect("capture-free pattern");
        assert!(matches!(
            kernel.prepare_consume(&table, &other_language.handle, &message, &pattern, &[]),
            Err(TheoremChannelError::LanguageMismatch)
        ));
    }

    #[test]
    fn typed_consume_carries_checked_message_and_capture_evidence() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let language = grant.handle.fingerprint();
        let kernel = theorem_kernel(language, SpaceRights::all());
        let term_hash = TermHash([6; 32]);
        let prepared = kernel
            .prepare_produce(&table, &grant.handle, term_hash)
            .expect("prepare produce");
        let message = kernel
            .commit_produce(&table, prepared, |message| message)
            .expect("commit produce");
        let capture_hash = TermHash([7; 32]);
        let pattern = TypedPatternDescriptor::new(
            language,
            CategoryId(0),
            [8; 32],
            Some(term_hash),
            vec![CategoryId(0)],
            8,
        )
        .expect("typed pattern");
        let prepared = kernel
            .prepare_consume(&table, &grant.handle, &message, &pattern, &[capture_hash])
            .expect("prepare typed match");
        let evidence = kernel
            .commit_consume(&table, prepared, |evidence| evidence)
            .expect("commit consume");
        assert_eq!(evidence.pattern_id(), pattern.id());
        assert_eq!(evidence.message(), &message);
        assert_eq!(evidence.captures().len(), 1);
        assert_eq!(evidence.captures()[0].term().term_hash(), capture_hash);
    }

    #[test]
    fn zero_capacity_proof_cache_is_semantics_inert() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let kernel = theorem_kernel_with(
            grant.handle.fingerprint(),
            AdmissionTheorem::membership(CategoryId(0)),
            AdmissionTheorem::membership(CategoryId(0)),
            SpaceRights::all(),
            0,
        );
        let prepared = kernel
            .prepare_produce(&table, &grant.handle, TermHash([9; 32]))
            .expect("proof checking must not depend on cache insertion");
        let message = kernel
            .commit_produce(&table, prepared, |message| message)
            .expect("cache-free produce commits");
        let pattern = TypedPatternDescriptor::new(
            grant.handle.fingerprint(),
            CategoryId(0),
            [10; 32],
            None,
            Vec::new(),
            0,
        )
        .expect("capture-free pattern");
        let prepared = kernel
            .prepare_consume(&table, &grant.handle, &message, &pattern, &[])
            .expect("cache-free consume prepares");
        kernel
            .commit_consume(&table, prepared, |_| ())
            .expect("cache-free consume commits");
    }

    #[test]
    fn theorem_reindexing_checks_the_target_predicate_and_recertifies() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let language = grant.handle.fingerprint();
        let membership = AdmissionTheorem::membership(CategoryId(0));
        let source = theorem_kernel_with(language, membership, membership, SpaceRights::all(), 4);
        let accepted_hash = TermHash([11; 32]);
        let message = source
            .commit_produce(
                &table,
                source
                    .prepare_produce(&table, &grant.handle, accepted_hash)
                    .expect("membership produce"),
                |message| message,
            )
            .expect("membership commit");
        let exact = AdmissionTheorem::exact(CategoryId(0), accepted_hash);
        let target = theorem_kernel_with(language, exact, membership, SpaceRights::all(), 4);
        let pattern =
            TypedPatternDescriptor::new(language, CategoryId(0), [12; 32], None, Vec::new(), 0)
                .expect("capture-free pattern");
        let checked = target
            .prepare_consume(&table, &grant.handle, &message, &pattern, &[])
            .expect("matching exact theorem is proved locally");
        let evidence = target
            .commit_consume(&table, checked, |evidence| evidence)
            .expect("reindexed consume");
        assert_eq!(evidence.message().certificate().theorem(), exact);

        let rejecting = theorem_kernel_with(
            language,
            AdmissionTheorem::exact(CategoryId(0), TermHash([13; 32])),
            membership,
            SpaceRights::all(),
            4,
        );
        assert!(matches!(
            rejecting.prepare_consume(&table, &grant.handle, &message, &pattern, &[]),
            Err(TheoremChannelError::Certificate(crate::CertificateError::TheoremDoesNotHold))
        ));
    }

    #[test]
    fn consume_revalidates_space_epoch_before_mutation() {
        let table = InstalledLanguageTable::new();
        let grant = install(
            &table,
            LanguageRights::from_rights([LanguageRight::Publish, LanguageRight::Match]),
        );
        let kernel = theorem_kernel(grant.handle.fingerprint(), SpaceRights::all());
        let message = kernel
            .commit_produce(
                &table,
                kernel
                    .prepare_produce(&table, &grant.handle, TermHash([14; 32]))
                    .expect("prepare produce"),
                |message| message,
            )
            .expect("commit produce");
        let pattern = TypedPatternDescriptor::new(
            grant.handle.fingerprint(),
            CategoryId(0),
            [15; 32],
            None,
            Vec::new(),
            0,
        )
        .expect("capture-free pattern");
        let prepared = kernel
            .prepare_consume(&table, &grant.handle, &message, &pattern, &[])
            .expect("prepare consume");
        kernel
            .attenuate_space_rights(&SpaceRights::from_rights([SpaceRight::Produce]))
            .expect("remove consume authority");
        let mut called = false;
        assert!(matches!(
            kernel.commit_consume(&table, prepared, |_| called = true),
            Err(TheoremChannelError::StaleEpoch)
        ));
        assert!(!called, "stale consume must not reach the mutation callback");
    }
}
