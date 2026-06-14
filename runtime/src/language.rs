//! Core language traits and types for MeTTaIL
//!
//! These types are shared between the macro-generated code and the REPL.

use std::any::Any;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::LanguageMetadata;

/// Seed facts for pre-populating Ascent relations before fixpoint.
///
/// Keys are relation names (e.g., `"certified"`), values are tuples
/// represented as string vectors (e.g., `vec![vec!["item_A"]]`).
/// The codegen parses each string into the relation's parameter type
/// at runtime.
pub type SeedFacts = HashMap<String, Vec<Vec<String>>>;

/// Exact observational key for a term in an extracted rewrite graph.
///
/// Generated languages populate this from their semantic hash write stream,
/// not from a fixed-width digest. Legacy/manual result graphs may leave it
/// absent, in which case traversal falls back to `term_id`.
pub type ExactTermKey = Vec<u8>;

/// Runtime seed id plus display text and priority weight.
///
/// Lower weights are explored first by weighted prefix traversal. The display
/// component is diagnostic only; it must not be used as an equivalence key.
pub type WeightedSeedId = (u64, String, f64);

/// Runtime backend selected for a language evaluation.
///
/// `Ascent` is the legacy/reference rewrite backend. `Dovetail` and
/// `RhoMachine` are explicit targets so user-facing execution can be routed by a
/// verified flip gate instead of hard-coding Ascent forever.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeBackend {
    Ascent,
    Dovetail,
    RhoMachine,
}

impl fmt::Display for RuntimeBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeBackend::Ascent => write!(f, "Ascent"),
            RuntimeBackend::Dovetail => write!(f, "Dovetail"),
            RuntimeBackend::RhoMachine => write!(f, "RhoMachine"),
        }
    }
}

/// Executable runtime backend capability for a concrete `Language` value.
///
/// Static generated metadata uses [`crate::BackendCapabilityDef`]. This owned
/// form is the runtime view: wrappers can add flip-gated backends and attach
/// plan-specific evidence without mutating generated static metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeBackendCapability {
    pub backend: RuntimeBackend,
    pub is_default: bool,
    pub evidence_refs: Vec<String>,
}

impl RuntimeBackendCapability {
    pub fn from_static(capability: &crate::BackendCapabilityDef) -> Self {
        Self {
            backend: capability.backend,
            is_default: capability.is_default,
            evidence_refs: capability
                .evidence_refs
                .iter()
                .map(|reference| (*reference).to_string())
                .collect(),
        }
    }
}

/// Executable artifact boundary used by a runtime backend report.
///
/// This is deliberately substrate-neutral. `RhoNormalizedAst` corresponds to a
/// direct `rhoapi::Par` value, not Rholang source text; `RhoBytecode` is the
/// forward-compatible execution artifact for the planned bytecode path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeBackendArtifact {
    /// Legacy/reference Ascent fixpoint facts.
    AscentFixpoint,
    /// Dovetail's checked, substrate-neutral rewrite report.
    DovetailRunReport,
    /// Normalized Rholang AST (`rhoapi::Par`) injected directly into RhoRuntime.
    RhoNormalizedAst,
    /// Rholang bytecode artifact, once the host runtime exposes bytecode.
    RhoBytecode,
}

impl fmt::Display for RuntimeBackendArtifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeBackendArtifact::AscentFixpoint => write!(f, "AscentFixpoint"),
            RuntimeBackendArtifact::DovetailRunReport => write!(f, "DovetailRunReport"),
            RuntimeBackendArtifact::RhoNormalizedAst => write!(f, "RhoNormalizedAst"),
            RuntimeBackendArtifact::RhoBytecode => write!(f, "RhoBytecode"),
        }
    }
}

/// Ground observation value returned by a non-Ascent runtime backend.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum RuntimeObservationValue {
    Int(i64),
    Bool(bool),
    Text(String),
    TermDisplay(String),
    Bytes(Vec<u8>),
    Uri(String),
    DoubleBits(u64),
    BigIntBytes(Vec<u8>),
    BigRationalBytes { numerator: Vec<u8>, denominator: Vec<u8> },
    FixedPointBytes { unscaled: Vec<u8>, scale: u32 },
    PrivateName(Vec<u8>),
    DeployId(Vec<u8>),
    DeployerId(Vec<u8>),
    SysAuthToken,
    List(Vec<RuntimeObservationValue>),
    Tuple(Vec<RuntimeObservationValue>),
    Set(Vec<RuntimeObservationValue>),
    Map(Vec<(RuntimeObservationValue, RuntimeObservationValue)>),
    Bag(Vec<(RuntimeObservationValue, usize)>),
}

impl fmt::Display for RuntimeObservationValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeObservationValue::Int(value) => write!(f, "{}", value),
            RuntimeObservationValue::Bool(value) => write!(f, "{}", value),
            RuntimeObservationValue::Text(value) => write!(f, "{:?}", value),
            RuntimeObservationValue::TermDisplay(value) => write!(f, "{}", value),
            RuntimeObservationValue::Bytes(value) => write!(f, "0x{}", hex_bytes(value)),
            RuntimeObservationValue::Uri(value) => write!(f, "Uri({:?})", value),
            RuntimeObservationValue::DoubleBits(value) => write!(f, "DoubleBits(0x{value:016x})"),
            RuntimeObservationValue::BigIntBytes(value) => {
                write!(f, "BigInt(0x{})", hex_bytes(value))
            },
            RuntimeObservationValue::BigRationalBytes { numerator, denominator } => {
                write!(f, "BigRat(0x{}/0x{})", hex_bytes(numerator), hex_bytes(denominator))
            },
            RuntimeObservationValue::FixedPointBytes { unscaled, scale } => {
                write!(f, "FixedPoint(0x{} scale {scale})", hex_bytes(unscaled))
            },
            RuntimeObservationValue::PrivateName(value) => {
                write!(f, "Private(0x{})", hex_bytes(value))
            },
            RuntimeObservationValue::DeployId(value) => {
                write!(f, "DeployId(0x{})", hex_bytes(value))
            },
            RuntimeObservationValue::DeployerId(value) => {
                write!(f, "DeployerId(0x{})", hex_bytes(value))
            },
            RuntimeObservationValue::SysAuthToken => write!(f, "SysAuthToken"),
            RuntimeObservationValue::List(values) => fmt_observation_sequence(f, "[", values, "]"),
            RuntimeObservationValue::Tuple(values) => fmt_observation_sequence(f, "(", values, ")"),
            RuntimeObservationValue::Set(values) => {
                fmt_observation_sequence(f, "Set{", values, "}")
            },
            RuntimeObservationValue::Map(entries) => {
                write!(f, "{{")?;
                for (idx, (key, value)) in entries.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", key, value)?;
                }
                write!(f, "}}")
            },
            RuntimeObservationValue::Bag(entries) => {
                write!(f, "Bag{{")?;
                for (idx, (value, count)) in entries.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} * {}", value, count)?;
                }
                write!(f, "}}")
            },
        }
    }
}

fn fmt_observation_sequence(
    f: &mut fmt::Formatter<'_>,
    open: &str,
    values: &[RuntimeObservationValue],
    close: &str,
) -> fmt::Result {
    write!(f, "{open}")?;
    for (idx, value) in values.iter().enumerate() {
        if idx > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{value}")?;
    }
    write!(f, "{close}")
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

/// Values observed on one runtime output channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeChannelObservation {
    pub channel: String,
    pub values: Vec<RuntimeObservationValue>,
}

impl RuntimeChannelObservation {
    pub fn new(channel: impl Into<String>, values: Vec<RuntimeObservationValue>) -> Self {
        Self { channel: channel.into(), values }
    }

    /// Number of values observed before any order-insensitive projection.
    pub fn observed_count(&self) -> usize {
        self.values.len()
    }

    /// Order-insensitive exact-membership fingerprint for set-semantics checks.
    pub fn membership_fingerprint(&self) -> BTreeSet<RuntimeObservationValue> {
        self.values.iter().cloned().collect()
    }

    /// Order-insensitive counted fingerprint for bag-sensitive checks.
    pub fn multiplicity_fingerprint(&self) -> BTreeMap<RuntimeObservationValue, usize> {
        self.values
            .iter()
            .cloned()
            .fold(BTreeMap::new(), |mut counts, value| {
                *counts.entry(value).or_insert(0) += 1;
                counts
            })
    }
}

/// Completeness status of a Dovetail runtime report projected into the generic
/// runtime layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RuntimeDovetailCompleteness {
    Complete,
    BoundedByCycleCut,
}

impl fmt::Display for RuntimeDovetailCompleteness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeDovetailCompleteness::Complete => write!(f, "Complete"),
            RuntimeDovetailCompleteness::BoundedByCycleCut => write!(f, "BoundedByCycleCut"),
        }
    }
}

/// One exact-keyed derivation node from a Dovetail report, projected into the
/// runtime-neutral report envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailTermRecord {
    pub ordinal: usize,
    pub class_id: u32,
    pub key: ExactTermKey,
    pub op_display: String,
    pub weight_display: String,
    pub is_root: bool,
}

/// Parent-to-child derivation edge from a Dovetail report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailDerivationEdge {
    pub ordinal: usize,
    pub parent_key: ExactTermKey,
    pub child_key: ExactTermKey,
    pub child_index: usize,
}

/// Structural validation failure for a runtime-projected Dovetail report.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum RuntimeDovetailReportError {
    RootOrdinalCountMismatch {
        roots: usize,
        root_ordinals: usize,
    },
    RootOrdinalOutOfBounds {
        root_index: usize,
        ordinal: usize,
        terms: usize,
    },
    RootKeyMismatch {
        root_index: usize,
        ordinal: usize,
    },
    RootTermNotMarked {
        root_index: usize,
        ordinal: usize,
    },
    TermOrdinalMismatch {
        index: usize,
        ordinal: usize,
    },
    DuplicateTermKey {
        ordinal: usize,
    },
    EdgeOrdinalMismatch {
        index: usize,
        ordinal: usize,
    },
    EdgeParentMissing {
        edge_ordinal: usize,
    },
    EdgeChildMissing {
        edge_ordinal: usize,
    },
    RootFlagWithoutRootKey {
        ordinal: usize,
    },
}

impl fmt::Display for RuntimeDovetailReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeDovetailReportError::RootOrdinalCountMismatch { roots, root_ordinals } => {
                write!(
                    f,
                    "root count {roots} does not match root ordinal count {root_ordinals}"
                )
            },
            RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                root_index,
                ordinal,
                terms,
            } => write!(
                f,
                "root {root_index} points to term ordinal {ordinal}, but report has {terms} terms"
            ),
            RuntimeDovetailReportError::RootKeyMismatch { root_index, ordinal } => write!(
                f,
                "root {root_index} key does not match term ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::RootTermNotMarked { root_index, ordinal } => write!(
                f,
                "root {root_index} points to term ordinal {ordinal}, but that term is not marked as a root"
            ),
            RuntimeDovetailReportError::TermOrdinalMismatch { index, ordinal } => write!(
                f,
                "term at table index {index} records ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::DuplicateTermKey { ordinal } => {
                write!(f, "term ordinal {ordinal} duplicates an earlier exact key")
            },
            RuntimeDovetailReportError::EdgeOrdinalMismatch { index, ordinal } => write!(
                f,
                "derivation edge at table index {index} records ordinal {ordinal}"
            ),
            RuntimeDovetailReportError::EdgeParentMissing { edge_ordinal } => write!(
                f,
                "derivation edge ordinal {edge_ordinal} references a missing parent term key"
            ),
            RuntimeDovetailReportError::EdgeChildMissing { edge_ordinal } => write!(
                f,
                "derivation edge ordinal {edge_ordinal} references a missing child term key"
            ),
            RuntimeDovetailReportError::RootFlagWithoutRootKey { ordinal } => write!(
                f,
                "term ordinal {ordinal} is marked as a root but is absent from the report roots"
            ),
        }
    }
}

impl std::error::Error for RuntimeDovetailReportError {}

/// Runtime-neutral projection of `dovetail::report::DovetailRunReport`.
///
/// The generic runtime crate cannot depend on Dovetail without reversing the
/// intended dependency direction, so this type carries the report data in
/// runtime-owned terms: exact keys, deterministic ordinals, display strings,
/// ordered derivation edges, and explicit completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDovetailRunReport {
    pub roots: Vec<ExactTermKey>,
    pub root_ordinals: Vec<usize>,
    pub terms: Vec<RuntimeDovetailTermRecord>,
    pub derivation_edges: Vec<RuntimeDovetailDerivationEdge>,
    pub completeness: RuntimeDovetailCompleteness,
}

impl RuntimeDovetailRunReport {
    pub fn is_complete(&self) -> bool {
        self.completeness == RuntimeDovetailCompleteness::Complete
    }

    pub fn assert_complete(&self) -> Result<(), RuntimeDovetailCompleteness> {
        if self.is_complete() {
            Ok(())
        } else {
            Err(self.completeness)
        }
    }

    pub fn validate_shape(&self) -> Result<(), RuntimeDovetailReportError> {
        if self.roots.len() != self.root_ordinals.len() {
            return Err(RuntimeDovetailReportError::RootOrdinalCountMismatch {
                roots: self.roots.len(),
                root_ordinals: self.root_ordinals.len(),
            });
        }

        let mut term_keys = HashSet::with_capacity(self.terms.len());
        for (index, term) in self.terms.iter().enumerate() {
            if term.ordinal != index {
                return Err(RuntimeDovetailReportError::TermOrdinalMismatch {
                    index,
                    ordinal: term.ordinal,
                });
            }
            if !term_keys.insert(term.key.clone()) {
                return Err(RuntimeDovetailReportError::DuplicateTermKey { ordinal: term.ordinal });
            }
        }

        let mut root_keys = HashSet::with_capacity(self.roots.len());
        for (root_index, (root_key, ordinal)) in self
            .roots
            .iter()
            .zip(self.root_ordinals.iter().copied())
            .enumerate()
        {
            let term = self.terms.get(ordinal).ok_or(
                RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                    root_index,
                    ordinal,
                    terms: self.terms.len(),
                },
            )?;
            if term.key != *root_key {
                return Err(RuntimeDovetailReportError::RootKeyMismatch { root_index, ordinal });
            }
            if !term.is_root {
                return Err(RuntimeDovetailReportError::RootTermNotMarked { root_index, ordinal });
            }
            root_keys.insert(root_key.clone());
        }

        for term in &self.terms {
            if term.is_root && !root_keys.contains(&term.key) {
                return Err(RuntimeDovetailReportError::RootFlagWithoutRootKey {
                    ordinal: term.ordinal,
                });
            }
        }

        for (index, edge) in self.derivation_edges.iter().enumerate() {
            if edge.ordinal != index {
                return Err(RuntimeDovetailReportError::EdgeOrdinalMismatch {
                    index,
                    ordinal: edge.ordinal,
                });
            }
            if !term_keys.contains(&edge.parent_key) {
                return Err(RuntimeDovetailReportError::EdgeParentMissing {
                    edge_ordinal: edge.ordinal,
                });
            }
            if !term_keys.contains(&edge.child_key) {
                return Err(RuntimeDovetailReportError::EdgeChildMissing {
                    edge_ordinal: edge.ordinal,
                });
            }
        }

        Ok(())
    }

    pub fn term_by_key(&self, key: &[u8]) -> Option<&RuntimeDovetailTermRecord> {
        self.terms.iter().find(|term| term.key.as_slice() == key)
    }

    pub fn root_count(&self) -> usize {
        self.roots.len()
    }
}

/// Runtime-neutral output of an installed backend.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum RuntimeBackendOutput {
    /// Legacy/reference rewrite graph materialized as Ascent facts.
    Ascent(AscentResults),
    /// Checked Dovetail extraction report.
    Dovetail(RuntimeDovetailRunReport),
    /// Resting observations from a substrate such as RSpace.
    Observations(Vec<RuntimeChannelObservation>),
}

impl RuntimeBackendOutput {
    pub fn kind_name(&self) -> &'static str {
        match self {
            RuntimeBackendOutput::Ascent(_) => "AscentResults",
            RuntimeBackendOutput::Dovetail(_) => "DovetailRunReport",
            RuntimeBackendOutput::Observations(_) => "runtime observations",
        }
    }
}

/// Runtime-neutral report returned by a selected backend.
#[derive(Debug, Clone)]
pub struct RuntimeBackendReport {
    pub backend: RuntimeBackend,
    pub artifact: RuntimeBackendArtifact,
    pub output: RuntimeBackendOutput,
    pub evidence_refs: Vec<String>,
}

impl RuntimeBackendReport {
    pub fn ascent(results: AscentResults) -> Self {
        Self {
            backend: RuntimeBackend::Ascent,
            artifact: RuntimeBackendArtifact::AscentFixpoint,
            output: RuntimeBackendOutput::Ascent(results),
            evidence_refs: Vec::new(),
        }
    }

    pub fn observations(
        backend: RuntimeBackend,
        artifact: RuntimeBackendArtifact,
        observations: Vec<RuntimeChannelObservation>,
        evidence_refs: Vec<String>,
    ) -> Self {
        Self {
            backend,
            artifact,
            output: RuntimeBackendOutput::Observations(observations),
            evidence_refs,
        }
    }

    pub fn try_dovetail(
        report: RuntimeDovetailRunReport,
        evidence_refs: Vec<String>,
    ) -> Result<Self, RuntimeDovetailReportError> {
        report.validate_shape()?;
        Ok(Self {
            backend: RuntimeBackend::Dovetail,
            artifact: RuntimeBackendArtifact::DovetailRunReport,
            output: RuntimeBackendOutput::Dovetail(report),
            evidence_refs,
        })
    }

    pub fn dovetail(report: RuntimeDovetailRunReport, evidence_refs: Vec<String>) -> Self {
        Self::try_dovetail(report, evidence_refs)
            .expect("malformed Dovetail runtime report must not enter RuntimeBackendReport")
    }

    pub fn as_ascent_results(&self) -> Option<&AscentResults> {
        match &self.output {
            RuntimeBackendOutput::Ascent(results) => Some(results),
            RuntimeBackendOutput::Dovetail(_) => None,
            RuntimeBackendOutput::Observations(_) => None,
        }
    }

    pub fn into_ascent_results(self) -> Result<AscentResults, Self> {
        match self.output {
            RuntimeBackendOutput::Ascent(results) => Ok(results),
            RuntimeBackendOutput::Dovetail(_) => Err(self),
            RuntimeBackendOutput::Observations(_) => Err(self),
        }
    }

    pub fn observations_for_channel(&self, channel: &str) -> Option<&RuntimeChannelObservation> {
        match &self.output {
            RuntimeBackendOutput::Ascent(_) => None,
            RuntimeBackendOutput::Dovetail(_) => None,
            RuntimeBackendOutput::Observations(observations) => observations
                .iter()
                .find(|observation| observation.channel == channel),
        }
    }
}

/// Exact rewrite-graph seed.
///
/// `term_id` remains for compatibility and diagnostics. `exact_key`, when
/// present, is the no-loss reachability key used by normal-form traversal.
#[derive(Debug, Clone, PartialEq)]
pub struct RewriteSeed {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
}

impl RewriteSeed {
    pub fn legacy(term_id: u64, display: String) -> Self {
        Self { term_id, exact_key: None, display }
    }

    pub fn exact(term_id: u64, exact_key: ExactTermKey, display: String) -> Self {
        Self {
            term_id,
            exact_key: Some(exact_key),
            display,
        }
    }
}

/// Exact weighted rewrite-graph seed.
#[derive(Debug, Clone, PartialEq)]
pub struct WeightedRewriteSeed {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
    pub weight: f64,
}

impl WeightedRewriteSeed {
    pub fn legacy(term_id: u64, display: String, weight: f64) -> Self {
        Self {
            term_id,
            exact_key: None,
            display,
            weight,
        }
    }

    pub fn exact(term_id: u64, exact_key: ExactTermKey, display: String, weight: f64) -> Self {
        Self {
            term_id,
            exact_key: Some(exact_key),
            display,
            weight,
        }
    }
}

// =============================================================================
// Type Inference Types
// =============================================================================

/// Runtime representation of inferred types for REPL display
///
/// This mirrors the compile-time `InferredType` but is available at runtime
/// for displaying types to users.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermType {
    /// Base type: Name, Proc, etc.
    Base(String),
    /// Function type: [Domain -> Codomain]
    Arrow(Box<TermType>, Box<TermType>),
    /// Multi-argument function type: [Domain* -> Codomain]
    MultiArrow(Box<TermType>, Box<TermType>),
    /// Phase D.7 (2026-05-17, M14.4): union type capturing inference
    /// over an `Ambiguous(Vec<Inner>)` term. Each alternative's
    /// inferred type lives in the inner vec; downstream callers can
    /// inspect every typing or pick one.
    ///
    /// Constructor `union(types)` deduplicates and collapses
    /// trivial cases: empty → `Unknown`; single-elem → that element;
    /// otherwise the resulting `Ambiguous(Vec<TermType>)`.
    Ambiguous(Vec<TermType>),
    /// Unknown type (inference failed or not applicable)
    Unknown,
}

impl fmt::Display for TermType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermType::Base(name) => write!(f, "{}", name),
            TermType::Arrow(domain, codomain) => write!(f, "[{} -> {}]", domain, codomain),
            TermType::MultiArrow(domain, codomain) => write!(f, "[{}* -> {}]", domain, codomain),
            TermType::Ambiguous(types) => {
                // Render as a pipe-separated union: `Int | Bool | Float`.
                let parts: Vec<String> = types.iter().map(|t| format!("{}", t)).collect();
                write!(f, "{}", parts.join(" | "))
            },
            TermType::Unknown => write!(f, "?"),
        }
    }
}

impl TermType {
    /// Create a base type
    pub fn base(name: impl Into<String>) -> Self {
        TermType::Base(name.into())
    }

    /// Create a function type
    pub fn arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::Arrow(Box::new(domain), Box::new(codomain))
    }

    /// Create a multi-argument function type
    pub fn multi_arrow(domain: TermType, codomain: TermType) -> Self {
        TermType::MultiArrow(Box::new(domain), Box::new(codomain))
    }

    /// Phase D.7 (2026-05-17, M14.4): construct an `Ambiguous` union
    /// type with trivial-case folding. Pass in any number of
    /// alternatives; the constructor deduplicates them and collapses:
    ///   - empty input  → `Unknown`
    ///   - 1 unique     → the single element (no wrapper)
    ///   - 2+ unique    → `Ambiguous(Vec<TermType>)`
    pub fn union(types: Vec<TermType>) -> Self {
        // Flatten nested Ambiguous and deduplicate.
        let mut seen: Vec<TermType> = Vec::with_capacity(types.len());
        for ty in types {
            let to_add: Vec<TermType> = match ty {
                TermType::Ambiguous(inner) => inner,
                other => vec![other],
            };
            for t in to_add {
                if !seen.contains(&t) {
                    seen.push(t);
                }
            }
        }
        match seen.len() {
            0 => TermType::Unknown,
            1 => seen.into_iter().next().expect("checked len == 1"),
            _ => TermType::Ambiguous(seen),
        }
    }

    /// Check if this is a function type
    pub fn is_function(&self) -> bool {
        matches!(self, TermType::Arrow(..) | TermType::MultiArrow(..))
    }

    /// Get the domain type if this is a function type
    pub fn domain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(d, _) | TermType::MultiArrow(d, _) => Some(d),
            _ => None,
        }
    }

    /// Get the codomain type if this is a function type
    pub fn codomain(&self) -> Option<&TermType> {
        match self {
            TermType::Arrow(_, c) | TermType::MultiArrow(_, c) => Some(c),
            _ => None,
        }
    }
}

/// Information about a variable's type in a term
#[derive(Debug, Clone)]
pub struct VarTypeInfo {
    /// The variable name
    pub name: String,
    /// The inferred type
    pub ty: TermType,
}

impl fmt::Display for VarTypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {}", self.name, self.ty)
    }
}

/// A trait for terms (AST nodes) that can be manipulated generically
pub trait Term: fmt::Display + fmt::Debug + Send + Sync {
    /// Clone this term into a Box
    fn clone_box(&self) -> Box<dyn Term>;

    /// Get a unique identifier for this term (for equality comparison)
    fn term_id(&self) -> u64;

    /// Check if this term is equal to another
    fn term_eq(&self, other: &dyn Term) -> bool;

    /// Get this as Any for downcasting
    fn as_any(&self) -> &dyn Any;

    /// Phase F.12.A (2026-05-20): return the rewrite-graph seeds for each
    /// single-category derivation this term represents.
    ///
    /// For unambiguous terms this returns exactly one entry whose `term_id`
    /// equals `self.term_id()`. For `Ambiguous` wrappers, each inner alt
    /// contributes one entry whose exact key, when present, MUST match the
    /// corresponding `TermInfo.exact_key` in `run_ascent`.
    ///
    /// Default impl: returns a legacy `term_id` seed,
    /// which is correct for any language that has no `Ambiguous` variant.
    /// Generated `impl Term for <Lang>Term` blocks override this when the
    /// language has cross-category projection.
    fn rewrite_seeds(&self) -> Vec<RewriteSeed> {
        vec![RewriteSeed::legacy(self.term_id(), format!("{}", self))]
    }

    /// Compatibility surface for callers that still carry only a 64-bit graph
    /// id. New code should prefer `rewrite_seeds` so the exact key survives
    /// into reachability traversal.
    fn rewrite_seed_ids(&self) -> Vec<(u64, String)> {
        self.rewrite_seeds()
            .into_iter()
            .map(|seed| (seed.term_id, seed.display))
            .collect()
    }

    /// Weighted variant of `rewrite_seeds`.
    fn rewrite_weighted_seeds(&self) -> Vec<WeightedRewriteSeed> {
        self.rewrite_seeds()
            .into_iter()
            .map(|seed| WeightedRewriteSeed {
                term_id: seed.term_id,
                exact_key: seed.exact_key,
                display: seed.display,
                weight: 0.0,
            })
            .collect()
    }

    /// Weighted variant of `rewrite_seed_ids`.
    ///
    /// Terms do not generally store parse/evidence weights, so the default
    /// exposes neutral weight. Parser surfaces that still have access to
    /// derivation weights should return their own weighted seed list.
    fn rewrite_weighted_seed_ids(&self) -> Vec<WeightedSeedId> {
        self.rewrite_weighted_seeds()
            .into_iter()
            .map(|seed| (seed.term_id, seed.display, seed.weight))
            .collect()
    }
}

/// A trait that all languages must implement
///
/// This trait is auto-generated by the `language!` macro.
pub trait Language: Send + Sync {
    /// Get the name of this language (e.g., "RhoCalc")
    fn name(&self) -> &'static str;

    /// Get static metadata for this language (types, terms, equations, rewrites)
    fn metadata(&self) -> &'static dyn LanguageMetadata;

    /// Parse a term from a string (clears var cache for fresh evaluation)
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Parse a term for environment storage (does NOT clear var cache)
    fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String>;

    /// Parse a term and return weighted rewrite seeds for lazy evaluation.
    ///
    /// The default falls back to neutral weights for languages whose generated
    /// parser does not expose derivation weights. Multi-category generated
    /// languages override this to preserve WPDA parse/evidence weights.
    fn parse_term_with_weighted_seed_ids(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedSeedId>), String> {
        let (term, seeds) = self.parse_term_with_weighted_rewrite_seeds(input)?;
        Ok((
            term,
            seeds
                .into_iter()
                .map(|seed| (seed.term_id, seed.display, seed.weight))
                .collect(),
        ))
    }

    /// Parse a term and return exact weighted rewrite seeds for lazy
    /// evaluation. Generated languages override this to preserve parse/evidence
    /// weights and exact semantic keys. Legacy implementations inherit exact
    /// absence and neutral weights from `Term::rewrite_weighted_seeds`.
    fn parse_term_with_weighted_rewrite_seeds(
        &self,
        input: &str,
    ) -> Result<(Box<dyn Term>, Vec<WeightedRewriteSeed>), String> {
        let term = self.parse_term(input)?;
        let seeds = term.rewrite_weighted_seeds();
        Ok((term, seeds))
    }

    /// Run Ascent on a term and return results
    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String>;

    /// Backend used by user-facing evaluation when no backend is requested
    /// explicitly.
    ///
    /// The runtime capability view must advertise only executable backends.
    /// When multiple entries are marked default, the first declaration wins,
    /// preserving the language author's generated order unless a wrapper
    /// deliberately installs a new default.
    fn default_runtime_backend(&self) -> RuntimeBackend {
        self.runtime_backend_capabilities()
            .iter()
            .find(|capability| capability.is_default)
            .map(|capability| capability.backend)
            .unwrap_or(RuntimeBackend::Ascent)
    }

    /// Runtime backends executable for this concrete language value.
    ///
    /// The default derives from static generated metadata. Runtime wrappers may
    /// override this to expose plan-specific evidence, for example a
    /// flip-gated Rho backend installed around an otherwise substrate-neutral
    /// generated language.
    fn runtime_backend_capabilities(&self) -> Vec<RuntimeBackendCapability> {
        self.metadata()
            .runtime_backends()
            .iter()
            .map(RuntimeBackendCapability::from_static)
            .collect()
    }

    /// Whether this language currently exposes the selected backend through the
    /// generic runtime trait.
    fn supports_runtime_backend(&self, backend: RuntimeBackend) -> bool {
        self.runtime_backend_capabilities()
            .iter()
            .any(|capability| capability.backend == backend)
    }

    /// Run the selected backend and return a runtime-neutral report.
    ///
    /// This is the production backend surface for Dovetail/Rho integration.
    /// `run_with_backend` remains as an Ascent-shaped compatibility wrapper and
    /// rejects non-Ascent report shapes instead of pretending that Rho
    /// observations are Ascent facts.
    fn run_backend_report(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Ascent => self.run_ascent(term).map(RuntimeBackendReport::ascent),
            other => {
                Err(format!("{} backend is not installed for language {}", other, self.name()))
            },
        }
    }

    /// Run the language's selected default backend and return a runtime-neutral
    /// report.
    fn run_default_backend_report(&self, term: &dyn Term) -> Result<RuntimeBackendReport, String> {
        self.run_backend_report(self.default_runtime_backend(), term)
    }

    /// Run the selected backend on a term and return results.
    ///
    /// `Ascent` remains available as an explicit reference/oracle backend. Other
    /// backends must be wired by a language only after their proof and runtime
    /// gates pass. This compatibility method is intentionally Ascent-shaped;
    /// callers that may select Dovetail/Rho should use
    /// [`Language::run_backend_report`] instead.
    fn run_with_backend(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
    ) -> Result<AscentResults, String> {
        let report = self.run_backend_report(backend, term)?;
        let output_kind = report.output.kind_name();
        report.into_ascent_results().map_err(|report| {
            format!(
                "{} backend for language {} returned {}; use run_backend_report for this backend",
                report.backend,
                self.name(),
                output_kind
            )
        })
    }

    /// Run the language's selected default backend.
    fn run_default_backend(&self, term: &dyn Term) -> Result<AscentResults, String> {
        self.run_with_backend(self.default_runtime_backend(), term)
    }

    /// Run Ascent on a term with pre-seeded relation facts.
    ///
    /// The `facts` map keys are relation names (e.g., `"certified"`)
    /// and values are tuples as string vectors (e.g.,
    /// `vec![vec!["item_A"]]`). Before fixpoint evaluation, the
    /// codegen:
    /// 1. Parses each tuple's strings into the relation's parameter
    ///    types and pushes them into the Ascent program struct
    /// 2. Populates the thread-local fact snapshot so the Comm rule's
    ///    `if { evaluate_pred_with_bindings(...) }` guard can check
    ///    per-instance predicates
    ///
    /// Default: delegates to `run_ascent` (ignores facts).
    fn run_ascent_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let _ = facts;
        self.run_ascent(term)
    }

    /// Run the selected backend with pre-seeded relation facts and return a
    /// runtime-neutral report.
    fn run_backend_report_with_facts(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        match backend {
            RuntimeBackend::Ascent => self
                .run_ascent_with_facts(term, facts)
                .map(RuntimeBackendReport::ascent),
            other => Err(format!(
                "{} backend with seeded facts is not installed for language {}",
                other,
                self.name()
            )),
        }
    }

    /// Run the selected backend with pre-seeded relation facts.
    ///
    /// Relation facts are currently an Ascent-shaped compatibility surface; a
    /// future Dovetail/Rho implementation must override this method rather than
    /// inheriting an accidental fallback.
    fn run_with_backend_with_facts(
        &self,
        backend: RuntimeBackend,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        let report = self.run_backend_report_with_facts(backend, term, facts)?;
        let output_kind = report.output.kind_name();
        report.into_ascent_results().map_err(|report| {
            format!(
                "{} backend with seeded facts for language {} returned {}; use run_backend_report_with_facts for this backend",
                report.backend,
                self.name(),
                output_kind
            )
        })
    }

    /// Run the language's selected default backend with pre-seeded relation
    /// facts.
    fn run_default_backend_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<AscentResults, String> {
        self.run_with_backend_with_facts(self.default_runtime_backend(), term, facts)
    }

    /// Run the language's selected default backend with pre-seeded relation
    /// facts and return a runtime-neutral report.
    fn run_default_backend_report_with_facts(
        &self,
        term: &dyn Term,
        facts: &SeedFacts,
    ) -> Result<RuntimeBackendReport, String> {
        self.run_backend_report_with_facts(self.default_runtime_backend(), term, facts)
    }

    /// If the term is fully evaluable (no free variables), evaluate it and return the result term.
    /// Otherwise return `None` (e.g. term contains vars, or language has no native eval).
    /// Default: `None` so languages without native types need not implement.
    fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
        let _ = term;
        None
    }

    /// Normalize a term (beta-reduce Apply/MApply of Lam/MLam, flatten collections, etc.)
    /// Default: returns a clone (no normalization).
    fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
        term.clone_box()
    }

    /// Format a term as a string
    fn format_term(&self, term: &dyn Term) -> String {
        format!("{}", term)
    }

    // === Environment Support ===

    /// Create a new empty environment for this language
    fn create_env(&self) -> Box<dyn Any + Send + Sync>;

    /// Add a term to the environment under the given name
    fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String>;

    /// Remove a binding from the environment
    fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String>;

    /// Clear all bindings from the environment
    fn clear_env(&self, env: &mut dyn Any);

    /// Apply environment substitution to a term (includes normalization/constant folding).
    fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String>;

    /// Substitute environment variables without normalizing (no constant folding).
    /// Use for step mode so the term tree is preserved and rewrites can be applied one by one.
    fn substitute_env_preserve_structure(
        &self,
        term: &dyn Term,
        env: &dyn Any,
    ) -> Result<Box<dyn Term>, String> {
        self.substitute_env(term, env)
    }

    /// List all environment bindings as (name, display, optional_comment) tuples
    ///
    /// Returns bindings in insertion order, with any associated comments.
    fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)>;

    /// Set a comment for a binding in the environment
    fn set_env_comment(&self, env: &mut dyn Any, name: &str, comment: String)
        -> Result<(), String>;

    /// Check if the environment is empty
    fn is_env_empty(&self, env: &dyn Any) -> bool;

    /// Get a term by name from the environment (any category).
    /// Used so that `exec z` uses the stored term for "z" instead of parsing "z" as a variable,
    /// which can leave e.g. IVar(z) unsubstituted when "z" is bound in another category (e.g. Proc).
    fn get_env_term(&self, env: &dyn Any, name: &str) -> Option<Box<dyn Term>> {
        let _ = (env, name);
        None
    }

    // === Type Inference Support ===

    /// Infer the type of a term
    ///
    /// For lambda expressions, returns the full function type (e.g., `[Name -> Proc]`).
    /// For other terms, returns their category (e.g., `Proc`, `Name`).
    fn infer_term_type(&self, term: &dyn Term) -> TermType;

    /// Get all free variables and their inferred types in a term
    ///
    /// Returns a list of variable names with their types, inferred from
    /// how they are used in the term.
    fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo>;

    /// Infer the type of a specific variable from its usage in a term
    ///
    /// Returns `None` if the variable is not found or its type cannot be inferred.
    fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType>;

    /// Decompose a parsed term into CEK evaluation frames.
    ///
    /// Pattern-matches on the language's AST variants and pushes appropriate
    /// `EvalFrame`s onto the evaluator's continuation stack. After this call,
    /// the evaluator is ready to be driven via `step()` or `run_to_completion()`.
    ///
    /// Returns `true` if the term was decomposed (frames were pushed),
    /// `false` if the language has no CEK decomposition (default).
    ///
    /// The same evaluator + observer pattern supports all consumers:
    /// - REPL `exec`: `NullEvalObserver` + `run_to_completion()`
    /// - nREPL: same, with `reset_with_term()` for env persistence
    /// - CLI debugger: custom observer + `step()` loop
    /// - DAP server: protocol observer + `step()` loop
    fn decompose_into_cek(
        &self,
        term: &dyn Term,
        evaluator: &mut mettail_prattail::cek_eval::CekEvaluator,
    ) -> bool {
        let _ = (term, evaluator);
        false
    }
}

/// Results from running Ascent
#[derive(Debug, Clone)]
pub struct AscentResults {
    /// All reachable terms
    pub all_terms: Vec<TermInfo>,

    /// All rewrites (from -> to)
    pub rewrites: Vec<Rewrite>,

    /// Equivalence classes (terms related by equations)
    pub equivalences: Vec<EquivClass>,

    /// Custom relations: name -> relation data
    pub custom_relations: std::collections::HashMap<String, RelationData>,
}

/// Data for a custom relation
#[derive(Debug, Clone)]
pub struct RelationData {
    /// Parameter type names (e.g., ["Proc", "Proc"])
    pub param_types: Vec<String>,
    /// Tuples as formatted strings (each tuple is a Vec of formatted elements)
    pub tuples: Vec<Vec<String>>,
}

/// Information about a term in the rewrite graph
#[derive(Debug, Clone)]
pub struct TermInfo {
    pub term_id: u64,
    pub exact_key: Option<ExactTermKey>,
    pub display: String,
    pub is_normal_form: bool,
}

/// A rewrite from one term to another
#[derive(Debug, Clone)]
pub struct Rewrite {
    pub from_id: u64,
    pub to_id: u64,
    pub from_key: Option<ExactTermKey>,
    pub to_key: Option<ExactTermKey>,
    pub rule_name: Option<String>,
}

/// An equivalence class of terms
#[derive(Debug, Clone)]
pub struct EquivClass {
    pub term_ids: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ReachKey {
    Exact(ExactTermKey),
    Legacy(u64),
}

impl TermInfo {
    fn reach_key(&self) -> ReachKey {
        self.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.term_id))
    }
}

impl Rewrite {
    fn from_reach_key(&self) -> ReachKey {
        self.from_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.from_id))
    }

    fn to_reach_key(&self) -> ReachKey {
        self.to_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or(ReachKey::Legacy(self.to_id))
    }
}

/// Lazy breadth-first iterator over normal forms reachable from one or more
/// rewrite-graph seeds.
///
/// The iterator preserves seed order and yields every reachable normal form by
/// graph identity. It does not rank by display text or any other presentation
/// heuristic. The rewrite adjacency index is built only when expansion is
/// needed, so an already-normal seed can be observed without scanning the whole
/// rewrite relation.
pub struct ReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: VecDeque<ReachKey>,
    visited: HashSet<ReachKey>,
    term_index: Option<HashMap<ReachKey, usize>>,
    rewrites_by_from: Option<HashMap<ReachKey, Vec<ReachKey>>>,
}

impl<'a> ReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, seed_ids: &[u64]) -> Self {
        let seeds: Vec<RewriteSeed> = seed_ids
            .iter()
            .flat_map(|&id| results.rewrite_seeds_for_legacy_id(id))
            .collect();
        Self::new_exact(results, &seeds)
    }

    fn new_exact(results: &'a AscentResults, seeds: &[RewriteSeed]) -> Self {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        for seed in seeds {
            let key = results.seed_reach_key(seed);
            if visited.insert(key.clone()) {
                queue.push_back(key);
            }
        }
        Self {
            results,
            queue,
            visited,
            term_index: None,
            rewrites_by_from: None,
        }
    }

    fn term_info(&self, key: &ReachKey) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(key).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.term_info_by_reach_key(key)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.reach_key(), idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<ReachKey, Vec<ReachKey>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_reach_key())
                    .or_default()
                    .push(rewrite.to_reach_key());
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for ReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(key) = self.queue.pop_front() {
            let info = match self.term_info(&key) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&key))
                .cloned()
                .unwrap_or_default();
            for to_key in next_ids {
                if self.visited.insert(to_key.clone()) {
                    self.queue.push_back(to_key);
                }
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy)]
struct WeightedQueueEntry {
    key_index: usize,
    weight: f64,
    sequence: usize,
}

impl PartialEq for WeightedQueueEntry {
    fn eq(&self, other: &Self) -> bool {
        self.key_index == other.key_index
            && self.weight.total_cmp(&other.weight) == Ordering::Equal
            && self.sequence == other.sequence
    }
}

impl Eq for WeightedQueueEntry {}

impl PartialOrd for WeightedQueueEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for WeightedQueueEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        // BinaryHeap pops the greatest element, so reverse the natural order:
        // lower weight first, then lower insertion sequence.
        other
            .weight
            .total_cmp(&self.weight)
            .then_with(|| other.sequence.cmp(&self.sequence))
            .then_with(|| other.key_index.cmp(&self.key_index))
    }
}

/// Lazy priority traversal over normal forms reachable from weighted seeds.
///
/// The queue orders work by the caller-provided seed weight, with seed order as
/// the deterministic tie breaker. Expansion indexes are still built only when a
/// non-normal term is popped, so an already-normal best seed can satisfy a
/// bounded prefix request without scanning the rewrite relation.
pub struct WeightedReachableNormalForms<'a> {
    results: &'a AscentResults,
    queue: BinaryHeap<WeightedQueueEntry>,
    keys: Vec<ReachKey>,
    key_index: HashMap<ReachKey, usize>,
    visited: HashSet<ReachKey>,
    term_index: Option<HashMap<ReachKey, usize>>,
    rewrites_by_from: Option<HashMap<ReachKey, Vec<ReachKey>>>,
    next_sequence: usize,
}

impl<'a> WeightedReachableNormalForms<'a> {
    fn new(results: &'a AscentResults, weighted_seed_ids: &[(u64, f64)]) -> Self {
        let seeds: Vec<WeightedRewriteSeed> = weighted_seed_ids
            .iter()
            .flat_map(|&(id, weight)| {
                results
                    .rewrite_seeds_for_legacy_id(id)
                    .into_iter()
                    .map(move |seed| WeightedRewriteSeed {
                        term_id: seed.term_id,
                        exact_key: seed.exact_key,
                        display: seed.display,
                        weight,
                    })
            })
            .collect();
        Self::new_exact(results, &seeds)
    }

    fn new_exact(results: &'a AscentResults, weighted_seeds: &[WeightedRewriteSeed]) -> Self {
        let mut best_by_key: HashMap<ReachKey, (f64, usize)> = HashMap::new();
        for (sequence, seed) in weighted_seeds.iter().enumerate() {
            let weight = seed.weight;
            let weight = if weight.is_nan() {
                f64::INFINITY
            } else {
                weight
            };
            best_by_key
                .entry(results.weighted_seed_reach_key(seed))
                .and_modify(|best| {
                    if weight.total_cmp(&best.0) == Ordering::Less
                        || (weight.total_cmp(&best.0) == Ordering::Equal && sequence < best.1)
                    {
                        *best = (weight, sequence);
                    }
                })
                .or_insert((weight, sequence));
        }

        let mut queue = BinaryHeap::new();
        let mut keys = Vec::with_capacity(best_by_key.len());
        let mut key_index = HashMap::with_capacity(best_by_key.len());
        let mut visited = HashSet::new();
        let mut next_sequence = weighted_seeds.len();
        for (key, (weight, sequence)) in best_by_key {
            let idx = keys.len();
            key_index.insert(key.clone(), idx);
            keys.push(key.clone());
            visited.insert(key);
            next_sequence = next_sequence.max(sequence.saturating_add(1));
            queue.push(WeightedQueueEntry { key_index: idx, weight, sequence });
        }

        Self {
            results,
            queue,
            keys,
            key_index,
            visited,
            term_index: None,
            rewrites_by_from: None,
            next_sequence,
        }
    }

    fn key_index_for(&mut self, key: ReachKey) -> usize {
        if let Some(&idx) = self.key_index.get(&key) {
            return idx;
        }
        let idx = self.keys.len();
        self.keys.push(key.clone());
        self.key_index.insert(key, idx);
        idx
    }

    fn term_info(&self, key: &ReachKey) -> Option<&'a TermInfo> {
        if let Some(index) = &self.term_index {
            return index.get(key).map(|&idx| &self.results.all_terms[idx]);
        }
        self.results.term_info_by_reach_key(key)
    }

    fn ensure_expansion_indexes(&mut self) {
        if self.term_index.is_none() {
            self.term_index = Some(
                self.results
                    .all_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, term)| (term.reach_key(), idx))
                    .collect(),
            );
        }
        if self.rewrites_by_from.is_none() {
            let mut rewrites_by_from: HashMap<ReachKey, Vec<ReachKey>> = HashMap::new();
            for rewrite in &self.results.rewrites {
                rewrites_by_from
                    .entry(rewrite.from_reach_key())
                    .or_default()
                    .push(rewrite.to_reach_key());
            }
            self.rewrites_by_from = Some(rewrites_by_from);
        }
    }
}

impl<'a> Iterator for WeightedReachableNormalForms<'a> {
    type Item = &'a TermInfo;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.queue.pop() {
            let key = match self.keys.get(entry.key_index) {
                Some(key) => key.clone(),
                None => continue,
            };
            let info = match self.term_info(&key) {
                Some(info) => info,
                None => continue,
            };
            if info.is_normal_form {
                return Some(info);
            }

            self.ensure_expansion_indexes();
            let next_ids = self
                .rewrites_by_from
                .as_ref()
                .and_then(|index| index.get(&key))
                .cloned()
                .unwrap_or_default();
            for to_key in next_ids {
                if self.visited.insert(to_key.clone()) {
                    let sequence = self.next_sequence;
                    self.next_sequence = self.next_sequence.saturating_add(1);
                    let key_index = self.key_index_for(to_key);
                    self.queue.push(WeightedQueueEntry {
                        key_index,
                        weight: entry.weight,
                        sequence,
                    });
                }
            }
        }
        None
    }
}

impl AscentResults {
    /// Create empty results
    pub fn empty() -> Self {
        Self {
            all_terms: Vec::new(),
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    /// Create minimal results for a single term (e.g. after direct eval). One term, no rewrites.
    pub fn from_single_term(term: &dyn Term) -> Self {
        Self {
            all_terms: vec![TermInfo {
                term_id: term.term_id(),
                exact_key: None,
                display: format!("{}", term),
                is_normal_form: true,
            }],
            rewrites: Vec::new(),
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    fn term_info_by_reach_key(&self, key: &ReachKey) -> Option<&TermInfo> {
        match key {
            ReachKey::Exact(exact) => self
                .all_terms
                .iter()
                .find(|term| term.exact_key.as_ref() == Some(exact)),
            ReachKey::Legacy(id) => self.all_terms.iter().find(|term| term.term_id == *id),
        }
    }

    fn seed_reach_key(&self, seed: &RewriteSeed) -> ReachKey {
        seed.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or_else(|| ReachKey::Legacy(seed.term_id))
    }

    fn weighted_seed_reach_key(&self, seed: &WeightedRewriteSeed) -> ReachKey {
        seed.exact_key
            .clone()
            .map(ReachKey::Exact)
            .unwrap_or_else(|| ReachKey::Legacy(seed.term_id))
    }

    fn rewrite_seeds_for_legacy_id(&self, id: u64) -> Vec<RewriteSeed> {
        let mut seeds = Vec::new();
        let mut seen = HashSet::new();
        for term in self.all_terms.iter().filter(|term| term.term_id == id) {
            let seed = RewriteSeed {
                term_id: term.term_id,
                exact_key: term.exact_key.clone(),
                display: term.display.clone(),
            };
            let key = self.seed_reach_key(&seed);
            if seen.insert(key) {
                seeds.push(seed);
            }
        }
        if seeds.is_empty() {
            seeds.push(RewriteSeed::legacy(id, String::new()));
        }
        seeds
    }

    /// Lazily iterate normal forms (terms with no outgoing rewrites).
    pub fn normal_forms_iter(&self) -> impl Iterator<Item = &TermInfo> {
        self.all_terms.iter().filter(|t| t.is_normal_form)
    }

    /// Get normal forms (terms with no outgoing rewrites).
    pub fn normal_forms(&self) -> Vec<&TermInfo> {
        self.normal_forms_iter().collect()
    }

    /// Lazily iterate rewrites from a specific term.
    pub fn rewrites_from_iter(&self, term_id: u64) -> impl Iterator<Item = &Rewrite> {
        self.rewrites.iter().filter(move |r| r.from_id == term_id)
    }

    /// Get rewrites from a specific term
    pub fn rewrites_from(&self, term_id: u64) -> Vec<&Rewrite> {
        self.rewrites_from_iter(term_id).collect()
    }

    /// Find a normal form reachable from the given term by following rewrites.
    /// Returns the first normal form reached (BFS). If the start term is already
    /// a normal form, returns it. Returns `None` if the term is not in the graph.
    pub fn normal_form_reachable_from(&self, start_id: u64) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(&[start_id])
            .next()
    }

    /// Multi-source normal-form traversal.
    ///
    /// Yields every normal form reachable from the given seeds, preserving
    /// seed/BFS order. This is the ambiguity-preserving surface for consumers
    /// that receive an `Ambiguous` wrapper from parsing and need to carry all
    /// alternatives into evaluation.
    ///
    /// The rewrite adjacency index is initialized only if a non-normal seed
    /// must be expanded; asking for the first result from an already-normal
    /// seed does not scan the rewrite relation.
    pub fn normal_forms_reachable_from_seeds_iter<'a>(
        &'a self,
        seed_ids: &[u64],
    ) -> ReachableNormalForms<'a> {
        ReachableNormalForms::new(self, seed_ids)
    }

    /// Exact multi-source normal-form traversal.
    ///
    /// Prefer this over `normal_forms_reachable_from_seeds_iter` when the
    /// caller has parser/generated exact semantic keys. This is the
    /// no-loss surface: traversal identity is the exact key, falling back to
    /// `term_id` only for legacy seeds.
    pub fn normal_forms_reachable_from_rewrite_seeds_iter<'a>(
        &'a self,
        seeds: &[RewriteSeed],
    ) -> ReachableNormalForms<'a> {
        ReachableNormalForms::new_exact(self, seeds)
    }

    /// Collect all normal forms reachable from the given seeds.
    pub fn normal_forms_reachable_from_seeds(&self, seed_ids: &[u64]) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids)
            .collect()
    }

    /// Collect all normal forms reachable from exact rewrite seeds.
    pub fn normal_forms_reachable_from_rewrite_seeds(
        &self,
        seeds: &[RewriteSeed],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_rewrite_seeds_iter(seeds)
            .collect()
    }

    /// Compatibility helper for callers that explicitly want one witness.
    ///
    /// This returns the first result from the lazy multi-source traversal. It
    /// deliberately does not choose by display length or any other heuristic.
    pub fn normal_form_reachable_from_seeds(&self, seed_ids: &[u64]) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_seeds_iter(seed_ids).next()
    }

    /// Compatibility helper for callers that explicitly want one exact-seeded
    /// witness.
    pub fn normal_form_reachable_from_rewrite_seeds(
        &self,
        seeds: &[RewriteSeed],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_rewrite_seeds_iter(seeds)
            .next()
    }

    /// Multi-source normal-form traversal ordered by seed weight.
    ///
    /// This is the explicit priority-queue surface for callers that carry
    /// parser/evidence weights through to evaluation. It is demand bounded:
    /// callers can use `.take(n)` or `.next()` without collecting all reachable
    /// normal forms.
    pub fn normal_forms_reachable_from_weighted_seeds_iter<'a>(
        &'a self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> WeightedReachableNormalForms<'a> {
        WeightedReachableNormalForms::new(self, weighted_seed_ids)
    }

    /// Exact weighted normal-form traversal.
    pub fn normal_forms_reachable_from_weighted_rewrite_seeds_iter<'a>(
        &'a self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> WeightedReachableNormalForms<'a> {
        WeightedReachableNormalForms::new_exact(self, weighted_seeds)
    }

    /// Collect all normal forms reachable from weighted seeds.
    pub fn normal_forms_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .collect()
    }

    /// Collect all normal forms reachable from exact weighted seeds.
    pub fn normal_forms_reachable_from_weighted_rewrite_seeds(
        &self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> Vec<&TermInfo> {
        self.normal_forms_reachable_from_weighted_rewrite_seeds_iter(weighted_seeds)
            .collect()
    }

    /// Return the first normal form from the lazy weighted traversal.
    pub fn normal_form_reachable_from_weighted_seeds(
        &self,
        weighted_seed_ids: &[(u64, f64)],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_weighted_seeds_iter(weighted_seed_ids)
            .next()
    }

    /// Return the first normal form from the exact lazy weighted traversal.
    pub fn normal_form_reachable_from_weighted_rewrite_seeds(
        &self,
        weighted_seeds: &[WeightedRewriteSeed],
    ) -> Option<&TermInfo> {
        self.normal_forms_reachable_from_weighted_rewrite_seeds_iter(weighted_seeds)
            .next()
    }

    /// Get the equivalence class containing a term
    pub fn equiv_class(&self, term_id: u64) -> Option<&EquivClass> {
        self.equivalences
            .iter()
            .find(|ec| ec.term_ids.contains(&term_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BackendCapabilityDef;

    #[derive(Debug, Clone)]
    struct DispatchTerm;

    impl fmt::Display for DispatchTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "dispatch")
        }
    }

    impl Term for DispatchTerm {
        fn clone_box(&self) -> Box<dyn Term> {
            Box::new(self.clone())
        }

        fn term_id(&self) -> u64 {
            1
        }

        fn term_eq(&self, other: &dyn Term) -> bool {
            other.as_any().is::<DispatchTerm>()
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    struct DispatchMetadata;

    static DISPATCH_BACKENDS: &[BackendCapabilityDef] = &[BackendCapabilityDef {
        backend: RuntimeBackend::Ascent,
        is_default: true,
        evidence_refs: &["runtime-test:dispatch-ascent"],
    }];

    impl LanguageMetadata for DispatchMetadata {
        fn name(&self) -> &'static str {
            "Dispatch"
        }

        fn types(&self) -> &'static [crate::metadata::TypeDef] {
            &[]
        }

        fn terms(&self) -> &'static [crate::metadata::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [crate::metadata::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [crate::metadata::RewriteDef] {
            &[]
        }

        fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
            DISPATCH_BACKENDS
        }
    }

    static DISPATCH_METADATA: DispatchMetadata = DispatchMetadata;

    struct DispatchLanguage;

    impl Language for DispatchLanguage {
        fn name(&self) -> &'static str {
            "Dispatch"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &DISPATCH_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DispatchTerm))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Ok(AscentResults::empty())
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::Unknown
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    struct RhoDispatchMetadata;

    static RHO_DISPATCH_BACKENDS: &[BackendCapabilityDef] = &[
        BackendCapabilityDef {
            backend: RuntimeBackend::RhoMachine,
            is_default: true,
            evidence_refs: &[
                "formal/rocq/rho_bridge/theories/RhoBackendFlipGate.v",
                "runtime-test:rho-dispatch",
            ],
        },
        BackendCapabilityDef {
            backend: RuntimeBackend::Ascent,
            is_default: false,
            evidence_refs: &["runtime-test:ascent-oracle"],
        },
    ];

    impl LanguageMetadata for RhoDispatchMetadata {
        fn name(&self) -> &'static str {
            "RhoDispatch"
        }

        fn types(&self) -> &'static [crate::metadata::TypeDef] {
            &[]
        }

        fn terms(&self) -> &'static [crate::metadata::TermDef] {
            &[]
        }

        fn equations(&self) -> &'static [crate::metadata::EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [crate::metadata::RewriteDef] {
            &[]
        }

        fn runtime_backends(&self) -> &'static [BackendCapabilityDef] {
            RHO_DISPATCH_BACKENDS
        }
    }

    static RHO_DISPATCH_METADATA: RhoDispatchMetadata = RhoDispatchMetadata;

    struct RhoDispatchLanguage;

    impl Language for RhoDispatchLanguage {
        fn name(&self) -> &'static str {
            "RhoDispatch"
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &RHO_DISPATCH_METADATA
        }

        fn parse_term(&self, _input: &str) -> Result<Box<dyn Term>, String> {
            Ok(Box::new(DispatchTerm))
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            self.parse_term(input)
        }

        fn run_ascent(&self, _term: &dyn Term) -> Result<AscentResults, String> {
            Ok(AscentResults::empty())
        }

        fn run_backend_report(
            &self,
            backend: RuntimeBackend,
            term: &dyn Term,
        ) -> Result<RuntimeBackendReport, String> {
            match backend {
                RuntimeBackend::Ascent => self.run_ascent(term).map(RuntimeBackendReport::ascent),
                RuntimeBackend::RhoMachine => Ok(RuntimeBackendReport::observations(
                    RuntimeBackend::RhoMachine,
                    RuntimeBackendArtifact::RhoNormalizedAst,
                    vec![RuntimeChannelObservation::new(
                        "OUT",
                        vec![RuntimeObservationValue::Text("rho-default".to_string())],
                    )],
                    vec!["runtime-test:rho-dispatch".to_string()],
                )),
                other => {
                    Err(format!("{} backend is not installed for language {}", other, self.name()))
                },
            }
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            Box::new(())
        }

        fn add_to_env(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _term: &dyn Term,
        ) -> Result<(), String> {
            Ok(())
        }

        fn remove_from_env(&self, _env: &mut dyn Any, _name: &str) -> Result<bool, String> {
            Ok(false)
        }

        fn clear_env(&self, _env: &mut dyn Any) {}

        fn substitute_env(&self, term: &dyn Term, _env: &dyn Any) -> Result<Box<dyn Term>, String> {
            Ok(term.clone_box())
        }

        fn list_env(&self, _env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            Vec::new()
        }

        fn set_env_comment(
            &self,
            _env: &mut dyn Any,
            _name: &str,
            _comment: String,
        ) -> Result<(), String> {
            Ok(())
        }

        fn is_env_empty(&self, _env: &dyn Any) -> bool {
            true
        }

        fn infer_term_type(&self, _term: &dyn Term) -> TermType {
            TermType::Unknown
        }

        fn infer_var_types(&self, _term: &dyn Term) -> Vec<VarTypeInfo> {
            Vec::new()
        }

        fn infer_var_type(&self, _term: &dyn Term, _var_name: &str) -> Option<TermType> {
            None
        }
    }

    fn sample_results() -> AscentResults {
        AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "start".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "mid".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 3,
                    exact_key: None,
                    display: "done".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 2,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("step1".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 3,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("step2".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        }
    }

    fn sample_dovetail_runtime_report() -> RuntimeDovetailRunReport {
        RuntimeDovetailRunReport {
            roots: vec![b"root".to_vec()],
            root_ordinals: vec![0],
            terms: vec![
                RuntimeDovetailTermRecord {
                    ordinal: 0,
                    class_id: 0,
                    key: b"root".to_vec(),
                    op_display: "Pair".to_string(),
                    weight_display: "1".to_string(),
                    is_root: true,
                },
                RuntimeDovetailTermRecord {
                    ordinal: 1,
                    class_id: 1,
                    key: b"child".to_vec(),
                    op_display: "Leaf".to_string(),
                    weight_display: "0".to_string(),
                    is_root: false,
                },
            ],
            derivation_edges: vec![RuntimeDovetailDerivationEdge {
                ordinal: 0,
                parent_key: b"root".to_vec(),
                child_key: b"child".to_vec(),
                child_index: 0,
            }],
            completeness: RuntimeDovetailCompleteness::Complete,
        }
    }

    #[test]
    fn dovetail_report_shape_validation_accepts_consistent_report() {
        let report = sample_dovetail_runtime_report();

        report
            .validate_shape()
            .expect("sample report is structurally valid");
        let backend_report = RuntimeBackendReport::try_dovetail(
            report,
            vec!["runtime-test:dovetail-shape".to_string()],
        )
        .expect("checked constructor accepts structurally valid Dovetail reports");

        assert_eq!(backend_report.backend, RuntimeBackend::Dovetail);
        assert_eq!(backend_report.artifact, RuntimeBackendArtifact::DovetailRunReport);
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_bad_root_ordinal() {
        let mut report = sample_dovetail_runtime_report();
        report.root_ordinals[0] = 99;

        let err = report
            .validate_shape()
            .expect_err("root ordinals must resolve into the term table");
        assert!(matches!(
            err,
            RuntimeDovetailReportError::RootOrdinalOutOfBounds {
                root_index: 0,
                ordinal: 99,
                terms: 2
            }
        ));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_dangling_edges() {
        let mut report = sample_dovetail_runtime_report();
        report.derivation_edges[0].child_key = b"missing".to_vec();

        let err = RuntimeBackendReport::try_dovetail(report, Vec::new())
            .expect_err("checked constructor rejects dangling derivation edges");
        assert!(matches!(err, RuntimeDovetailReportError::EdgeChildMissing { edge_ordinal: 0 }));
    }

    #[test]
    fn dovetail_report_shape_validation_rejects_duplicate_term_keys() {
        let mut report = sample_dovetail_runtime_report();
        report.terms.push(RuntimeDovetailTermRecord {
            ordinal: 2,
            class_id: 2,
            key: b"child".to_vec(),
            op_display: "DuplicateLeaf".to_string(),
            weight_display: "0".to_string(),
            is_root: false,
        });

        let err = report
            .validate_shape()
            .expect_err("term records must be unique by exact key");
        assert!(matches!(err, RuntimeDovetailReportError::DuplicateTermKey { ordinal: 2 }));
    }

    #[test]
    fn runtime_backend_dispatch_defaults_to_ascent_and_fails_closed() {
        let language = DispatchLanguage;
        let term = DispatchTerm;

        assert_eq!(language.metadata().runtime_backends(), DISPATCH_BACKENDS);
        assert_eq!(language.default_runtime_backend(), RuntimeBackend::Ascent);
        assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));
        assert!(!language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(language.run_default_backend(&term).is_ok());

        let err = language
            .run_with_backend(RuntimeBackend::Dovetail, &term)
            .expect_err("absent Dovetail backend must not fall back to Ascent");
        assert!(err.contains("Dovetail backend is not installed for language Dispatch"));
    }

    #[test]
    fn runtime_backend_dispatch_uses_metadata_default_when_backend_is_installed() {
        let language = RhoDispatchLanguage;
        let term = DispatchTerm;

        assert_eq!(language.metadata().runtime_backends(), RHO_DISPATCH_BACKENDS);
        assert_eq!(language.default_runtime_backend(), RuntimeBackend::RhoMachine);
        assert!(language.supports_runtime_backend(RuntimeBackend::RhoMachine));
        assert!(language.supports_runtime_backend(RuntimeBackend::Ascent));
        assert!(!language.supports_runtime_backend(RuntimeBackend::Dovetail));

        let report = language
            .run_default_backend_report(&term)
            .expect("metadata-selected Rho backend must dispatch");
        assert_eq!(report.backend, RuntimeBackend::RhoMachine);
        assert_eq!(report.artifact, RuntimeBackendArtifact::RhoNormalizedAst);
        assert_eq!(report.evidence_refs, vec!["runtime-test:rho-dispatch"]);

        let out = report
            .observations_for_channel("OUT")
            .expect("Rho report must expose the OUT channel");
        assert_eq!(out.observed_count(), 1);
        assert_eq!(
            out.membership_fingerprint(),
            BTreeSet::from([RuntimeObservationValue::Text("rho-default".to_string())])
        );

        let err = language
            .run_default_backend(&term)
            .expect_err("Ascent-shaped compatibility API must reject Rho observations");
        assert!(
            err.contains(
                "RhoMachine backend for language RhoDispatch returned runtime observations"
            ),
            "{err}"
        );
    }

    #[test]
    fn normal_forms_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .normal_forms_iter()
            .map(|term| term.display.as_str())
            .collect();
        let eager: Vec<_> = results
            .normal_forms()
            .iter()
            .map(|term| term.display.as_str())
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec!["done"]);
    }

    #[test]
    fn rewrites_from_iter_matches_collecting_api() {
        let results = sample_results();
        let lazy: Vec<_> = results
            .rewrites_from_iter(1)
            .map(|rewrite| rewrite.to_id)
            .collect();
        let eager: Vec<_> = results
            .rewrites_from(1)
            .iter()
            .map(|rewrite| rewrite.to_id)
            .collect();

        assert_eq!(lazy, eager);
        assert_eq!(lazy, vec![2]);
    }

    #[test]
    fn reachable_normal_form_uses_lazy_rewrite_iteration() {
        let results = sample_results();
        let nf = results
            .normal_form_reachable_from(1)
            .expect("normal form should be reachable");

        assert_eq!(nf.term_id, 3);
        assert_eq!(nf.display, "done");
    }

    #[test]
    fn reachable_normal_forms_from_seeds_preserves_ambiguous_alternatives() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "longer-but-first".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "a".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("left".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("right".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_seeds(&[1, 2])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["longer-but-first", "a"]);

        let first = results
            .normal_form_reachable_from_seeds(&[1, 2])
            .expect("at least one normal form should be reachable");
        assert_eq!(
            first.display, "longer-but-first",
            "single-witness helper must not choose the shortest display"
        );
    }

    #[test]
    fn weighted_reachable_normal_forms_choose_lower_weight_seed_first() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "higher_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "lower_weight_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "higher_weight_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "lower_weight_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("high".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("low".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let first = results
            .normal_form_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .expect("weighted normal form should be reachable");
        assert_eq!(first.display, "lower_weight_result");

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 9.0), (2, 1.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["lower_weight_result", "higher_weight_result"]);
    }

    #[test]
    fn weighted_reachable_normal_forms_preserve_equal_weight_seed_order() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 1,
                    exact_key: None,
                    display: "first_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 2,
                    exact_key: None,
                    display: "second_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 10,
                    exact_key: None,
                    display: "first_result".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 20,
                    exact_key: None,
                    display: "second_result".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 1,
                    to_id: 10,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("first".to_string()),
                },
                Rewrite {
                    from_id: 2,
                    to_id: 20,
                    from_key: None,
                    to_key: None,
                    rule_name: Some("second".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let all: Vec<_> = results
            .normal_forms_reachable_from_weighted_seeds(&[(1, 3.0), (2, 3.0)])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(all, vec!["first_result", "second_result"]);
    }

    #[test]
    fn reachable_normal_forms_use_exact_keys_despite_term_id_collision() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![0]),
                    display: "left_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![1]),
                    display: "right_seed_same_u64".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![10]),
                    display: "left_nf".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![20]),
                    display: "right_nf_same_u64".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![0]),
                    to_key: Some(vec![10]),
                    rule_name: Some("left".to_string()),
                },
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![1]),
                    to_key: Some(vec![20]),
                    rule_name: Some("right".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let exact_seeds = vec![
            RewriteSeed::exact(7, vec![0], "left_seed".to_string()),
            RewriteSeed::exact(7, vec![1], "right_seed_same_u64".to_string()),
        ];
        let exact: Vec<_> = results
            .normal_forms_reachable_from_rewrite_seeds(&exact_seeds)
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(exact, vec!["left_nf", "right_nf_same_u64"]);

        let legacy: Vec<_> = results
            .normal_forms_reachable_from_seeds(&[7])
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(
            legacy,
            vec!["left_nf", "right_nf_same_u64"],
            "legacy seed ids must expand colliding ids rather than dropping a candidate"
        );
    }

    #[test]
    fn weighted_reachable_normal_forms_use_exact_keys_despite_term_id_collision() {
        let results = AscentResults {
            all_terms: vec![
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![0]),
                    display: "slow_seed".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 7,
                    exact_key: Some(vec![1]),
                    display: "fast_seed_same_u64".to_string(),
                    is_normal_form: false,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![10]),
                    display: "slow_nf".to_string(),
                    is_normal_form: true,
                },
                TermInfo {
                    term_id: 11,
                    exact_key: Some(vec![20]),
                    display: "fast_nf_same_u64".to_string(),
                    is_normal_form: true,
                },
            ],
            rewrites: vec![
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![0]),
                    to_key: Some(vec![10]),
                    rule_name: Some("slow".to_string()),
                },
                Rewrite {
                    from_id: 7,
                    to_id: 11,
                    from_key: Some(vec![1]),
                    to_key: Some(vec![20]),
                    rule_name: Some("fast".to_string()),
                },
            ],
            equivalences: Vec::new(),
            custom_relations: std::collections::HashMap::new(),
        };

        let exact_seeds = vec![
            WeightedRewriteSeed::exact(7, vec![0], "slow_seed".to_string(), 5.0),
            WeightedRewriteSeed::exact(7, vec![1], "fast_seed_same_u64".to_string(), 1.0),
        ];
        let exact: Vec<_> = results
            .normal_forms_reachable_from_weighted_rewrite_seeds(&exact_seeds)
            .into_iter()
            .map(|term| term.display.as_str())
            .collect();
        assert_eq!(exact, vec!["fast_nf_same_u64", "slow_nf"]);
    }
}
