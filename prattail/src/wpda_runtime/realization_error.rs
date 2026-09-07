use std::fmt;

use super::ActionInvocationError;

/// A forest/occurrence reconstruction obligation that could not be satisfied.
/// None of these failures is evidence that the input has no valid parse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReconstructionFailure {
    MissingNode,
    MissingAction { rule_idx: u32 },
    MissingLeafValue,
    DependencyUnavailable { dependency: crate::sppf::SppfId },
    UnexpectedNodeKind,
    CyclicContainer,
    CoordinateUnavailable { coordinate: usize },
    InvalidPlanArity { expected: usize, actual: usize },
    InvalidCollectionItem { found: &'static str },
    TraversalLimit { limit: usize },
    AllocationFailed { requested: usize },
}

impl fmt::Display for ReconstructionFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingNode => formatter.write_str("node is missing from the parse forest"),
            Self::MissingAction { rule_idx } => {
                write!(formatter, "no semantic action exists for rule {rule_idx:#x}")
            },
            Self::MissingLeafValue => {
                formatter.write_str("forest leaf has no backing semantic value")
            },
            Self::DependencyUnavailable { dependency } => {
                write!(formatter, "dependency {dependency} has no completed semantic family")
            },
            Self::UnexpectedNodeKind => {
                formatter.write_str("node has no semantic value in this position")
            },
            Self::CyclicContainer => {
                formatter.write_str("structural container traversal encountered a cycle")
            },
            Self::CoordinateUnavailable { coordinate } => {
                write!(formatter, "selected occurrence coordinate {coordinate} is unavailable")
            },
            Self::InvalidPlanArity { expected, actual } => {
                write!(formatter, "occurrence plan requires {expected} values, but has {actual}")
            },
            Self::InvalidCollectionItem { found } => write!(
                formatter,
                "selected collection requires terms or absent values, but received {found}"
            ),
            Self::TraversalLimit { limit } => {
                write!(formatter, "occurrence traversal exceeded its work limit {limit}")
            },
            Self::AllocationFailed { requested } => {
                write!(
                    formatter,
                    "could not reserve storage for {requested} reconstruction entries"
                )
            },
        }
    }
}

impl std::error::Error for ReconstructionFailure {}

/// Failure of one atomic forest-realization request.
///
/// A failure discards that request's provisional output, not the authoritative
/// forest. It is distinct from invalid source syntax, an exhausted empty
/// family, and a completed ambiguity judgment. In particular, neither a
/// reconstruction limit nor a key-cache limit establishes semantic absence.
/// Successful bounded requests still require separate completeness evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealizationError {
    SemanticKey(mettail_semantic_key::ContentKeyCacheError),
    Reconstruction {
        node: crate::sppf::SppfId,
        cause: ReconstructionFailure,
    },
    Action {
        rule_idx: u32,
        cause: ActionInvocationError,
    },
}

impl From<mettail_semantic_key::ContentKeyCacheError> for RealizationError {
    fn from(error: mettail_semantic_key::ContentKeyCacheError) -> Self {
        Self::SemanticKey(error)
    }
}

impl fmt::Display for RealizationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SemanticKey(error) => fmt::Display::fmt(error, formatter),
            Self::Reconstruction { node, cause } => {
                write!(formatter, "reconstruction at forest node {node} failed: {cause}")
            },
            Self::Action { rule_idx, cause } => {
                write!(formatter, "reconstruction action for rule {rule_idx:#x} failed: {cause}")
            },
        }
    }
}

impl std::error::Error for RealizationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SemanticKey(error) => Some(error),
            Self::Reconstruction { cause, .. } => Some(cause),
            Self::Action { cause, .. } => Some(cause),
        }
    }
}
