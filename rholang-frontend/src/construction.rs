//! Consuming construction algebra shared with the direct node adapter.
//!
//! `Value` deliberately has no `Clone` bound. A direct adapter moves concrete
//! node values into their parents; the neutral adapter retains checked arena
//! references. The latter implements the persistent-reference protocol, while
//! the former does not need a permanent arena of copied node subtrees.

/// The first implemented operation family. Arity is fixed by each variant.
/// Integer decoding/range checking precedes this signed-64-bit carrier.
#[derive(Debug, PartialEq, Eq)]
pub enum ValueOp {
    Empty,
    Integer(i64),
    Boolean(bool),
    Text(String),
    Append,
    Bound { scope: usize, index: usize },
    Wildcard { connective: bool },
}

impl ValueOp {
    pub fn arity(&self) -> usize {
        match self {
            Self::Append => 2,
            Self::Empty
            | Self::Integer(_)
            | Self::Boolean(_)
            | Self::Text(_)
            | Self::Bound { .. }
            | Self::Wildcard { .. } => 0,
        }
    }

    pub(crate) fn payload_bytes(&self) -> usize {
        match self {
            Self::Text(text) => text.len(),
            _ => 0,
        }
    }
}

/// A bound reference validated before any index-sized metadata allocation.
/// The total lexical scope is not restricted to an emitted signed field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckedBoundReference {
    emitted_index: i32,
    metadata_bytes: usize,
}

impl CheckedBoundReference {
    pub fn new(scope: usize, index: usize) -> Result<Self, ConstructionError> {
        let emitted_index =
            i32::try_from(index).map_err(|_| ConstructionError::TargetIndexOutOfRange { index })?;
        if index >= scope {
            return Err(ConstructionError::IndexOutOfScope { scope, index });
        }
        let metadata_bytes = index
            .checked_add(1)
            .ok_or(ConstructionError::ReferenceIndexOverflow)?;
        Ok(Self { emitted_index, metadata_bytes })
    }

    pub fn emitted_index(self) -> i32 {
        self.emitted_index
    }
    pub fn metadata_bytes(self) -> usize {
        self.metadata_bytes
    }
}

/// Structural information used by construction, not evaluated semantics.
/// The slice borrows the actual target/value, not a phantom session lifetime.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructuralObservation<'a> {
    pub single_string: bool,
    pub locally_free: &'a [u8],
    pub connective_used: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind {
    Nodes,
    Edges,
    PayloadBytes,
    Work,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstructionError {
    MissingReference { index: u32 },
    ChildArity { expected: usize, actual: usize },
    LimitExceeded(LimitKind),
    ReferenceIndexOverflow,
    AllocationFailed,
    Cancelled,
    TargetIndexOutOfRange { index: usize },
    IndexOutOfScope { scope: usize, index: usize },
}

impl std::fmt::Display for ConstructionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for ConstructionError {}

/// Constructors consume child values; observations only borrow them.
/// Forwarding denotes quote/drop/parentheses, without a semantic wrapper.
pub trait ValueTarget {
    type Value;

    fn construct(
        &mut self,
        operation: ValueOp,
        children: Vec<Self::Value>,
    ) -> Result<Self::Value, ConstructionError>;

    fn observe<'a>(
        &'a self,
        value: &'a Self::Value,
    ) -> Result<StructuralObservation<'a>, ConstructionError>;

    fn forward(&mut self, value: Self::Value) -> Result<Self::Value, ConstructionError>;

    /// Typed binary path. Direct owned targets can avoid allocating a temporary
    /// child vector; the meaning is exactly `construct(Append, [left, right])`.
    fn append(
        &mut self,
        left: Self::Value,
        right: Self::Value,
    ) -> Result<Self::Value, ConstructionError> {
        self.construct(ValueOp::Append, vec![left, right])
    }
}

/// The existing parallel continuation: construct empty, then append children
/// left-to-right. Even an empty fold calls the target's checked constructor.
/// Stop at the first error; no identity substitute or target rollback occurs.
pub fn append_fold<T: ValueTarget>(
    target: &mut T,
    children: impl IntoIterator<Item = T::Value>,
) -> Result<T::Value, ConstructionError> {
    let empty = target.construct(ValueOp::Empty, Vec::new())?;
    children
        .into_iter()
        .try_fold(empty, |left, right| target.append(left, right))
}
