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

/// Projection of an already-opened binder roster. URI order and binder order
/// must originate from the same normalized pairs; this type does not sort.
#[derive(Debug, PartialEq, Eq)]
pub enum FreshShape {
    Plain { binder_count: usize },
    Uri { binder_count: usize, uris: Vec<String> },
}

/// Checked structural layout, not a language handle or an injection authority.
/// Body/injection values and resource admission are separate caller obligations.
/// The current graph operation family does not yet consume this descriptor.
#[derive(Debug, PartialEq, Eq)]
pub struct CheckedFreshDescriptor {
    binder_count: usize,
    emitted_binder_count: i32,
    uris: Vec<String>,
    injection_keys: Vec<String>,
    arity: usize,
}

fn strictly_ordered(values: &[String]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

/// Body plus all injection children. The machine-sized arity is not an i32
/// field and must not inherit the emitted binder-count restriction.
pub fn checked_fresh_arity(injection_count: usize) -> Result<usize, ConstructionError> {
    injection_count
        .checked_add(1)
        .ok_or(ConstructionError::ArityOverflow)
}

impl CheckedFreshDescriptor {
    /// Validate the normalized layout, then emitted count, then machine arity.
    /// A subsequent constructor must still check its actual injection count.
    pub fn new(shape: FreshShape, injection_keys: Vec<String>) -> Result<Self, ConstructionError> {
        let (binder_count, uris) = match shape {
            FreshShape::Plain { binder_count } => (binder_count, Vec::new()),
            FreshShape::Uri { binder_count, uris } => {
                let valid = uris.len() == binder_count
                    && uris.first().is_some_and(|uri| !uri.is_empty())
                    && strictly_ordered(&uris);
                if !valid {
                    return Err(ConstructionError::InvalidBinderLayout);
                }
                (binder_count, uris)
            },
        };
        if !strictly_ordered(&injection_keys) {
            return Err(ConstructionError::InvalidBinderLayout);
        }
        let emitted_binder_count = i32::try_from(binder_count)
            .map_err(|_| ConstructionError::TargetIndexOutOfRange { index: binder_count })?;
        let arity = checked_fresh_arity(injection_keys.len())?;
        Ok(Self {
            binder_count,
            emitted_binder_count,
            uris,
            injection_keys,
            arity,
        })
    }

    pub fn binder_count(&self) -> usize {
        self.binder_count
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn validate_injection_count(&self, count: usize) -> Result<(), ConstructionError> {
        let actual = checked_fresh_arity(count)?;
        if actual != self.arity {
            return Err(ConstructionError::ChildArity { expected: self.arity, actual });
        }
        Ok(())
    }

    /// Move the admitted fields into the target without cloning string payloads.
    pub fn into_parts(self) -> (i32, Vec<String>, Vec<String>) {
        (self.emitted_binder_count, self.uris, self.injection_keys)
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
    InvalidBinderLayout,
    ArityOverflow,
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

#[cfg(test)]
#[path = "construction_tests.rs"]
mod tests;
