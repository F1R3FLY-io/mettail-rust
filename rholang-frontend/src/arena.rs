//! Flat, session-branded construction with checked earlier references.
//!
//! Create exactly one target per brand with [`with_neutral_target`]. Neither
//! target nor reference exposes a constructor, reset, fork or unbranding API.
//! A brand prevents safe cross-session use; bounds are still checked. It is
//! not a capability, a serialized identity or proof of host admission.
//!
//! Append retains two edges and caches observations, rather than copying an
//! expanding head list. Every owned node and error cleanup is non-recursive.

use crate::construction::{
    CheckedBoundReference, ConstructionError, LimitKind, StructuralObservation, ValueOp,
    ValueTarget,
};
use std::marker::PhantomData;

type Invariant<'id> = PhantomData<fn(&'id ()) -> &'id ()>;

/// A checked reference usable only with its originating live session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueRef<'id> {
    index: u32,
    brand: Invariant<'id>,
}

/// Explicit construction limits, not estimates of allocator RSS or gas grades.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstructionLimits {
    pub nodes: usize,
    pub edges: usize,
    pub payload_bytes: usize,
    pub work: usize,
}

/// Retained graph sizes plus cumulative attempted logical work. Failed
/// construction does not grow the graph; work already performed is retained.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConstructionUsage {
    pub nodes: usize,
    pub edges: usize,
    pub payload_bytes: usize,
    pub work: usize,
}

struct Meter {
    limits: ConstructionLimits,
    usage: ConstructionUsage,
}

impl Meter {
    fn work(&mut self, cancelled: &mut impl FnMut() -> bool) -> Result<(), ConstructionError> {
        if cancelled() {
            return Err(ConstructionError::Cancelled);
        }
        self.usage.work = bounded_add(self.usage.work, 1, self.limits.work, LimitKind::Work)?;
        Ok(())
    }

    fn growth(&self, edges: usize, bytes: usize) -> Result<ConstructionUsage, ConstructionError> {
        Ok(ConstructionUsage {
            nodes: bounded_add(self.usage.nodes, 1, self.limits.nodes, LimitKind::Nodes)?,
            edges: bounded_add(self.usage.edges, edges, self.limits.edges, LimitKind::Edges)?,
            payload_bytes: bounded_add(
                self.usage.payload_bytes,
                bytes,
                self.limits.payload_bytes,
                LimitKind::PayloadBytes,
            )?,
            work: self.usage.work,
        })
    }
}

fn bounded_add(
    current: usize,
    amount: usize,
    limit: usize,
    kind: LimitKind,
) -> Result<usize, ConstructionError> {
    current
        .checked_add(amount)
        .filter(|&next| next <= limit)
        .ok_or(ConstructionError::LimitExceeded(kind))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HeadShape {
    Empty,
    SingleText,
    Other,
}

impl HeadShape {
    fn append(self, right: Self) -> Self {
        match (self, right) {
            (Self::Empty, shape) | (shape, Self::Empty) => shape,
            _ => Self::Other,
        }
    }
}

struct Fact {
    shape: HeadShape,
    locally_free: Vec<u8>,
    connective_used: bool,
}

impl Fact {
    fn closed(shape: HeadShape) -> Self {
        Self {
            shape,
            locally_free: Vec::new(),
            connective_used: false,
        }
    }
    fn observation(&self) -> StructuralObservation<'_> {
        StructuralObservation {
            single_string: self.shape == HeadShape::SingleText,
            locally_free: &self.locally_free,
            connective_used: self.connective_used,
        }
    }
}

struct Node {
    operation: ValueOp,
    children: Vec<u32>,
    fact: Fact,
}

/// Read-only view of one graph node. Numeric links are local to the borrowed
/// graph; they cannot be converted into a live branded construction reference.
pub struct NodeView<'a> {
    pub operation: &'a ValueOp,
    pub children: &'a [u32],
    pub observation: StructuralObservation<'a>,
}

/// Owned construction component only. This is not the full frontend artifact
/// and carries no source admission, provider grant, funding or publication proof.
pub struct ConstructionGraph {
    nodes: Vec<Node>,
    root: u32,
    usage: ConstructionUsage,
}

impl ConstructionGraph {
    pub fn root(&self) -> u32 {
        self.root
    }
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    pub fn usage(&self) -> ConstructionUsage {
        self.usage
    }
    pub fn node(&self, index: u32) -> Option<NodeView<'_>> {
        self.nodes.get(index as usize).map(|node| NodeView {
            operation: &node.operation,
            children: &node.children,
            observation: node.fact.observation(),
        })
    }
}

pub struct NeutralTarget<'id, C: FnMut() -> bool> {
    nodes: Vec<Node>,
    meter: Meter,
    cancelled: C,
    brand: Invariant<'id>,
}

/// The higher-ranked closure supplies a fresh invariant lifetime without
/// global counters or runtime identity allocations. Only an owned graph, not
/// the target or its branded references, can leave this scope.
pub fn with_neutral_target<R, C: FnMut() -> bool>(
    limits: ConstructionLimits,
    cancelled: C,
    build: impl for<'id> FnOnce(NeutralTarget<'id, C>) -> R,
) -> R {
    build(NeutralTarget {
        nodes: Vec::new(),
        meter: Meter {
            limits,
            usage: ConstructionUsage::default(),
        },
        cancelled,
        brand: PhantomData,
    })
}

impl<'id, C: FnMut() -> bool> NeutralTarget<'id, C> {
    pub fn usage(&self) -> ConstructionUsage {
        self.meter.usage
    }

    fn get(&self, value: ValueRef<'id>) -> Result<&Node, ConstructionError> {
        self.nodes
            .get(value.index as usize)
            .ok_or(ConstructionError::MissingReference { index: value.index })
    }

    /// Consume the target and retain its complete graph, including repeated
    /// edges and nodes not reachable from this root. Session descriptors and
    /// occurrence maps are owned by the enclosing frontend session, not here.
    pub fn finish_graph(
        mut self,
        root: ValueRef<'id>,
    ) -> Result<ConstructionGraph, ConstructionError> {
        self.meter.work(&mut self.cancelled)?;
        self.get(root)?;
        Ok(ConstructionGraph {
            nodes: self.nodes,
            root: root.index,
            usage: self.meter.usage,
        })
    }
}

impl<'id, C: FnMut() -> bool> ValueTarget for NeutralTarget<'id, C> {
    type Value = ValueRef<'id>;

    fn construct(
        &mut self,
        operation: ValueOp,
        children: Vec<Self::Value>,
    ) -> Result<Self::Value, ConstructionError> {
        self.meter.work(&mut self.cancelled)?;
        // Resolve before arity validation, preserving the protocol's first
        // missing-reference error. Resource/cancellation failure is separate.
        for &child in &children {
            self.meter.work(&mut self.cancelled)?;
            self.get(child)?;
        }
        if children.len() != operation.arity() {
            return Err(ConstructionError::ChildArity {
                expected: operation.arity(),
                actual: children.len(),
            });
        }
        let index = u32::try_from(self.nodes.len())
            .map_err(|_| ConstructionError::ReferenceIndexOverflow)?;
        // All limits precede allocation of a new node or edge vector.
        let free_bytes = match operation {
            ValueOp::Bound { scope, index } => {
                CheckedBoundReference::new(scope, index)?.metadata_bytes()
            },
            ValueOp::Append => self
                .get(children[0])?
                .fact
                .locally_free
                .len()
                .max(self.get(children[1])?.fact.locally_free.len()),
            _ => 0,
        };
        let bytes = operation
            .payload_bytes()
            .checked_add(free_bytes)
            .ok_or(ConstructionError::LimitExceeded(LimitKind::PayloadBytes))?;
        self.meter.growth(children.len(), bytes)?;

        let fact = match &operation {
            ValueOp::Empty => Fact::closed(HeadShape::Empty),
            ValueOp::Text(_) => Fact::closed(HeadShape::SingleText),
            ValueOp::Integer(_) | ValueOp::Boolean(_) => Fact::closed(HeadShape::Other),
            ValueOp::Bound { index, .. } => {
                let mut locally_free = Vec::new();
                locally_free
                    .try_reserve_exact(free_bytes)
                    .map_err(|_| ConstructionError::AllocationFailed)?;
                for offset in 0..free_bytes {
                    self.meter.work(&mut self.cancelled)?;
                    locally_free.push(u8::from(offset == *index));
                }
                Fact {
                    shape: HeadShape::Other,
                    locally_free,
                    connective_used: false,
                }
            },
            ValueOp::Wildcard { connective } => Fact {
                shape: HeadShape::Other,
                locally_free: Vec::new(),
                connective_used: *connective,
            },
            ValueOp::Append => {
                let lhs = &self.nodes[children[0].index as usize].fact;
                let rhs = &self.nodes[children[1].index as usize].fact;
                let mut locally_free = Vec::new();
                locally_free
                    .try_reserve_exact(free_bytes)
                    .map_err(|_| ConstructionError::AllocationFailed)?;
                for index in 0..free_bytes {
                    self.meter.work(&mut self.cancelled)?;
                    locally_free.push(
                        lhs.locally_free.get(index).copied().unwrap_or(0)
                            | rhs.locally_free.get(index).copied().unwrap_or(0),
                    );
                }
                Fact {
                    shape: lhs.shape.append(rhs.shape),
                    locally_free,
                    connective_used: lhs.connective_used || rhs.connective_used,
                }
            },
        };
        let mut indices = Vec::new();
        indices
            .try_reserve_exact(children.len())
            .map_err(|_| ConstructionError::AllocationFailed)?;
        for child in children {
            indices.push(child.index);
        }
        self.nodes
            .try_reserve(1)
            .map_err(|_| ConstructionError::AllocationFailed)?;
        let usage = self.meter.growth(indices.len(), bytes)?;
        self.nodes.push(Node { operation, children: indices, fact });
        self.meter.usage = usage;
        Ok(ValueRef { index, brand: PhantomData })
    }

    fn observe<'a>(
        &'a self,
        value: &'a Self::Value,
    ) -> Result<StructuralObservation<'a>, ConstructionError> {
        Ok(self.get(*value)?.fact.observation())
    }

    fn forward(&mut self, value: Self::Value) -> Result<Self::Value, ConstructionError> {
        self.meter.work(&mut self.cancelled)?;
        self.get(value)?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
