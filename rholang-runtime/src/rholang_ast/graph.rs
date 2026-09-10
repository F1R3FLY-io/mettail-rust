//! Bounded interpretation of the initial, already constructed neutral graph.
//!
//! This walks graph references, not Rholang syntax. It reuses the node target
//! and shared worklist; each reference occurrence is interpreted independently.
//! No memoized `Par` subtrees, source parsing, evaluation, or admission occurs.

use super::target::DirectNodeTarget;
use mettail_rholang_codegen::{DynamicReflectionError, ReflectedCodecBudget};
use mettail_rholang_frontend::arena::{ConstructionGraph, NodeView};
use mettail_rholang_frontend::construction::{
    CheckedBoundReference, ConstructionError, ValueOp, ValueTarget,
};
use mettail_runtime::worklist::{ReductionError, Worklist, WorklistError};
use models::rhoapi::Par;

/// Failure never supplies a substitute program or refunds prior reservations.
#[derive(Debug, PartialEq, Eq)]
pub enum GraphInterpretationError {
    Construction(ConstructionError),
    Storage(WorklistError),
    Resource(DynamicReflectionError),
    SizeOverflow,
    NonEarlierReference { owner: u32, child: u32 },
    ObservationMismatch { index: u32 },
}

impl std::fmt::Display for GraphInterpretationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "construction graph interpretation failed: {self:?}")
    }
}

impl std::error::Error for GraphInterpretationError {}

impl From<ConstructionError> for GraphInterpretationError {
    fn from(error: ConstructionError) -> Self {
        Self::Construction(error)
    }
}

impl From<WorklistError> for GraphInterpretationError {
    fn from(error: WorklistError) -> Self {
        Self::Storage(error)
    }
}

impl From<DynamicReflectionError> for GraphInterpretationError {
    fn from(error: DynamicReflectionError) -> Self {
        Self::Resource(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Footprint {
    entries: usize,
    text_bytes: usize,
}

/// Logical metadata byte passes and allocated/copied payload volume are
/// distinct. The retained outer length is neither of these quantities.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct MetadataCharge {
    work: usize,
    units: usize,
}

impl MetadataCharge {
    fn bound(bytes: usize) -> Result<Self, GraphInterpretationError> {
        Ok(Self {
            work: bytes
                .checked_mul(3)
                .ok_or(GraphInterpretationError::SizeOverflow)?,
            units: bytes
                .checked_mul(2)
                .ok_or(GraphInterpretationError::SizeOverflow)?,
        })
    }

    fn append(left: usize, right: usize) -> Result<Self, GraphInterpretationError> {
        let result = left.max(right);
        Ok(Self {
            work: result
                .checked_mul(3)
                .and_then(|passes| left.checked_add(passes))
                .ok_or(GraphInterpretationError::SizeOverflow)?,
            units: left
                .checked_add(result)
                .ok_or(GraphInterpretationError::SizeOverflow)?,
        })
    }
}

impl Footprint {
    fn plus(self, right: Self) -> Result<Self, GraphInterpretationError> {
        Ok(Self {
            entries: self
                .entries
                .checked_add(right.entries)
                .ok_or(GraphInterpretationError::SizeOverflow)?,
            text_bytes: self
                .text_bytes
                .checked_add(right.text_bytes)
                .ok_or(GraphInterpretationError::SizeOverflow)?,
        })
    }

    fn charge<C: FnMut() -> bool>(
        self,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<(), GraphInterpretationError> {
        self.charge_with_metadata(budget, MetadataCharge::default())
    }

    fn charge_with_metadata<C: FnMut() -> bool>(
        self,
        budget: &mut ReflectedCodecBudget<'_, C>,
        metadata: MetadataCharge,
    ) -> Result<(), GraphInterpretationError> {
        let work = self
            .entries
            .checked_add(self.text_bytes)
            .and_then(|work| work.checked_add(metadata.work))
            .ok_or(GraphInterpretationError::SizeOverflow)?;
        // Fixed logical entry units, NOT native layout or physical allocation.
        let units = self
            .entries
            .checked_mul(4)
            .and_then(|units| units.checked_add(self.text_bytes))
            .and_then(|units| units.checked_add(metadata.units))
            .ok_or(GraphInterpretationError::SizeOverflow)?;
        budget.charge(work, units)?;
        Ok(())
    }
}

struct Materialized {
    value: Par,
    footprint: Footprint,
}

enum Job {
    Visit(u32),
    Append(u32),
}

impl Job {
    fn arity(&self) -> Option<usize> {
        match self {
            Self::Visit(_) => None,
            Self::Append(_) => Some(2),
        }
    }
}

fn capacities(root: u32) -> Result<(usize, usize), GraphInterpretationError> {
    let depth = usize::try_from(root)
        .ok()
        .and_then(|index| index.checked_add(1))
        .ok_or(GraphInterpretationError::SizeOverflow)?;
    let jobs = depth
        .checked_mul(2)
        .and_then(|slots| slots.checked_add(1))
        .ok_or(GraphInterpretationError::SizeOverflow)?;
    let values = depth
        .checked_add(1)
        .ok_or(GraphInterpretationError::SizeOverflow)?;
    Ok((jobs, values))
}

fn node(graph: &ConstructionGraph, index: u32) -> Result<NodeView<'_>, GraphInterpretationError> {
    graph
        .node(index)
        .ok_or_else(|| ConstructionError::MissingReference { index }.into())
}

fn checked_value(
    graph: &ConstructionGraph,
    index: u32,
    value: Par,
    footprint: Footprint,
) -> Result<Materialized, GraphInterpretationError> {
    if DirectNodeTarget::observation(&value) != node(graph, index)?.observation {
        return Err(GraphInterpretationError::ObservationMismatch { index });
    }
    Ok(Materialized { value, footprint })
}

fn precharged<C: FnMut() -> bool, T>(
    budget: &mut ReflectedCodecBudget<'_, C>,
    footprint: Footprint,
    metadata: MetadataCharge,
    build: impl FnOnce() -> Result<T, GraphInterpretationError>,
) -> Result<T, GraphInterpretationError> {
    footprint.charge_with_metadata(budget, metadata)?;
    build()
}

/// Interpret empty/integer/Boolean/text/bound/wildcard/append construction.
///
/// This is a structural component, not full source admission or a prepared
/// executable program. The caller owns the graph and cumulative budget.
/// Repeated edges expand repeatedly, in left-to-right order; expansion and
/// existing helper copies are charged before construction. Later unreachable
/// nodes are not visited. No result is published on failure.
///
/// For root index `r`, decreasing references give depth at most `r + 1`.
/// `RholangInitialGraphMachine.v` proves capacities `2 * (r + 1) + 1` jobs and
/// `(r + 1) + 1` values for every intermediate state. Reserve those once, charging
/// one work unit and four logical units per slot. Each popped job costs one
/// additional work unit; each copied expression entry costs one work/four
/// logical units, and each copied text byte costs one work/one logical unit.
/// `RholangInitialGraphResources.v` proves the associated footprint/debit laws.
/// Bound/wildcard leaves retain the same scheduling and stack-capacity proof.
/// For bound metadata length `b = index + 1`, additionally reserve `3*b` work
/// and `2*b` units before initialization, the node helper's clone and observation.
/// For append metadata lengths `l`, `r`, put `m = max(l, r)` and additionally
/// reserve `l + 3*m` work and `l + m` units before left cloning, union initialization/
/// filling and observation. `RholangBoundMetadata.v` proves these separate byte-pass
/// equations. Retained metadata has length `m`, not an additive subtree measure.
///
/// These allowances are not semantic gas, protobuf size or RSS. Existing
/// worklist/constructor allocation is infallible; cancellation is checked at
/// reservation boundaries, not inside those helpers. Arithmetic overflow is
/// rejected before allocation. Owned node cleanup uses the node's existing
/// lifecycle implementation, not a recursive graph walk.
pub fn interpret_construction_graph<C: FnMut() -> bool>(
    graph: &ConstructionGraph,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Par, GraphInterpretationError> {
    let (jobs, values) = capacities(graph.root())?;
    let slots = jobs
        .checked_add(values)
        .ok_or(GraphInterpretationError::SizeOverflow)?;
    Footprint { entries: slots, text_bytes: 0 }.charge(budget)?;
    let mut work: Worklist<Job, Materialized> = Worklist::with_capacity(jobs, values);
    work.push(Job::Visit(graph.root()), Job::arity)?;
    work.check()?;
    while let Some(job) = work.pop(Job::arity)? {
        budget.charge(1, 0)?;
        match job {
            Job::Visit(index) => {
                let current = node(graph, index)?;
                if current.children.len() != current.operation.arity() {
                    return Err(ConstructionError::ChildArity {
                        expected: current.operation.arity(),
                        actual: current.children.len(),
                    }
                    .into());
                }
                match current.operation {
                    ValueOp::Append => {
                        let [left, right] = current.children else {
                            unreachable!("binary arity checked before scheduling")
                        };
                        for &child in [left, right] {
                            if child >= index {
                                return Err(GraphInterpretationError::NonEarlierReference {
                                    owner: index,
                                    child,
                                });
                            }
                        }
                        // LIFO: left is visited first; duplicate edges stay duplicated.
                        work.push(Job::Append(index), Job::arity)?;
                        work.push(Job::Visit(*right), Job::arity)?;
                        work.push(Job::Visit(*left), Job::arity)?;
                    },
                    scalar => {
                        let reference = match scalar {
                            ValueOp::Bound { scope, index } => {
                                Some(CheckedBoundReference::new(*scope, *index)?)
                            },
                            _ => None,
                        };
                        let metadata = match reference {
                            Some(reference) => MetadataCharge::bound(reference.metadata_bytes())?,
                            None => MetadataCharge::default(),
                        };
                        let footprint = match scalar {
                            ValueOp::Empty => Footprint { entries: 0, text_bytes: 0 },
                            ValueOp::Text(text) => Footprint { entries: 1, text_bytes: text.len() },
                            ValueOp::Integer(_)
                            | ValueOp::Boolean(_)
                            | ValueOp::Bound { .. }
                            | ValueOp::Wildcard { .. } => Footprint { entries: 1, text_bytes: 0 },
                            ValueOp::Append => unreachable!("append scheduled separately"),
                        };
                        let value = precharged(budget, footprint, metadata, || {
                            // In particular the text clone is AFTER reservation.
                            let value = match scalar {
                                ValueOp::Empty => DirectNodeTarget::empty(),
                                ValueOp::Integer(value) => DirectNodeTarget::integer(*value),
                                ValueOp::Boolean(value) => DirectNodeTarget::boolean(*value),
                                ValueOp::Text(value) => DirectNodeTarget::text(value.clone()),
                                ValueOp::Bound { .. } => DirectNodeTarget::bound(
                                    reference.expect("validated bound descriptor"),
                                ),
                                ValueOp::Wildcard { connective } => {
                                    DirectNodeTarget::wildcard(*connective)
                                },
                                ValueOp::Append => unreachable!("append scheduled separately"),
                            };
                            checked_value(graph, index, value, footprint)
                        })?;
                        work.value(value);
                    },
                }
            },
            Job::Append(index) => {
                work.reduce_pair(|left, right| {
                    let footprint = left.footprint.plus(right.footprint)?;
                    // Par::append clones left, then concat clones left and right.
                    let copies = left.footprint.plus(footprint)?;
                    let metadata = MetadataCharge::append(
                        left.value.locally_free.len(),
                        right.value.locally_free.len(),
                    )?;
                    precharged(budget, copies, metadata, || {
                        let value =
                            ValueTarget::append(&mut DirectNodeTarget, left.value, right.value)?;
                        checked_value(graph, index, value, footprint)
                    })
                })
                .map_err(|error| match error {
                    ReductionError::Storage(error) => GraphInterpretationError::Storage(error),
                    ReductionError::Construction(error) => error,
                })?;
            },
        }
        work.check()?;
    }
    Ok(work.finish()?.value)
}

#[cfg(test)]
#[path = "graph_tests.rs"]
mod tests;
