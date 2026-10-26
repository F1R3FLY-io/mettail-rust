//! Source-bound projection of `SourceEquationCarrierDomain.StableKeySorts`.
//!
//! Reuse the runtime signatures, then perform two finite worklist traversals.
//! Physical Map entries have the model's `EntryType`, not `ValueType(pair)`:
//! contracting that internal node gives edges to its key and value without
//! admitting unrelated constructors whose result happens to be the pair sort.

use super::*;
use std::mem::size_of;

/// A sufficient universal domain check, separate from bounded normalization.
#[derive(Debug)]
pub struct EquationSectionCarrierAdmission<'a> {
    /// `None` means this check did not establish equation-inert key domains.
    /// It does not reject the source or an individual normalization request.
    pub certificate: Option<VerifiedEquationSectionCarrier<'a>>,
    pub boundary_work: u64,
}

/// Evidence for one selected carrier of the exact source-certified section.
///
/// Every reachable keyed collection has an equation-inert key sort. Together
/// with ordinary typed, collection-canonical input admission, this discharges
/// the model's key-domain premise. Mathematical completion does not promise
/// success within a particular normalization resource budget.
#[derive(Debug)]
pub struct VerifiedEquationSectionCarrier<'a> {
    source: &'a VerifiedSourceEquationSectionV1<'a>,
    root: TheorySortId,
}

impl<'a> VerifiedEquationSectionCarrier<'a> {
    pub fn source_section(&self) -> &'a VerifiedSourceEquationSectionV1<'a> {
        self.source
    }

    pub fn root_sort(&self) -> TheorySortId {
        self.root
    }
}

impl<'a> SourceEquationSection<'a> {
    /// Check the sufficient typed key-domain condition for this selected root.
    ///
    /// This uses only the immutable owner already authenticated by the source
    /// certificate. All constructors and rich operators contribute their full
    /// child contracts, including substitutions returning a different sort.
    /// `Ok` with no certificate means unsupported universal evidence; invalid
    /// identities, cancellation, work/input limits and allocation failures are
    /// errors. Neither result changes installation or `normalize_in_sort`.
    ///
    /// `nodes` bounds sort vertices. `bytes` bounds requested graph, worklist
    /// and maximum temporary signature storage (excluding the borrowed image).
    /// `work` meters table rows, signature copies, edges and worklist visits.
    /// The graph and both traversals use O(source rows + signature children)
    /// work and storage, with no recursive traversal.
    pub fn check_carrier_domain<C: FnMut() -> bool>(
        &self,
        root_sort: TheorySortId,
        limits: SemanticInputLimits,
        is_cancelled: C,
    ) -> Result<EquationSectionCarrierAdmission<'a>, EquationSectionFailure> {
        let mut check = CarrierCheck {
            image: self.certificate.semantic_image(),
            limits,
            work: 0,
            cancelled: is_cancelled,
        };
        match check.run(root_sort, self.certificate.roles().sort) {
            Ok(supported) => Ok(EquationSectionCarrierAdmission {
                certificate: supported.then_some(VerifiedEquationSectionCarrier {
                    source: self.certificate,
                    root: root_sort,
                }),
                boundary_work: check.work,
            }),
            Err(reason) => Err(EquationSectionFailure {
                reason: EquationSectionFailureKind::Boundary(reason),
                boundary_work: check.work,
            }),
        }
    }
}

const NO_EDGE: usize = usize::MAX;

struct CarrierVertex {
    forward: usize,
    reverse: usize,
    from_root: bool,
    to_equation: bool,
}

struct CarrierEdge {
    source: usize,
    target: usize,
    next_forward: usize,
    next_reverse: usize,
}

/// Dense source IDs and linked adjacency avoid hashing, repeated table scans,
/// recursive graph utilities and per-vertex allocation. Duplicate edges remain
/// harmless: each declared dependency is visited a constant number of times.
struct CarrierGraph {
    vertices: Vec<CarrierVertex>,
    edges: Vec<CarrierEdge>,
    pending: Vec<usize>,
    edge_limit: usize,
}

struct CarrierCheck<'a, C> {
    image: &'a TheorySemanticImageV1,
    limits: SemanticInputLimits,
    work: u64,
    cancelled: C,
}

impl<C: FnMut() -> bool> CarrierCheck<'_, C> {
    fn charge(&mut self) -> Result<(), SemanticMatchUndetermined> {
        charge_work(&mut self.work, self.limits.work, &mut self.cancelled)
    }

    fn run(
        &mut self,
        root: TheorySortId,
        equation: TheorySortId,
    ) -> Result<bool, SemanticMatchUndetermined> {
        self.charge()?;
        let image = self.image;
        runtime_sort_kind(image, root)?;
        runtime_sort_kind(image, equation)?;
        let edge_count = self.storage_bound()?;
        let mut graph = CarrierGraph {
            vertices: Vec::new(),
            edges: Vec::new(),
            pending: Vec::new(),
            edge_limit: edge_count,
        };
        graph
            .vertices
            .try_reserve_exact(image.sorts.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        graph
            .edges
            .try_reserve_exact(edge_count)
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        graph
            .pending
            .try_reserve_exact(image.sorts.len())
            .map_err(|_| SemanticMatchUndetermined::AllocationFailed)?;
        for _ in &image.sorts {
            self.charge()?;
            graph.vertices.push(CarrierVertex {
                forward: NO_EDGE,
                reverse: NO_EDGE,
                from_root: false,
                to_equation: false,
            });
        }
        self.project_dependencies(&mut graph)?;
        if graph.edges.len() != edge_count {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        self.visit(&mut graph, root, false)?;
        self.visit(&mut graph, equation, true)?;
        for sort in &image.sorts {
            self.charge()?;
            if !graph.vertices[sort.id.0 as usize].from_root {
                continue;
            }
            if let TheorySortKindImageV1::Collection {
                kind: CollectionKind::Map | CollectionKind::PathMap,
                key: Some(key),
                ..
            } = &sort.kind
            {
                if graph.vertices[key.0 as usize].to_equation {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Count storage before any graph or signature allocation. These lengths
    /// size the existing signature projection below; they do not infer sorts.
    fn storage_bound(&mut self) -> Result<usize, SemanticMatchUndetermined> {
        let limit = SemanticMatchUndetermined::InputLimitExceeded;
        let image = self.image;
        let vertices = image.sorts.len();
        if vertices > self.limits.nodes {
            return Err(limit);
        }
        let mut edges = 0_usize;
        let mut scratch = 0_usize;
        for (index, constructor) in image.constructors.iter().enumerate() {
            self.charge()?;
            if constructor.id.0 as usize != index {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            edges = edges.checked_add(constructor.domain.len()).ok_or(limit)?;
            scratch = scratch.max(constructor.domain.len());
        }
        for (index, sort) in image.sorts.iter().enumerate() {
            self.charge()?;
            if sort.id.0 as usize != index {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            }
            let children = match &sort.kind {
                TheorySortKindImageV1::Function { .. } => {
                    scratch = scratch.max(2);
                    4 // Two abstraction children and two substitution children.
                },
                TheorySortKindImageV1::Product { factors } => {
                    scratch = scratch.max(factors.len());
                    factors.len()
                },
                TheorySortKindImageV1::Collection { kind, .. } => match kind {
                    CollectionKind::List | CollectionKind::Bag | CollectionKind::Set => 1,
                    CollectionKind::Map => 2,
                    CollectionKind::PathMap => 3, // Set key plus Map key and value.
                },
                TheorySortKindImageV1::Syntax { .. } | TheorySortKindImageV1::Opaque { .. } => 0,
            };
            edges = edges.checked_add(children).ok_or(limit)?;
        }
        let bytes = vertices
            .checked_mul(size_of::<CarrierVertex>() + size_of::<usize>())
            .and_then(|bytes| bytes.checked_add(edges.checked_mul(size_of::<CarrierEdge>())?))
            .and_then(|bytes| bytes.checked_add(scratch.checked_mul(size_of::<TheorySortId>())?))
            .ok_or(limit)?;
        if bytes > self.limits.bytes {
            return Err(limit);
        }
        Ok(edges)
    }

    fn project_dependencies(
        &mut self,
        graph: &mut CarrierGraph,
    ) -> Result<(), SemanticMatchUndetermined> {
        let image = self.image;
        // Constructors apply to rich result sorts as well as syntax sorts.
        for constructor in &image.constructors {
            self.operator(
                graph,
                TheoryImageOperatorV1::Constructor(constructor.id),
                None,
                constructor.domain.len(),
            )?;
        }
        for sort in &image.sorts {
            self.charge()?;
            match &sort.kind {
                TheorySortKindImageV1::Function { codomain, .. } => {
                    self.operator(
                        graph,
                        TheoryImageOperatorV1::Abstraction { sort: sort.id },
                        None,
                        2,
                    )?;
                    self.operator(
                        graph,
                        TheoryImageOperatorV1::Substitution { sort: *codomain, function: sort.id },
                        None,
                        2,
                    )?;
                },
                TheorySortKindImageV1::Product { factors } => self.operator(
                    graph,
                    TheoryImageOperatorV1::Product { sort: sort.id },
                    None,
                    factors.len(),
                )?,
                TheorySortKindImageV1::Collection { kind, element, .. } => {
                    let operator = TheoryImageOperatorV1::Collection {
                        sort: sort.id,
                        element: *element,
                        kind: *kind,
                    };
                    if *kind == CollectionKind::PathMap {
                        for mode in
                            [PathMapModeV1::NeutralEmpty, PathMapModeV1::Set, PathMapModeV1::Map]
                        {
                            self.operator(graph, operator.clone(), Some(mode), 0)?;
                        }
                    } else {
                        self.operator(graph, operator, None, 0)?;
                    }
                },
                // Exact literals have no children. Their payload/carrier check
                // stays in runtime_operator_signature at term admission; no
                // fabricated sample literal stands in for the source carrier.
                TheorySortKindImageV1::Syntax { .. } | TheorySortKindImageV1::Opaque { .. } => {},
            }
        }
        Ok(())
    }

    fn operator(
        &mut self,
        graph: &mut CarrierGraph,
        operator: TheoryImageOperatorV1,
        mode: Option<PathMapModeV1>,
        copied_children: usize,
    ) -> Result<(), SemanticMatchUndetermined> {
        self.charge()?;
        // Charge the existing fallible signature clone before it allocates or
        // copies a potentially large constructor domain or product factor list.
        charge_work_units(&mut self.work, self.limits.work, copied_children, &mut self.cancelled)?;
        let signature = runtime_operator_signature(self.image, &operator, mode)?;
        runtime_sort_kind(self.image, signature.result)?;
        match signature.children {
            RuntimeChildSortContract::Fixed(children) => {
                for child in children {
                    self.edge(graph, signature.result, child)?;
                }
            },
            RuntimeChildSortContract::Homogeneous(child) => {
                if let TheoryImageOperatorV1::Collection { sort, element, kind } = &operator {
                    if *kind == CollectionKind::Map
                        || (*kind == CollectionKind::PathMap && mode == Some(PathMapModeV1::Map))
                    {
                        let entry =
                            runtime_keyed_collection_sorts(self.image, *sort, *kind, *element)?;
                        if child != entry.pair {
                            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
                        }
                        // The checked physical Product has exactly these two
                        // factors. Its EntryType has no constructor alternatives.
                        self.edge(graph, signature.result, entry.key)?;
                        self.edge(graph, signature.result, entry.value)?;
                        return Ok(());
                    }
                }
                self.edge(graph, signature.result, child)?;
            },
            // A universal carrier check visits each concrete PathMap mode;
            // a mode-polymorphic remainder is not a ground value signature.
            RuntimeChildSortContract::RemainderOnly => {
                return Err(SemanticMatchUndetermined::InvalidImageEvidence);
            },
        }
        Ok(())
    }

    fn edge(
        &mut self,
        graph: &mut CarrierGraph,
        source: TheorySortId,
        target: TheorySortId,
    ) -> Result<(), SemanticMatchUndetermined> {
        self.charge()?;
        runtime_sort_kind(self.image, source)?;
        runtime_sort_kind(self.image, target)?;
        if graph.edges.len() == graph.edge_limit {
            return Err(SemanticMatchUndetermined::InvalidImageEvidence);
        }
        let source = source.0 as usize;
        let target = target.0 as usize;
        let index = graph.edges.len();
        graph.edges.push(CarrierEdge {
            source,
            target,
            next_forward: graph.vertices[source].forward,
            next_reverse: graph.vertices[target].reverse,
        });
        graph.vertices[source].forward = index;
        graph.vertices[target].reverse = index;
        Ok(())
    }

    fn visit(
        &mut self,
        graph: &mut CarrierGraph,
        root: TheorySortId,
        reverse: bool,
    ) -> Result<(), SemanticMatchUndetermined> {
        self.charge()?;
        graph.pending.clear();
        let root = root.0 as usize;
        if reverse {
            graph.vertices[root].to_equation = true;
        } else {
            graph.vertices[root].from_root = true;
        }
        graph.pending.push(root);
        while let Some(vertex) = graph.pending.pop() {
            self.charge()?;
            let mut next = if reverse {
                graph.vertices[vertex].reverse
            } else {
                graph.vertices[vertex].forward
            };
            while next != NO_EDGE {
                self.charge()?;
                let edge = &graph.edges[next];
                let target = if reverse { edge.source } else { edge.target };
                next = if reverse {
                    edge.next_reverse
                } else {
                    edge.next_forward
                };
                let visited = if reverse {
                    &mut graph.vertices[target].to_equation
                } else {
                    &mut graph.vertices[target].from_root
                };
                if !*visited {
                    *visited = true;
                    // Mark before insertion: at most one pending entry per
                    // sort, including self-loops and mutually recursive sorts.
                    graph.pending.push(target);
                }
            }
        }
        Ok(())
    }
}
