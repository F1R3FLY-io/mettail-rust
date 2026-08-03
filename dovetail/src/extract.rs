//! Exact, exhaustive-on-demand, best-first derivation enumeration over the
//! e-graph hypergraph (Huang & Chiang 2005, **Algorithm 3** — the EXACT lazy
//! algorithm, NOT the cube-pruning beam).
//!
//! ## Governing invariant — MISSES NOTHING
//! - Demand only DEFERS: [`Extractor::derivations`] is resumable to exhaustion;
//!   pulling far enough yields EVERY derivation of the root when the returned
//!   [`ExtractionCompleteness`] is [`Complete`](ExtractionCompleteness::Complete).
//! - The ONLY removal is by **evidence**: a derivation whose composed weight is
//!   the semiring zero (`0̄`) is excluded. Nothing is removed by weight, beam, or
//!   heuristic.
//! - Weight ORDERS the stream; it never PRUNES. Equal-weight DISTINCT derivations
//!   (distinct by exact [`ContentKey`]) BOTH survive, ordered by `(weight, key)`.
//! - An **admissible** heuristic ([`Extractor::with_heuristic`], A*/KA*) may
//!   guide exploration but never changes the result set or order.
//!
//! ## Monotonicity precondition (MON)
//! Best-first order relies on `⊗` being monotone non-decreasing in each argument
//! w.r.t. the [`BestOrder`]. Public extraction requires [`MonotoneBestOrder`] so
//! this precondition is a type-level contract, not just a doc comment.
//!
//! ## Cycles
//! Cyclic INSIDE weights / the 1-best are EXACT (Newton-SCC closed, via
//! [`Extractor::with_heuristic`] / `wta::compute_inside_closed`). Exhaustive
//! finite k-best ENUMERATION across productive back-edges is impossible in
//! general: a self-cycle with an acyclic exit has one distinct derivation for
//! every unrolling depth. Dovetail therefore cuts back-edges with a recursion
//! guard, remains safe (no infinite loop / no panic), returns the finite
//! acyclic evidence it found, and reports [`Extractor::had_cycle_cut`] /
//! [`ExtractionCompleteness::BoundedByCycleCut`] instead of claiming complete
//! cyclic exhaustion.

use crate::hash::{HashMap, HashSet};
use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::rc::Rc;

use rigail::Semiring;

use crate::egraph::{EClassId, EGraph, ENode};
use crate::key::{ContentKey, SemanticHash};

/// The best-first order on weights: `cmp_best(a, b) == Less` means `a` is the
/// BETTER (preferred-earlier) derivation weight — "smaller = better". Named
/// explicitly so it is distinct from any other `Ord` a weight may carry.
pub trait BestOrder: Semiring {
    fn cmp_best(&self, other: &Self) -> Ordering;
}

/// Any totally-ordered semiring whose `Ord` already means "smaller = better"
/// (`TropicalWeight`, `LexicographicWeight`) is a `BestOrder`.
impl<W: Semiring + Ord> BestOrder for W {
    #[inline]
    fn cmp_best(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}

mod sealed {
    pub trait Sealed {}

    impl Sealed for rigail::TropicalWeight {}
    impl Sealed for rigail::LexicographicWeight {}
}

/// Marker for weights whose `times` is monotone with respect to [`BestOrder`].
///
/// The lazy frontier proof depends on this property: increasing a child rank must
/// not produce a strictly better parent candidate. Implement this only for weight
/// types whose algebra has been checked against the extractor's ordering.
pub trait MonotoneBestOrder: BestOrder + sealed::Sealed {}

impl MonotoneBestOrder for rigail::TropicalWeight {}
impl MonotoneBestOrder for rigail::LexicographicWeight {}

/// Whether an extraction result is exhaustive or bounded by a detected cycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtractionCompleteness {
    /// No cycle guard fired; exhaustion means complete exhaustion.
    Complete,
    /// A back-edge was cut by the recursion guard, so cyclic unrollings were
    /// intentionally not enumerated.
    BoundedByCycleCut,
}

/// A value produced by extraction plus the completeness status of that run.
#[must_use = "extraction results carry completeness; inspect `completeness` before treating the value as exhaustive"]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extraction<T> {
    pub value: T,
    pub completeness: ExtractionCompleteness,
}

/// Backward-compatible spelling for checked extraction results.
pub type ExtractionResult<T> = Extraction<T>;

impl<T> Extraction<T> {
    fn new(value: T, completeness: ExtractionCompleteness) -> Self {
        Extraction { value, completeness }
    }
}

/// One checked step from a lazy derivation stream.
#[must_use = "the terminal step carries completeness; handle `Done` before treating the stream as exhaustive"]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtractionStep<T> {
    /// A concrete derivation is available.
    Item(T),
    /// The stream is exhausted under this completeness status.
    Done(ExtractionCompleteness),
}

/// A fully-chosen derivation tree of an e-class: the root operator, the chosen
/// child derivations (shared via `Rc`), the composed weight, and the exact,
/// injective [`ContentKey`] of the whole tree (equal key ⟺ identical tree).
pub struct Derivation<L, W> {
    pub op: L,
    pub class: EClassId,
    pub children: Vec<Rc<Derivation<L, W>>>,
    pub weight: W,
    pub key: ContentKey,
}

impl<L, W> Drop for Derivation<L, W> {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.children);
        while let Some(child) = pending.pop() {
            if let Ok(mut uniquely_owned) = Rc::try_unwrap(child) {
                pending.append(&mut uniquely_owned.children);
                // `uniquely_owned` now has no recursive children, so its own `Drop` is constant
                // stack. Shared children are merely decremented and will be drained by whichever
                // owner eventually becomes last.
            }
        }
    }
}

impl<L: std::fmt::Debug, W: std::fmt::Debug> std::fmt::Debug for Derivation<L, W> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a, L, W> {
            Node(&'a Derivation<L, W>),
            Separator,
            Tail(&'a Derivation<L, W>),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Node(node) => {
                    write!(
                        formatter,
                        "Derivation {{ op: {:?}, class: {:?}, children: [",
                        node.op, node.class,
                    )?;
                    tasks.push(Task::Tail(node));
                    for (index, child) in node.children.iter().enumerate().rev() {
                        tasks.push(Task::Node(child));
                        if index > 0 {
                            tasks.push(Task::Separator);
                        }
                    }
                },
                Task::Separator => formatter.write_str(", ")?,
                Task::Tail(node) => {
                    write!(formatter, "], weight: {:?}, key: {:?} }}", node.weight, node.key,)?
                },
            }
        }
        Ok(())
    }
}

/// Visit a derivation tree in root-first, left-to-right order without using the host call stack.
pub fn visit_derivation_preorder<L, W>(
    root: &Rc<Derivation<L, W>>,
    mut visit: impl FnMut(&Rc<Derivation<L, W>>),
) {
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        visit(node);
        for child in node.children.iter().rev() {
            pending.push(child);
        }
    }
}

/// Replace every selected subtree and rebuild its ancestors with an explicit post-order PDA.
///
/// Rebuilt nodes retain the source node's e-class as provenance while their exact key and
/// composed weight are recalculated from the replacement children. This is the step-graph
/// operation: the returned tree is consumed structurally by a reconstructor and is not inserted
/// back into the source e-graph.
pub fn splice_derivation_tree<L, W>(
    root: &Rc<Derivation<L, W>>,
    replacement: &Rc<Derivation<L, W>>,
    mut weigh: impl FnMut(&ENode<L>) -> W,
    mut replace: impl FnMut(&Derivation<L, W>) -> bool,
) -> Rc<Derivation<L, W>>
where
    L: Clone + SemanticHash,
    W: Semiring + Clone,
{
    enum SpliceTask<'a, L, W> {
        Visit(&'a Rc<Derivation<L, W>>),
        Assemble(&'a Rc<Derivation<L, W>>, usize),
    }

    let mut tasks = vec![SpliceTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            SpliceTask::Visit(node) => {
                if replace(node) {
                    values.push(Rc::clone(replacement));
                } else {
                    let arity = node.children.len();
                    tasks.push(SpliceTask::Assemble(node, arity));
                    for child in node.children.iter().rev() {
                        tasks.push(SpliceTask::Visit(child));
                    }
                }
            },
            SpliceTask::Assemble(node, arity) => {
                let first_child = values
                    .len()
                    .checked_sub(arity)
                    .expect("derivation splice PDA lost a child result");
                let children = values.split_off(first_child);
                let op = node.op.clone();
                let child_classes = children.iter().map(|child| child.class).collect();
                let mut weight = weigh(&ENode::new(op.clone(), child_classes));
                let mut key_children = Vec::with_capacity(children.len());
                for child in &children {
                    weight = weight.times(&child.weight);
                    key_children.push(child.key.clone());
                }
                let key = ContentKey::tree(&op, key_children);
                values.push(Rc::new(Derivation {
                    op,
                    class: node.class,
                    children,
                    weight,
                    key,
                }));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("derivation splice PDA produced no result")
}

/// A frontier candidate: the fully-built derivation for a hyperedge of a class at a
/// given per-child rank vector, plus the `(edge_idx, ranks)` that identify it.
///
/// The derivation is composed exactly once — when the candidate is CREATED in
/// the PDA's `Compose` continuation, which computes the full
/// `(op, w, key, children)` — and then reused by an `Rc::clone` when the candidate
/// is popped, so the pop path never recomposes (removing the former
/// `build_derivation` recompute, ~half of all `compose` calls). Heap order is best
/// weight first, then `ContentKey`, read directly off the derivation, so equal-weight
/// distinct derivations both survive in a deterministic order — byte-identical to the
/// former `OrdKey` order.
struct Candidate<L, W> {
    derivation: Rc<Derivation<L, W>>,
    edge_idx: usize,
    ranks: Vec<usize>,
}
impl<L, W: BestOrder> Ord for Candidate<L, W> {
    fn cmp(&self, o: &Self) -> Ordering {
        self.derivation
            .weight
            .cmp_best(&o.derivation.weight)
            .then_with(|| self.derivation.key.cmp(&o.derivation.key))
    }
}
impl<L, W: BestOrder> PartialOrd for Candidate<L, W> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl<L, W: BestOrder> PartialEq for Candidate<L, W> {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}
impl<L, W: BestOrder> Eq for Candidate<L, W> {}

struct ClassState<L, W> {
    initialized: bool,
    exhausted: bool,
    on_stack: bool,
    built: Vec<Rc<Derivation<L, W>>>,
    built_keys: HashSet<ContentKey>,
    cand: BinaryHeap<Reverse<Candidate<L, W>>>,
    pending_expansions: Vec<Candidate<L, W>>,
    seen: HashSet<(usize, Vec<usize>)>,
}

/// Explicit continuation algebra for [`Extractor::kth_raw`]. `Compose` is the recursive
/// call-site continuation from the former `compose -> kth_raw` SCC; the two `Accept*` frames
/// preserve the exact heap-insertion points of initialization and successor expansion.
enum KthTask<L, W> {
    Kth {
        class: EClassId,
        rank: usize,
    },
    Drive {
        class: EClassId,
        rank: usize,
    },
    EnsureInit {
        class: EClassId,
        next_edge: usize,
    },
    AcceptInitCandidate {
        class: EClassId,
    },
    ExpandCandidate {
        class: EClassId,
        candidate: Candidate<L, W>,
        next_child: usize,
    },
    AcceptSuccessorCandidate {
        class: EClassId,
    },
    Compose {
        class: EClassId,
        edge_idx: usize,
        ranks: Vec<usize>,
        child_classes: Vec<EClassId>,
        next_child: usize,
        awaiting_child: bool,
        op: L,
        weight: W,
        key_children: Vec<ContentKey>,
        children: Vec<Rc<Derivation<L, W>>>,
    },
}

enum UniqueDerivationTask {
    Visit(EClassId),
    Assemble(EClassId),
}
impl<L, W> Default for ClassState<L, W> {
    fn default() -> Self {
        ClassState {
            initialized: false,
            exhausted: false,
            on_stack: false,
            built: Vec::new(),
            built_keys: HashSet::default(),
            cand: BinaryHeap::new(),
            pending_expansions: Vec::new(),
            seen: HashSet::default(),
        }
    }
}

/// Exact lazy best-first derivation extractor over an e-graph weighted by a
/// `weigh` function.
pub struct Extractor<'g, L, W, F> {
    egraph: &'g EGraph<L>,
    weigh: F,
    state: HashMap<EClassId, ClassState<L, W>>,
    cycle_cut: bool,
    use_heuristic: bool,
    inside: Option<HashMap<EClassId, W>>,
}

impl<'g, L, W, F> Extractor<'g, L, W, F>
where
    L: Clone + Eq + std::hash::Hash + SemanticHash,
    W: MonotoneBestOrder,
    F: Fn(&ENode<L>) -> W,
{
    /// View `egraph` as a WTA weighted by `weigh` and prepare lazy extraction.
    pub fn new(egraph: &'g EGraph<L>, weigh: F) -> Self {
        Extractor {
            egraph,
            weigh,
            state: HashMap::default(),
            cycle_cut: false,
            use_heuristic: false,
            inside: None,
        }
    }

    /// Enable the admissible A*/KA* heuristic: memoize the EXACT (Newton-SCC
    /// closed, cyclic-correct) bottom-up 1-best inside weights and use them ONLY
    /// as a sound reachability skip (a class whose inside is `0̄` has no non-`0̄`
    /// derivation). This reorders/short-cuts exploration; it never changes the
    /// result set or order. Requires a commutative star semiring for the cyclic
    /// closure; `TropicalWeight` qualifies.
    pub fn with_heuristic(mut self) -> Self
    where
        W: crate::wta::CommutativeStarSemiring,
    {
        self.inside = Some(crate::wta::compute_inside_closed(self.egraph, &self.weigh));
        self.use_heuristic = true;
        self
    }

    /// True iff a back-edge was cut by the cycle guard (so finite enumeration
    /// for some class is bounded by a productive cyclic derivation space).
    /// Always false for acyclic inputs.
    pub fn had_cycle_cut(&self) -> bool {
        self.cycle_cut
    }

    /// Current completeness status for this extractor.
    pub fn completeness(&self) -> ExtractionCompleteness {
        if self.cycle_cut {
            ExtractionCompleteness::BoundedByCycleCut
        } else {
            ExtractionCompleteness::Complete
        }
    }

    /// The funded 1-best derivation of `root`, with completeness scoped to the
    /// selected derivation rather than to exhaustive enumeration of every
    /// cyclic expansion.
    ///
    /// This is the runtime-report contract for normal-form extraction. A
    /// productive cyclic class can have infinitely many expanded derivations, so
    /// [`Extractor::derivations`] must honestly report
    /// [`ExtractionCompleteness::BoundedByCycleCut`] for full-stream
    /// enumeration. For a funded runtime report, however, the question is
    /// narrower: did we emit a cycle-free derivation whose cost is the exact
    /// closed inside weight of the root class? If yes, the selected normal form
    /// is complete even when unchosen cyclic expansions were cut.
    pub fn funded_best(&mut self, root: EClassId) -> Extraction<Option<Rc<Derivation<L, W>>>>
    where
        W: crate::wta::CommutativeStarSemiring,
    {
        let q = self.egraph.find(root);
        if self.inside.is_none() {
            self.inside = Some(crate::wta::compute_inside_closed(self.egraph, &self.weigh));
        }

        let value = self.kth_raw(q, 0);
        let completeness = match &value {
            Some(derivation) if self.completeness() == ExtractionCompleteness::Complete => {
                let _ = derivation;
                ExtractionCompleteness::Complete
            },
            Some(derivation) if self.funded_derivation_is_certified(q, derivation) => {
                ExtractionCompleteness::Complete
            },
            _ => self.completeness(),
        };
        Extraction::new(value, completeness)
    }

    /// The k-th best (0-indexed) derivation of `root`, plus the current
    /// completeness status. `value == None` means no such derivation was found
    /// under the current completeness status.
    pub fn kth(&mut self, root: EClassId, k: usize) -> Extraction<Option<Rc<Derivation<L, W>>>> {
        let value = self.kth_raw(root, k);
        Extraction::new(value, self.completeness())
    }

    /// Build the only derivation of a structurally unique e-graph region in iterative postorder.
    /// Returns `None` when any reachable class has zero or multiple e-nodes. This is intended for
    /// diagnostics and unsaturated structural roundtrips; normal best-first extraction remains
    /// [`Self::funded_best`].
    pub fn unique_derivation(
        &mut self,
        root: EClassId,
    ) -> Extraction<Option<Rc<Derivation<L, W>>>> {
        let root = self.egraph.find(root);
        let mut tasks = vec![UniqueDerivationTask::Visit(root)];
        let mut values = Vec::<Rc<Derivation<L, W>>>::new();
        let mut memo = HashMap::<EClassId, Rc<Derivation<L, W>>>::default();
        let mut active = HashSet::<EClassId>::default();

        while let Some(task) = tasks.pop() {
            match task {
                UniqueDerivationTask::Visit(class) => {
                    let class = self.egraph.find(class);
                    if let Some(derivation) = memo.get(&class) {
                        values.push(Rc::clone(derivation));
                        continue;
                    }
                    if !active.insert(class) {
                        self.cycle_cut = true;
                        return Extraction::new(None, ExtractionCompleteness::BoundedByCycleCut);
                    }
                    let nodes = self.egraph.nodes(class);
                    if nodes.len() != 1 {
                        active.remove(&class);
                        return Extraction::new(None, self.completeness());
                    }
                    tasks.push(UniqueDerivationTask::Assemble(class));
                    for &child in nodes[0].children.iter().rev() {
                        tasks.push(UniqueDerivationTask::Visit(self.egraph.find(child)));
                    }
                },
                UniqueDerivationTask::Assemble(class) => {
                    let node = &self.egraph.nodes(class)[0];
                    let first = values
                        .len()
                        .checked_sub(node.children.len())
                        .expect("unique-derivation PDA lost a child result");
                    let children = values.split_off(first);
                    let op = node.op.clone();
                    let mut weight = (self.weigh)(node);
                    let mut key_children = Vec::with_capacity(children.len());
                    for child in &children {
                        weight = weight.times(&child.weight);
                        key_children.push(child.key.clone());
                    }
                    let key = ContentKey::tree(&op, key_children);
                    let derivation = Rc::new(Derivation { op, class, children, weight, key });
                    active.remove(&class);
                    memo.insert(class, Rc::clone(&derivation));
                    values.push(derivation);
                },
            }
        }

        let value = if values.len() == 1 {
            values.pop()
        } else {
            None
        };
        Extraction::new(value, self.completeness())
    }

    /// Internal raw k-th lookup used by composition. Public callers use [`Extractor::kth`] so
    /// cycle-cut boundedness is not silently lost.
    ///
    /// This is an explicit PDA for the former `kth_raw -> ensure_init/make_candidate -> compose
    /// -> kth_raw` mutually-recursive SCC. The task order is the recursive DFS order: initialize
    /// edges in declaration order, compose children left-to-right, then expand successor ranks
    /// left-to-right. Consequently candidate/key order and first cycle-cut behavior are unchanged.
    fn kth_raw(&mut self, root: EClassId, k: usize) -> Option<Rc<Derivation<L, W>>> {
        let mut tasks = vec![KthTask::Kth { class: self.egraph.find(root), rank: k }];
        let mut derivation_result: Option<Option<Rc<Derivation<L, W>>>> = None;
        let mut candidate_result: Option<Option<Candidate<L, W>>> = None;

        while let Some(task) = tasks.pop() {
            match task {
                KthTask::Kth { class, rank } => {
                    let class = self.egraph.find(class);
                    if self.state.get(&class).is_some_and(|state| state.on_stack) {
                        self.cycle_cut = true;
                        derivation_result = Some(None);
                        continue;
                    }
                    if let Some(found) = self
                        .state
                        .get(&class)
                        .and_then(|state| state.built.get(rank).cloned())
                    {
                        derivation_result = Some(Some(found));
                        continue;
                    }
                    if self.state.get(&class).is_some_and(|state| state.exhausted)
                        || (self.use_heuristic
                            && self.inside.as_ref().is_some_and(|inside| {
                                inside.get(&class).copied().is_some_and(|w| w.is_zero())
                            }))
                    {
                        derivation_result = Some(None);
                        continue;
                    }

                    self.state.entry(class).or_default().on_stack = true;
                    tasks.push(KthTask::Drive { class, rank });
                    tasks.push(KthTask::EnsureInit { class, next_edge: 0 });
                },
                KthTask::EnsureInit { class, next_edge } => {
                    if next_edge == 0 {
                        if self
                            .state
                            .get(&class)
                            .is_some_and(|state| state.initialized)
                        {
                            continue;
                        }
                        self.state.entry(class).or_default().initialized = true;
                    }
                    let edge_count = self.egraph.nodes(class).len();
                    if next_edge >= edge_count {
                        continue;
                    }

                    tasks.push(KthTask::EnsureInit { class, next_edge: next_edge + 1 });
                    let arity = self.egraph.nodes(class)[next_edge].children.len();
                    let ranks = vec![0usize; arity];
                    let fresh = self
                        .state
                        .get_mut(&class)
                        .expect("class state present")
                        .seen
                        .insert((next_edge, ranks.clone()));
                    if fresh {
                        tasks.push(KthTask::AcceptInitCandidate { class });
                        tasks.push(self.compose_task(class, next_edge, ranks));
                    }
                },
                KthTask::AcceptInitCandidate { class } => {
                    if let Some(candidate) = candidate_result
                        .take()
                        .expect("compose task must produce an initialization candidate")
                    {
                        self.state
                            .get_mut(&class)
                            .expect("class state present")
                            .cand
                            .push(Reverse(candidate));
                    }
                },
                KthTask::Drive { class, rank } => {
                    if self.state.get(&class).map_or(0, |state| state.built.len()) > rank {
                        self.state
                            .get_mut(&class)
                            .expect("class state present")
                            .on_stack = false;
                        derivation_result = Some(
                            self.state
                                .get(&class)
                                .and_then(|state| state.built.get(rank).cloned()),
                        );
                        continue;
                    }

                    if let Some(candidate) = self
                        .state
                        .get_mut(&class)
                        .expect("class state present")
                        .pending_expansions
                        .pop()
                    {
                        tasks.push(KthTask::Drive { class, rank });
                        tasks.push(KthTask::ExpandCandidate { class, candidate, next_child: 0 });
                        continue;
                    }

                    let popped = self
                        .state
                        .get_mut(&class)
                        .expect("class state present")
                        .cand
                        .pop();
                    let Some(Reverse(candidate)) = popped else {
                        let state = self.state.get_mut(&class).expect("class state present");
                        state.exhausted = true;
                        state.on_stack = false;
                        derivation_result = Some(state.built.get(rank).cloned());
                        continue;
                    };
                    let built = Rc::clone(&candidate.derivation);
                    if !built.weight.is_zero() {
                        let state = self.state.get_mut(&class).expect("class state present");
                        if state.built_keys.insert(built.key.clone()) {
                            state.built.push(built);
                        }
                    }
                    self.state
                        .get_mut(&class)
                        .expect("class state present")
                        .pending_expansions
                        .push(candidate);
                    tasks.push(KthTask::Drive { class, rank });
                },
                KthTask::ExpandCandidate { class, candidate, next_child } => {
                    if next_child >= candidate.ranks.len() {
                        continue;
                    }

                    let mut ranks = candidate.ranks.clone();
                    ranks[next_child] += 1;
                    let fresh = self
                        .state
                        .get_mut(&class)
                        .expect("class state present")
                        .seen
                        .insert((candidate.edge_idx, ranks.clone()));
                    let edge_idx = candidate.edge_idx;
                    tasks.push(KthTask::ExpandCandidate {
                        class,
                        candidate,
                        next_child: next_child + 1,
                    });
                    if fresh {
                        tasks.push(KthTask::AcceptSuccessorCandidate { class });
                        tasks.push(self.compose_task(class, edge_idx, ranks));
                    }
                },
                KthTask::AcceptSuccessorCandidate { class } => {
                    if let Some(candidate) = candidate_result
                        .take()
                        .expect("compose task must produce a successor candidate")
                    {
                        self.state
                            .get_mut(&class)
                            .expect("class state present")
                            .cand
                            .push(Reverse(candidate));
                    }
                },
                KthTask::Compose {
                    class,
                    edge_idx,
                    ranks,
                    child_classes,
                    mut next_child,
                    awaiting_child,
                    op,
                    mut weight,
                    mut key_children,
                    mut children,
                } => {
                    if awaiting_child {
                        let Some(child) = derivation_result
                            .take()
                            .expect("child kth task must produce a derivation result")
                        else {
                            candidate_result = Some(None);
                            continue;
                        };
                        weight = weight.times(&child.weight);
                        key_children.push(child.key.clone());
                        children.push(child);
                        next_child += 1;
                    }

                    if next_child < child_classes.len() {
                        let child_class = child_classes[next_child];
                        let child_rank = ranks[next_child];
                        tasks.push(KthTask::Compose {
                            class,
                            edge_idx,
                            ranks,
                            child_classes,
                            next_child,
                            awaiting_child: true,
                            op,
                            weight,
                            key_children,
                            children,
                        });
                        tasks.push(KthTask::Kth { class: child_class, rank: child_rank });
                    } else {
                        let key = ContentKey::tree(&op, key_children);
                        let derivation = Rc::new(Derivation { op, class, children, weight, key });
                        candidate_result = Some(Some(Candidate { derivation, edge_idx, ranks }));
                    }
                },
            }
        }

        derivation_result.expect("top-level kth task must produce a derivation result")
    }

    /// A lazy, best-first derivation stream over `root`.
    ///
    /// Use [`Derivations::next_checked`] or [`Derivations::collect_checked`] so
    /// the terminal completeness status is observed.
    pub fn derivations(&mut self, root: EClassId) -> Derivations<'_, 'g, L, W, F> {
        Derivations {
            extractor: self,
            root,
            next_k: 0,
            done: false,
        }
    }

    // --- internals ---------------------------------------------------------

    /// Materialize the non-recursive prefix of candidate composition and return its continuation.
    fn compose_task(&self, class: EClassId, edge_idx: usize, ranks: Vec<usize>) -> KthTask<L, W> {
        let node = &self.egraph.nodes(class)[edge_idx];
        let op = node.op.clone();
        let weight = (self.weigh)(node);
        let child_classes = node
            .children
            .iter()
            .map(|&child| self.egraph.find(child))
            .collect::<Vec<_>>();
        KthTask::Compose {
            class,
            edge_idx,
            ranks,
            child_classes,
            next_child: 0,
            awaiting_child: false,
            op,
            weight,
            key_children: Vec::with_capacity(node.children.len()),
            children: Vec::with_capacity(node.children.len()),
        }
    }

    fn funded_derivation_is_certified(
        &self,
        root: EClassId,
        derivation: &Rc<Derivation<L, W>>,
    ) -> bool {
        let Some(inside) = &self.inside else {
            return false;
        };
        let Some(closed_weight) = inside.get(&root) else {
            return false;
        };
        derivation.weight == *closed_weight && !derivation_has_class_cycle(derivation)
    }
}

fn derivation_has_class_cycle<L, W>(root: &Rc<Derivation<L, W>>) -> bool {
    enum Frame<L, W> {
        Enter(Rc<Derivation<L, W>>),
        Exit(EClassId),
    }

    let mut active = HashSet::default();
    let mut stack = vec![Frame::Enter(root.clone())];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Enter(derivation) => {
                if !active.insert(derivation.class) {
                    return true;
                }
                stack.push(Frame::Exit(derivation.class));
                for child in derivation.children.iter().rev() {
                    stack.push(Frame::Enter(child.clone()));
                }
            },
            Frame::Exit(class) => {
                active.remove(&class);
            },
        }
    }
    false
}

/// Lazy derivation stream with explicit checked stepping.
#[must_use = "derivation streams carry terminal completeness; call `next_checked` or `collect_checked`"]
pub struct Derivations<'a, 'g, L, W, F>
where
    L: Clone + Eq + std::hash::Hash + SemanticHash,
    W: MonotoneBestOrder,
    F: Fn(&ENode<L>) -> W,
{
    extractor: &'a mut Extractor<'g, L, W, F>,
    root: EClassId,
    next_k: usize,
    done: bool,
}

impl<'a, 'g, L, W, F> Derivations<'a, 'g, L, W, F>
where
    L: Clone + Eq + std::hash::Hash + SemanticHash,
    W: MonotoneBestOrder,
    F: Fn(&ENode<L>) -> W,
{
    /// Return the next stream item or the terminal completeness status.
    pub fn next_checked(&mut self) -> ExtractionStep<Rc<Derivation<L, W>>> {
        if self.done {
            return ExtractionStep::Done(self.extractor.completeness());
        }
        match self.extractor.kth_raw(self.root, self.next_k) {
            Some(derivation) => {
                self.next_k += 1;
                ExtractionStep::Item(derivation)
            },
            None => {
                self.done = true;
                ExtractionStep::Done(self.extractor.completeness())
            },
        }
    }

    /// Collect every derivation reachable under this stream and return the
    /// terminal completeness status alongside the vector.
    pub fn collect_checked(mut self) -> Extraction<Vec<Rc<Derivation<L, W>>>> {
        let mut value = Vec::new();
        loop {
            match self.next_checked() {
                ExtractionStep::Item(derivation) => value.push(derivation),
                ExtractionStep::Done(completeness) => return Extraction::new(value, completeness),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rigail::TropicalWeight;

    fn prim(w: TropicalWeight) -> f64 {
        w.0
    }

    /// Weigh helper: a leaf op "Nn"/letter maps to its numeric weight; structural
    /// ops to a small cost.
    fn weigh(n: &ENode<String>) -> TropicalWeight {
        match n.op.as_str() {
            "a" => TropicalWeight(5.0),
            "b" => TropicalWeight(3.0),
            "c" => TropicalWeight(3.0),
            "x" => TropicalWeight(1.0),
            "x2" => TropicalWeight(4.0),
            "y" => TropicalWeight(2.0),
            "r" => TropicalWeight(2.0),
            "dead" => TropicalWeight(f64::INFINITY), // 0̄
            "add" => TropicalWeight(1.0),
            "mul" => TropicalWeight(1.0),
            "f" => TropicalWeight(1.0),
            _ => TropicalWeight(0.0),
        }
    }

    #[test]
    fn t1_single_leaf() {
        let mut eg = EGraph::<String>::new();
        let l = eg.add(ENode::leaf("b".into()));
        let mut ex = Extractor::new(&eg, weigh);
        let d0 = ex.kth(l, 0).value.expect("one derivation");
        assert_eq!(prim(d0.weight), 3.0);
        assert!(ex.kth(l, 1).value.is_none());
        let mut ex2 = Extractor::new(&eg, weigh);
        let all = ex2.derivations(l).collect_checked();
        assert_eq!(all.completeness, ExtractionCompleteness::Complete);
        assert_eq!(all.value.len(), 1);
    }

    #[test]
    fn deep_unique_derivation_and_lifecycle_are_stack_safe() {
        let depth = 16_384usize;
        let mut eg = EGraph::<String>::new();
        let mut root = eg.add(ENode::leaf("b".into()));
        for _ in 0..depth {
            root = eg.add(ENode::new("f".into(), vec![root]));
        }

        let mut extractor = Extractor::new(&eg, weigh);
        let extraction = extractor.unique_derivation(root);
        assert_eq!(extraction.completeness, ExtractionCompleteness::Complete);
        let mut cursor = extraction.value.expect("unique deep derivation");
        let mut measured = 0usize;
        while let Some(child) = cursor.children.first() {
            measured += 1;
            cursor = child.clone();
        }
        assert_eq!(measured, depth);
    }

    #[test]
    fn deep_kth_pda_and_persistent_keys_are_stack_safe() {
        let depth = 16_384usize;
        let mut eg = EGraph::<String>::new();
        let mut root = eg.add(ENode::leaf("b".into()));
        for _ in 0..depth {
            root = eg.add(ENode::new("f".into(), vec![root]));
        }

        let mut extractor = Extractor::new(&eg, weigh);
        let derivation = extractor
            .kth(root, 0)
            .value
            .expect("deep 1-best derivation");
        assert!(derivation.key.len() > depth);
        assert!(extractor.kth(root, 1).value.is_none());
    }

    #[test]
    fn deep_derivation_splice_and_preorder_visit_are_stack_safe() {
        let depth = 16_384usize;
        let mut eg = EGraph::<String>::new();
        let leaf = eg.add(ENode::leaf("b".into()));
        let replacement_leaf = eg.add(ENode::leaf("x".into()));
        let mut root = leaf;
        for _ in 0..depth {
            root = eg.add(ENode::new("f".into(), vec![root]));
        }

        let mut extractor = Extractor::new(&eg, weigh);
        let original = extractor
            .unique_derivation(root)
            .value
            .expect("deep source derivation");
        let replacement = extractor
            .unique_derivation(replacement_leaf)
            .value
            .expect("replacement derivation");
        let spliced =
            splice_derivation_tree(&original, &replacement, weigh, |node| node.class == leaf);

        let mut visited = 0usize;
        let mut last_op = None;
        visit_derivation_preorder(&spliced, |node| {
            visited += 1;
            last_op = Some(node.op.clone());
        });
        assert_eq!(visited, depth + 1);
        assert_eq!(last_op.as_deref(), Some("x"));
        assert_ne!(spliced.key, original.key);
    }

    #[test]
    fn checked_stream_reports_terminal_completeness() {
        let mut eg = EGraph::<String>::new();
        let l = eg.add(ENode::leaf("b".into()));
        let mut ex = Extractor::new(&eg, weigh);
        let mut stream = ex.derivations(l);

        match stream.next_checked() {
            ExtractionStep::Item(d) => assert_eq!(prim(d.weight), 3.0),
            ExtractionStep::Done(status) => panic!("unexpected terminal status {status:?}"),
        }
        assert!(matches!(
            stream.next_checked(),
            ExtractionStep::Done(ExtractionCompleteness::Complete)
        ));
        assert!(
            matches!(stream.next_checked(), ExtractionStep::Done(ExtractionCompleteness::Complete)),
            "terminal status remains available after exhaustion"
        );
    }

    #[test]
    fn t2_ambiguous_hand_built_no_miss() {
        // a(5), b(3), c(3) merged into one class ⇒ 3 derivations.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let c = eg.add(ENode::leaf("c".into()));
        eg.merge(a, b);
        eg.merge(b, c);
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh);
        let collected = ex.derivations(a).collect_checked();
        assert_eq!(collected.completeness, ExtractionCompleteness::Complete);
        let ds = collected.value;
        let ws: Vec<f64> = ds.iter().map(|d| prim(d.weight)).collect();
        assert_eq!(ws, vec![3.0, 3.0, 5.0], "non-decreasing; both w=3 present, then w=5");
        assert_ne!(ds[0].key, ds[1].key, "the two w=3 derivations are distinct (no merge)");
        assert!(ex.kth(a, 3).value.is_none(), "exactly 3 — exhaustion terminates");
    }

    #[test]
    fn t3_cartesian_product_no_miss() {
        // s has two edges add(x,y) and mul(x,y); x is ambiguous {x@1, x2@4}; y@2.
        let mut eg = EGraph::<String>::new();
        let x = eg.add(ENode::leaf("x".into()));
        let x2 = eg.add(ENode::leaf("x2".into()));
        eg.merge(x, x2);
        eg.rebuild();
        let y = eg.add(ENode::leaf("y".into()));
        let xq = eg.find(x);
        let add = eg.add(ENode::new("add".into(), vec![xq, y]));
        let mul = eg.add(ENode::new("mul".into(), vec![xq, y]));
        eg.merge(add, mul);
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh);
        let collected = ex.derivations(eg.find(add)).collect_checked();
        assert_eq!(collected.completeness, ExtractionCompleteness::Complete);
        let ds = collected.value;
        let ws: Vec<f64> = ds.iter().map(|d| prim(d.weight)).collect();
        // add/mul (1) ⊗ x(1 or 4) ⊗ y(2): {1+1+2, 1+1+2, 1+4+2, 1+4+2} = [4,4,7,7]
        assert_eq!(ws, vec![4.0, 4.0, 7.0, 7.0]);
        let keys: HashSet<_> = ds.iter().map(|d| d.key.clone()).collect();
        assert_eq!(keys.len(), 4, "all four derivations distinct, none missed");
        assert!(ex.kth(eg.find(add), 4).value.is_none());
    }

    #[test]
    fn t4_zero_weight_excluded() {
        // dead(0̄) merged with r(2): only r survives; 0̄ excluded.
        let mut eg = EGraph::<String>::new();
        let dead = eg.add(ENode::leaf("dead".into()));
        let r = eg.add(ENode::leaf("r".into()));
        eg.merge(dead, r);
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh);
        let collected = ex.derivations(r).collect_checked();
        assert_eq!(collected.completeness, ExtractionCompleteness::Complete);
        let ds = collected.value;
        assert_eq!(ds.len(), 1, "the 0̄ derivation is excluded");
        assert_eq!(prim(ds[0].weight), 2.0);
        // 0̄ child poisons parent: f(dead) composed = 1 + inf = inf = 0̄ ⟹ excluded.
        let mut eg2 = EGraph::<String>::new();
        let d2 = eg2.add(ENode::leaf("dead".into()));
        let fd = eg2.add(ENode::new("f".into(), vec![d2]));
        let mut ex2 = Extractor::new(&eg2, weigh);
        assert!(ex2.kth(fd, 0).value.is_none(), "0̄-child poisons parent ⟹ excluded");
    }

    #[test]
    fn t5_resumable_and_idempotent_past_exhaustion() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        eg.merge(a, b);
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh);
        // random-access + memo consistency: pull 1, then 0, then 2(None).
        let d1 = ex.kth(a, 1).value.expect("2nd best exists");
        assert_eq!(prim(d1.weight), 5.0);
        let d0 = ex.kth(a, 0).value.expect("memoized 1st best");
        assert_eq!(prim(d0.weight), 3.0);
        assert!(ex.kth(a, 2).value.is_none());
        assert!(ex.kth(a, 2).value.is_none(), "idempotent past exhaustion, no panic");
    }

    #[test]
    fn t7_determinism() {
        let build = || {
            let mut eg = EGraph::<String>::new();
            let a = eg.add(ENode::leaf("a".into()));
            let b = eg.add(ENode::leaf("b".into()));
            let c = eg.add(ENode::leaf("c".into()));
            eg.merge(a, b);
            eg.merge(b, c);
            eg.rebuild();
            let q = eg.find(a);
            (eg, q)
        };
        let (eg1, q1) = build();
        let mut e1 = Extractor::new(&eg1, weigh);
        let d1 = e1.derivations(q1).collect_checked();
        assert_eq!(d1.completeness, ExtractionCompleteness::Complete);
        let k1: Vec<_> = d1.value.iter().map(|d| d.key.clone()).collect();
        let (eg2, q2) = build();
        let mut e2 = Extractor::new(&eg2, weigh);
        let d2 = e2.derivations(q2).collect_checked();
        assert_eq!(d2.completeness, ExtractionCompleteness::Complete);
        let k2: Vec<_> = d2.value.iter().map(|d| d.key.clone()).collect();
        assert_eq!(k1, k2, "deterministic key sequence");
    }

    #[test]
    fn t9_heuristic_invariance() {
        let build = || {
            let mut eg = EGraph::<String>::new();
            let x = eg.add(ENode::leaf("x".into()));
            let x2 = eg.add(ENode::leaf("x2".into()));
            eg.merge(x, x2);
            eg.rebuild();
            let y = eg.add(ENode::leaf("y".into()));
            let xq = eg.find(x);
            let add = eg.add(ENode::new("add".into(), vec![xq, y]));
            let mul = eg.add(ENode::new("mul".into(), vec![xq, y]));
            eg.merge(add, mul);
            eg.rebuild();
            (eg, add)
        };
        let (eg1, add1) = build();
        let mut plain = Extractor::new(&eg1, weigh);
        let plain_collected = plain.derivations(eg1.find(add1)).collect_checked();
        assert_eq!(plain_collected.completeness, ExtractionCompleteness::Complete);
        let a: Vec<_> = plain_collected
            .value
            .iter()
            .map(|d| (prim(d.weight), d.key.clone()))
            .collect();
        let (eg2, add2) = build();
        let mut heur = Extractor::new(&eg2, weigh).with_heuristic();
        let heur_collected = heur.derivations(eg2.find(add2)).collect_checked();
        assert_eq!(heur_collected.completeness, ExtractionCompleteness::Complete);
        let b: Vec<_> = heur_collected
            .value
            .iter()
            .map(|d| (prim(d.weight), d.key.clone()))
            .collect();
        assert_eq!(a, b, "heuristic must not change result set or order");
    }

    #[test]
    fn t6_lexicographic_tiebreak() {
        use rigail::LexicographicWeight as Lw;
        // p and q have EQUAL primary (1.0) but different src_idx (0 vs 1).
        fn weigh_lex(n: &ENode<String>) -> Lw {
            match n.op.as_str() {
                "p" => Lw::from_cost(1.0, 0, 0),
                "q" => Lw::from_cost(1.0, 1, 0),
                _ => Lw::from_cost(0.0, 0, 0),
            }
        }
        let mut eg = EGraph::<String>::new();
        let p = eg.add(ENode::leaf("p".into()));
        let q = eg.add(ENode::leaf("q".into()));
        eg.merge(p, q);
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh_lex);
        let collected = ex.derivations(eg.find(p)).collect_checked();
        assert_eq!(collected.completeness, ExtractionCompleteness::Complete);
        let ds = collected.value;
        assert_eq!(ds.len(), 2, "both equal-primary alternatives survive");
        // Full lex order: equal primary -> equal lex_alt -> src_idx: p(0) before q(1).
        assert_eq!(ds[0].op, "p");
        assert_eq!(ds[1].op, "q");
    }

    #[test]
    fn t8_cycle_safety_terminates_and_cuts() {
        // P = { leaf "base", g(P) } — a self-cycle. Extraction must TERMINATE,
        // yield the acyclic derivation, and report the back-edge cut (the
        // documented bounded-by-cycle-cut contract for finitely reported
        // evidence through productive cycles).
        let mut eg = EGraph::<String>::new();
        let base = eg.add(ENode::leaf("base".into()));
        let g = eg.add(ENode::new("g".into(), vec![base]));
        eg.merge(base, g); // class P; g's child canonicalizes to P => g(P) in P
        eg.rebuild();
        let mut ex = Extractor::new(&eg, weigh);
        let collected = ex.derivations(eg.find(base)).collect_checked(); // must terminate
        assert_eq!(collected.completeness, ExtractionCompleteness::BoundedByCycleCut);
        let ds = collected.value;
        assert!(ds.iter().any(|d| d.op == "base"), "acyclic base derivation present");
        assert!(ex.had_cycle_cut(), "the g(P) back-edge was cut");
    }

    #[test]
    fn funded_best_certifies_unchosen_self_referential_expansion() {
        // P = value | f(P). Full enumeration is bounded because f can unroll
        // forever, but the selected funded normal form is the cycle-free value
        // and its cost is the closed inside weight for P.
        let mut eg = EGraph::<String>::new();
        let value = eg.add(ENode::leaf("x".into()));
        let f = eg.add(ENode::new("f".into(), vec![value]));
        eg.merge(value, f);
        eg.rebuild();
        let p = eg.find(value);

        let mut stream_ex = Extractor::new(&eg, weigh);
        let stream = stream_ex.derivations(p).collect_checked();
        assert_eq!(stream.completeness, ExtractionCompleteness::BoundedByCycleCut);

        let mut funded_ex = Extractor::new(&eg, weigh);
        let best = funded_ex.funded_best(p);
        assert_eq!(best.completeness, ExtractionCompleteness::Complete);
        assert_eq!(best.value.expect("funded best exists").op, "x");
        assert!(
            funded_ex.had_cycle_cut(),
            "the complete funded result may still observe unchosen cyclic expansions"
        );
    }

    #[test]
    fn funded_best_certifies_fold_result_equal_to_operand() {
        // Generic shape of idempotent/native folds like 0 + 0 = 0 and -0 = 0:
        // the result value is congruence-merged with a fold operand, so the
        // retained fold redex points back at its own class.
        let mut eg = EGraph::<String>::new();
        let value = eg.add(ENode::leaf("x".into()));
        let fold = eg.add(ENode::new("fold".into(), vec![value, value]));
        eg.merge(value, fold);
        eg.rebuild();
        let p = eg.find(value);

        let mut stream_ex = Extractor::new(&eg, weigh);
        assert_eq!(
            stream_ex.derivations(p).collect_checked().completeness,
            ExtractionCompleteness::BoundedByCycleCut
        );

        let mut funded_ex = Extractor::new(&eg, weigh);
        let best = funded_ex.funded_best(p);
        assert_eq!(best.completeness, ExtractionCompleteness::Complete);
        assert_eq!(best.value.expect("funded best exists").op, "x");
    }

    #[test]
    fn t10_cyclic_1best_equals_newton_inside() {
        // P = a(5) | f(P). The extractor's 1-best (acyclic; the back-edge is cut)
        // equals the Newton-closed inside weight (Increment 6).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let f = eg.add(ENode::new("f".into(), vec![a]));
        eg.merge(a, f);
        eg.rebuild();
        let p = eg.find(a);
        let inside = crate::wta::compute_inside_closed(&eg, &weigh);
        let mut ex = Extractor::new(&eg, weigh).with_heuristic();
        let d0_result = ex.kth(p, 0);
        assert_eq!(d0_result.completeness, ExtractionCompleteness::BoundedByCycleCut);
        let d0 = d0_result.value.expect("a 1-best exists");
        assert_eq!(prim(d0.weight), 5.0);
        assert_eq!(d0.weight, inside[&p], "extractor 1-best == Newton-closed inside");

        let mut funded = Extractor::new(&eg, weigh);
        let funded_result = funded.funded_best(p);
        assert_eq!(funded_result.completeness, ExtractionCompleteness::Complete);
    }

    #[test]
    fn t11_cyclic_heuristic_invariance() {
        let build = || {
            let mut eg = EGraph::<String>::new();
            let a = eg.add(ENode::leaf("a".into()));
            let f = eg.add(ENode::new("f".into(), vec![a]));
            eg.merge(a, f);
            eg.rebuild();
            let p = eg.find(a);
            (eg, p)
        };
        let (eg1, p1) = build();
        let mut plain = Extractor::new(&eg1, weigh);
        let plain_collected = plain.derivations(p1).collect_checked();
        assert_eq!(plain_collected.completeness, ExtractionCompleteness::BoundedByCycleCut);
        let av: Vec<_> = plain_collected
            .value
            .iter()
            .map(|d| (prim(d.weight), d.key.clone()))
            .collect();
        let (eg2, p2) = build();
        let mut heur = Extractor::new(&eg2, weigh).with_heuristic();
        let heur_collected = heur.derivations(p2).collect_checked();
        assert_eq!(heur_collected.completeness, ExtractionCompleteness::BoundedByCycleCut);
        let bv: Vec<_> = heur_collected
            .value
            .iter()
            .map(|d| (prim(d.weight), d.key.clone()))
            .collect();
        assert_eq!(av, bv, "cyclic heuristic invariance (closed inside doesn't change results)");
    }
}
