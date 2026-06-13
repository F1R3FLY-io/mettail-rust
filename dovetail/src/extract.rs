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

use std::cmp::{Ordering, Reverse};
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::rc::Rc;

use rigail::Semiring;

use crate::egraph::{EClassId, EGraph, ENode};
use crate::key::{write_ordered_framed, ContentKey, SemanticHash};

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
#[derive(Debug)]
pub struct Derivation<L, W> {
    pub op: L,
    pub class: EClassId,
    pub children: Vec<Rc<Derivation<L, W>>>,
    pub weight: W,
    pub key: ContentKey,
}

/// Total heap order: best weight first, then `ContentKey` (so equal-weight
/// distinct derivations both survive in a deterministic order).
struct OrdKey<W> {
    w: W,
    key: ContentKey,
}
impl<W: BestOrder> Ord for OrdKey<W> {
    fn cmp(&self, o: &Self) -> Ordering {
        self.w.cmp_best(&o.w).then_with(|| self.key.cmp(&o.key))
    }
}
impl<W: BestOrder> PartialOrd for OrdKey<W> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl<W: BestOrder> PartialEq for OrdKey<W> {
    fn eq(&self, o: &Self) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}
impl<W: BestOrder> Eq for OrdKey<W> {}

/// A frontier candidate: a hyperedge of a class + a per-child rank vector.
struct Candidate<W> {
    ord: OrdKey<W>,
    edge_idx: usize,
    ranks: Vec<usize>,
}
impl<W: BestOrder> Ord for Candidate<W> {
    fn cmp(&self, o: &Self) -> Ordering {
        self.ord.cmp(&o.ord)
    }
}
impl<W: BestOrder> PartialOrd for Candidate<W> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl<W: BestOrder> PartialEq for Candidate<W> {
    fn eq(&self, o: &Self) -> bool {
        self.ord == o.ord
    }
}
impl<W: BestOrder> Eq for Candidate<W> {}

struct ClassState<L, W> {
    initialized: bool,
    exhausted: bool,
    on_stack: bool,
    built: Vec<Rc<Derivation<L, W>>>,
    built_keys: HashSet<ContentKey>,
    cand: BinaryHeap<Reverse<Candidate<W>>>,
    seen: HashSet<(usize, Vec<usize>)>,
}
impl<L, W> Default for ClassState<L, W> {
    fn default() -> Self {
        ClassState {
            initialized: false,
            exhausted: false,
            on_stack: false,
            built: Vec::new(),
            built_keys: HashSet::new(),
            cand: BinaryHeap::new(),
            seen: HashSet::new(),
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
            state: HashMap::new(),
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

    /// The k-th best (0-indexed) derivation of `root`, plus the current
    /// completeness status. `value == None` means no such derivation was found
    /// under the current completeness status.
    pub fn kth(&mut self, root: EClassId, k: usize) -> Extraction<Option<Rc<Derivation<L, W>>>> {
        let value = self.kth_raw(root, k);
        Extraction::new(value, self.completeness())
    }

    /// Internal raw k-th lookup used by recursive composition. Public callers use
    /// [`Extractor::kth`] so cycle-cut boundedness is not silently lost.
    fn kth_raw(&mut self, root: EClassId, k: usize) -> Option<Rc<Derivation<L, W>>> {
        let q = self.egraph.find(root);

        // Cyclic re-entry: this class is already being computed on the stack.
        if self.state.get(&q).is_some_and(|s| s.on_stack) {
            self.cycle_cut = true;
            return None;
        }
        // Fast memoized path.
        if let Some(d) = self.state.get(&q).and_then(|s| s.built.get(k).cloned()) {
            return Some(d);
        }
        if self.state.get(&q).is_some_and(|s| s.exhausted) {
            return None;
        }
        // Admissible reachability skip (no result change: a 0̄-inside class has
        // no non-0̄ derivation anyway).
        if self.use_heuristic {
            if let Some(inside) = &self.inside {
                if inside.get(&q).copied().is_some_and(|w| w.is_zero()) {
                    return None;
                }
            }
        }

        self.state.entry(q).or_default().on_stack = true;
        self.ensure_init(q);

        while self.state.get(&q).map_or(0, |s| s.built.len()) <= k {
            let popped = {
                let st = self.state.get_mut(&q).expect("class state present");
                st.cand.pop()
            };
            let cand = match popped {
                Some(Reverse(c)) => c,
                None => {
                    self.state
                        .get_mut(&q)
                        .expect("class state present")
                        .exhausted = true;
                    break;
                },
            };

            let built_d = self.build_derivation(q, cand.edge_idx, &cand.ranks);

            // Push successors that bump exactly one child's rank (always — never
            // close the lattice on a zero/duplicate).
            for i in 0..cand.ranks.len() {
                let mut r = cand.ranks.clone();
                r[i] += 1;
                let fresh = self
                    .state
                    .get_mut(&q)
                    .expect("class state present")
                    .seen
                    .insert((cand.edge_idx, r.clone()));
                if fresh {
                    if let Some(c2) = self.make_candidate(q, cand.edge_idx, r) {
                        self.state
                            .get_mut(&q)
                            .expect("class state present")
                            .cand
                            .push(Reverse(c2));
                    }
                }
            }

            // Append iff non-`0̄` and key-fresh (the only removal is `0̄`; the
            // key-fresh check drops only genuinely identical trees).
            if let Some(d) = built_d {
                if !d.weight.is_zero() {
                    let st = self.state.get_mut(&q).expect("class state present");
                    if st.built_keys.insert(d.key.clone()) {
                        st.built.push(d);
                    }
                }
            }
        }

        self.state
            .get_mut(&q)
            .expect("class state present")
            .on_stack = false;
        self.state.get(&q).and_then(|s| s.built.get(k).cloned())
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

    /// Seed a class's candidate heap with the zero-rank candidate of each edge.
    fn ensure_init(&mut self, q: EClassId) {
        if self.state.get(&q).is_some_and(|s| s.initialized) {
            return;
        }
        self.state.entry(q).or_default().initialized = true;
        let eg = self.egraph;
        let n_edges = eg.nodes(q).len();
        for edge_idx in 0..n_edges {
            let arity = eg.nodes(q)[edge_idx].children.len();
            let ranks = vec![0usize; arity];
            let fresh = self
                .state
                .get_mut(&q)
                .expect("class state present")
                .seen
                .insert((edge_idx, ranks.clone()));
            if fresh {
                if let Some(c) = self.make_candidate(q, edge_idx, ranks) {
                    self.state
                        .get_mut(&q)
                        .expect("class state present")
                        .cand
                        .push(Reverse(c));
                }
            }
        }
    }

    /// Compose the derivation denoted by `(edge_idx, ranks)`: pull each child's
    /// `ranks[i]`-th derivation (RECURSES), fold the weight, build the tree key.
    /// Returns `None` if any child has no `ranks[i]`-th derivation (exhausted or
    /// cycle-cut), i.e. the combination does not exist.
    #[allow(clippy::type_complexity)]
    fn compose(
        &mut self,
        q: EClassId,
        edge_idx: usize,
        ranks: &[usize],
    ) -> Option<(L, W, ContentKey, Vec<Rc<Derivation<L, W>>>)> {
        // `eg` is a copy of the `&'g` reference, decoupled from `self`, so the
        // node borrow does not conflict with the `&mut self` recursion below.
        let eg = self.egraph;
        let node = &eg.nodes(q)[edge_idx];
        let op = node.op.clone();
        let w_edge = (self.weigh)(node); // `self.weigh` borrow ends here
        let child_classes: Vec<EClassId> = node.children.iter().map(|&c| eg.find(c)).collect();

        let mut key_bytes = Vec::new();
        op.write_content(&mut key_bytes);
        let mut w = w_edge;
        let mut children: Vec<Rc<Derivation<L, W>>> = Vec::with_capacity(child_classes.len());
        for (i, &ci) in child_classes.iter().enumerate() {
            let cd = self.kth_raw(ci, ranks[i])?; // recurse; None ⟹ combination absent
            w = w.times(&cd.weight);
            write_ordered_framed(&mut key_bytes, cd.key.as_bytes());
            children.push(cd);
        }
        Some((op, w, ContentKey::from_bytes(key_bytes), children))
    }

    fn make_candidate(
        &mut self,
        q: EClassId,
        edge_idx: usize,
        ranks: Vec<usize>,
    ) -> Option<Candidate<W>> {
        let (_op, w, key, _children) = self.compose(q, edge_idx, &ranks)?;
        Some(Candidate { ord: OrdKey { w, key }, edge_idx, ranks })
    }

    fn build_derivation(
        &mut self,
        q: EClassId,
        edge_idx: usize,
        ranks: &[usize],
    ) -> Option<Rc<Derivation<L, W>>> {
        let (op, w, key, children) = self.compose(q, edge_idx, ranks)?;
        Some(Rc::new(Derivation { op, class: q, children, weight: w, key }))
    }
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
