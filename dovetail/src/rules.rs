//! Rules-as-data: rewrite rules over the e-graph + an equality-saturation driver.
//!
//! Rules are DATA (`RewriteRule<L>`), not macro-generated code — a language's
//! reduction rules are loaded and run, not compiled in. Saturation grows the
//! e-graph of equalities (every rewrite adds an equality, never replacing a
//! term); the weighted [`crate::extract`] extractor then enumerates normal forms
//! best-first. **Nothing is pruned during saturation**; node and iteration
//! limits are explicit [`SaturationOutcome`] values, never silent.

use std::collections::{HashMap, HashSet};

use crate::egraph::{EClassId, EGraph, ENode};
use crate::key::SemanticHash;

/// A pattern over operator labels `L` with named pattern variables.
#[derive(Clone, Debug)]
pub enum Pattern<L> {
    /// A pattern variable, binding to an e-class.
    Var(String),
    /// An operator applied to argument patterns (POSITIONAL).
    App { op: L, args: Vec<Pattern<L>> },
    /// An associative-commutative (AC) operator applied to a multiset of
    /// children: the `fixed` patterns match a SUB-MULTISET of an `op`-bag node's
    /// children (in any pairing), and `rest`, if present, binds to the multiset
    /// COMPLEMENT (a fresh canonical n-ary `op` node).
    ///
    /// On the LHS this matches every distinct sub-multiset selection + pairing as
    /// a DISTINCT alternative; the non-linear `Var` re-bind check prunes pairings
    /// whose shared variables disagree (by evidence). On the RHS it builds the
    /// result bag: each `fixed` pattern instantiated, unioned with the bound
    /// `rest` complement.
    AcApp {
        op: L,
        fixed: Vec<Pattern<L>>,
        rest: Option<String>,
    },
}

impl<L> Pattern<L> {
    pub fn var(name: impl Into<String>) -> Self {
        Pattern::Var(name.into())
    }
    pub fn leaf(op: L) -> Self {
        Pattern::App { op, args: Vec::new() }
    }
    pub fn app(op: L, args: Vec<Pattern<L>>) -> Self {
        Pattern::App { op, args }
    }
    /// An AC (associative-commutative) bag pattern: `fixed` patterns match a
    /// sub-multiset of an `op`-bag; `rest` (if any) binds the complement.
    pub fn ac(op: L, fixed: Vec<Pattern<L>>, rest: Option<String>) -> Self {
        Pattern::AcApp { op, fixed, rest }
    }
}

/// A substitution from pattern-variable name to e-class.
pub type Subst = HashMap<String, EClassId>;

/// A LAZY iterator over size-`k` sub-multiset selections (by position) of a bag
/// of e-class children, paired with the multiset COMPLEMENT.
///
/// AC selection is exponential, so selections are materialized ON DEMAND (mandate
/// 2 — laziness): the iterator holds only the current `k`-combination of indices
/// and advances ONE index at a time (lexicographic next-combination, mirroring
/// `enum_vectors`'s single-coordinate advance in
/// `EnumerationCompleteness.v`/`CollectionAcLowering.v`). It never builds a `Vec`
/// of all selections.
///
/// Each `next()` yields `(selection, complement)`: `selection` is the chosen
/// positions' classes (in position order), `complement` the unchosen positions'
/// classes. Together they partition the bag (no element lost or duplicated) — the
/// `is_split` / `ac_select` contract proven in `CollectionAcLowering.v`.
pub struct LazyAcSelect {
    bag: Vec<EClassId>,
    k: usize,
    /// The current `k`-combination of indices into `bag` (strictly increasing),
    /// or `None` once exhausted.
    combo: Option<Vec<usize>>,
}

impl LazyAcSelect {
    fn new(bag: &[EClassId], k: usize) -> Self {
        let n = bag.len();
        let combo = if k <= n {
            // The first combination is [0, 1, ..., k-1].
            Some((0..k).collect())
        } else {
            None // k > n: no size-k selection exists.
        };
        LazyAcSelect { bag: bag.to_vec(), k, combo }
    }

    /// Advance `self.combo` to the lexicographically-next strictly-increasing
    /// `k`-combination of `[0, n)`, or set it to `None` when exhausted. O(k).
    fn advance(&mut self) {
        let n = self.bag.len();
        let Some(combo) = self.combo.as_mut() else { return };
        if self.k == 0 {
            // The single empty selection has no successor.
            self.combo = None;
            return;
        }
        // Find the rightmost index that can be incremented: position `i` whose
        // value is below its ceiling `n - k + i`.
        let mut i = self.k;
        loop {
            if i == 0 {
                self.combo = None;
                return;
            }
            i -= 1;
            if combo[i] < n - self.k + i {
                combo[i] += 1;
                // Reset every position to the right to be contiguous.
                for j in (i + 1)..self.k {
                    combo[j] = combo[j - 1] + 1;
                }
                return;
            }
        }
    }
}

impl Iterator for LazyAcSelect {
    type Item = (Vec<EClassId>, Vec<EClassId>);

    fn next(&mut self) -> Option<Self::Item> {
        let combo = self.combo.clone()?;
        // Build (selection, complement) from the current index combination.
        let mut selection = Vec::with_capacity(self.k);
        let mut complement = Vec::with_capacity(self.bag.len() - self.k);
        let mut ci = 0usize;
        for (idx, &child) in self.bag.iter().enumerate() {
            if ci < combo.len() && combo[ci] == idx {
                selection.push(child);
                ci += 1;
            } else {
                complement.push(child);
            }
        }
        self.advance();
        Some((selection, complement))
    }
}

/// Construct the lazy size-`k` sub-multiset selection iterator over `bag`. See
/// [`LazyAcSelect`].
pub fn lazy_ac_select(bag: &[EClassId], k: usize) -> LazyAcSelect {
    LazyAcSelect::new(bag, k)
}

/// A rewrite rule `lhs -> rhs` (rules ARE data). RHS variables must be a subset
/// of LHS variables (every RHS var is bound by the match).
#[derive(Clone, Debug)]
pub struct RewriteRule<L> {
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
    pub label: Option<String>,
}

/// Terminal outcome of equality saturation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaturationOutcome {
    /// A fixpoint was reached (an iteration produced no new merges).
    Converged,
    /// The node budget was hit and saturation stopped early.
    NodeLimit,
    /// `max_iters` was exhausted before a fixpoint was observed.
    IterationLimit,
}

/// Saturation counters shared by every outcome.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SatStats {
    /// Iterations performed.
    pub iterations: usize,
    /// Total merges applied.
    pub total_merges: usize,
}

/// Outcome of equality saturation.
#[must_use = "saturation can stop from node or iteration limits; inspect `outcome` before extracting as if complete"]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatReport {
    pub outcome: SaturationOutcome,
    pub stats: SatStats,
}

impl SatReport {
    fn new(outcome: SaturationOutcome, stats: SatStats) -> Self {
        SatReport { outcome, stats }
    }
}

impl<L: Clone + Eq + std::hash::Hash + SemanticHash> EGraph<L> {
    /// All `(root e-class, substitution)` matches of `pattern` across the graph.
    ///
    /// Takes `&mut self` because AC (`AcApp`) matching materializes a fresh
    /// canonical n-ary `op` node for each `rest` complement — an honest,
    /// budget-gated e-graph growth (the only mutation; positional matching adds
    /// nothing). Pulling AC selections is on-demand and lazy ([`lazy_ac_select`]).
    pub fn search(&mut self, pattern: &Pattern<L>) -> Vec<(EClassId, Subst)> {
        let mut out = Vec::new();
        let classes: Vec<EClassId> = self.classes().collect();
        for q in classes {
            self.collect_matches(pattern, q, &Subst::new(), &mut out);
        }
        out
    }

    fn collect_matches(
        &mut self,
        pattern: &Pattern<L>,
        class: EClassId,
        subst: &Subst,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        let class = self.find(class);
        match pattern {
            Pattern::Var(name) => match subst.get(name) {
                Some(&existing) if self.find(existing) == class => out.push((class, subst.clone())),
                Some(_) => {}, // bound to a different class — no match
                None => {
                    let mut s = subst.clone();
                    s.insert(name.clone(), class);
                    out.push((class, s));
                },
            },
            Pattern::App { op, args } => {
                // Snapshot the class's nodes so the `&mut self` recursion below
                // does not conflict with the node borrow.
                let candidates: Vec<Vec<EClassId>> = self
                    .nodes(class)
                    .iter()
                    .filter(|n| n.op == *op && n.children.len() == args.len())
                    .map(|n| n.children.clone())
                    .collect();
                for children in candidates {
                    self.match_children(args, &children, subst, class, out);
                }
            },
            Pattern::AcApp { op, fixed, rest } => {
                self.collect_ac_matches(op, fixed, rest, class, subst, out);
            },
        }
    }

    fn match_children(
        &mut self,
        patterns: &[Pattern<L>],
        children: &[EClassId],
        subst: &Subst,
        root: EClassId,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        if patterns.is_empty() {
            out.push((root, subst.clone()));
            return;
        }
        let mut child_matches = Vec::new();
        self.collect_matches(&patterns[0], children[0], subst, &mut child_matches);
        for (_, cs) in child_matches {
            self.match_children(&patterns[1..], &children[1..], &cs, root, out);
        }
    }

    /// Match an AC (`AcApp`) pattern against `class`: find each `op`-bag node with
    /// at least `|fixed|` children, LAZILY enumerate size-`|fixed|` sub-multiset
    /// selections of its children, pair each selection against the `fixed`
    /// patterns over ALL permutations (the non-linear `Var` re-bind check in
    /// [`collect_matches`] prunes disagreeing shared-variable pairings BY
    /// EVIDENCE), and bind `rest` (if any) to a fresh canonical n-ary `op` node
    /// over the multiset COMPLEMENT (budget-gated). Each surviving `(class,
    /// subst)` is a DISTINCT alternative.
    fn collect_ac_matches(
        &mut self,
        op: &L,
        fixed: &[Pattern<L>],
        rest: &Option<String>,
        class: EClassId,
        subst: &Subst,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        let k = fixed.len();
        // Snapshot the matching bag nodes (canonicalized children) so the
        // `&mut self` recursion / complement materialization below does not
        // conflict with the node borrow.
        let bags: Vec<Vec<EClassId>> = self
            .nodes(class)
            .iter()
            .filter(|n| n.op == *op && n.children.len() >= k)
            .map(|n| n.children.iter().map(|&c| self.find(c)).collect())
            .collect();

        for bag in bags {
            // Lazily enumerate (selection, complement) splits of size k.
            for (selection, complement) in lazy_ac_select(&bag, k) {
                // Pair the `fixed` patterns to the `selection` over ALL
                // permutations. `pair_fixed` recurses `collect_matches` per
                // position; the non-linear Var check prunes by evidence.
                let mut paired: Vec<Subst> = Vec::new();
                self.pair_fixed(fixed, &selection, subst, &mut paired);
                if paired.is_empty() {
                    continue;
                }
                // Bind `rest` to a fresh canonical n-ary `op` node over the
                // complement (budget-gated). If the budget refuses the node, the
                // whole match is dropped honestly (NodeLimit is reported by the
                // caller via `node_limit_reached`).
                let rest_binding = match rest {
                    Some(_) => match self.add_canonical_bag(op.clone(), &complement) {
                        Some(id) => Some(id),
                        None => continue, // budget refused the complement node
                    },
                    None => None,
                };
                for s in paired {
                    let mut s = s;
                    if let (Some(name), Some(id)) = (rest.as_ref(), rest_binding) {
                        s.insert(name.clone(), id);
                    }
                    out.push((class, s));
                }
            }
        }
    }

    /// Pair `fixed` patterns to `selection` children over every permutation,
    /// recursing [`collect_matches`] per position. Produces one [`Subst`] per
    /// surviving pairing (the non-linear `Var` re-bind check inside
    /// `collect_matches` prunes pairings whose shared variables disagree).
    ///
    /// `selection` and `fixed` have equal length `k` (guaranteed by the caller).
    /// Permutations are enumerated by picking, for `fixed[0]`, each not-yet-used
    /// `selection` index, then recursing on the rest — `k!` orderings, tiny for
    /// the rules in scope (`k = 2` for OpenRule).
    fn pair_fixed(
        &mut self,
        fixed: &[Pattern<L>],
        selection: &[EClassId],
        subst: &Subst,
        out: &mut Vec<Subst>,
    ) {
        // Recurse with an explicit "used selection index" mask.
        let mut used = vec![false; selection.len()];
        self.pair_fixed_rec(fixed, selection, &mut used, subst, out);
    }

    fn pair_fixed_rec(
        &mut self,
        fixed: &[Pattern<L>],
        selection: &[EClassId],
        used: &mut [bool],
        subst: &Subst,
        out: &mut Vec<Subst>,
    ) {
        if fixed.is_empty() {
            out.push(subst.clone());
            return;
        }
        for i in 0..selection.len() {
            if used[i] {
                continue;
            }
            let mut child_matches = Vec::new();
            self.collect_matches(&fixed[0], selection[i], subst, &mut child_matches);
            if child_matches.is_empty() {
                continue;
            }
            used[i] = true;
            for (_, cs) in child_matches {
                self.pair_fixed_rec(&fixed[1..], selection, used, &cs, out);
            }
            used[i] = false;
        }
    }

    /// Add a fresh canonical n-ary `op` node over `children` (sorted by canonical
    /// class key — the same canonical bag order the lowering produces), within
    /// the node budget. `None` (with [`node_limit_reached`](EGraph::node_limit_reached)
    /// set) if a fresh node would overflow the budget.
    fn add_canonical_bag(&mut self, op: L, children: &[EClassId]) -> Option<EClassId> {
        let mut sorted: Vec<EClassId> = children.iter().map(|&c| self.find(c)).collect();
        // `sort_by_cached_key` computes each (non-trivial) canonical key ONCE,
        // rather than twice per comparison.
        sorted.sort_by_cached_key(|&c| self.canonical_class_key(c));
        self.try_add_with_budget(ENode::new(op, sorted))
    }

    /// Add a canonical n-ary `op` bag, FLATTENING any child that is itself an
    /// `op`-bag — the ASSOCIATIVE half of AC: `op{P, op{Q, R}} ≡ op{P, Q, R}`.
    /// A constructed rewrite result is thus one flat bag (matching the generated
    /// `normalize()`'s iterative `insert_into_<bag>`), not a bag-of-bags.
    ///
    /// Only constructed RESULTS are flattened here; seeds keep their parsed
    /// structure (the grammar already parses `{p | p | ...}` as a flat bag, so
    /// seeds carry no same-`op` nesting to peel — only a rewrite that places a
    /// bag-valued binding into a new bag introduces a layer).
    ///
    /// Iterative work-stack (no recursion, so deep nesting cannot overflow the
    /// call stack). MULTIPLICITY-preserving: a bag class spliced as two distinct
    /// siblings flattens twice (`op{op{B}, op{B}} ⇒ op{B, B}`). CYCLE-guarded by
    /// a per-splice-path ancestor set: a class reachable as its own splice
    /// ancestor — which a terminating rewrite never produces (RHS bag members are
    /// proper subterms), but the generic e-graph could after merges — is kept as
    /// a leaf rather than looping. A class is a bag iff it carries an `op`-labeled
    /// node, the same interpretation the matcher and the `rest` splice use.
    fn add_flattened_bag(&mut self, op: L, children: &[EClassId]) -> Option<EClassId> {
        let mut flat: Vec<EClassId> = Vec::with_capacity(children.len());
        // (class to place, the set of bag classes whose splice is in progress
        // strictly above it on this path). Pushed in reverse for a stable
        // left-to-right splice order (the final canonical sort makes order
        // irrelevant, but determinism aids debugging).
        let mut stack: Vec<(EClassId, HashSet<EClassId>)> = children
            .iter()
            .rev()
            .map(|&c| (self.find(c), HashSet::new()))
            .collect();
        while let Some((class, ancestors)) = stack.pop() {
            let class = self.find(class);
            let bag_children: Option<Vec<EClassId>> = if ancestors.contains(&class) {
                None // cycle on this path: keep as a leaf, do not expand.
            } else {
                self.nodes(class)
                    .iter()
                    .find(|n| n.op == op)
                    .map(|n| n.children.iter().map(|&c| self.find(c)).collect())
            };
            match bag_children {
                Some(grandchildren) => {
                    let mut child_ancestors = ancestors.clone();
                    child_ancestors.insert(class);
                    for &gc in grandchildren.iter().rev() {
                        stack.push((self.find(gc), child_ancestors.clone()));
                    }
                },
                None => flat.push(class),
            }
        }
        self.add_canonical_bag(op, &flat)
    }

    fn rhs_vars_bound(pattern: &Pattern<L>, subst: &Subst) -> bool {
        match pattern {
            Pattern::Var(name) => subst.contains_key(name),
            Pattern::App { args, .. } => args.iter().all(|arg| Self::rhs_vars_bound(arg, subst)),
            Pattern::AcApp { fixed, rest, .. } => {
                fixed.iter().all(|arg| Self::rhs_vars_bound(arg, subst))
                    && rest.as_ref().is_none_or(|name| subst.contains_key(name))
            },
        }
    }

    /// Instantiate a RHS pattern under a substitution, adding nodes within the
    /// node budget. Returns `None` if a variable is unbound (ill-formed rule) or
    /// the budget refused a fresh node (then `node_limit_reached()` is set).
    fn instantiate(&mut self, pattern: &Pattern<L>, subst: &Subst) -> Option<EClassId> {
        match pattern {
            Pattern::Var(name) => subst.get(name).map(|&id| self.find(id)),
            Pattern::App { op, args } => {
                let mut children = Vec::with_capacity(args.len());
                for a in args {
                    children.push(self.instantiate(a, subst)?);
                }
                self.try_add_with_budget(ENode::new(op.clone(), children))
            },
            Pattern::AcApp { op, fixed, rest } => {
                // Build the result bag from the instantiated `fixed` patterns plus
                // the bound `rest` complement, then FLATTEN: any member that is
                // itself an `op`-bag is spliced in (associativity), so the result
                // is one flat canonical bag, not a bag-of-bags. This covers both
                // the complement (always an `op`-bag) and any `fixed` pattern that
                // instantiates to a parallel composition — e.g. opening `n[B | C]`
                // binds the ambient body to the bag `{B, C}`, which must merge
                // into the surrounding parallel rather than nest.
                let mut children = Vec::with_capacity(fixed.len() + 1);
                for f in fixed {
                    children.push(self.instantiate(f, subst)?);
                }
                if let Some(name) = rest {
                    children.push(self.find(*subst.get(name)?));
                }
                self.add_flattened_bag(op.clone(), &children)
            },
        }
    }

    /// Equality saturation: apply `rules` to a fixpoint, or until the node budget
    /// or `max_iters` is hit. Every fired rule ADDS an equality (merge); nothing
    /// is pruned. Limits are reported in [`SatReport::outcome`].
    pub fn saturate(&mut self, rules: &[RewriteRule<L>], max_iters: usize) -> SatReport {
        let mut stats = SatStats::default();
        for iteration in 0..max_iters {
            stats.iterations = iteration + 1;
            let mut iter_merges = 0usize;
            for rule in rules {
                let matches = self.search(&rule.lhs);
                let mut rule_merges = 0usize;
                let mut budget_hit = false;
                for (root, subst) in matches {
                    if !Self::rhs_vars_bound(&rule.rhs, &subst) {
                        // Ill-formed rule for this match: reject before adding
                        // any partial RHS nodes.
                        continue;
                    }
                    if let Some(rhs_id) = self.instantiate(&rule.rhs, &subst) {
                        if self.find(root) != self.find(rhs_id) {
                            self.merge(root, rhs_id);
                            rule_merges += 1;
                        }
                    } else if self.node_limit_reached() {
                        budget_hit = true;
                        break;
                    }
                    // else: a budgeted add refused a fresh node without setting
                    // the sticky flag; skip defensively.
                }
                if rule_merges > 0 {
                    self.rebuild();
                }
                iter_merges += rule_merges;
                stats.total_merges += rule_merges;
                if budget_hit {
                    return SatReport::new(SaturationOutcome::NodeLimit, stats);
                }
            }
            if iter_merges == 0 {
                return SatReport::new(SaturationOutcome::Converged, stats);
            }
        }
        SatReport::new(SaturationOutcome::IterationLimit, stats)
    }
}

// ════════════════════════════════════════════════════════════════════════════
// EP-P6a DV-0 PROBE (measurement-only; 2026-06-12)
// ════════════════════════════════════════════════════════════════════════════
//
// Binding contract: docs/design/evidence-pruning/02-staged-implementation-plan.md
// §P6a. This is a MEASUREMENT-ONLY probe deciding the DV-1 gate; it implements
// NOTHING beyond the counters. It does not alter any production code path (the
// 39 baseline tests are untouched).
//
// Counters required by the contract:
//   - `enodes_added_total`            : e-nodes created DURING saturation
//                                       (post-saturation live node_count minus
//                                       the pre-saturation seed node_count).
//   - `enodes_in_extracted_derivations`: distinct e-nodes (by exact ContentKey of
//                                       the canonical (op, child-classes) node)
//                                       that appear in the chosen best derivation
//                                       trees of the demanded roots — MARKED by
//                                       walking those derivations.
//   - saturation share of eval wall-time (saturation ns / (saturation+extraction) ns).
//
// GATE: untouched-share = 1 - (in_extracted / added_total) ≥ 50% AND
//       saturation ≥ 20% of eval wall-time  →  recommend DV-1; else record the non-goal.
//
// CORPUS CAVEAT (recorded in findings.md): the rhocalc eval corpus does NOT route
// through dovetail today — `mettail-rho-runtime` runs f1r3node's RhoRuntime
// directly (run.rs) and the `dovetail` reference in its lib.rs is a doc comment;
// dovetail is M-E.0 (inert), no live caller. So this probe measures the LARGEST
// EXISTING dovetail workload: a saturate→extract arithmetic-rewrite system that
// mirrors the equality-saturation shape the flip would create. The
// corpus-representativeness caveat carries to the flip epic.
#[cfg(test)]
mod dv0_probe {
    use std::collections::HashSet;
    use std::time::Instant;

    use rigail::TropicalWeight;

    use crate::egraph::{EClassId, EGraph, ENode};
    use crate::extract::{Derivation, Extractor};
    use crate::key::ContentKey;
    use crate::rules::{Pattern, RewriteRule};

    /// Cost model: leaf digits cost their value, structural ops a flat 1, and the
    /// `h`-nesting "expander" (an unbounded-growth rule, mirroring the saturation
    /// blow-up the budget guards) costs 1 so the cheaper non-expanded form wins.
    fn weigh(n: &ENode<String>) -> TropicalWeight {
        match n.op.as_str() {
            "add" | "mul" => TropicalWeight(1.0),
            "h" => TropicalWeight(1.0),
            s => match s.parse::<f64>() {
                Ok(v) => TropicalWeight(v.max(1.0)),
                Err(_) => TropicalWeight(1.0),
            },
        }
    }

    /// The exact ContentKey of a node's CANONICAL (op, child-classes) identity —
    /// the same identity the e-graph hashconses on. Used to MARK e-nodes reached
    /// by the extracted derivations.
    fn node_key(op: &str, child_classes: &[EClassId]) -> ContentKey {
        let mut bytes = Vec::new();
        crate::key::SemanticHash::write_content(&op.to_string(), &mut bytes);
        for c in child_classes {
            crate::key::write_framed(&mut bytes, &c.0.to_le_bytes());
        }
        ContentKey::from_bytes(bytes)
    }

    /// Walk a chosen derivation tree, inserting each node's canonical key into
    /// `marked`. A derivation node carries `class` (its e-class) and `children`
    /// (the chosen child derivations), so the canonical (op, child-class) key is
    /// reconstructable and matches the e-graph's hashcons identity.
    fn mark_derivation(
        eg: &EGraph<String>,
        d: &Derivation<String, TropicalWeight>,
        marked: &mut HashSet<ContentKey>,
    ) {
        let child_classes: Vec<EClassId> = d.children.iter().map(|c| eg.find(c.class)).collect();
        marked.insert(node_key(&d.op, &child_classes));
        for c in &d.children {
            mark_derivation(eg, c, marked);
        }
    }

    /// Build a saturate→extract workload, returning
    /// (enodes_added_total, enodes_in_extracted_derivations, sat_ns, extract_ns,
    ///  total_live_nodes, demanded_roots, nf_count).
    #[allow(clippy::type_complexity)]
    fn run_workload(
        seed: &str,
        depth_terms: usize,
        kbest: usize,
    ) -> (usize, usize, u128, u128, usize, usize, usize) {
        // ── Build the e-graph + seed a small batch of distinct arithmetic terms.
        let mut eg = EGraph::<String>::new();
        let mut roots: Vec<EClassId> = Vec::new();
        // A pool of leaves shared across the seeded terms (so saturation/congruence
        // has cross-term structure to grow, like a real reduction corpus).
        let leaves: Vec<EClassId> = (0..6)
            .map(|i| eg.add(ENode::leaf(format!("{}", i + 1))))
            .collect();
        for t in 0..depth_terms {
            // add(mul(a,b), c)  with a/b/c rotating through the leaf pool.
            let a = leaves[t % leaves.len()];
            let b = leaves[(t + 1) % leaves.len()];
            let c = leaves[(t + 2) % leaves.len()];
            let m = eg.add(ENode::new("mul".into(), vec![a, b]));
            let r = eg.add(ENode::new("add".into(), vec![m, c]));
            roots.push(r);
        }
        let _ = seed; // (seed label reserved for diagnostic naming)
        eg.rebuild();
        let seed_nodes = eg.node_count();

        // ── Rewrite system that GROWS the e-graph with equivalent-but-costlier
        //    forms (the CESK runtime-backend replacement analog: every rule adds
        //    an equality, nothing is pruned). `x -> add(x, h(x))`-style expanders plus
        //    commutativity create many materialized e-nodes that extraction will
        //    NOT choose (the cheaper original wins), which is exactly the
        //    "added but untouched" share DV-0 quantifies.
        let rules = vec![
            // commutativity of mul: mul(x,y) ~ mul(y,x)
            RewriteRule {
                lhs: Pattern::app("mul".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("mul".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("mul_comm".into()),
            },
            // commutativity of add
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("add".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("add_comm".into()),
            },
            // an expander that introduces costlier equivalent structure:
            //   add(x,y) ~ add(x, mul(1, y))   (identity-via-mul, costlier ⇒ unchosen)
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app(
                    "add".into(),
                    vec![
                        Pattern::var("x"),
                        Pattern::app(
                            "mul".into(),
                            vec![Pattern::leaf("1".into()), Pattern::var("y")],
                        ),
                    ],
                ),
                label: Some("add_mul_ident".into()),
            },
        ];

        // ── SATURATION (timed). Bounded iters so commutativity doesn't ping-pong
        //    forever; the expander grows structure each pass.
        let t0 = Instant::now();
        let _report = eg.saturate(&rules, 6);
        let sat_ns = t0.elapsed().as_nanos();
        let total_live_nodes = eg.node_count();
        let enodes_added_total = total_live_nodes.saturating_sub(seed_nodes);

        // ── EXTRACTION (timed): exact lazy k-best with the admissible 0̄-inside
        //    skip, over EVERY demanded root. MARK the touched e-nodes.
        let t1 = Instant::now();
        let mut marked: HashSet<ContentKey> = HashSet::new();
        let mut nf_count = 0usize;
        {
            let mut ex = Extractor::new(&eg, weigh).with_heuristic();
            for &root in &roots {
                for k in 0..kbest {
                    match ex.kth(root, k).value {
                        Some(d) => {
                            mark_derivation(&eg, &d, &mut marked);
                            nf_count += 1;
                        },
                        None => break,
                    }
                }
            }
        }
        let extract_ns = t1.elapsed().as_nanos();
        let enodes_in_extracted = marked.len();

        (
            enodes_added_total,
            enodes_in_extracted,
            sat_ns,
            extract_ns,
            total_live_nodes,
            roots.len(),
            nf_count,
        )
    }

    #[test]
    fn dv0_saturation_vs_extraction_reach_report() {
        // Three workload sizes so the share is observed across scale, not a single
        // point. Printed for the ledger; the test ASSERTS only the invariants the
        // measurement relies on (it refutes nothing — DV-0 is measurement-only).
        println!("\n=== EP-P6a DV-0 PROBE (dovetail saturate→extract) ===");
        println!(
            "{:<10} {:>10} {:>12} {:>14} {:>10} {:>10} {:>9} {:>10} {:>11}",
            "workload",
            "live_nodes",
            "added(sat)",
            "in_extracted",
            "untouched%",
            "sat_ns",
            "ext_ns",
            "sat%wall",
            "roots/nf"
        );
        // 1-best (k=1) is the normal-form extraction the flip would use.
        for (name, depth, kbest) in [
            ("small_k1", 4usize, 1usize),
            ("med_k1", 12, 1),
            ("large_k1", 32, 1),
            // a k=3 variant: pulling more alternatives touches MORE nodes, the
            // honest upper bound on extraction reach.
            ("large_k3", 32, 3),
        ] {
            let (added, in_ex, sat_ns, ext_ns, live, roots, nf) = run_workload(name, depth, kbest);
            let untouched_pct = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(in_ex.min(added)) as f64) / (added as f64)
            };
            let total_ns = sat_ns + ext_ns;
            let sat_pct = if total_ns == 0 {
                0.0
            } else {
                100.0 * (sat_ns as f64) / (total_ns as f64)
            };
            println!(
                "{:<10} {:>10} {:>12} {:>14} {:>9.1}% {:>10} {:>10} {:>8.1}% {:>5}/{:<5}",
                name, live, added, in_ex, untouched_pct, sat_ns, ext_ns, sat_pct, roots, nf
            );

            // Measurement-soundness invariants (NOT pruning assertions):
            assert!(live >= added, "live nodes ≥ saturation-added (sanity)");
            assert!(in_ex >= 1, "extraction touched at least one e-node");
        }
        println!(
            "GATE: DV-1 iff untouched-share ≥ 50% AND sat ≥ 20% of eval wall-time.\n\
             (See /tmp/p6_probes/findings.md for the verdict + corpus caveat.)\n"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraphConfig;

    #[test]
    fn search_finds_matches() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let pat = Pattern::app("f".to_string(), vec![Pattern::var("x")]);
        let matches = eg.search(&pat);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].1.get("x"), Some(&eg.find(a)));
    }

    #[test]
    fn saturate_simple_rewrite_to_fixpoint() {
        // f(x) -> x. Seed f(a). After saturation: f(a) ~ a.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("unwrap_f".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged, "reaches a fixpoint");
        assert!(eg.equiv(fa, a), "f(a) ~ a after saturation");
    }

    #[test]
    fn saturate_congruence_via_rule() {
        // a -> b, and f(a), f(b): after a~b, congruence gives f(a)~f(b).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let fb = eg.add(ENode::new("f".into(), vec![b]));
        let rule = RewriteRule {
            lhs: Pattern::leaf("a".to_string()),
            rhs: Pattern::leaf("b".to_string()),
            label: None,
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert!(eg.equiv(a, b));
        assert!(eg.equiv(fa, fb), "congruence: f(a) ~ f(b) after a ~ b");
    }

    #[test]
    fn saturate_reports_node_limit_without_overshoot() {
        // f(x) -> f(h(x)) grows UNBOUNDEDLY: each iteration introduces a fresh
        // `h`-nesting depth that cannot collapse (unlike f(x)->f(f(x)), which
        // converges because f(f(a)) = f(class-of-f(a)) dedups). The budget caps
        // the growth and REPORTS it.
        let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 5 });
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "f".to_string(),
                vec![Pattern::app("h".to_string(), vec![Pattern::var("x")])],
            ),
            label: None,
        };
        let rep = eg.saturate(&[rule], 100);
        assert_eq!(
            rep.outcome,
            SaturationOutcome::NodeLimit,
            "budget overflow REPORTED, not silent"
        );
        assert!(eg.node_count() <= 5, "no overshoot past the budget");
    }

    #[test]
    fn saturate_reports_iteration_limit() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "f".to_string(),
                vec![Pattern::app("h".to_string(), vec![Pattern::var("x")])],
            ),
            label: None,
        };
        let rep = eg.saturate(&[rule], 1);
        assert_eq!(rep.outcome, SaturationOutcome::IterationLimit);
        assert_eq!(rep.stats.iterations, 1);
        assert!(rep.stats.total_merges > 0);
    }

    #[test]
    fn unbound_rhs_variable_does_not_leave_partial_nodes() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let before = eg.node_count();
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "pair".to_string(),
                vec![
                    Pattern::app("g".to_string(), vec![Pattern::var("x")]),
                    Pattern::var("missing"),
                ],
            ),
            label: Some("ill_formed_rhs".into()),
        };

        let rep = eg.saturate(&[rule], 10);

        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        assert_eq!(
            eg.node_count(),
            before,
            "unbound RHS variable must reject before adding partial RHS nodes"
        );
    }

    // ════════════════════════════════════════════════════════════════════════
    //  AC (associative-commutative) matching
    // ════════════════════════════════════════════════════════════════════════

    use crate::egraph::EClassId;

    fn ids(xs: &[u32]) -> Vec<EClassId> {
        xs.iter().map(|&x| EClassId(x)).collect()
    }

    #[test]
    fn lazy_ac_select_enumerates_every_size_k_split_once() {
        // bag = [10,11,12], k=2 ⇒ C(3,2)=3 splits, complements correct.
        let bag = ids(&[10, 11, 12]);
        let got: Vec<(Vec<EClassId>, Vec<EClassId>)> = lazy_ac_select(&bag, 2).collect();
        assert_eq!(got.len(), 3, "C(3,2) = 3 size-2 selections");
        let expected = vec![
            (ids(&[10, 11]), ids(&[12])),
            (ids(&[10, 12]), ids(&[11])),
            (ids(&[11, 12]), ids(&[10])),
        ];
        assert_eq!(got, expected, "lexicographic combinations + exact complements");
    }

    #[test]
    fn lazy_ac_select_edge_cases() {
        let bag = ids(&[1, 2, 3]);
        // k = 0: one empty selection, whole bag as complement.
        let k0: Vec<_> = lazy_ac_select(&bag, 0).collect();
        assert_eq!(k0, vec![(ids(&[]), ids(&[1, 2, 3]))]);
        // k = n: one full selection, empty complement.
        let kn: Vec<_> = lazy_ac_select(&bag, 3).collect();
        assert_eq!(kn, vec![(ids(&[1, 2, 3]), ids(&[]))]);
        // k > n: no selections.
        let kbig: Vec<_> = lazy_ac_select(&bag, 4).collect();
        assert!(kbig.is_empty(), "k > n ⇒ no size-k selection");
        // empty bag, k = 0: one empty split.
        let empty: Vec<_> = lazy_ac_select(&[], 0).collect();
        assert_eq!(empty, vec![(ids(&[]), ids(&[]))]);
    }

    #[test]
    fn lazy_ac_select_is_lazy_partial_consumption() {
        // A large bag where the full combination count is astronomical; pulling a
        // few items must be cheap (no eager Vec of all selections). C(40,5) ≈ 658k
        // — we pull only 3. This terminates instantly iff the iterator is lazy.
        let bag: Vec<EClassId> = (0..40).map(EClassId).collect();
        let mut it = lazy_ac_select(&bag, 5);
        let first = it.next().expect("at least one");
        assert_eq!(first.0, ids(&[0, 1, 2, 3, 4]));
        assert_eq!(first.0.len() + first.1.len(), 40, "split partitions the bag");
        let _second = it.next().expect("second");
        let _third = it.next().expect("third");
        // (We never collect the ~658k total — the point is it didn't try to.)
    }

    #[test]
    fn ac_open_rule_single_pairing_reduces() {
        // PPar { open(n,A), n[B] } ~> PPar { A, B }  (no rest).
        // Bag node "par" over [open, amb]; open = open(n, A), amb = amb(n, B).
        // The shared name n is the non-linear constraint (here trivially shared).
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, vb]));
        // canonical bag for the par node
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        // OpenRule: par{ open(N,P), amb(N,Q), ...rest } ~> par{ P, Q, ...rest }.
        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged, "reaches a fixpoint");

        // The result bag par{A, B} must exist and be equivalent to the redex.
        let mut result_bag = vec![eg.find(va), eg.find(vb)];
        result_bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let expected = eg.add(ENode::new("par".into(), result_bag));
        assert!(eg.equiv(par, expected), "open(n,A) | n[B] ~> A | B");
    }

    #[test]
    fn ac_open_rule_shared_name_constraint_prunes_mismatch() {
        // par { open(n, A), m[B] } with n ≠ m: the shared-name N constraint is
        // UNSATISFIABLE (open's name n must equal amb's name, but the only ambient
        // has name m). No reduction must fire.
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let m = eg.add(ENode::leaf("m".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![m, vb]));
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();
        let before = eg.node_count();

        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);
        // par{A,B} must NOT have been produced (the name constraint refutes the
        // only candidate pairing).
        let expected_children = {
            let mut c = vec![eg.find(va), eg.find(vb)];
            c.sort_by_cached_key(|&a| eg.canonical_class_key(a));
            c
        };
        // node_count must be unchanged (no complement/result nodes added) and the
        // would-be result is not equivalent to the redex.
        assert_eq!(eg.node_count(), before, "no AC reduction fired for n ≠ m");
        // (Adding the would-be result now is a fresh node, so it cannot be
        // equivalent to `par` unless the rule had fired.)
        let expected = eg.add(ENode::new("par".into(), expected_children));
        assert!(!eg.equiv(par, expected), "n ≠ m: open|amb must not reduce");
    }

    #[test]
    fn ac_open_rule_flattens_nested_ambient_body() {
        // Associativity: open(n, A) | n[ B | C ] ~> A | B | C  (ONE flat bag),
        // NOT A | (B | C) (a bag-of-bags). The ambient body is itself a `par`
        // bag, so opening it must SPLICE its members into the surrounding
        // parallel — the associative half of AC. Without `add_flattened_bag`
        // the redex would instead reduce to the nested `par{A, par{B,C}}`.
        let mut eg = EGraph::<String>::new();
        let n = eg.add(ENode::leaf("n".into()));
        let va = eg.add(ENode::leaf("A".into()));
        let vb = eg.add(ENode::leaf("B".into()));
        let vc = eg.add(ENode::leaf("C".into()));
        // The ambient body is itself a `par` bag { B, C }.
        let mut body_bag = vec![vb, vc];
        body_bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let body = eg.add(ENode::new("par".into(), body_bag));
        let open = eg.add(ENode::new("open".into(), vec![n, va]));
        let amb = eg.add(ENode::new("amb".into(), vec![n, body]));
        let mut bag = vec![open, amb];
        bag.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let par = eg.add(ENode::new("par".into(), bag));
        eg.rebuild();

        let rule = RewriteRule {
            lhs: Pattern::ac(
                "par".into(),
                vec![
                    Pattern::app("open".into(), vec![Pattern::var("N"), Pattern::var("P")]),
                    Pattern::app("amb".into(), vec![Pattern::var("N"), Pattern::var("Q")]),
                ],
                Some("rest".into()),
            ),
            rhs: Pattern::ac(
                "par".into(),
                vec![Pattern::var("P"), Pattern::var("Q")],
                Some("rest".into()),
            ),
            label: Some("OpenRule".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert_eq!(rep.outcome, SaturationOutcome::Converged);

        // The FLAT result par{A, B, C} must be equivalent to the redex.
        let mut flat = vec![eg.find(va), eg.find(vb), eg.find(vc)];
        flat.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let expected_flat = eg.add(ENode::new("par".into(), flat));
        assert!(
            eg.equiv(par, expected_flat),
            "open(n,A) | n[B|C] ~> A | B | C (one flat bag)"
        );

        // The NESTED bag-of-bags par{A, par{B,C}} must NOT be the result: it has
        // a distinct canonical key, so associativity must have flattened it away.
        let mut nested = vec![eg.find(va), eg.find(body)];
        nested.sort_by_cached_key(|&a| eg.canonical_class_key(a));
        let nested_node = eg.add(ENode::new("par".into(), nested));
        assert!(
            !eg.equiv(par, nested_node),
            "the result must be flat, never a nested bag-of-bags"
        );
    }
}
