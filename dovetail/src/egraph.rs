//! A runtime, payload-generic, EXACT-keyed e-graph — the reduction core viewed
//! as a deterministic finite tree automaton (states = e-classes, transitions =
//! e-nodes).
//!
//! Ported from the proven compile-time e-graph (`prattail/src/egraph.rs`,
//! Willsey et al. "egg", POPL 2021) and generalized two ways:
//!
//! 1. **Payload-generic.** The operator/leaf label is a type parameter `L`
//!    rather than a fixed `String`, so any caller content (symbols, tagged
//!    literals, …) can label e-nodes.
//! 2. **Exact identity, never a finite hash.** E-node identity is *structural* —
//!    the label's [`Eq`] plus the canonical children — so two
//!    observationally-distinct e-nodes are never conflated. (A 64-bit-hash key
//!    is proven unsound here: `hash_only_pair_dedup_can_drop_distinct_keys`.)
//!    The label's `Eq`/`Hash` must agree with its [`SemanticHash`] content (the
//!    natural contract); [`ENode::content_key`] materializes that identity as an
//!    exact [`ContentKey`] for the extraction layer.
//!
//! Carries the budget hooks from commit b56e1e5 (`try_add_with_budget`,
//! `rebuild_exact_indices`, `node_limit_reached`).

use std::collections::HashMap;

use crate::key::{write_framed, ContentKey, SemanticHash};

/// Identifier of an e-class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EClassId(pub u32);

/// A payload-generic e-node: an operator/leaf label `L` applied to child
/// e-classes. Identity is structural (label `Eq` + canonical children).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ENode<L> {
    pub op: L,
    pub children: Vec<EClassId>,
}

impl<L: Clone> ENode<L> {
    /// A nullary e-node (a leaf / 0-arity operator).
    pub fn leaf(op: L) -> Self {
        ENode { op, children: Vec::new() }
    }

    /// An e-node with children.
    pub fn new(op: L, children: Vec<EClassId>) -> Self {
        ENode { op, children }
    }

    /// A copy with each child mapped to its union-find representative.
    fn canonicalize(&self, uf: &UnionFind) -> ENode<L> {
        ENode {
            op: self.op.clone(),
            children: self.children.iter().map(|&c| uf.find(c)).collect(),
        }
    }
}

impl<L: SemanticHash> ENode<L> {
    /// The exact content key of this e-node: the label's content bytes followed
    /// by each child id, length-framed so structure cannot alias. For a
    /// *canonical* key, canonicalize the children first (see the e-graph).
    pub fn content_key(&self) -> ContentKey {
        let mut out = Vec::new();
        self.op.write_content(&mut out);
        for c in &self.children {
            write_framed(&mut out, &c.0.to_le_bytes());
        }
        ContentKey::from_bytes(out)
    }
}

/// Union-find with path compression and union by rank (over e-class ids).
#[derive(Clone, Debug, Default)]
struct UnionFind {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind { parent: Vec::new(), rank: Vec::new() }
    }

    fn make_set(&mut self) -> EClassId {
        let id = self.parent.len() as u32;
        self.parent.push(id);
        self.rank.push(0);
        EClassId(id)
    }

    /// Representative of `id` (immutable; no path compression).
    fn find(&self, id: EClassId) -> EClassId {
        let mut root = id.0;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }
        EClassId(root)
    }

    /// Representative of `id`, compressing the path.
    fn find_mut(&mut self, id: EClassId) -> EClassId {
        let root = self.find(id).0;
        let mut cur = id.0;
        while self.parent[cur as usize] != root {
            let next = self.parent[cur as usize];
            self.parent[cur as usize] = root;
            cur = next;
        }
        EClassId(root)
    }

    fn union(&mut self, a: EClassId, b: EClassId) -> EClassId {
        let a = self.find_mut(a);
        let b = self.find_mut(b);
        if a == b {
            return a;
        }
        let (winner, loser) = if self.rank[a.0 as usize] >= self.rank[b.0 as usize] {
            (a, b)
        } else {
            (b, a)
        };
        self.parent[loser.0 as usize] = winner.0;
        if self.rank[winner.0 as usize] == self.rank[loser.0 as usize] {
            self.rank[winner.0 as usize] += 1;
        }
        winner
    }
}

#[derive(Clone, Debug)]
struct EClass<L> {
    nodes: Vec<ENode<L>>,
    /// Parent e-nodes referencing this class (for congruence closure).
    parents: Vec<(ENode<L>, EClassId)>,
}

/// E-graph configuration (the runtime node budget).
#[derive(Clone, Debug)]
pub struct EGraphConfig {
    /// Maximum number of live e-nodes before [`EGraph::try_add_with_budget`]
    /// refuses to add a fresh one.
    pub max_nodes: usize,
}

impl Default for EGraphConfig {
    fn default() -> Self {
        EGraphConfig { max_nodes: 1_000_000 }
    }
}

/// A runtime payload-generic e-graph keyed by exact structural identity.
pub struct EGraph<L> {
    classes: HashMap<EClassId, EClass<L>>,
    union_find: UnionFind,
    memo: HashMap<ENode<L>, EClassId>,
    pending: Vec<(EClassId, EClassId)>,
    config: EGraphConfig,
    node_count: usize,
    node_limit_hit: bool,
}

impl<L: Clone + Eq + std::hash::Hash> Default for EGraph<L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<L: Clone + Eq + std::hash::Hash> EGraph<L> {
    /// A new e-graph with default configuration.
    pub fn new() -> Self {
        EGraph {
            classes: HashMap::new(),
            union_find: UnionFind::new(),
            memo: HashMap::new(),
            pending: Vec::new(),
            config: EGraphConfig::default(),
            node_count: 0,
            node_limit_hit: false,
        }
    }

    /// A new e-graph with the given configuration.
    pub fn with_config(config: EGraphConfig) -> Self {
        EGraph { config, ..Self::new() }
    }

    /// Canonical representative for an e-class.
    pub fn find(&self, id: EClassId) -> EClassId {
        self.union_find.find(id)
    }

    /// Whether two e-class ids are equivalent.
    pub fn equiv(&self, a: EClassId, b: EClassId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Number of equivalence classes (canonical representatives).
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Total number of live e-nodes across all classes.
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    /// Whether a budgeted add was ever refused (the node limit was hit).
    pub fn node_limit_reached(&self) -> bool {
        self.node_limit_hit
    }

    /// Iterate the live canonical e-class ids (the WTA states).
    pub fn classes(&self) -> impl Iterator<Item = EClassId> + '_ {
        self.classes.keys().copied()
    }

    /// The exact (canonical, deduplicated) e-nodes of a class — the WTA
    /// transitions into it. Empty if `id` names no live class.
    pub fn nodes(&self, id: EClassId) -> &[ENode<L>] {
        self.classes
            .get(&self.find(id))
            .map(|c| c.nodes.as_slice())
            .unwrap_or(&[])
    }

    /// Add a hashconsed e-node; returns the e-class it belongs to.
    pub fn add(&mut self, enode: ENode<L>) -> EClassId {
        let canonical = enode.canonicalize(&self.union_find);
        if let Some(&id) = self.memo.get(&canonical) {
            return self.find(id);
        }

        let id = self.union_find.make_set();
        let eclass = EClass {
            nodes: vec![canonical.clone()],
            parents: Vec::new(),
        };

        // Register parent pointers for congruence closure.
        for &child in &canonical.children {
            let child_canon = self.find(child);
            if let Some(child_class) = self.classes.get_mut(&child_canon) {
                child_class.parents.push((canonical.clone(), id));
            }
        }

        self.classes.insert(id, eclass);
        self.memo.insert(canonical, id);
        self.node_count += 1;
        id
    }

    /// Add a hashconsed e-node without exceeding the configured node budget.
    /// Returns `None` (and records [`node_limit_reached`]) when a *fresh* node
    /// would overflow the budget; an existing (deduped) node always succeeds.
    pub fn try_add_with_budget(&mut self, enode: ENode<L>) -> Option<EClassId> {
        let canonical = enode.canonicalize(&self.union_find);
        if let Some(&id) = self.memo.get(&canonical) {
            return Some(self.find(id));
        }
        if self.node_count >= self.config.max_nodes {
            self.node_limit_hit = true;
            return None;
        }
        Some(self.add(canonical))
    }

    /// Assert that two e-classes are equal. Defers congruence closure to
    /// [`rebuild`](Self::rebuild).
    pub fn merge(&mut self, a: EClassId, b: EClassId) -> EClassId {
        let a = self.find(a);
        let b = self.find(b);
        if a == b {
            return a;
        }
        self.pending.push((a, b));
        let winner = self.union_find.union(a, b);
        let loser = if winner == a { b } else { a };
        if let Some(loser_class) = self.classes.remove(&loser) {
            if let Some(winner_class) = self.classes.get_mut(&winner) {
                winner_class.nodes.extend(loser_class.nodes);
                winner_class.parents.extend(loser_class.parents);
            }
        }
        winner
    }

    /// Restore the hashcons invariant and propagate congruence closure: after
    /// merges, e-nodes that became congruent (same label, same canonical
    /// children) are merged. Ends by restoring the exact class/memo/parent
    /// indexes (see [`rebuild_exact_indices`](Self::rebuild_exact_indices)).
    pub fn rebuild(&mut self) {
        while !self.pending.is_empty() {
            let pending = std::mem::take(&mut self.pending);
            let mut to_recanon: Vec<(ENode<L>, EClassId)> = Vec::new();
            for (a, b) in &pending {
                let canon = self.find(*a);
                if let Some(class) = self.classes.get(&canon) {
                    to_recanon.extend(class.parents.clone());
                }
                let canon_b = self.find(*b);
                if canon_b != canon {
                    if let Some(class) = self.classes.get(&canon_b) {
                        to_recanon.extend(class.parents.clone());
                    }
                }
            }

            // Re-canonicalize all memo entries, merging congruent duplicates.
            let mut new_memo: HashMap<ENode<L>, EClassId> = HashMap::new();
            let old_memo = std::mem::take(&mut self.memo);
            for (enode, id) in old_memo {
                let canon_node = enode.canonicalize(&self.union_find);
                let canon_id = self.find(id);
                match new_memo.get(&canon_node) {
                    Some(&existing_id) if self.find(existing_id) != canon_id => {
                        let existing_canon = self.find(existing_id);
                        if existing_canon != canon_id {
                            self.pending.push((existing_canon, canon_id));
                            let winner = self.union_find.union(existing_canon, canon_id);
                            let loser = if winner == existing_canon {
                                canon_id
                            } else {
                                existing_canon
                            };
                            if let Some(loser_class) = self.classes.remove(&loser) {
                                if let Some(winner_class) = self.classes.get_mut(&winner) {
                                    winner_class.nodes.extend(loser_class.nodes);
                                    winner_class.parents.extend(loser_class.parents);
                                }
                            }
                            new_memo.insert(canon_node, winner);
                        }
                    },
                    _ => {
                        new_memo.insert(canon_node, canon_id);
                    },
                }
            }
            self.memo = new_memo;

            // Re-canonicalize parent e-nodes from the merged classes.
            for (enode, id) in to_recanon {
                let canon_node = enode.canonicalize(&self.union_find);
                let canon_id = self.find(id);
                match self.memo.get(&canon_node) {
                    Some(&existing_id) if self.find(existing_id) != canon_id => {
                        let existing_canon = self.find(existing_id);
                        if existing_canon != canon_id {
                            self.pending.push((existing_canon, canon_id));
                            let winner = self.union_find.union(existing_canon, canon_id);
                            let loser = if winner == existing_canon {
                                canon_id
                            } else {
                                existing_canon
                            };
                            if let Some(loser_class) = self.classes.remove(&loser) {
                                if let Some(winner_class) = self.classes.get_mut(&winner) {
                                    winner_class.nodes.extend(loser_class.nodes);
                                    winner_class.parents.extend(loser_class.parents);
                                }
                            }
                            self.memo.insert(canon_node, winner);
                        }
                    },
                    _ => {
                        self.memo.insert(canon_node, canon_id);
                    },
                }
            }
        }
        self.rebuild_exact_indices();
    }

    /// Rebuild the memo and parent indexes from exact canonical e-nodes,
    /// deduplicating class-local node vectors so no duplicate match is replayed.
    /// Recomputes [`node_count`](Self::node_count) as the count of live exact
    /// e-nodes. (Carried from commit b56e1e5.)
    fn rebuild_exact_indices(&mut self) {
        let uf_snapshot = self.union_find.clone();
        for class in self.classes.values_mut() {
            let mut seen: HashMap<ENode<L>, ()> = HashMap::new();
            let mut canonical_nodes = Vec::with_capacity(class.nodes.len());
            for enode in class.nodes.drain(..) {
                let canonical = enode.canonicalize(&uf_snapshot);
                if seen.insert(canonical.clone(), ()).is_none() {
                    canonical_nodes.push(canonical);
                }
            }
            class.nodes = canonical_nodes;
            class.parents.clear();
        }

        let mut memo: HashMap<ENode<L>, EClassId> = HashMap::new();
        let mut parent_edges: Vec<(EClassId, ENode<L>, EClassId)> = Vec::new();
        let mut live_nodes = 0usize;
        let class_ids: Vec<EClassId> = self.classes.keys().copied().collect();
        for class_id in class_ids {
            let canon_class_id = self.find(class_id);
            let nodes = self
                .classes
                .get(&class_id)
                .map(|c| c.nodes.clone())
                .unwrap_or_default();
            for enode in &nodes {
                if memo.insert(enode.clone(), canon_class_id).is_none() {
                    live_nodes += 1;
                }
                for &child in &enode.children {
                    parent_edges.push((self.find(child), enode.clone(), canon_class_id));
                }
            }
        }

        let mut seen_parent_edges: HashMap<(EClassId, ENode<L>, EClassId), ()> = HashMap::new();
        for (child, enode, parent) in parent_edges {
            if seen_parent_edges
                .insert((child, enode.clone(), parent), ())
                .is_none()
            {
                if let Some(child_class) = self.classes.get_mut(&child) {
                    child_class.parents.push((enode, parent));
                }
            }
        }

        self.memo = memo;
        self.node_count = live_nodes;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(eg: &mut EGraph<String>, s: &str) -> EClassId {
        eg.add(ENode::leaf(s.to_string()))
    }
    fn app(eg: &mut EGraph<String>, s: &str, children: Vec<EClassId>) -> EClassId {
        eg.add(ENode::new(s.to_string(), children))
    }

    #[test]
    fn distinct_labels_are_distinct_classes_same_label_dedups() {
        let mut eg = EGraph::<String>::new();
        let x = leaf(&mut eg, "x");
        let y = leaf(&mut eg, "y");
        assert!(!eg.equiv(x, y), "distinct labels must not be conflated");
        let x2 = leaf(&mut eg, "x");
        assert_eq!(eg.find(x), eg.find(x2), "same label must hashcons");
        assert_eq!(eg.node_count(), 2, "x2 is a dedup, not a new node");
    }

    #[test]
    fn rebuild_congruence_propagates() {
        let mut eg = EGraph::<String>::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let fa = app(&mut eg, "f", vec![a]);
        let fb = app(&mut eg, "f", vec![b]);
        assert!(!eg.equiv(fa, fb));
        eg.merge(a, b);
        eg.rebuild();
        assert!(eg.equiv(fa, fb), "f(a) ~ f(b) after a ~ b");
    }

    #[test]
    fn rebuild_deep_congruence() {
        let mut eg = EGraph::<String>::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let fa = app(&mut eg, "f", vec![a]);
        let fb = app(&mut eg, "f", vec![b]);
        let gfa = app(&mut eg, "g", vec![fa]);
        let gfb = app(&mut eg, "g", vec![fb]);
        eg.merge(a, b);
        eg.rebuild();
        assert!(eg.equiv(gfa, gfb), "g(f(a)) ~ g(f(b)) after a ~ b");
    }

    #[test]
    fn rebuild_exact_indices_share_only_exact_canonical_enodes() {
        // Mirrors the b56e1e5 test: distinct head symbols stay distinct after a
        // shared-child merge, and node_count collapses exactly.
        let mut eg = EGraph::<String>::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let fa = app(&mut eg, "f", vec![a]);
        let fb = app(&mut eg, "f", vec![b]);
        let ga = app(&mut eg, "g", vec![a]);
        let gb = app(&mut eg, "g", vec![b]);
        assert_eq!(eg.node_count(), 6);
        eg.merge(a, b);
        eg.rebuild();
        assert!(eg.equiv(fa, fb));
        assert!(eg.equiv(ga, gb));
        assert!(!eg.equiv(fa, ga), "f and g must NOT be conflated");
        // Live exact nodes: {leaf a, leaf b} + {f(rep)} + {g(rep)} = 4.
        assert_eq!(eg.node_count(), 4);
    }

    #[test]
    fn budget_refuses_fresh_node_without_overshoot() {
        let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 2 });
        assert!(eg.try_add_with_budget(ENode::leaf("a".into())).is_some());
        assert!(eg.try_add_with_budget(ENode::leaf("b".into())).is_some());
        assert!(!eg.node_limit_reached());
        let c = eg.try_add_with_budget(ENode::leaf("c".into()));
        assert!(c.is_none(), "fresh node beyond budget is refused");
        assert!(eg.node_limit_reached());
        assert_eq!(eg.node_count(), 2, "no overshoot");
        // An existing node still resolves (dedup, no growth).
        let a_again = eg.try_add_with_budget(ENode::leaf("a".into()));
        assert!(a_again.is_some());
        assert_eq!(eg.node_count(), 2);
    }

    #[test]
    fn content_key_is_exact_and_order_sensitive() {
        let n = ENode::new("f".to_string(), vec![EClassId(1), EClassId(2)]);
        let same = ENode::new("f".to_string(), vec![EClassId(1), EClassId(2)]);
        let swapped = ENode::new("f".to_string(), vec![EClassId(2), EClassId(1)]);
        let other_op = ENode::new("g".to_string(), vec![EClassId(1), EClassId(2)]);
        assert_eq!(n.content_key(), same.content_key());
        assert_ne!(n.content_key(), swapped.content_key(), "child order is identity");
        assert_ne!(n.content_key(), other_op.content_key(), "label is identity");
    }
}
