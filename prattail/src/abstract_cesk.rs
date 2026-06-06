//! Abstract CESK Machine: Abstract GC + WPDS Introspective Extension.
//!
//! Implements the abstract CESK machine from Van Horn & Might's "Abstracting
//! Abstract Machines" (ICFP 2010, §3–4) and Earl et al.'s "Introspective
//! Pushdown Analysis" (JFP 2013, §4–7).
//!
//! ## Abstract GC
//!
//! In the abstract machine, the store maps addresses to **sets** of values
//! (due to address reuse in 0CFA/k-CFA). The `LL_σ` (live locations)
//! function from AAM §4 computes which addresses are reachable from the
//! current configuration. Unreachable abstract cells can be removed,
//! improving analysis precision.
//!
//! ## Evaluation WPDS
//!
//! Extends the parsing WPDS (`wpds.rs`) with an evaluation WPDS that models
//! the CESK machine as a pushdown system:
//! - Control states: `(Exp × Env_hat × Store_hat)`
//! - Stack alphabet: `EvalFrame` variants
//!
//! ## Dyck State Graphs
//!
//! Compact representations of all reachable evaluation configurations,
//! constructed iteratively. Enables static analysis queries like
//! "Can closure f flow to call site s?" via DSG reachability.
//!
//! ## References
//!
//! - Van Horn, D. & Might, M. (2010). Abstracting Abstract Machines. *ICFP 2010*.
//! - Earl, C. et al. (2013). Introspective Pushdown Analysis. *JFP*.
//! - Bouajjani, A. et al. (1997). Reachability analysis of pushdown automata.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::cesk_store::StoreAddr;
#[cfg(test)]
use crate::cesk_store::{
    AllocStrategy, CeskConfig, KCfaAlloc, MonotonicAlloc, OneCfaAlloc, ZeroCfaAlloc,
};

// ══════════════════════════════════════════════════════════════════════════════
// Abstract Store — Maps addrs to SETS of values
// ══════════════════════════════════════════════════════════════════════════════

/// Abstract store: maps addresses to **sets** of abstract values.
///
/// In abstract interpretation, multiple concrete values may be allocated
/// at the same abstract address (e.g., in 0CFA where `alloc(v, _) = v`).
/// The abstract store joins these into a set: `σ_hat[a] = {v₁, v₂, ...}`.
///
/// Abstract GC removes addresses whose value sets are unreachable,
/// which prevents spurious flows from accumulating.
#[derive(Debug, Clone)]
pub struct AbstractStore {
    /// Abstract cells: addr → set of values.
    cells: HashMap<u64, HashSet<AbstractValue>>,
}

/// Abstract value in the abstract store.
///
/// Simplified representation for static analysis. Concrete `StoreValue`
/// variants are abstracted:
/// - `Simple(s)` → `AbstractValue::Atom(s)` (keep the string for matching)
/// - `Closure { env, body }` → `AbstractValue::Closure(env_addrs, body)`
/// - `Void` → `AbstractValue::Void`
/// - Others → `AbstractValue::Top` (over-approximation)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AbstractValue {
    /// Atomic value (string constant or identifier).
    Atom(String),
    /// Abstract closure: set of captured address ids + body.
    Closure {
        /// Global address ids captured by this closure.
        captured_addrs: Vec<u64>,
        /// Body expression (display form).
        body: String,
    },
    /// Void/unit value.
    Void,
    /// Top element: over-approximation of any value.
    Top,
}

impl AbstractStore {
    /// Create an empty abstract store.
    pub fn new() -> Self {
        Self { cells: HashMap::new() }
    }

    /// Join a value into the abstract cell at the given address.
    ///
    /// If the address already has values, the new value is added to the set.
    /// This is the fundamental widening operation of the abstract store.
    pub fn join(&mut self, addr: u64, value: AbstractValue) {
        self.cells.entry(addr).or_default().insert(value);
    }

    /// Get the set of values at an address.
    pub fn get(&self, addr: u64) -> Option<&HashSet<AbstractValue>> {
        self.cells.get(&addr)
    }

    /// Number of abstract cells.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the abstract store is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// All addresses in the abstract store.
    pub fn addresses(&self) -> Vec<u64> {
        self.cells.keys().copied().collect()
    }

    /// Remove an address from the abstract store (GC sweep).
    pub fn remove(&mut self, addr: u64) {
        self.cells.remove(&addr);
    }
}

impl Default for AbstractStore {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Abstract GC — LL_σ for abstract stores
// ══════════════════════════════════════════════════════════════════════════════

/// Compute abstract live locations from a root set.
///
/// Extension of `LL_σ` (gc.rs) to abstract stores where cells contain
/// **sets** of values. Each value in a cell's set contributes its
/// referenced addresses to the worklist.
///
/// ```text
///   LL_σ_hat(ρ) = rng(ρ) ∪ ⋃_{a ∈ rng(ρ)} ⋃_{v ∈ σ_hat(a)} refs(v)
/// ```
pub fn abstract_live_locations(
    env: &HashMap<String, StoreAddr>,
    store: &AbstractStore,
) -> HashSet<u64> {
    let mut live = HashSet::new();
    let mut worklist: VecDeque<u64> = env.values().map(|a| a.id()).collect();

    while let Some(addr) = worklist.pop_front() {
        if !live.insert(addr) {
            continue;
        }

        if let Some(values) = store.get(addr) {
            for value in values {
                match value {
                    AbstractValue::Closure { captured_addrs, .. } => {
                        for &a in captured_addrs {
                            if !live.contains(&a) {
                                worklist.push_back(a);
                            }
                        }
                    },
                    AbstractValue::Atom(_) | AbstractValue::Void | AbstractValue::Top => {},
                }
            }
        }
    }

    live
}

/// Perform abstract GC on an abstract store.
///
/// Removes all addresses not reachable from the root environment.
/// Returns the number of addresses collected.
pub fn abstract_gc(env: &HashMap<String, StoreAddr>, store: &mut AbstractStore) -> usize {
    let live = abstract_live_locations(env, store);
    let all_addrs: Vec<u64> = store.addresses();
    let mut collected = 0;
    for addr in all_addrs {
        if !live.contains(&addr) {
            store.remove(addr);
            collected += 1;
        }
    }
    collected
}

// ══════════════════════════════════════════════════════════════════════════════
// Evaluation WPDS — Pushdown model of CESK evaluation
// ══════════════════════════════════════════════════════════════════════════════

/// A WPDS control state for the evaluation machine.
///
/// In the evaluation WPDS, control states encode the current expression
/// being evaluated along with the abstract environment and store.
/// For soundness, the environment and store are abstracted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EvalControlState {
    /// The expression being evaluated (display form, canonicalized).
    pub expr: String,
    /// Abstract environment fingerprint (hash of env content).
    pub env_fingerprint: u64,
    /// Abstract store fingerprint (hash of store content).
    pub store_fingerprint: u64,
}

/// A stack symbol in the evaluation WPDS.
///
/// Mirrors `EvalFrame` variants but abstracted to hashable form.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EvalStackSymbol {
    /// Binary operator context: `lhs ⊕ □`
    BinOp { operator: String },
    /// Unary operator context: `⊕ □`
    UnaryOp { operator: String },
    /// Let-binding context: `let x = □ in body`
    LetBody { var_name: String },
    /// Parallel context: `□ | remaining...`
    Parallel { remaining_count: usize },
    /// Rewrite continuation
    RewriteCont { rule_name: String },
    /// Set continuation: `set! x □`
    SetCont { var_name: String },
}

/// A transition rule in the evaluation WPDS.
///
/// `(p, γ) → (p', w)` where:
/// - `p` is the source control state
/// - `γ` is the top stack symbol consumed
/// - `p'` is the target control state
/// - `w` is the stack word pushed (0, 1, or 2 symbols)
#[derive(Debug, Clone)]
pub struct EvalWpdsRule {
    /// Source control state.
    pub source: EvalControlState,
    /// Stack symbol consumed.
    pub consumed: EvalStackSymbol,
    /// Target control state.
    pub target: EvalControlState,
    /// Stack symbols pushed (right-to-left: last element is new top).
    pub pushed: Vec<EvalStackSymbol>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Dyck State Graph — Compact reachable configuration representation
// ══════════════════════════════════════════════════════════════════════════════

/// A node in the Dyck State Graph.
///
/// Represents a reachable evaluation configuration: the control state
/// at some point during abstract evaluation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DsgNode {
    /// The evaluation control state.
    pub state: EvalControlState,
}

/// An edge in the Dyck State Graph.
///
/// Labeled with the stack symbol that was pushed or popped
/// during the transition.
#[derive(Debug, Clone)]
pub struct DsgEdge {
    /// Source node index.
    pub source: usize,
    /// Target node index.
    pub target: usize,
    /// Stack symbol label.
    pub symbol: EvalStackSymbol,
    /// Whether this is a push (true) or pop (false) edge.
    pub is_push: bool,
}

/// Dyck State Graph: compact representation of reachable configurations.
///
/// Constructed iteratively by expanding from an initial configuration.
/// The graph encodes the reachable subset of the evaluation pushdown
/// system and enables static analysis queries via graph reachability.
///
/// ## Construction (Earl et al. §6, p.20)
///
/// ```text
/// 1. Initialize: DSG = {initial_config}
/// 2. For each unexpanded config c:
///    a. Compute successors via CESK transition
///    b. Add successor nodes/edges to DSG
///    c. Mark c as expanded
/// 3. Repeat until no unexpanded configs remain (fixpoint)
/// ```
#[derive(Debug, Clone)]
pub struct DyckStateGraph {
    /// Nodes: reachable control states.
    pub nodes: Vec<DsgNode>,
    /// Node lookup: state → index.
    node_index: HashMap<EvalControlState, usize>,
    /// Edges: transitions between states.
    pub edges: Vec<DsgEdge>,
}

impl DyckStateGraph {
    /// Create an empty DSG.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            node_index: HashMap::new(),
            edges: Vec::new(),
        }
    }

    /// Add a node to the DSG, returning its index.
    ///
    /// If the node already exists, returns the existing index.
    pub fn add_node(&mut self, state: EvalControlState) -> usize {
        if let Some(&idx) = self.node_index.get(&state) {
            return idx;
        }
        let idx = self.nodes.len();
        self.node_index.insert(state.clone(), idx);
        self.nodes.push(DsgNode { state });
        idx
    }

    /// Add an edge to the DSG.
    pub fn add_edge(
        &mut self,
        source: usize,
        target: usize,
        symbol: EvalStackSymbol,
        is_push: bool,
    ) {
        self.edges.push(DsgEdge { source, target, symbol, is_push });
    }

    /// Number of nodes in the DSG.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Number of edges in the DSG.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Check if an expression can flow to a particular control state.
    ///
    /// "Can closure `f` flow to call site `s`?" → DSG reachability.
    pub fn is_reachable(&self, from_expr: &str, to_expr: &str) -> bool {
        let from_nodes: Vec<usize> = self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.state.expr == from_expr)
            .map(|(i, _)| i)
            .collect();

        let to_nodes: HashSet<usize> = self
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.state.expr == to_expr)
            .map(|(i, _)| i)
            .collect();

        // BFS from from_nodes
        let mut visited = HashSet::new();
        let mut queue: VecDeque<usize> = from_nodes.into_iter().collect();

        while let Some(node) = queue.pop_front() {
            if to_nodes.contains(&node) {
                return true;
            }
            if !visited.insert(node) {
                continue;
            }
            for edge in &self.edges {
                if edge.source == node && !visited.contains(&edge.target) {
                    queue.push_back(edge.target);
                }
            }
        }

        false
    }
}

impl Default for DyckStateGraph {
    fn default() -> Self {
        Self::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abstract_store_join_and_get() {
        let mut store = AbstractStore::new();
        store.join(0, AbstractValue::Atom("a".to_string()));
        store.join(0, AbstractValue::Atom("b".to_string()));
        store.join(1, AbstractValue::Void);

        assert_eq!(store.len(), 2);
        let vals = store.get(0).expect("should have addr 0");
        assert_eq!(vals.len(), 2);
        assert!(vals.contains(&AbstractValue::Atom("a".to_string())));
        assert!(vals.contains(&AbstractValue::Atom("b".to_string())));
    }

    #[test]
    fn abstract_live_locations_basic() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), StoreAddr::Local(0));
        env.insert("y".to_string(), StoreAddr::Local(1));

        let mut store = AbstractStore::new();
        store.join(0, AbstractValue::Atom("live".to_string()));
        store.join(1, AbstractValue::Atom("live".to_string()));
        store.join(2, AbstractValue::Atom("dead".to_string()));

        let live = abstract_live_locations(&env, &store);
        assert!(live.contains(&0));
        assert!(live.contains(&1));
        assert!(!live.contains(&2));
    }

    #[test]
    fn abstract_live_locations_follows_closures() {
        let mut env = HashMap::new();
        env.insert("f".to_string(), StoreAddr::Local(0));

        let mut store = AbstractStore::new();
        store.join(
            0,
            AbstractValue::Closure {
                captured_addrs: vec![1],
                body: "body".to_string(),
            },
        );
        store.join(1, AbstractValue::Atom("reachable".to_string()));
        store.join(2, AbstractValue::Atom("dead".to_string()));

        let live = abstract_live_locations(&env, &store);
        assert!(live.contains(&0)); // Root
        assert!(live.contains(&1)); // Via closure
        assert!(!live.contains(&2)); // Dead
    }

    #[test]
    fn abstract_gc_collects_unreachable() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), StoreAddr::Local(0));

        let mut store = AbstractStore::new();
        store.join(0, AbstractValue::Atom("live".to_string()));
        store.join(1, AbstractValue::Atom("dead1".to_string()));
        store.join(2, AbstractValue::Atom("dead2".to_string()));

        let collected = abstract_gc(&env, &mut store);
        assert_eq!(collected, 2);
        assert_eq!(store.len(), 1);
        assert!(store.get(0).is_some());
        assert!(store.get(1).is_none());
    }

    #[test]
    fn dsg_construction_and_reachability() {
        let mut dsg = DyckStateGraph::new();

        let s0 = dsg.add_node(EvalControlState {
            expr: "f(x)".to_string(),
            env_fingerprint: 0,
            store_fingerprint: 0,
        });
        let s1 = dsg.add_node(EvalControlState {
            expr: "g(y)".to_string(),
            env_fingerprint: 0,
            store_fingerprint: 0,
        });
        let s2 = dsg.add_node(EvalControlState {
            expr: "result".to_string(),
            env_fingerprint: 0,
            store_fingerprint: 0,
        });

        dsg.add_edge(s0, s1, EvalStackSymbol::BinOp { operator: "+".to_string() }, true);
        dsg.add_edge(s1, s2, EvalStackSymbol::BinOp { operator: "+".to_string() }, false);

        assert_eq!(dsg.node_count(), 3);
        assert_eq!(dsg.edge_count(), 2);
        assert!(dsg.is_reachable("f(x)", "result"));
        assert!(!dsg.is_reachable("result", "f(x)"));
    }

    #[test]
    fn dsg_add_duplicate_node() {
        let mut dsg = DyckStateGraph::new();
        let state = EvalControlState {
            expr: "x".to_string(),
            env_fingerprint: 0,
            store_fingerprint: 0,
        };
        let i1 = dsg.add_node(state.clone());
        let i2 = dsg.add_node(state);
        assert_eq!(i1, i2);
        assert_eq!(dsg.node_count(), 1);
    }

    // ── AllocStrategy tests (CESK-12) ───────────────────────────────────

    #[test]
    fn monotonic_alloc_strictly_increasing() {
        let alloc = MonotonicAlloc::new();
        let config = CeskConfig {
            control: "x".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };
        let a0 = alloc.alloc("x", &config);
        let a1 = alloc.alloc("y", &config);
        let a2 = alloc.alloc("z", &config);
        assert_eq!(a0, 0);
        assert_eq!(a1, 1);
        assert_eq!(a2, 2);
    }

    #[test]
    fn zero_cfa_same_var_same_addr() {
        let alloc = ZeroCfaAlloc;
        let config = CeskConfig {
            control: "expr1".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };
        let a1 = alloc.alloc("x", &config);
        let config2 = CeskConfig { control: "expr2".to_string(), ..config };
        let a2 = alloc.alloc("x", &config2);
        assert_eq!(a1, a2, "0CFA: same var → same addr regardless of context");
    }

    #[test]
    fn one_cfa_different_context_different_addr() {
        let alloc = OneCfaAlloc;
        let config1 = CeskConfig {
            control: "call_site_1".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };
        let config2 = CeskConfig {
            control: "call_site_2".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };
        let a1 = alloc.alloc("x", &config1);
        let a2 = alloc.alloc("x", &config2);
        assert_ne!(a1, a2, "1CFA: same var at different call sites → different addrs");
    }

    #[test]
    fn k_cfa_uses_context_history() {
        let alloc = KCfaAlloc::new(2);
        let config_a = CeskConfig {
            control: "a".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };
        let config_b = CeskConfig {
            control: "b".to_string(),
            env_size: 0,
            store_size: 0,
            stack_depth: 0,
        };

        // Build context: [a, b]
        alloc.tick(&config_a);
        alloc.tick(&config_b);
        let addr_ab = alloc.alloc("x", &config_b);

        // Build context: [b, a] (different order)
        alloc.tick(&config_a); // now context = [b, a]
        let addr_ba = alloc.alloc("x", &config_a);

        assert_ne!(addr_ab, addr_ba, "k-CFA: different context histories → different addrs");
    }
}
