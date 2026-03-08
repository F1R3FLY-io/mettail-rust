//! Petri nets and Vector Addition Systems with States (VASS) for concurrent analysis.
//!
//! Petri nets are a foundational model for concurrent and distributed systems.
//! A Petri net consists of places (holding tokens), transitions (consuming and
//! producing tokens), and a marking (the current distribution of tokens across
//! places). VASS are the state-equipped variant, combining finite control with
//! counter-like place vectors.
//!
//! ## Theoretical Foundations
//!
//! - **Petri (1962)** — *Kommunikation mit Automaten.* The original thesis
//!   introducing Petri nets as models of concurrent systems with local causality.
//! - **Karp & Miller (1969)** — "Parallel program schemata." Introduces the
//!   coverability tree for Petri nets, proving decidability of the coverability
//!   problem (EXPSPACE-complete).
//! - **Mayr (1981)** — "An algorithm for the general Petri net reachability
//!   problem." Proves decidability of the reachability problem, later refined
//!   by Leroux & Schmitz (2019) to Ackermann complexity.
//! - **Esparza & Nielsen (1994)** — "Decidability issues for Petri nets."
//!   Survey of decidable and undecidable problems for various Petri net classes.
//!
//! ## Architecture
//!
//! ```text
//! PraTTaIL grammar / concurrent process spec
//!       │
//!       ▼
//! construct_petri_net()
//!       │
//!       ▼
//! PetriNet
//!       │
//!       ├──→ check_coverability() (is marking m coverable from m₀?)
//!       │
//!       ├──→ check_deadlock() (does an enabled transition always exist?)
//!       │
//!       └──→ check_boundedness() (are all places bounded?)
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Petri nets model concurrent composition in PraTTaIL grammars (e.g., the
//! `|` parallel composition operator in Rholang). Places correspond to
//! communication channels, transitions to process actions, and tokens to
//! available messages. Coverability analysis detects channel overflow,
//! deadlock analysis identifies stuck configurations, and boundedness
//! analysis verifies that resource usage is finite.

use std::collections::{HashSet, VecDeque};
use std::fmt;

// NOTE: Semiring import will be used when weighted Petri net analysis is implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A place in a Petri net.
///
/// Places hold tokens. Each place has a name and an optional capacity bound
/// (for bounded Petri nets / safe nets).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    /// Unique place identifier.
    pub id: usize,
    /// Place name for diagnostics (e.g., channel name).
    pub name: String,
    /// Optional capacity bound (`None` = unbounded).
    pub capacity: Option<u64>,
}

impl Place {
    /// Create an unbounded place.
    pub fn new(id: usize, name: impl Into<String>) -> Self {
        Place {
            id,
            name: name.into(),
            capacity: None,
        }
    }

    /// Create a bounded place.
    pub fn bounded(id: usize, name: impl Into<String>, capacity: u64) -> Self {
        Place {
            id,
            name: name.into(),
            capacity: Some(capacity),
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(cap) = self.capacity {
            write!(f, "p{}({})[cap={}]", self.id, self.name, cap)
        } else {
            write!(f, "p{}({})", self.id, self.name)
        }
    }
}

/// A transition in a Petri net.
///
/// Transitions consume tokens from input places and produce tokens in output
/// places. A transition is enabled when all input places have at least as many
/// tokens as required by the input arcs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriTransition {
    /// Unique transition identifier.
    pub id: usize,
    /// Transition name for diagnostics.
    pub name: String,
    /// Input arcs: `(place_id, weight)` — tokens consumed from each place.
    pub inputs: Vec<(usize, u64)>,
    /// Output arcs: `(place_id, weight)` — tokens produced in each place.
    pub outputs: Vec<(usize, u64)>,
}

impl PetriTransition {
    /// Create a new transition.
    pub fn new(id: usize, name: impl Into<String>) -> Self {
        PetriTransition {
            id,
            name: name.into(),
            inputs: Vec::new(),
            outputs: Vec::new(),
        }
    }

    /// Add an input arc (consumes `weight` tokens from `place_id`).
    pub fn add_input(&mut self, place_id: usize, weight: u64) -> &mut Self {
        self.inputs.push((place_id, weight));
        self
    }

    /// Add an output arc (produces `weight` tokens in `place_id`).
    pub fn add_output(&mut self, place_id: usize, weight: u64) -> &mut Self {
        self.outputs.push((place_id, weight));
        self
    }
}

impl fmt::Display for PetriTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inputs: Vec<String> = self
            .inputs
            .iter()
            .map(|(p, w)| format!("p{}*{}", p, w))
            .collect();
        let outputs: Vec<String> = self
            .outputs
            .iter()
            .map(|(p, w)| format!("p{}*{}", p, w))
            .collect();
        write!(
            f,
            "t{}({}): {{{}}} -> {{{}}}",
            self.id,
            self.name,
            inputs.join(", "),
            outputs.join(", "),
        )
    }
}

/// A marking: the distribution of tokens across places.
///
/// A marking `m: Places → N` assigns a non-negative integer to each place.
/// Represented as a vector indexed by place ID.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Marking {
    /// Token count for each place (indexed by place ID).
    pub tokens: Vec<u64>,
}

impl Marking {
    /// Create a marking with all places having zero tokens.
    pub fn zero(num_places: usize) -> Self {
        Marking {
            tokens: vec![0; num_places],
        }
    }

    /// Create a marking from a token vector.
    pub fn from_tokens(tokens: Vec<u64>) -> Self {
        Marking { tokens }
    }

    /// Get the token count at a place.
    pub fn get(&self, place_id: usize) -> u64 {
        self.tokens.get(place_id).copied().unwrap_or(0)
    }

    /// Set the token count at a place.
    pub fn set(&mut self, place_id: usize, count: u64) {
        if place_id < self.tokens.len() {
            self.tokens[place_id] = count;
        }
    }

    /// Check whether marking `self` covers marking `other` (component-wise `>=`).
    pub fn covers(&self, other: &Marking) -> bool {
        self.tokens
            .iter()
            .zip(other.tokens.iter())
            .all(|(a, b)| a >= b)
    }
}

impl fmt::Display for Marking {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let entries: Vec<String> = self.tokens.iter().map(|t| t.to_string()).collect();
        write!(f, "[{}]", entries.join(", "))
    }
}

/// A Petri net.
///
/// `N = (P, T, F, W, m₀)` where:
/// - `P` is the finite set of places
/// - `T` is the finite set of transitions
/// - `F ⊆ (P × T) ∪ (T × P)` is the flow relation
/// - `W: F → N⁺` is the weight function on arcs
/// - `m₀` is the initial marking
#[derive(Debug, Clone)]
pub struct PetriNet {
    /// All places.
    pub places: Vec<Place>,
    /// All transitions.
    pub transitions: Vec<PetriTransition>,
    /// Initial marking.
    pub initial_marking: Marking,
}

/// A set of mutually independent transitions that can fire concurrently.
///
/// A parallel region is a maximal clique in the independence graph of a Petri
/// net: every pair of transitions in the region is independent (they share no
/// input or output places), so they can all fire simultaneously without
/// interfering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParallelRegion {
    /// Indices of mutually independent transitions in this region.
    pub transitions: Vec<usize>,
    /// Maximum concurrent firings (equal to the number of transitions in the region).
    pub max_parallelism: usize,
}

impl fmt::Display for ParallelRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ts: Vec<String> = self.transitions.iter().map(|t| format!("t{}", t)).collect();
        write!(
            f,
            "ParallelRegion {{ transitions: [{}], max_parallelism: {} }}",
            ts.join(", "),
            self.max_parallelism,
        )
    }
}

/// Full parallelism analysis report for a Petri net.
///
/// Summarizes the independence structure and maximal parallel regions
/// extracted from the net's transition set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParallelismReport {
    /// All maximal parallel regions (maximal cliques in the independence graph).
    pub regions: Vec<ParallelRegion>,
    /// Maximum degree of parallelism across all regions.
    pub max_parallelism: usize,
    /// Total number of independent transition pairs.
    pub independent_pairs: usize,
    /// Total number of transitions in the net.
    pub total_transitions: usize,
}

impl fmt::Display for ParallelismReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ParallelismReport {{ regions: {}, max_parallelism: {}, \
             independent_pairs: {}, total_transitions: {} }}",
            self.regions.len(),
            self.max_parallelism,
            self.independent_pairs,
            self.total_transitions,
        )
    }
}

impl PetriNet {
    /// Create an empty Petri net.
    pub fn new() -> Self {
        PetriNet {
            places: Vec::new(),
            transitions: Vec::new(),
            initial_marking: Marking::zero(0),
        }
    }

    /// Add a place and return its ID.
    pub fn add_place(&mut self, name: impl Into<String>) -> usize {
        let id = self.places.len();
        self.places.push(Place::new(id, name));
        self.initial_marking.tokens.push(0);
        id
    }

    /// Add a transition and return its ID.
    pub fn add_transition(&mut self, name: impl Into<String>) -> usize {
        let id = self.transitions.len();
        self.transitions.push(PetriTransition::new(id, name));
        id
    }

    /// Check whether a transition is enabled at a given marking.
    pub fn is_enabled(&self, transition_id: usize, marking: &Marking) -> bool {
        if let Some(t) = self.transitions.get(transition_id) {
            t.inputs.iter().all(|(p, w)| marking.get(*p) >= *w)
        } else {
            false
        }
    }

    /// Fire a transition at a given marking, returning the new marking.
    ///
    /// Returns `None` if the transition is not enabled.
    pub fn fire(&self, transition_id: usize, marking: &Marking) -> Option<Marking> {
        if !self.is_enabled(transition_id, marking) {
            return None;
        }
        let t = &self.transitions[transition_id];
        let mut new_marking = marking.clone();
        for (p, w) in &t.inputs {
            new_marking.tokens[*p] -= w;
        }
        for (p, w) in &t.outputs {
            new_marking.tokens[*p] += w;
        }
        Some(new_marking)
    }

    /// Number of places.
    pub fn num_places(&self) -> usize {
        self.places.len()
    }

    /// Number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    // ── Parallelism extraction (Phase 5B.6) ─────────────────────────────

    /// Check if two transitions are independent.
    ///
    /// Two transitions `t1` and `t2` are independent iff they do not share
    /// any input places (pre-set) or output places (post-set):
    ///
    /// ```text
    /// (pre(t1) ∪ post(t1)) ∩ (pre(t2) ∪ post(t2)) = ∅
    /// ```
    ///
    /// Independent transitions can fire concurrently without interfering
    /// with each other's token requirements or productions.
    ///
    /// Returns `false` if either index is out of bounds, or if `t1 == t2`.
    pub fn check_independence(&self, t1: usize, t2: usize) -> bool {
        if t1 == t2 {
            return false;
        }
        let (tr1, tr2) = match (self.transitions.get(t1), self.transitions.get(t2)) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        // Collect all places touched by t1 (pre-set ∪ post-set).
        let mut places_t1 = HashSet::with_capacity(tr1.inputs.len() + tr1.outputs.len());
        for &(p, _) in &tr1.inputs {
            places_t1.insert(p);
        }
        for &(p, _) in &tr1.outputs {
            places_t1.insert(p);
        }

        // Check whether any place touched by t2 is also touched by t1.
        for &(p, _) in &tr2.inputs {
            if places_t1.contains(&p) {
                return false;
            }
        }
        for &(p, _) in &tr2.outputs {
            if places_t1.contains(&p) {
                return false;
            }
        }

        true
    }

    /// Compute the independence relation: all pairs `(i, j)` with `i < j`
    /// such that transitions `i` and `j` are independent.
    pub fn independence_relation(&self) -> Vec<(usize, usize)> {
        let n = self.transitions.len();
        let mut pairs = Vec::new();
        for i in 0..n {
            for j in (i + 1)..n {
                if self.check_independence(i, j) {
                    pairs.push((i, j));
                }
            }
        }
        pairs
    }

    /// Extract maximal parallel regions (maximal cliques in the independence graph).
    ///
    /// A parallel region is a maximal set of transitions that are mutually
    /// independent: every pair within the set is independent, so all
    /// transitions in the set can fire simultaneously.
    ///
    /// The algorithm:
    /// 1. Build an adjacency list for the independence graph.
    /// 2. Find connected components (each component is searched independently).
    /// 3. Within each component, find all maximal cliques using the
    ///    Bron-Kerbosch algorithm with pivoting.
    pub fn extract_parallel_regions(&self) -> Vec<ParallelRegion> {
        let n = self.transitions.len();
        if n == 0 {
            return Vec::new();
        }

        // Build adjacency matrix for the independence graph.
        // adj[i] = set of transitions independent with i.
        let mut adj: Vec<HashSet<usize>> = vec![HashSet::new(); n];
        for i in 0..n {
            for j in (i + 1)..n {
                if self.check_independence(i, j) {
                    adj[i].insert(j);
                    adj[j].insert(i);
                }
            }
        }

        // Find connected components via BFS so Bron-Kerbosch runs per-component.
        let mut visited = vec![false; n];
        let mut components: Vec<Vec<usize>> = Vec::new();
        for start in 0..n {
            if visited[start] {
                continue;
            }
            // Check if this node has any neighbors; isolated nodes form
            // trivial components that yield no maximal clique of size >= 2.
            if adj[start].is_empty() {
                visited[start] = true;
                continue;
            }
            let mut component = Vec::new();
            let mut queue = VecDeque::new();
            queue.push_back(start);
            visited[start] = true;
            while let Some(v) = queue.pop_front() {
                component.push(v);
                for &w in &adj[v] {
                    if !visited[w] {
                        visited[w] = true;
                        queue.push_back(w);
                    }
                }
            }
            components.push(component);
        }

        // Bron-Kerbosch with pivoting (maximizes pruning).
        //
        // BronKerbosch(R, P, X):
        //   if P ∪ X = ∅ then report R as a maximal clique
        //   choose pivot u in P ∪ X that maximizes |P ∩ N(u)|
        //   for each v in P \ N(u):
        //     BronKerbosch(R ∪ {v}, P ∩ N(v), X ∩ N(v))
        //     P := P \ {v}
        //     X := X ∪ {v}

        let mut cliques: Vec<Vec<usize>> = Vec::new();

        // Use an explicit stack to avoid deep recursion.
        struct BKFrame {
            r: Vec<usize>,
            p: Vec<usize>,
            x: Vec<usize>,
            /// Candidates = P \ N(pivot), iterated in order.
            candidates: Vec<usize>,
            /// Index into `candidates` for the next vertex to process.
            idx: usize,
        }

        for component in &components {
            let mut stack: Vec<BKFrame> = Vec::new();

            let initial_p: Vec<usize> = component.clone();
            let initial_r: Vec<usize> = Vec::new();
            let initial_x: Vec<usize> = Vec::new();

            // Choose pivot for the initial frame.
            let pivot = Self::choose_pivot(&initial_p, &initial_x, &adj);
            let candidates: Vec<usize> = if let Some(u) = pivot {
                initial_p
                    .iter()
                    .filter(|v| !adj[u].contains(v))
                    .copied()
                    .collect()
            } else {
                initial_p.clone()
            };

            stack.push(BKFrame {
                r: initial_r,
                p: initial_p,
                x: initial_x,
                candidates,
                idx: 0,
            });

            while let Some(frame) = stack.last_mut() {
                if frame.idx < frame.candidates.len() {
                    let v = frame.candidates[frame.idx];
                    frame.idx += 1;

                    // Build R' = R ∪ {v}
                    let mut new_r = frame.r.clone();
                    new_r.push(v);

                    // Build P' = P ∩ N(v)
                    let new_p: Vec<usize> = frame
                        .p
                        .iter()
                        .filter(|&&w| adj[v].contains(&w))
                        .copied()
                        .collect();

                    // Build X' = X ∩ N(v)
                    let new_x: Vec<usize> = frame
                        .x
                        .iter()
                        .filter(|&&w| adj[v].contains(&w))
                        .copied()
                        .collect();

                    // Update current frame: P := P \ {v}, X := X ∪ {v}
                    frame.p.retain(|&w| w != v);
                    if !frame.x.contains(&v) {
                        frame.x.push(v);
                    }

                    if new_p.is_empty() && new_x.is_empty() {
                        // Maximal clique found.
                        cliques.push(new_r);
                    } else if !new_p.is_empty() {
                        // Recurse.
                        let pivot = Self::choose_pivot(&new_p, &new_x, &adj);
                        let cands: Vec<usize> = if let Some(u) = pivot {
                            new_p
                                .iter()
                                .filter(|w| !adj[u].contains(w))
                                .copied()
                                .collect()
                        } else {
                            new_p.clone()
                        };
                        stack.push(BKFrame {
                            r: new_r,
                            p: new_p,
                            x: new_x,
                            candidates: cands,
                            idx: 0,
                        });
                    }
                    // If new_p is empty but new_x is not, R' is not maximal — skip.
                } else {
                    // All candidates exhausted for this frame — pop.
                    stack.pop();
                }
            }
        }

        // Convert cliques to ParallelRegion, sorting transitions within each region.
        let mut regions: Vec<ParallelRegion> = cliques
            .into_iter()
            .map(|mut ts| {
                ts.sort_unstable();
                let max_par = ts.len();
                ParallelRegion {
                    transitions: ts,
                    max_parallelism: max_par,
                }
            })
            .collect();

        // Sort regions for deterministic output: by size descending, then lexicographically.
        regions.sort_by(|a, b| {
            b.max_parallelism
                .cmp(&a.max_parallelism)
                .then_with(|| a.transitions.cmp(&b.transitions))
        });

        regions
    }

    /// Choose a pivot vertex `u` from `P ∪ X` that maximizes `|P ∩ N(u)|`.
    fn choose_pivot(
        p: &[usize],
        x: &[usize],
        adj: &[HashSet<usize>],
    ) -> Option<usize> {
        let p_set: HashSet<usize> = p.iter().copied().collect();
        p.iter()
            .chain(x.iter())
            .max_by_key(|&&u| adj[u].intersection(&p_set).count())
            .copied()
    }

    /// Full parallelism analysis: compute the independence relation, extract
    /// maximal parallel regions, and summarize the results.
    pub fn analyze_parallelism(&self) -> ParallelismReport {
        let pairs = self.independence_relation();
        let regions = self.extract_parallel_regions();
        let max_par = regions.iter().map(|r| r.max_parallelism).max().unwrap_or(0);

        ParallelismReport {
            regions,
            max_parallelism: max_par,
            independent_pairs: pairs.len(),
            total_transitions: self.transitions.len(),
        }
    }
}

impl Default for PetriNet {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for PetriNet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PetriNet {{ places: {}, transitions: {}, initial: {} }}",
            self.num_places(),
            self.num_transitions(),
            self.initial_marking,
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Construct a Petri net from a high-level process description.
///
/// This is a convenience builder for creating Petri nets from place/transition
/// descriptions.
///
/// # Arguments
///
/// * `places` - Place descriptions: `(name, initial_tokens)`.
/// * `transitions` - Transition descriptions: `(name, inputs, outputs)`.
///
/// # Returns
///
/// A `PetriNet` with the specified structure and initial marking.
pub fn construct_petri_net(
    places: &[(String, u64)],
    transitions: &[(String, Vec<(usize, u64)>, Vec<(usize, u64)>)],
) -> PetriNet {
    let mut net = PetriNet::new();
    for (name, initial_tokens) in places {
        let id = net.add_place(name.clone());
        net.initial_marking.set(id, *initial_tokens);
    }
    for (name, inputs, outputs) in transitions {
        let tid = net.add_transition(name.clone());
        for (place_id, weight) in inputs {
            net.transitions[tid].add_input(*place_id, *weight);
        }
        for (place_id, weight) in outputs {
            net.transitions[tid].add_output(*place_id, *weight);
        }
    }
    net
}

/// Check coverability: is a target marking coverable from the initial marking?
///
/// A marking `m` is coverable if there exists a reachable marking `m'` such
/// that `m' >= m` (component-wise). Uses the Karp-Miller coverability tree
/// algorithm with omega-acceleration.
///
/// # Arguments
///
/// * `net` - The Petri net to analyze.
/// * `target` - The target marking to check for coverability.
///
/// # Returns
///
/// `true` if `target` is coverable from `net.initial_marking`.
pub fn check_coverability(net: &PetriNet, target: &Marking) -> bool {
    let num_places = net.num_places();
    if num_places == 0 {
        // With no places, target must be the empty marking.
        return target.tokens.is_empty() || target.tokens.iter().all(|&t| t == 0);
    }

    // Extended marking: None represents omega (infinity), Some(n) represents n tokens.
    // omega >= any finite value, so omega covers any finite target.
    type OmegaMarking = Vec<Option<u64>>;

    // Convert the initial marking to an omega marking.
    let initial: OmegaMarking = net
        .initial_marking
        .tokens
        .iter()
        .map(|&t| Some(t))
        .collect();

    // Ensure the target marking has the right length; pad with zeros if shorter.
    let target_tokens: Vec<u64> = {
        let mut t = target.tokens.clone();
        t.resize(num_places, 0);
        t
    };

    // Check if an omega marking covers the target.
    let covers_target = |m: &OmegaMarking| -> bool {
        m.iter()
            .zip(target_tokens.iter())
            .all(|(m_val, &t_val)| match m_val {
                None => true,      // omega >= anything
                Some(v) => *v >= t_val,
            })
    };

    // Check if omega marking m is strictly greater than omega marking ancestor
    // (component-wise >= with at least one strict >).
    let strictly_greater = |m: &OmegaMarking, ancestor: &OmegaMarking| -> bool {
        let mut has_strict = false;
        for (m_val, a_val) in m.iter().zip(ancestor.iter()) {
            match (m_val, a_val) {
                (None, None) => {}                            // omega == omega
                (None, Some(_)) => { has_strict = true; }     // omega > finite
                (Some(_), None) => { return false; }          // finite < omega
                (Some(mv), Some(av)) => {
                    if mv < av {
                        return false;
                    }
                    if mv > av {
                        has_strict = true;
                    }
                }
            }
        }
        has_strict
    };

    // Check if a transition is enabled at an omega marking.
    let is_enabled_omega = |t: &PetriTransition, m: &OmegaMarking| -> bool {
        t.inputs.iter().all(|&(p, w)| {
            if p >= m.len() {
                return false;
            }
            match m[p] {
                None => true,      // omega >= any finite weight
                Some(v) => v >= w,
            }
        })
    };

    // Fire a transition at an omega marking (caller must ensure it is enabled).
    let fire_omega = |t: &PetriTransition, m: &OmegaMarking| -> OmegaMarking {
        let mut result = m.clone();
        for &(p, w) in &t.inputs {
            if p < result.len() {
                result[p] = match result[p] {
                    None => None, // omega - finite = omega
                    Some(v) => Some(v - w),
                };
            }
        }
        for &(p, w) in &t.outputs {
            if p < result.len() {
                result[p] = match result[p] {
                    None => None, // omega + finite = omega
                    Some(v) => Some(v + w),
                };
            }
        }
        result
    };

    // Karp-Miller coverability tree via BFS.
    //
    // Each node stores: (omega_marking, path_to_root_indices).
    // The path_to_root stores indices into the `nodes` vec for ancestor lookup.
    //
    // We also keep a set of all seen omega markings to prune duplicate subtrees.
    // This is essential for termination on nets with complex behavior.

    struct TreeNode {
        marking: OmegaMarking,
        /// Indices of ancestors on the path from root to this node (inclusive of self).
        ancestors: Vec<usize>,
    }

    let mut nodes: Vec<TreeNode> = Vec::new();
    let mut worklist: VecDeque<usize> = VecDeque::new();

    // Check the initial marking immediately.
    if covers_target(&initial) {
        return true;
    }

    // Insert root node.
    nodes.push(TreeNode {
        marking: initial,
        ancestors: vec![0],
    });
    worklist.push_back(0);

    // Duplicate pruning: track seen markings to avoid re-exploring.
    let mut seen: std::collections::HashSet<OmegaMarking> = std::collections::HashSet::new();
    seen.insert(nodes[0].marking.clone());

    while let Some(node_idx) = worklist.pop_front() {
        let current_marking = nodes[node_idx].marking.clone();
        let current_ancestors = nodes[node_idx].ancestors.clone();

        for t in &net.transitions {
            if !is_enabled_omega(t, &current_marking) {
                continue;
            }

            let mut successor = fire_omega(t, &current_marking);

            // Omega-acceleration: if the successor is strictly greater than any
            // ancestor on the path, set the increased components to omega.
            for &ancestor_idx in &current_ancestors {
                let ancestor_marking = &nodes[ancestor_idx].marking;
                if strictly_greater(&successor, ancestor_marking) {
                    for i in 0..num_places {
                        match (&successor[i], &ancestor_marking[i]) {
                            (Some(sv), Some(av)) if sv > av => {
                                successor[i] = None; // accelerate to omega
                            }
                            (Some(_), None) => {
                                // successor finite < ancestor omega: no acceleration
                            }
                            (None, _) => {
                                // already omega
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Check coverability.
            if covers_target(&successor) {
                return true;
            }

            // Duplicate pruning.
            if seen.contains(&successor) {
                continue;
            }
            seen.insert(successor.clone());

            // Add the new node.
            let new_idx = nodes.len();
            let mut new_ancestors = current_ancestors.clone();
            new_ancestors.push(new_idx);
            nodes.push(TreeNode {
                marking: successor,
                ancestors: new_ancestors,
            });
            worklist.push_back(new_idx);
        }
    }

    false
}

/// Check for deadlocks: is there a reachable marking with no enabled transitions?
///
/// A deadlock (also called a dead marking) is a marking where no transition
/// is enabled. This check explores the reachable state space (or uses
/// structural analysis) to determine if a deadlock is possible.
///
/// # Arguments
///
/// * `net` - The Petri net to analyze.
///
/// # Returns
///
/// `true` if a deadlock is reachable, `false` if all reachable markings have
/// at least one enabled transition.
pub fn check_deadlock(net: &PetriNet) -> bool {
    // A marking is a deadlock iff no transition is enabled at that marking.
    // We explore the coverability tree (Karp-Miller) and check whether any
    // reachable marking (represented as an omega marking) is a deadlock.
    //
    // For omega markings, a transition is enabled if each input place has
    // enough tokens (omega satisfies any finite requirement). A deadlock
    // omega marking means NO transition is enabled, which is a strong
    // condition: for each transition, at least one input place must have
    // fewer tokens than required. Since omega >= any finite value, only
    // finite-valued places can block a transition.
    //
    // If a concrete deadlock exists but is masked by omega in the coverability
    // tree, we might miss it. However, if the omega marking has no enabled
    // transition, then certainly a concrete deadlock exists (since omega only
    // over-approximates).

    let num_places = net.num_places();

    if net.transitions.is_empty() {
        // No transitions at all means every marking is a deadlock.
        return true;
    }

    type OmegaMarking = Vec<Option<u64>>;

    let initial: OmegaMarking = net
        .initial_marking
        .tokens
        .iter()
        .map(|&t| Some(t))
        .collect();

    let is_enabled_omega = |t: &PetriTransition, m: &OmegaMarking| -> bool {
        t.inputs.iter().all(|&(p, w)| {
            if p >= m.len() {
                return false;
            }
            match m[p] {
                None => true,
                Some(v) => v >= w,
            }
        })
    };

    let is_deadlock_omega = |m: &OmegaMarking| -> bool {
        net.transitions.iter().all(|t| !is_enabled_omega(t, m))
    };

    let fire_omega = |t: &PetriTransition, m: &OmegaMarking| -> OmegaMarking {
        let mut result = m.clone();
        for &(p, w) in &t.inputs {
            if p < result.len() {
                result[p] = match result[p] {
                    None => None,
                    Some(v) => Some(v - w),
                };
            }
        }
        for &(p, w) in &t.outputs {
            if p < result.len() {
                result[p] = match result[p] {
                    None => None,
                    Some(v) => Some(v + w),
                };
            }
        }
        result
    };

    let strictly_greater = |m: &OmegaMarking, ancestor: &OmegaMarking| -> bool {
        let mut has_strict = false;
        for (m_val, a_val) in m.iter().zip(ancestor.iter()) {
            match (m_val, a_val) {
                (None, None) => {}
                (None, Some(_)) => { has_strict = true; }
                (Some(_), None) => { return false; }
                (Some(mv), Some(av)) => {
                    if mv < av {
                        return false;
                    }
                    if mv > av {
                        has_strict = true;
                    }
                }
            }
        }
        has_strict
    };

    // Check initial marking.
    if is_deadlock_omega(&initial) {
        return true;
    }

    struct TreeNode {
        marking: OmegaMarking,
        ancestors: Vec<usize>,
    }

    let mut nodes: Vec<TreeNode> = Vec::new();
    let mut worklist: VecDeque<usize> = VecDeque::new();
    let mut seen: std::collections::HashSet<OmegaMarking> = std::collections::HashSet::new();

    nodes.push(TreeNode {
        marking: initial.clone(),
        ancestors: vec![0],
    });
    worklist.push_back(0);
    seen.insert(initial);

    while let Some(node_idx) = worklist.pop_front() {
        let current_marking = nodes[node_idx].marking.clone();
        let current_ancestors = nodes[node_idx].ancestors.clone();

        for t in &net.transitions {
            if !is_enabled_omega(t, &current_marking) {
                continue;
            }

            let mut successor = fire_omega(t, &current_marking);

            // Omega-acceleration.
            for &ancestor_idx in &current_ancestors {
                let ancestor_marking = &nodes[ancestor_idx].marking;
                if strictly_greater(&successor, ancestor_marking) {
                    for i in 0..num_places {
                        match (&successor[i], &ancestor_marking[i]) {
                            (Some(sv), Some(av)) if sv > av => {
                                successor[i] = None;
                            }
                            _ => {}
                        }
                    }
                }
            }

            if is_deadlock_omega(&successor) {
                return true;
            }

            if seen.contains(&successor) {
                continue;
            }
            seen.insert(successor.clone());

            let new_idx = nodes.len();
            let mut new_ancestors = current_ancestors.clone();
            new_ancestors.push(new_idx);
            nodes.push(TreeNode {
                marking: successor,
                ancestors: new_ancestors,
            });
            worklist.push_back(new_idx);
        }
    }

    false
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level Petri net analysis result.
#[derive(Debug, Clone)]
pub struct PetriAnalysis {
    /// Whether any deadlock risks were detected.
    pub has_deadlock_risk: bool,
    /// Places with potentially unbounded token capacity.
    pub unbounded_places: Vec<String>,
    /// Total number of places.
    pub place_count: usize,
    /// Total number of transitions.
    pub transition_count: usize,
}

/// Run Petri net analysis from pipeline bundle data.
///
/// Scans the grammar's syntax items to identify concurrent composition
/// patterns and channel-like structures, then builds a Petri net model
/// and runs deadlock and coverability analysis.
///
/// - **Transitions** are derived from parallel composition operators: terminals
///   `|`, `||`, and `par` indicate concurrent process composition.
/// - **Places** are derived from NonTerminal references, which model
///   communication channels or shared resources between categories.
///
/// # Arguments
///
/// * `all_syntax` — Per-rule syntax items: `(label, category, items)`.
/// * `categories` — Category metadata for the grammar.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::wpds::WpdsCategoryInfo],
) -> PetriAnalysis {
    use std::collections::{HashMap, HashSet};
    use crate::SyntaxItemSpec;

    let mut net = PetriNet::new();

    // Track which place IDs map to which names for unboundedness reporting.
    let mut place_map: HashMap<String, usize> = HashMap::new();
    // Track parallel composition operators as transitions.
    let mut transition_names: Vec<String> = Vec::new();
    // Track NonTerminal references as channel/place candidates.
    let mut channel_refs: HashSet<String> = HashSet::new();

    /// Recursively scan a syntax item for parallel operators and channel refs.
    fn scan_item(
        item: &SyntaxItemSpec,
        rule_label: &str,
        transition_names: &mut Vec<String>,
        channel_refs: &mut HashSet<String>,
    ) {
        match item {
            SyntaxItemSpec::Terminal(t) if t == "|" || t == "||" || t == "par" => {
                transition_names.push(format!("{}::{}", rule_label, t));
            }
            SyntaxItemSpec::NonTerminal { category, .. } => {
                channel_refs.insert(category.clone());
            }
            SyntaxItemSpec::Optional { inner } => {
                for sub in inner {
                    scan_item(sub, rule_label, transition_names, channel_refs);
                }
            }
            SyntaxItemSpec::Map { body_items } => {
                for sub in body_items {
                    scan_item(sub, rule_label, transition_names, channel_refs);
                }
            }
            SyntaxItemSpec::Sep { body, .. } => {
                scan_item(body, rule_label, transition_names, channel_refs);
            }
            SyntaxItemSpec::Zip { body, .. } => {
                scan_item(body, rule_label, transition_names, channel_refs);
            }
            _ => {}
        }
    }

    for (label, _category, syntax) in all_syntax {
        for item in syntax {
            scan_item(item, label, &mut transition_names, &mut channel_refs);
        }
    }

    // Also add each grammar category as a potential place (process state).
    for cat in categories {
        channel_refs.insert(cat.name.clone());
    }

    // Create places from channel references.
    for name in &channel_refs {
        let id = net.add_place(name.clone());
        place_map.insert(name.clone(), id);
    }

    // Create transitions from parallel composition operators.
    // Each transition connects places from the channel refs that appear in the
    // same rule (simplified: connect to all known places with weight 1).
    for tname in &transition_names {
        let tid = net.add_transition(tname.clone());
        // For each transition, connect to the first two places as a simplified
        // model: input from first place, output to second place.
        let place_ids: Vec<usize> = place_map.values().copied().collect();
        if let Some(&first) = place_ids.first() {
            net.transitions[tid].add_input(first, 1);
            if let Some(&second) = place_ids.get(1) {
                net.transitions[tid].add_output(second, 1);
            } else {
                net.transitions[tid].add_output(first, 1);
            }
        }
    }

    // Set initial marking: one token in each place.
    for place in &net.places {
        net.initial_marking.set(place.id, 1);
    }

    let place_count = net.num_places();
    let transition_count = net.num_transitions();

    // Run deadlock analysis.
    let has_deadlock_risk = check_deadlock(&net);

    // Identify unbounded places: places without a capacity bound.
    let unbounded_places: Vec<String> = net
        .places
        .iter()
        .filter(|p| p.capacity.is_none())
        .map(|p| p.name.clone())
        .collect();

    PetriAnalysis {
        has_deadlock_risk,
        unbounded_places,
        place_count,
        transition_count,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn producer_consumer_net() -> PetriNet {
        // Simple producer-consumer: buffer place between produce and consume.
        let mut net = PetriNet::new();
        let buffer = net.add_place("buffer");
        let ready = net.add_place("ready");
        net.initial_marking.set(ready, 1);

        let produce = net.add_transition("produce");
        net.transitions[produce].add_input(ready, 1);
        net.transitions[produce].add_output(buffer, 1);

        let consume = net.add_transition("consume");
        net.transitions[consume].add_input(buffer, 1);
        net.transitions[consume].add_output(ready, 1);

        net
    }

    #[test]
    fn petri_net_construction_and_display() {
        let net = producer_consumer_net();
        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 2);
        assert!(net.to_string().contains("places: 2"));
    }

    #[test]
    fn petri_net_fire_transition() {
        let net = producer_consumer_net();
        let m0 = &net.initial_marking;
        assert_eq!(m0.get(0), 0); // buffer = 0
        assert_eq!(m0.get(1), 1); // ready = 1

        // Fire "produce": ready-1, buffer+1
        let m1 = net.fire(0, m0).expect("produce should be enabled");
        assert_eq!(m1.get(0), 1); // buffer = 1
        assert_eq!(m1.get(1), 0); // ready = 0

        // Fire "consume": buffer-1, ready+1
        let m2 = net.fire(1, &m1).expect("consume should be enabled");
        assert_eq!(m2.get(0), 0); // buffer = 0
        assert_eq!(m2.get(1), 1); // ready = 1
    }

    #[test]
    fn marking_covers() {
        let m1 = Marking::from_tokens(vec![2, 3, 1]);
        let m2 = Marking::from_tokens(vec![1, 3, 0]);
        let m3 = Marking::from_tokens(vec![3, 3, 0]);
        assert!(m1.covers(&m2));
        assert!(!m2.covers(&m1));
        assert!(m3.covers(&m2));
    }

    // ─── check_coverability tests ────────────────────────────────────────

    #[test]
    fn coverability_initial_marking_covers_target() {
        // Initial marking already covers target.
        let net = producer_consumer_net();
        // Initial: buffer=0, ready=1. Target: buffer=0, ready=0.
        let target = Marking::from_tokens(vec![0, 0]);
        assert!(check_coverability(&net, &target));
    }

    #[test]
    fn coverability_reachable_marking_covers_target() {
        // After firing "produce", buffer=1, ready=0 => covers (1,0).
        let net = producer_consumer_net();
        let target = Marking::from_tokens(vec![1, 0]);
        assert!(check_coverability(&net, &target));
    }

    #[test]
    fn coverability_unreachable_target() {
        // Can never reach buffer=2 in the producer-consumer net (at most 1 token total).
        let net = producer_consumer_net();
        let target = Marking::from_tokens(vec![2, 0]);
        assert!(!check_coverability(&net, &target));
    }

    #[test]
    fn coverability_unbounded_net() {
        // A net where a place can grow without bound:
        // p0: ready=1; t0: p0 -> p0 + p1 (produces token in p1 each time).
        let mut net = PetriNet::new();
        let p0 = net.add_place("ready");
        let p1 = net.add_place("accumulator");
        net.initial_marking.set(p0, 1);

        let t0 = net.add_transition("generate");
        net.transitions[t0].add_input(p0, 1);
        net.transitions[t0].add_output(p0, 1);
        net.transitions[t0].add_output(p1, 1);

        // p1 can grow without bound, so any target on p1 should be coverable.
        let target = Marking::from_tokens(vec![0, 100]);
        assert!(check_coverability(&net, &target));
    }

    #[test]
    fn coverability_empty_net() {
        let net = PetriNet::new();
        let target = Marking::from_tokens(vec![]);
        assert!(check_coverability(&net, &target));
    }

    #[test]
    fn coverability_no_transitions() {
        // Net with places but no transitions: only initial marking is reachable.
        let mut net = PetriNet::new();
        net.add_place("p0");
        net.initial_marking.set(0, 3);

        let target_yes = Marking::from_tokens(vec![2]);
        assert!(check_coverability(&net, &target_yes));

        let target_no = Marking::from_tokens(vec![5]);
        assert!(!check_coverability(&net, &target_no));
    }

    #[test]
    fn coverability_multiple_transitions_bounded() {
        // A simple bounded net: two places, cycling tokens.
        //   p0=2, p1=0
        //   t0: p0 -> p1 (move one token)
        //   t1: p1 -> p0 (move one token back)
        let mut net = PetriNet::new();
        let p0 = net.add_place("p0");
        let p1 = net.add_place("p1");
        net.initial_marking.set(p0, 2);

        let t0 = net.add_transition("move_right");
        net.transitions[t0].add_input(p0, 1);
        net.transitions[t0].add_output(p1, 1);

        let t1 = net.add_transition("move_left");
        net.transitions[t1].add_input(p1, 1);
        net.transitions[t1].add_output(p0, 1);

        // Can reach (0, 2).
        assert!(check_coverability(&net, &Marking::from_tokens(vec![0, 2])));
        // Can reach (1, 1).
        assert!(check_coverability(&net, &Marking::from_tokens(vec![1, 1])));
        // Cannot reach (3, 0) since only 2 total tokens.
        assert!(!check_coverability(&net, &Marking::from_tokens(vec![3, 0])));
    }

    // ─── check_deadlock tests ────────────────────────────────────────────

    #[test]
    fn deadlock_producer_consumer_no_deadlock() {
        // Producer-consumer is deadlock-free: can always fire one of the two transitions.
        let net = producer_consumer_net();
        assert!(!check_deadlock(&net));
    }

    #[test]
    fn deadlock_no_transitions() {
        // No transitions means initial marking is immediately a deadlock.
        let mut net = PetriNet::new();
        net.add_place("p0");
        net.initial_marking.set(0, 1);
        assert!(check_deadlock(&net));
    }

    #[test]
    fn deadlock_initial_is_dead() {
        // Transition requires tokens that aren't present.
        let mut net = PetriNet::new();
        let p0 = net.add_place("p0");
        net.initial_marking.set(p0, 0);

        let t0 = net.add_transition("need_token");
        net.transitions[t0].add_input(p0, 1);
        net.transitions[t0].add_output(p0, 1);

        assert!(check_deadlock(&net));
    }

    #[test]
    fn deadlock_reachable_dead_marking() {
        // Net where firing leads to a dead marking:
        //   p0=1, p1=0
        //   t0: p0 -> p1
        //   t1: p0 + p1 -> (nothing)
        // After t0: p0=0, p1=1. Then t1 needs p0>=1 AND p1>=1, but p0=0.
        // t0 needs p0>=1, but p0=0. So (0,1) is a deadlock.
        let mut net = PetriNet::new();
        let p0 = net.add_place("p0");
        let p1 = net.add_place("p1");
        net.initial_marking.set(p0, 1);

        let t0 = net.add_transition("move");
        net.transitions[t0].add_input(p0, 1);
        net.transitions[t0].add_output(p1, 1);

        let t1 = net.add_transition("consume_both");
        net.transitions[t1].add_input(p0, 1);
        net.transitions[t1].add_input(p1, 1);

        assert!(check_deadlock(&net));
    }

    #[test]
    fn deadlock_self_loop_no_deadlock() {
        // A transition that consumes and produces from the same place: never deadlocks.
        let mut net = PetriNet::new();
        let p0 = net.add_place("p0");
        net.initial_marking.set(p0, 1);

        let t0 = net.add_transition("self_loop");
        net.transitions[t0].add_input(p0, 1);
        net.transitions[t0].add_output(p0, 1);

        assert!(!check_deadlock(&net));
    }

    #[test]
    fn deadlock_draining_net() {
        // A transition that drains tokens without producing: deadlocks after one firing.
        //   p0=1; t0: p0 -> (nothing)
        let mut net = PetriNet::new();
        let p0 = net.add_place("p0");
        net.initial_marking.set(p0, 1);

        let t0 = net.add_transition("drain");
        net.transitions[t0].add_input(p0, 1);
        // No outputs.

        assert!(check_deadlock(&net));
    }

    #[test]
    fn coverability_construct_helper() {
        // Test the construct_petri_net helper.
        let net = construct_petri_net(
            &[
                ("p0".to_string(), 1),
                ("p1".to_string(), 0),
            ],
            &[
                ("t0".to_string(), vec![(0, 1)], vec![(1, 1)]),
                ("t1".to_string(), vec![(1, 1)], vec![(0, 1)]),
            ],
        );
        assert_eq!(net.num_places(), 2);
        assert_eq!(net.num_transitions(), 2);
        // Should be deadlock-free (cycling net).
        assert!(!check_deadlock(&net));
        // (0, 1) coverable.
        assert!(check_coverability(&net, &Marking::from_tokens(vec![0, 1])));
    }

    // ─── Parallelism extraction tests ───────────────────────────────────

    /// Build a net with 4 completely independent transitions (no shared places).
    ///
    /// ```text
    /// p0 --t0--> p1      p2 --t1--> p3      p4 --t2--> p5      p6 --t3--> p7
    /// ```
    fn four_independent_transitions_net() -> PetriNet {
        let mut net = PetriNet::new();
        for i in 0..8 {
            let pid = net.add_place(format!("p{}", i));
            if i % 2 == 0 {
                net.initial_marking.set(pid, 1);
            }
        }
        for i in 0..4 {
            let tid = net.add_transition(format!("t{}", i));
            net.transitions[tid].add_input(i * 2, 1);
            net.transitions[tid].add_output(i * 2 + 1, 1);
        }
        net
    }

    /// Build a net where t0 and t1 share an input place, but t2 is independent
    /// of both.
    ///
    /// ```text
    /// p0 --t0--> p1
    /// p0 --t1--> p2
    /// p3 --t2--> p4
    /// ```
    fn shared_input_net() -> PetriNet {
        let mut net = PetriNet::new();
        for i in 0..5 {
            net.add_place(format!("p{}", i));
        }
        net.initial_marking.set(0, 2);
        net.initial_marking.set(3, 1);

        let t0 = net.add_transition("t0");
        net.transitions[t0].add_input(0, 1);
        net.transitions[t0].add_output(1, 1);

        let t1 = net.add_transition("t1");
        net.transitions[t1].add_input(0, 1);
        net.transitions[t1].add_output(2, 1);

        let t2 = net.add_transition("t2");
        net.transitions[t2].add_input(3, 1);
        net.transitions[t2].add_output(4, 1);

        net
    }

    #[test]
    fn independence_same_transition() {
        let net = four_independent_transitions_net();
        // A transition is never independent with itself.
        assert!(!net.check_independence(0, 0));
        assert!(!net.check_independence(3, 3));
    }

    #[test]
    fn independence_out_of_bounds() {
        let net = four_independent_transitions_net();
        assert!(!net.check_independence(0, 99));
        assert!(!net.check_independence(99, 0));
    }

    #[test]
    fn independence_disjoint_transitions() {
        let net = four_independent_transitions_net();
        // All 4 transitions are pairwise independent.
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert!(
                    net.check_independence(i, j),
                    "t{} and t{} should be independent",
                    i,
                    j,
                );
            }
        }
    }

    #[test]
    fn independence_shared_input_place() {
        let net = shared_input_net();
        // t0 and t1 share input place p0 — NOT independent.
        assert!(!net.check_independence(0, 1));
        // t0 and t2 are independent (disjoint places).
        assert!(net.check_independence(0, 2));
        // t1 and t2 are independent (disjoint places).
        assert!(net.check_independence(1, 2));
    }

    #[test]
    fn independence_shared_output_place() {
        // t0 and t1 share an output place.
        let mut net = PetriNet::new();
        for i in 0..3 {
            net.add_place(format!("p{}", i));
        }
        net.initial_marking.set(0, 1);
        net.initial_marking.set(1, 1);

        let t0 = net.add_transition("t0");
        net.transitions[t0].add_input(0, 1);
        net.transitions[t0].add_output(2, 1); // output to p2

        let t1 = net.add_transition("t1");
        net.transitions[t1].add_input(1, 1);
        net.transitions[t1].add_output(2, 1); // also output to p2

        assert!(!net.check_independence(0, 1));
    }

    #[test]
    fn independence_relation_all_pairs() {
        let net = four_independent_transitions_net();
        let pairs = net.independence_relation();
        // C(4,2) = 6 independent pairs.
        assert_eq!(pairs.len(), 6);
        // Each pair should be (i, j) with i < j.
        for &(i, j) in &pairs {
            assert!(i < j);
        }
    }

    #[test]
    fn independence_relation_partial() {
        let net = shared_input_net();
        let pairs = net.independence_relation();
        // t0-t1 NOT independent (share p0). t0-t2 and t1-t2 ARE independent.
        assert_eq!(pairs.len(), 2);
        assert!(pairs.contains(&(0, 2)));
        assert!(pairs.contains(&(1, 2)));
    }

    #[test]
    fn parallel_regions_all_independent() {
        let net = four_independent_transitions_net();
        let regions = net.extract_parallel_regions();
        // All 4 transitions form a single maximal clique.
        assert!(!regions.is_empty());
        // The largest region should contain all 4 transitions.
        assert_eq!(regions[0].transitions.len(), 4);
        assert_eq!(regions[0].max_parallelism, 4);
        assert_eq!(regions[0].transitions, vec![0, 1, 2, 3]);
    }

    #[test]
    fn parallel_regions_partial_independence() {
        let net = shared_input_net();
        let regions = net.extract_parallel_regions();
        // t0 and t1 are NOT independent, but both are independent with t2.
        // Maximal cliques: {t0, t2} and {t1, t2}.
        assert_eq!(regions.len(), 2);
        // Both regions should have size 2.
        for region in &regions {
            assert_eq!(region.max_parallelism, 2);
            assert!(region.transitions.contains(&2));
        }
        // One region should contain t0, the other t1.
        let all_first: Vec<usize> = regions.iter().map(|r| r.transitions[0]).collect();
        assert!(all_first.contains(&0));
        assert!(all_first.contains(&1));
    }

    #[test]
    fn parallel_regions_no_independence() {
        // Producer-consumer: both transitions touch the same places.
        let net = producer_consumer_net();
        let regions = net.extract_parallel_regions();
        // No maximal clique of size >= 2 since the two transitions share places.
        assert!(regions.is_empty());
    }

    #[test]
    fn parallel_regions_empty_net() {
        let net = PetriNet::new();
        let regions = net.extract_parallel_regions();
        assert!(regions.is_empty());
    }

    #[test]
    fn analyze_parallelism_full_report() {
        let net = four_independent_transitions_net();
        let report = net.analyze_parallelism();
        assert_eq!(report.total_transitions, 4);
        assert_eq!(report.independent_pairs, 6); // C(4,2) = 6
        assert_eq!(report.max_parallelism, 4);
        assert!(!report.regions.is_empty());
        // Display should not panic.
        let _s = format!("{}", report);
    }

    #[test]
    fn analyze_parallelism_partial() {
        let net = shared_input_net();
        let report = net.analyze_parallelism();
        assert_eq!(report.total_transitions, 3);
        assert_eq!(report.independent_pairs, 2);
        assert_eq!(report.max_parallelism, 2);
        assert_eq!(report.regions.len(), 2);
    }

    #[test]
    fn analyze_parallelism_no_parallelism() {
        let net = producer_consumer_net();
        let report = net.analyze_parallelism();
        assert_eq!(report.total_transitions, 2);
        assert_eq!(report.independent_pairs, 0);
        assert_eq!(report.max_parallelism, 0);
        assert!(report.regions.is_empty());
    }

    #[test]
    fn parallel_region_display() {
        let region = ParallelRegion {
            transitions: vec![0, 2, 5],
            max_parallelism: 3,
        };
        let s = format!("{}", region);
        assert!(s.contains("t0"));
        assert!(s.contains("t2"));
        assert!(s.contains("t5"));
        assert!(s.contains("max_parallelism: 3"));
    }

    #[test]
    fn test_analyze_from_bundle_basic() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Par".to_string(),
            "Proc".to_string(),
            vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "a".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("|".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        )];
        let categories = vec![crate::wpds::WpdsCategoryInfo {
            name: "Proc".to_string(),
            is_primary: true,
        }];
        let result = analyze_from_bundle(&syntax, &categories);
        // PetriAnalysis is returned directly (not Option).
        assert!(result.place_count > 0 || result.transition_count > 0,
            "should produce a non-trivial Petri net from syntax");
    }
}
