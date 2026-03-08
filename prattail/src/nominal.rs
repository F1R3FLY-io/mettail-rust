//! Nominal automata with orbit-finite sets for name-passing calculi.
//!
//! Nominal automata extend classical finite automata to operate over infinite
//! alphabets with symmetry. The key idea is that states and transitions are
//! defined up to name permutation — two configurations that differ only in the
//! choice of names are equivalent. This is formalized via the theory of nominal
//! sets, where the state space is orbit-finite (finitely many orbits under the
//! symmetry group action) even though the raw state space may be infinite.
//!
//! ## Theoretical Foundations
//!
//! - **Bojańczyk, Klin & Lasota (2014)** — "Automata theory in nominal sets."
//!   Establishes the foundations of nominal automata: orbit-finite alphabets,
//!   equivariant transitions, and decidable emptiness/universality for nominal
//!   DFAs.
//! - **Pitts (2013)** — *Nominal Sets: Names and Symmetry in Computer Science.*
//!   The standard monograph on nominal set theory: atoms, support, freshness,
//!   and the Fraenkel-Mostowski permutation model.
//! - **Montanari & Pistore (2005)** — "History-dependent automata." An earlier
//!   framework for automata with name generation, closely related to nominal
//!   automata.
//! - **Tzevelekos (2011)** — "Fresh-register automata." Operational semantics
//!   with explicit registers for storing fresh names.
//!
//! ## PraTTaIL Integration
//!
//! Nominal automata model name-binding and alpha-equivalence in PraTTaIL
//! grammars. Binder positions (`Binder`, `BinderCollection` in `SyntaxItemSpec`)
//! introduce fresh names, and the nominal automaton tracks which names are
//! in scope at each parse state. This enables:
//! - Scope checking: verifying that variable references are in scope
//! - Alpha-equivalence: identifying terms that differ only in bound names
//! - Freshness analysis: detecting name clashes and shadowing

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// NOTE: Semiring import will be used when weighted nominal automata are implemented.
#[allow(unused_imports)]
use crate::automata::semiring::Semiring;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// An orbit of states under the symmetry group action.
///
/// An orbit is an equivalence class of states that are related by name
/// permutation. All states in an orbit have the same "shape" — they differ
/// only in which concrete names occupy which positions.
///
/// For example, if atoms are `{a, b, c, ...}`, the states `{a, b}` and
/// `{c, d}` are in the same orbit (both are "two-element subsets"), while
/// `{a}` and `{a, b}` are in different orbits.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Orbit {
    /// Unique orbit identifier.
    pub id: usize,
    /// Representative element description (for display/diagnostics).
    pub representative: String,
    /// The support size (number of free names in the orbit representative).
    pub support_size: usize,
}

impl Orbit {
    /// Create a new orbit.
    pub fn new(id: usize, representative: impl Into<String>, support_size: usize) -> Self {
        Orbit {
            id,
            representative: representative.into(),
            support_size,
        }
    }
}

impl fmt::Display for Orbit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "orbit{}({}, support={})",
            self.id, self.representative, self.support_size,
        )
    }
}

/// A state in a nominal automaton.
///
/// Each state belongs to an orbit and has an associated support — the finite
/// set of names that are "significant" to the state. The state is equivariant
/// with respect to names outside its support.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NominalState {
    /// Unique state identifier.
    pub id: usize,
    /// The orbit this state belongs to.
    pub orbit_id: usize,
    /// The support: set of names significant to this state.
    pub support: HashSet<String>,
    /// Whether this is an accepting state.
    pub is_accepting: bool,
    /// Optional label for diagnostics.
    pub label: Option<String>,
}

impl NominalState {
    /// Create a new state with the given support.
    pub fn new(id: usize, orbit_id: usize, support: HashSet<String>) -> Self {
        NominalState {
            id,
            orbit_id,
            support,
            is_accepting: false,
            label: None,
        }
    }

    /// Create an accepting state.
    pub fn accepting(id: usize, orbit_id: usize, support: HashSet<String>) -> Self {
        NominalState {
            id,
            orbit_id,
            support,
            is_accepting: true,
            label: None,
        }
    }
}

impl fmt::Display for NominalState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let acc = if self.is_accepting { "*" } else { "" };
        let support_str: Vec<&str> = self.support.iter().map(|s| s.as_str()).collect();
        if let Some(ref label) = self.label {
            write!(
                f,
                "n{}{}({}, orbit={}, supp={{{}}})",
                self.id, acc, label, self.orbit_id,
                support_str.join(", "),
            )
        } else {
            write!(
                f,
                "n{}{}(orbit={}, supp={{{}}})",
                self.id, acc, self.orbit_id,
                support_str.join(", "),
            )
        }
    }
}

/// A nominal automaton operating over an orbit-finite alphabet.
///
/// `A = (Q, A, δ, q₀, F)` where:
/// - `Q` is an orbit-finite set of states (finitely many orbits)
/// - `A` is the (possibly infinite) input alphabet with symmetry
/// - `δ` is the equivariant transition function
/// - `q₀` is the initial state
/// - `F ⊆ Q` is the set of accepting states
///
/// The automaton is represented orbit-by-orbit: transitions are defined
/// between orbits with support constraints.
#[derive(Debug, Clone)]
pub struct NominalAutomaton {
    /// All orbits of states.
    pub orbits: Vec<Orbit>,
    /// All states (orbit representatives and their permutations).
    pub states: Vec<NominalState>,
    /// Equivariant transitions: `(source_orbit, input_orbit) → target_orbit`
    /// with freshness/support constraints.
    pub transitions: Vec<NominalTransition>,
    /// Initial state ID.
    pub initial_state: Option<usize>,
    /// Accepting state IDs.
    pub accepting_states: HashSet<usize>,
}

/// A transition in a nominal automaton.
///
/// Transitions are equivariant: they respect the symmetry group action.
/// The freshness constraint specifies which names in the input must be
/// fresh (not in the source state's support).
#[derive(Debug, Clone)]
pub struct NominalTransition {
    /// Source state ID.
    pub from: usize,
    /// Target state ID.
    pub to: usize,
    /// Input pattern (orbit representative).
    pub input_pattern: String,
    /// Freshness constraint: names in the input that must be fresh
    /// with respect to the source state's support.
    pub fresh_names: HashSet<String>,
}

impl fmt::Display for NominalTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.fresh_names.is_empty() {
            write!(f, "n{} --{}-> n{}", self.from, self.input_pattern, self.to)
        } else {
            let fresh: Vec<&str> = self.fresh_names.iter().map(|s| s.as_str()).collect();
            write!(
                f,
                "n{} --{}[fresh: {{{}}}]-> n{}",
                self.from,
                self.input_pattern,
                fresh.join(", "),
                self.to,
            )
        }
    }
}

/// Usage information for a single name across the nominal automaton.
///
/// Tracks which states reference a name in their support sets and which
/// transitions reference it (in input patterns or freshness constraints),
/// along with depth information from BFS traversal of the state graph.
#[derive(Debug, Clone)]
pub struct NameUsage {
    /// The name being tracked.
    pub name: String,
    /// State IDs where this name appears in the support set.
    pub states_using: HashSet<usize>,
    /// Indices into `NominalAutomaton::transitions` that reference this name
    /// (either in `input_pattern` or `fresh_names`).
    pub transitions_using: Vec<usize>,
    /// BFS depth at which this name first appears (in any state's support).
    /// `usize::MAX` if the name is never used in a reachable state.
    pub scope_depth: usize,
    /// BFS depth at which this name last appears (in any state's support).
    /// `0` if the name is never used in a reachable state.
    pub last_use_depth: usize,
}

impl NameUsage {
    fn new(name: String) -> Self {
        NameUsage {
            name,
            states_using: HashSet::new(),
            transitions_using: Vec::new(),
            scope_depth: usize::MAX,
            last_use_depth: 0,
        }
    }
}

impl fmt::Display for NameUsage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "NameUsage({}: {} states, {} transitions, depth {}..{})",
            self.name,
            self.states_using.len(),
            self.transitions_using.len(),
            if self.scope_depth == usize::MAX {
                "∞".to_string()
            } else {
                self.scope_depth.to_string()
            },
            self.last_use_depth,
        )
    }
}

/// Result of scope narrowing analysis on a nominal automaton.
///
/// Identifies which names from the original global scope are actually used
/// in reachable states and which can be safely eliminated to produce a
/// minimal scope.
#[derive(Debug, Clone)]
pub struct ScopeNarrowingResult {
    /// All names that appear in any state's support across the automaton.
    pub original_scope: Vec<String>,
    /// The minimal set of names that are actually used in reachable states.
    pub narrowed_scope: Vec<String>,
    /// Names from the original scope that are not used in any reachable state
    /// and can be safely removed.
    pub eliminated_names: Vec<String>,
    /// Number of names eliminated (`original_scope.len() - narrowed_scope.len()`).
    pub savings: usize,
}

impl fmt::Display for ScopeNarrowingResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ScopeNarrowing: {} → {} names ({} eliminated)",
            self.original_scope.len(),
            self.narrowed_scope.len(),
            self.savings,
        )
    }
}

impl NominalAutomaton {
    /// Create an empty nominal automaton.
    pub fn new() -> Self {
        NominalAutomaton {
            orbits: Vec::new(),
            states: Vec::new(),
            transitions: Vec::new(),
            initial_state: None,
            accepting_states: HashSet::new(),
        }
    }

    /// Add an orbit and return its ID.
    pub fn add_orbit(&mut self, representative: impl Into<String>, support_size: usize) -> usize {
        let id = self.orbits.len();
        self.orbits.push(Orbit::new(id, representative, support_size));
        id
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, orbit_id: usize, support: HashSet<String>, is_accepting: bool) -> usize {
        let id = self.states.len();
        let state = if is_accepting {
            NominalState::accepting(id, orbit_id, support)
        } else {
            NominalState::new(id, orbit_id, support)
        };
        if is_accepting {
            self.accepting_states.insert(id);
        }
        self.states.push(state);
        id
    }

    /// Number of orbits.
    pub fn num_orbits(&self) -> usize {
        self.orbits.len()
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    // ══════════════════════════════════════════════════════════════════════
    // Scope narrowing analysis (Phase 5B.7)
    // ══════════════════════════════════════════════════════════════════════

    /// Compute the set of state IDs reachable from the initial state via BFS.
    ///
    /// Returns a map from state ID to its BFS depth. If there is no initial
    /// state, returns an empty map.
    fn reachable_depths(&self) -> HashMap<usize, usize> {
        let mut depths: HashMap<usize, usize> = HashMap::new();
        let initial = match self.initial_state {
            Some(id) => id,
            None => return depths,
        };

        // Build an adjacency list from transitions: source → [target, ...]
        let mut adjacency: HashMap<usize, Vec<usize>> = HashMap::new();
        for tr in &self.transitions {
            adjacency.entry(tr.from).or_default().push(tr.to);
        }

        let mut queue = VecDeque::new();
        queue.push_back((initial, 0usize));
        depths.insert(initial, 0);

        while let Some((state_id, depth)) = queue.pop_front() {
            if let Some(neighbors) = adjacency.get(&state_id) {
                for &next in neighbors {
                    if !depths.contains_key(&next) {
                        depths.insert(next, depth + 1);
                        queue.push_back((next, depth + 1));
                    }
                }
            }
        }

        depths
    }

    /// Compute usage information for every name that appears in the automaton.
    ///
    /// For each name found in any state's support set or any transition's
    /// freshness constraints / input pattern, this method returns a [`NameUsage`]
    /// record describing:
    /// - Which states reference the name (in their support set).
    /// - Which transitions reference it (by index).
    /// - The BFS depth at which the name first and last appears among
    ///   reachable states.
    ///
    /// Names that appear only in unreachable states will have
    /// `scope_depth == usize::MAX` and `last_use_depth == 0`.
    pub fn compute_name_usage(&self) -> HashMap<String, NameUsage> {
        let depths = self.reachable_depths();
        let mut usages: HashMap<String, NameUsage> = HashMap::new();

        // Scan state support sets.
        for state in &self.states {
            for name in &state.support {
                let usage = usages
                    .entry(name.clone())
                    .or_insert_with(|| NameUsage::new(name.clone()));
                usage.states_using.insert(state.id);

                // Update depth bounds if this state is reachable.
                if let Some(&d) = depths.get(&state.id) {
                    if d < usage.scope_depth {
                        usage.scope_depth = d;
                    }
                    if d > usage.last_use_depth {
                        usage.last_use_depth = d;
                    }
                }
            }
        }

        // Scan transitions for name references in input_pattern and fresh_names.
        for (idx, tr) in self.transitions.iter().enumerate() {
            // Input pattern is treated as a name reference.
            let usage = usages
                .entry(tr.input_pattern.clone())
                .or_insert_with(|| NameUsage::new(tr.input_pattern.clone()));
            usage.transitions_using.push(idx);

            // Fresh names in the transition are also name references.
            for fresh in &tr.fresh_names {
                let usage = usages
                    .entry(fresh.clone())
                    .or_insert_with(|| NameUsage::new(fresh.clone()));
                usage.transitions_using.push(idx);
            }
        }

        usages
    }

    /// Analyze the scope of this automaton to determine the minimal set of
    /// names required.
    ///
    /// A name can be eliminated from the scope if it does not appear in the
    /// support set of any state reachable from the initial state. The analysis
    /// performs BFS reachability from the initial state and partitions names
    /// into those that are used (the narrowed scope) and those that can be
    /// removed (eliminated names).
    ///
    /// # Returns
    ///
    /// A [`ScopeNarrowingResult`] describing the original scope, the narrowed
    /// scope, the eliminated names, and the savings.
    pub fn analyze_scope(&self) -> ScopeNarrowingResult {
        let depths = self.reachable_depths();
        let reachable_ids: HashSet<usize> = depths.keys().copied().collect();

        // Collect the full original scope: all names across all states' supports.
        let mut original_set: HashSet<String> = HashSet::new();
        for state in &self.states {
            for name in &state.support {
                original_set.insert(name.clone());
            }
        }

        // Determine which names are used in reachable states.
        let mut used_set: HashSet<String> = HashSet::new();
        for state in &self.states {
            if reachable_ids.contains(&state.id) {
                for name in &state.support {
                    used_set.insert(name.clone());
                }
            }
        }

        let mut original_scope: Vec<String> = original_set.iter().cloned().collect();
        original_scope.sort();

        let mut narrowed_scope: Vec<String> = used_set.iter().cloned().collect();
        narrowed_scope.sort();

        let mut eliminated_names: Vec<String> = original_set
            .difference(&used_set)
            .cloned()
            .collect();
        eliminated_names.sort();

        let savings = eliminated_names.len();

        ScopeNarrowingResult {
            original_scope,
            narrowed_scope,
            eliminated_names,
            savings,
        }
    }

    /// Return a new automaton with narrowed scopes.
    ///
    /// This method:
    /// 1. Computes reachable states from the initial state via BFS.
    /// 2. Determines the minimal scope (names used in reachable states).
    /// 3. Removes unused names from all orbit support sets.
    /// 4. Removes orbits that become empty (support size drops to 0) **only if**
    ///    they had a non-zero support size before narrowing and no states belong
    ///    to them in the reachable set.
    /// 5. Preserves all transitions and state structure for reachable states.
    ///
    /// # Returns
    ///
    /// A new [`NominalAutomaton`] with narrowed support sets.
    pub fn narrow_scope(&self) -> NominalAutomaton {
        let analysis = self.analyze_scope();
        let used_names: HashSet<String> = analysis.narrowed_scope.into_iter().collect();
        let depths = self.reachable_depths();
        let reachable_ids: HashSet<usize> = depths.keys().copied().collect();

        // Build a mapping from old state IDs to new state IDs (only reachable states).
        let mut old_to_new: HashMap<usize, usize> = HashMap::new();
        let mut new_states: Vec<NominalState> = Vec::new();
        let mut new_accepting: HashSet<usize> = HashSet::new();

        // Collect reachable state IDs in a deterministic order.
        let mut reachable_ordered: Vec<usize> = reachable_ids.iter().copied().collect();
        reachable_ordered.sort();

        for &old_id in &reachable_ordered {
            let state = &self.states[old_id];
            let new_id = new_states.len();
            old_to_new.insert(old_id, new_id);

            // Narrow the support: keep only names in the used set.
            let narrowed_support: HashSet<String> = state
                .support
                .intersection(&used_names)
                .cloned()
                .collect();

            let mut new_state = NominalState::new(new_id, state.orbit_id, narrowed_support);
            new_state.is_accepting = state.is_accepting;
            new_state.label = state.label.clone();

            if state.is_accepting {
                new_accepting.insert(new_id);
            }
            new_states.push(new_state);
        }

        // Rebuild orbits: adjust support sizes based on narrowed state supports.
        // Compute the maximum narrowed support size per orbit among reachable states.
        let mut orbit_max_support: HashMap<usize, usize> = HashMap::new();
        for state in &new_states {
            let entry = orbit_max_support.entry(state.orbit_id).or_insert(0);
            if state.support.len() > *entry {
                *entry = state.support.len();
            }
        }

        let new_orbits: Vec<Orbit> = self
            .orbits
            .iter()
            .map(|orbit| {
                let new_support_size = orbit_max_support
                    .get(&orbit.id)
                    .copied()
                    .unwrap_or(orbit.support_size);
                Orbit::new(orbit.id, orbit.representative.clone(), new_support_size)
            })
            .collect();

        // Rebuild transitions: only keep transitions between reachable states,
        // remap state IDs.
        let new_transitions: Vec<NominalTransition> = self
            .transitions
            .iter()
            .filter(|tr| old_to_new.contains_key(&tr.from) && old_to_new.contains_key(&tr.to))
            .map(|tr| NominalTransition {
                from: old_to_new[&tr.from],
                to: old_to_new[&tr.to],
                input_pattern: tr.input_pattern.clone(),
                fresh_names: tr.fresh_names.clone(),
            })
            .collect();

        let new_initial = self
            .initial_state
            .and_then(|id| old_to_new.get(&id).copied());

        NominalAutomaton {
            orbits: new_orbits,
            states: new_states,
            transitions: new_transitions,
            initial_state: new_initial,
            accepting_states: new_accepting,
        }
    }
}

impl Default for NominalAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for NominalAutomaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "NominalAutomaton {{ orbits: {}, states: {}, transitions: {}, accepting: {} }}",
            self.num_orbits(),
            self.num_states(),
            self.transitions.len(),
            self.accepting_states.len(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Construct a nominal automaton from orbit descriptions.
///
/// Builds the orbit-finite state space and equivariant transition function
/// from a high-level description of orbits and their relationships.
///
/// # Arguments
///
/// * `orbit_descs` - Descriptions of each orbit: `(representative, support_size)`.
/// * `transitions` - Equivariant transitions: `(source, pattern, fresh_names, target)`.
/// * `initial` - Index of the initial orbit.
/// * `accepting` - Indices of accepting orbits.
///
/// # Returns
///
/// A `NominalAutomaton` with the specified structure.
pub fn construct_nominal(
    orbit_descs: &[(String, usize)],
    transitions: &[(usize, String, HashSet<String>, usize)],
    initial: usize,
    accepting: &[usize],
) -> NominalAutomaton {
    let num_orbits = orbit_descs.len();

    // Build orbits and one representative state per orbit.
    let mut automaton = NominalAutomaton::new();

    for (id, (representative, support_size)) in orbit_descs.iter().enumerate() {
        automaton.orbits.push(Orbit::new(id, representative.clone(), *support_size));

        // Build a representative support set: generate placeholder names a0..a(n-1)
        // with cardinality equal to support_size.
        let support: HashSet<String> = (0..*support_size)
            .map(|i| format!("a{}", i))
            .collect();

        let is_accepting = accepting.contains(&id);
        let state = if is_accepting {
            NominalState::accepting(id, id, support)
        } else {
            NominalState::new(id, id, support)
        };
        if is_accepting {
            automaton.accepting_states.insert(id);
        }
        automaton.states.push(state);
    }

    // Validate initial orbit index.
    assert!(
        initial < num_orbits,
        "Initial orbit index {} is out of range (num_orbits = {})",
        initial,
        num_orbits,
    );
    automaton.initial_state = Some(initial);

    // Validate and add equivariant transitions.
    let accepting_set: HashSet<usize> = accepting.iter().copied().collect();
    let _ = accepting_set;

    for (source, pattern, fresh_names, target) in transitions {
        assert!(
            *source < num_orbits,
            "Transition source orbit {} is out of range (num_orbits = {})",
            source,
            num_orbits,
        );
        assert!(
            *target < num_orbits,
            "Transition target orbit {} is out of range (num_orbits = {})",
            target,
            num_orbits,
        );

        // Equivariance check: fresh names in the transition must not overlap
        // with the source state's support. This ensures the transition respects
        // name permutations — a fresh name is one that is not already "known"
        // to the source state.
        let source_support = &automaton.states[*source].support;
        for fresh in fresh_names {
            assert!(
                !source_support.contains(fresh),
                "Fresh name '{}' in transition from orbit {} must not be in the source support {:?}",
                fresh,
                source,
                source_support,
            );
        }

        automaton.transitions.push(NominalTransition {
            from: *source,
            to: *target,
            input_pattern: pattern.clone(),
            fresh_names: fresh_names.clone(),
        });
    }

    automaton
}

/// Check a freshness property on a nominal automaton.
///
/// Verifies that a name is fresh (not in the support) at a given state.
/// This is the fundamental operation for scope checking in nominal theories.
///
/// # Arguments
///
/// * `automaton` - The nominal automaton.
/// * `state_id` - The state to check.
/// * `name` - The name to check for freshness.
///
/// # Returns
///
/// `true` if `name` is fresh at `state_id` (not in the state's support).
pub fn check_freshness(
    automaton: &NominalAutomaton,
    state_id: usize,
    name: &str,
) -> bool {
    if let Some(state) = automaton.states.get(state_id) {
        !state.support.contains(name)
    } else {
        false
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level nominal analysis result.
#[derive(Debug, Clone)]
pub struct NominalAnalysis {
    /// Names used outside their binding scope.
    pub scope_violations: Vec<(String, String)>, // (name, context)
    /// PNew scopes that can be tightened.
    pub narrowing_candidates: Vec<(String, String)>, // (binder, suggestion)
    /// Number of orbits.
    pub orbit_count: usize,
}

/// Analyze nominal (name-binding) structure from a grammar syntax bundle.
///
/// Scans all rules for `Binder` items, builds an orbit-based model of name
/// scopes, and detects potential scope violations where a binder name from
/// one rule is referenced in another without proper scoping.
///
/// # Arguments
///
/// * `all_syntax` — Slice of `(rule_label, category, items)` triples from the
///   parser bundle.
///
/// # Returns
///
/// A [`NominalAnalysis`] with scope violations, narrowing candidates, and
/// orbit count.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
) -> NominalAnalysis {
    // Phase 1: Collect all binder names and the rules they appear in.
    // Each unique binder name gets its own orbit.
    let mut binder_to_rules: HashMap<String, Vec<(String, String)>> = HashMap::new(); // name → [(rule_label, category)]
    let mut binder_categories: HashMap<String, HashSet<String>> = HashMap::new(); // name → {categories}

    for (rule_label, category, items) in all_syntax {
        collect_binders_recursive(
            items,
            rule_label,
            category,
            &mut binder_to_rules,
            &mut binder_categories,
        );
    }

    // Phase 2: Build orbits — one orbit per unique binder name.
    let mut orbit_names: Vec<String> = binder_to_rules.keys().cloned().collect();
    orbit_names.sort();
    let orbit_count = orbit_names.len();

    // Phase 3: Detect scope violations.
    // A scope violation occurs when a binder name appears in rules belonging
    // to more than one category without being re-bound — this means the name
    // "escapes" its intended scope.
    let mut scope_violations: Vec<(String, String)> = Vec::new();
    for name in &orbit_names {
        if let Some(cats) = binder_categories.get(name) {
            if cats.len() > 1 {
                let mut cat_list: Vec<&String> = cats.iter().collect();
                cat_list.sort();
                let context = format!(
                    "binder '{}' appears in {} categories: {}",
                    name,
                    cats.len(),
                    cat_list.iter().map(|c| c.as_str()).collect::<Vec<_>>().join(", "),
                );
                scope_violations.push((name.clone(), context));
            }
        }
    }

    // Phase 4: Identify narrowing candidates.
    // A binder that appears in only one rule within its category could have
    // its PNew scope tightened to just that rule's production.
    let mut narrowing_candidates: Vec<(String, String)> = Vec::new();
    for name in &orbit_names {
        if let Some(rules) = binder_to_rules.get(name) {
            if rules.len() == 1 {
                let (rule_label, category) = &rules[0];
                let suggestion = format!(
                    "binder '{}' used only in rule '{}' (category '{}'); scope can be tightened to this production",
                    name, rule_label, category,
                );
                narrowing_candidates.push((name.clone(), suggestion));
            }
        }
    }

    NominalAnalysis {
        scope_violations,
        narrowing_candidates,
        orbit_count,
    }
}

/// Recursively collect binder names from a list of syntax items.
fn collect_binders_recursive(
    items: &[crate::SyntaxItemSpec],
    rule_label: &str,
    category: &str,
    binder_to_rules: &mut HashMap<String, Vec<(String, String)>>,
    binder_categories: &mut HashMap<String, HashSet<String>>,
) {
    for item in items {
        match item {
            crate::SyntaxItemSpec::Binder { param_name, .. } => {
                binder_to_rules
                    .entry(param_name.clone())
                    .or_default()
                    .push((rule_label.to_string(), category.to_string()));
                binder_categories
                    .entry(param_name.clone())
                    .or_default()
                    .insert(category.to_string());
            }
            crate::SyntaxItemSpec::BinderCollection { param_name, .. } => {
                binder_to_rules
                    .entry(param_name.clone())
                    .or_default()
                    .push((rule_label.to_string(), category.to_string()));
                binder_categories
                    .entry(param_name.clone())
                    .or_default()
                    .insert(category.to_string());
            }
            crate::SyntaxItemSpec::Optional { inner } => {
                collect_binders_recursive(
                    inner,
                    rule_label,
                    category,
                    binder_to_rules,
                    binder_categories,
                );
            }
            crate::SyntaxItemSpec::Map { body_items } => {
                collect_binders_recursive(
                    body_items,
                    rule_label,
                    category,
                    binder_to_rules,
                    binder_categories,
                );
            }
            crate::SyntaxItemSpec::Sep { body, .. } => {
                collect_binders_recursive(
                    std::slice::from_ref(body.as_ref()),
                    rule_label,
                    category,
                    binder_to_rules,
                    binder_categories,
                );
            }
            crate::SyntaxItemSpec::Zip { body, .. } => {
                collect_binders_recursive(
                    std::slice::from_ref(body.as_ref()),
                    rule_label,
                    category,
                    binder_to_rules,
                    binder_categories,
                );
            }
            _ => {}
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orbit_display() {
        let orbit = Orbit::new(0, "{a, b}", 2);
        assert_eq!(orbit.to_string(), "orbit0({a, b}, support=2)");
    }

    #[test]
    fn nominal_automaton_construction() {
        let mut na = NominalAutomaton::new();
        let o0 = na.add_orbit("empty", 0);
        let o1 = na.add_orbit("{x}", 1);
        let q0 = na.add_state(o0, HashSet::new(), false);
        let q1 = na.add_state(o1, ["x".to_string()].into_iter().collect(), true);
        na.initial_state = Some(q0);

        assert_eq!(na.num_orbits(), 2);
        assert_eq!(na.num_states(), 2);
        assert!(na.accepting_states.contains(&q1));
    }

    #[test]
    fn freshness_check() {
        let mut na = NominalAutomaton::new();
        let o0 = na.add_orbit("{x}", 1);
        let q0 = na.add_state(o0, ["x".to_string()].into_iter().collect(), false);

        assert!(!check_freshness(&na, q0, "x"), "x is in support, not fresh");
        assert!(check_freshness(&na, q0, "y"), "y is not in support, is fresh");
    }

    #[test]
    fn construct_nominal_basic() {
        let orbit_descs = vec![
            ("empty".to_string(), 0),
            ("{x}".to_string(), 1),
            ("{x,y}".to_string(), 2),
        ];
        let transitions = vec![
            (0, "bind".to_string(), ["fresh_a".to_string()].into_iter().collect(), 1),
            (1, "bind".to_string(), ["fresh_b".to_string()].into_iter().collect(), 2),
        ];
        let na = construct_nominal(&orbit_descs, &transitions, 0, &[2]);

        assert_eq!(na.num_orbits(), 3);
        assert_eq!(na.num_states(), 3);
        assert_eq!(na.transitions.len(), 2);
        assert_eq!(na.initial_state, Some(0));
        assert!(na.accepting_states.contains(&2));
        assert!(!na.accepting_states.contains(&0));
    }

    #[test]
    fn construct_nominal_freshness_on_transitions() {
        // A simple automaton: orbit 0 (empty support) transitions to orbit 1
        // (support size 1) via a "bind" transition with a fresh name.
        let orbit_descs = vec![
            ("empty".to_string(), 0),
            ("{x}".to_string(), 1),
        ];
        let transitions = vec![
            (0, "bind_x".to_string(), ["x".to_string()].into_iter().collect(), 1),
        ];
        let na = construct_nominal(&orbit_descs, &transitions, 0, &[1]);

        // The initial state (orbit 0) has empty support, so "x" IS fresh there.
        assert!(check_freshness(&na, 0, "x"));
        // The accepting state (orbit 1) has support {a0}, so "a0" is NOT fresh.
        assert!(!check_freshness(&na, 1, "a0"));
        // But "z" is fresh at orbit 1 since it is not in {a0}.
        assert!(check_freshness(&na, 1, "z"));
    }

    #[test]
    #[should_panic(expected = "Fresh name 'a0' in transition from orbit 1")]
    fn construct_nominal_rejects_non_fresh_name_in_transition() {
        // Orbit 1 has support_size = 1, so its representative state has
        // support = {"a0"}. A transition from orbit 1 with fresh_names = {"a0"}
        // violates equivariance (a0 is already in the source support).
        let orbit_descs = vec![
            ("empty".to_string(), 0),
            ("{x}".to_string(), 1),
        ];
        let transitions = vec![
            (1, "bad".to_string(), ["a0".to_string()].into_iter().collect(), 0),
        ];
        construct_nominal(&orbit_descs, &transitions, 0, &[]);
    }

    // ══════════════════════════════════════════════════════════════════════
    // Scope narrowing tests (Phase 5B.7)
    // ══════════════════════════════════════════════════════════════════════

    /// Helper: build a 3-state linear automaton.
    ///
    /// ```text
    /// q0{} --bind_x[fresh:x]--> q1{x} --bind_y[fresh:y]--> q2{x,y}*
    /// ```
    ///
    /// Additionally, an unreachable state q3{z} is added (no incoming transitions).
    fn build_linear_with_unreachable() -> NominalAutomaton {
        let mut na = NominalAutomaton::new();
        let o0 = na.add_orbit("empty", 0);
        let o1 = na.add_orbit("{x}", 1);
        let o2 = na.add_orbit("{x,y}", 2);
        let o3 = na.add_orbit("{z}", 1);

        let q0 = na.add_state(o0, HashSet::new(), false);
        let q1 = na.add_state(o1, ["x".to_string()].into_iter().collect(), false);
        let q2 = na.add_state(o2, ["x".to_string(), "y".to_string()].into_iter().collect(), true);
        // q3 is unreachable — has name "z" in its support.
        let _q3 = na.add_state(o3, ["z".to_string()].into_iter().collect(), false);

        na.initial_state = Some(q0);
        na.transitions.push(NominalTransition {
            from: q0,
            to: q1,
            input_pattern: "bind_x".to_string(),
            fresh_names: ["x".to_string()].into_iter().collect(),
        });
        na.transitions.push(NominalTransition {
            from: q1,
            to: q2,
            input_pattern: "bind_y".to_string(),
            fresh_names: ["y".to_string()].into_iter().collect(),
        });

        na
    }

    #[test]
    fn name_usage_computation_basic() {
        let na = build_linear_with_unreachable();
        let usages = na.compute_name_usage();

        // "x" appears in q1 and q2 (both reachable).
        let x_usage = usages.get("x").expect("x should be tracked");
        assert!(x_usage.states_using.contains(&1), "x used in q1");
        assert!(x_usage.states_using.contains(&2), "x used in q2");
        assert_eq!(x_usage.states_using.len(), 2);
        // BFS depths: q1 is depth 1, q2 is depth 2.
        assert_eq!(x_usage.scope_depth, 1);
        assert_eq!(x_usage.last_use_depth, 2);

        // "y" appears only in q2 (reachable, depth 2).
        let y_usage = usages.get("y").expect("y should be tracked");
        assert!(y_usage.states_using.contains(&2));
        assert_eq!(y_usage.states_using.len(), 1);
        assert_eq!(y_usage.scope_depth, 2);
        assert_eq!(y_usage.last_use_depth, 2);

        // "z" appears only in q3 (unreachable), so depth stays at defaults.
        let z_usage = usages.get("z").expect("z should be tracked");
        assert!(z_usage.states_using.contains(&3));
        assert_eq!(z_usage.states_using.len(), 1);
        assert_eq!(z_usage.scope_depth, usize::MAX, "z is in an unreachable state");
        assert_eq!(z_usage.last_use_depth, 0, "z is in an unreachable state");
    }

    #[test]
    fn name_usage_tracks_transitions() {
        let na = build_linear_with_unreachable();
        let usages = na.compute_name_usage();

        // "bind_x" is the input_pattern of transition 0.
        let bind_x = usages.get("bind_x").expect("bind_x should be tracked");
        assert!(bind_x.transitions_using.contains(&0));

        // "x" is a fresh name in transition 0.
        let x_usage = usages.get("x").expect("x should be tracked");
        assert!(
            x_usage.transitions_using.contains(&0),
            "x is a fresh name in transition 0",
        );

        // "y" is a fresh name in transition 1.
        let y_usage = usages.get("y").expect("y should be tracked");
        assert!(
            y_usage.transitions_using.contains(&1),
            "y is a fresh name in transition 1",
        );
    }

    #[test]
    fn scope_analysis_eliminates_unreachable_names() {
        let na = build_linear_with_unreachable();
        let result = na.analyze_scope();

        // Original scope: {x, y, z} (all names in any state's support).
        assert_eq!(result.original_scope.len(), 3);
        assert!(result.original_scope.contains(&"x".to_string()));
        assert!(result.original_scope.contains(&"y".to_string()));
        assert!(result.original_scope.contains(&"z".to_string()));

        // Narrowed scope: {x, y} (only reachable states q0, q1, q2).
        assert_eq!(result.narrowed_scope.len(), 2);
        assert!(result.narrowed_scope.contains(&"x".to_string()));
        assert!(result.narrowed_scope.contains(&"y".to_string()));

        // Eliminated: {z}.
        assert_eq!(result.eliminated_names, vec!["z".to_string()]);
        assert_eq!(result.savings, 1);
    }

    #[test]
    fn scope_analysis_empty_automaton() {
        let na = NominalAutomaton::new();
        let result = na.analyze_scope();

        assert!(result.original_scope.is_empty());
        assert!(result.narrowed_scope.is_empty());
        assert!(result.eliminated_names.is_empty());
        assert_eq!(result.savings, 0);
    }

    #[test]
    fn narrow_scope_removes_unreachable_state() {
        let na = build_linear_with_unreachable();
        let narrowed = na.narrow_scope();

        // Only 3 reachable states remain (q0, q1, q2); q3 is gone.
        assert_eq!(narrowed.num_states(), 3);
        // All 2 transitions preserved.
        assert_eq!(narrowed.transitions.len(), 2);
        // Initial state is remapped to new ID 0.
        assert_eq!(narrowed.initial_state, Some(0));
        // q2 was accepting; it becomes new state 2.
        assert!(narrowed.accepting_states.contains(&2));
        assert_eq!(narrowed.accepting_states.len(), 1);

        // The name "z" should not appear in any remaining state's support.
        for state in &narrowed.states {
            assert!(
                !state.support.contains("z"),
                "z should have been eliminated from state {}",
                state.id,
            );
        }
    }

    #[test]
    fn narrow_scope_preserves_used_names() {
        let na = build_linear_with_unreachable();
        let narrowed = na.narrow_scope();

        // q1 (now state 1) should still have "x" in its support.
        let q1_new = &narrowed.states[1];
        assert!(
            q1_new.support.contains("x"),
            "x should be preserved in narrowed q1",
        );

        // q2 (now state 2) should still have "x" and "y".
        let q2_new = &narrowed.states[2];
        assert!(
            q2_new.support.contains("x"),
            "x should be preserved in narrowed q2",
        );
        assert!(
            q2_new.support.contains("y"),
            "y should be preserved in narrowed q2",
        );
    }

    #[test]
    fn narrow_scope_round_trip_reachability() {
        // Narrowing a fully-reachable automaton with no unused names should
        // produce an equivalent automaton.
        let mut na = NominalAutomaton::new();
        let o0 = na.add_orbit("empty", 0);
        let o1 = na.add_orbit("{a}", 1);

        let q0 = na.add_state(o0, HashSet::new(), false);
        let q1 = na.add_state(o1, ["a".to_string()].into_iter().collect(), true);
        na.initial_state = Some(q0);
        na.transitions.push(NominalTransition {
            from: q0,
            to: q1,
            input_pattern: "step".to_string(),
            fresh_names: HashSet::new(),
        });

        let narrowed = na.narrow_scope();

        // Same number of states and transitions.
        assert_eq!(narrowed.num_states(), na.num_states());
        assert_eq!(narrowed.transitions.len(), na.transitions.len());
        assert_eq!(narrowed.accepting_states.len(), na.accepting_states.len());

        // Scope analysis should report zero savings.
        let analysis = narrowed.analyze_scope();
        assert_eq!(analysis.savings, 0);
    }

    #[test]
    fn narrow_scope_idempotent() {
        // Narrowing an already-narrowed automaton should produce the same result.
        let na = build_linear_with_unreachable();
        let first = na.narrow_scope();
        let second = first.narrow_scope();

        assert_eq!(first.num_states(), second.num_states());
        assert_eq!(first.transitions.len(), second.transitions.len());
        assert_eq!(first.accepting_states.len(), second.accepting_states.len());

        // Both should have the same scope analysis.
        let a1 = first.analyze_scope();
        let a2 = second.analyze_scope();
        assert_eq!(a1.narrowed_scope, a2.narrowed_scope);
        assert_eq!(a1.eliminated_names, a2.eliminated_names);
        assert_eq!(a1.savings, 0, "narrowed automaton should have no further savings");
        assert_eq!(a2.savings, 0, "double-narrowed should have no further savings");
    }

    #[test]
    fn test_analyze_from_bundle_with_binders() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "PNew".to_string(),
            "Proc".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("new".to_string()),
                crate::SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                },
                crate::SyntaxItemSpec::Terminal("in".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Proc".to_string(),
                    param_name: "body".to_string(),
                },
            ],
        )];
        let result = analyze_from_bundle(&syntax);
        // NominalAnalysis is returned directly (not Option).
        assert!(result.orbit_count > 0, "should detect at least one orbit from binder");
    }

    #[test]
    fn test_analyze_from_bundle_no_binders() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
            ],
        )];
        let result = analyze_from_bundle(&syntax);
        assert_eq!(result.orbit_count, 0, "no binders means no orbits");
    }
}
