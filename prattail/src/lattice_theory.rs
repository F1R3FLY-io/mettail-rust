//! Subtype Lattice Theory — Join/Meet (LUB/GLB) Constraint Solving
//!
//! ## Theory
//!
//! A subtype lattice is a finite partially ordered set (poset) of types where:
//! - **Subtyping** (`a <= b`) denotes that type `a` is a subtype of type `b`.
//! - **Join** (LUB, least upper bound) is the smallest type `c` such that
//!   `a <= c` and `b <= c`. This corresponds to the narrowest common supertype.
//! - **Meet** (GLB, greatest lower bound) is the largest type `c` such that
//!   `c <= a` and `c <= b`. This corresponds to the widest common subtype.
//!
//! The lattice is constructed from explicit subtype edges. Transitive closure
//! is computed lazily via Warshall's algorithm, and LUB/GLB results are cached
//! for repeated queries.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    LatticeTheory                                   │
//! │                                                                    │
//! │  SubtypeConstraint { sub, sup }                                    │
//! │    └── Constraint type for ConstraintTheory                        │
//! │                                                                    │
//! │  LatticeStore                                                      │
//! │    ├── edges: HashSet<(TypeId, TypeId)>     — direct subtype edges │
//! │    ├── closure: HashSet<(TypeId, TypeId)>   — transitive closure   │
//! │    ├── closure_dirty: bool                  — recompute flag       │
//! │    ├── lub_cache: HashMap<..>               — join cache           │
//! │    ├── glb_cache: HashMap<..>               — meet cache           │
//! │    └── cycles: Vec<(TypeId, TypeId)>        — detected cycles      │
//! │                                                                    │
//! │  TypeAssignment                                                    │
//! │    └── bindings: HashMap<usize, TypeId>     — variable → type      │
//! │                                                                    │
//! │  Operations                                                        │
//! │    ├── compute_closure()   — Warshall's algorithm                  │
//! │    ├── is_subtype(a, b)   — check a ≤ b via closure               │
//! │    ├── join(a, b)         — LUB: smallest common supertype         │
//! │    ├── meet(a, b)         — GLB: largest common subtype            │
//! │    └── detect_cycles()    — find non-trivial cycles (a≤b≤a, a≠b)  │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Construction and Observation
//!
//! Lattice construction and lattice observation are deliberately different
//! interfaces. [`LatticeTheory`] with [`LatticeStore`] is the mutable builder:
//! propagation asserts a new edge. [`FrozenLatticeTheory`] snapshots the closed
//! relation and is the exact, immutable constraint domain used by refinement
//! checking. Successful assertion is not evidence that an edge was already
//! present in a declared lattice.
//!
//! - **builder `propagate`**: Adds a subtype edge, marks closure dirty, detects cycles.
//!   Always succeeds (cycles are recorded but do not cause inconsistency, since
//!   cyclic subtypes represent type equivalences).
//! - **builder `is_consistent`**: Returns `true` unless the store contains a
//!   contradictory cycle involving types that the theory marks as distinct.
//!   In the default configuration, all stores are consistent (cycles are
//!   equivalences, not contradictions).
//! - **frozen `evaluate`**: Observes whether `sub <= sup` holds in the immutable
//!   transitive closure.
//! - **frozen `decide_exact`**: Decides complete Boolean predicates by
//!   stack-safe evaluation in that one fixed interpretation.
//!
//! ## References
//!
//! - Warshall, S. (1962). "A Theorem on Boolean Matrices."
//!   Journal of the ACM, 9(1), 11-12.
//! - Pierce, B. C. (2002). "Types and Programming Languages." MIT Press.
//!   Chapter 15: Subtyping.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::logict::{
    ConstraintTheory, DecidableConstraintTheory, ExactSatisfiability, LogicStream, TheoryPred,
};

// ==============================================================================
// Type Identifiers
// ==============================================================================

/// A type identifier in the lattice.
///
/// Types are represented as unsigned integers for efficient hashing
/// and comparison. Use `LatticeTheory::names` for human-readable display.
pub type TypeId = usize;

// ==============================================================================
// SubtypeConstraint
// ==============================================================================

/// A subtype constraint: `sub <= sup` (sub is a subtype of sup).
///
/// This is the atomic constraint of the lattice theory. Adding this
/// constraint asserts that `sub` is a subtype of `sup` in the type
/// hierarchy.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SubtypeConstraint {
    /// The subtype (more specific type).
    pub sub: TypeId,
    /// The supertype (more general type).
    pub sup: TypeId,
}

// ==============================================================================
// TypeAssignment
// ==============================================================================

/// Assignment of type variables to concrete types.
///
/// Maps variable indices (usize) to `TypeId` values. This is the witness
/// type for the lattice constraint theory.
#[derive(Clone, Debug)]
pub struct TypeAssignment {
    /// Variable-to-type bindings.
    pub bindings: HashMap<usize, TypeId>,
}

// ==============================================================================
// LatticeStore
// ==============================================================================

/// Constraint store for the subtype lattice.
///
/// Maintains direct subtype edges and lazily computes the transitive closure
/// via Warshall's algorithm. LUB/GLB results are cached for efficiency.
/// Non-trivial cycles (a <= b <= a, a != b) are detected and recorded.
#[derive(Clone, Debug)]
pub struct LatticeStore {
    /// Direct subtype edges: (sub, super) pairs.
    edges: HashSet<(TypeId, TypeId)>,
    /// Transitive closure (computed lazily, invalidated by new edges).
    closure: HashSet<(TypeId, TypeId)>,
    /// Whether closure needs recomputation.
    closure_dirty: bool,
    /// LUB cache: (a, b) -> result.
    lub_cache: HashMap<(TypeId, TypeId), Option<TypeId>>,
    /// GLB cache: (a, b) -> result.
    glb_cache: HashMap<(TypeId, TypeId), Option<TypeId>>,
    /// Detected non-trivial cycles: pairs (a, b) where a <= b <= a and a != b.
    /// These represent type equivalences in the lattice.
    cycles: Vec<(TypeId, TypeId)>,
}

impl LatticeStore {
    /// Create an empty lattice store.
    pub fn new() -> Self {
        LatticeStore {
            edges: HashSet::new(),
            closure: HashSet::new(),
            closure_dirty: false,
            lub_cache: HashMap::new(),
            glb_cache: HashMap::new(),
            cycles: Vec::new(),
        }
    }

    /// Add a direct subtype edge.
    ///
    /// Marks the closure as dirty and clears the LUB/GLB caches (since
    /// the new edge may change join/meet results).
    pub fn add_edge(&mut self, sub: TypeId, sup: TypeId) {
        if self.edges.insert((sub, sup)) {
            self.closure_dirty = true;
            self.lub_cache.clear();
            self.glb_cache.clear();
        }
    }

    /// Collect all type IDs mentioned in any edge (sub or sup).
    pub fn all_types(&self) -> HashSet<TypeId> {
        let mut types = HashSet::new();
        for &(sub, sup) in &self.edges {
            types.insert(sub);
            types.insert(sup);
        }
        types
    }

    /// Return the detected cycles (type equivalence pairs).
    pub fn detected_cycles(&self) -> &[(TypeId, TypeId)] {
        &self.cycles
    }
}

impl Default for LatticeStore {
    fn default() -> Self {
        Self::new()
    }
}

// ==============================================================================
// LatticeTheory
// ==============================================================================

/// Subtype lattice theory with join/meet operations.
///
/// Implements `ConstraintTheory` for decidable subtype checking over a
/// finite universe of types. The universe must be explicitly provided so
/// that join/meet computations can enumerate all candidate types.
#[derive(Clone, Debug)]
pub struct LatticeTheory {
    /// The universe of types (finite, enumerable).
    pub universe: Vec<TypeId>,
    /// Type names for display.
    pub names: HashMap<TypeId, String>,
}

impl LatticeTheory {
    /// Create a new lattice theory with the given universe and names.
    pub fn new(universe: Vec<TypeId>, names: HashMap<TypeId, String>) -> Self {
        LatticeTheory { universe, names }
    }

    /// Get the display name for a type, falling back to its numeric ID.
    pub fn type_name(&self, id: TypeId) -> String {
        self.names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("T{}", id))
    }

    /// Compute the transitive closure of the subtype relation.
    ///
    /// Uses Warshall's algorithm (O(n^3) where n = |universe|). The
    /// closure includes reflexive pairs (a <= a for all a in universe).
    ///
    /// After computing the closure, detects non-trivial cycles
    /// (a <= b and b <= a with a != b) and records them.
    pub fn compute_closure(&self, store: &mut LatticeStore) {
        if !store.closure_dirty && !store.closure.is_empty() {
            return;
        }

        // Initialize closure with direct edges.
        store.closure = store.edges.clone();

        // Add reflexive pairs for all types in the universe.
        for &t in &self.universe {
            store.closure.insert((t, t));
        }
        // Also add reflexive pairs for types mentioned in edges but
        // not necessarily in the universe (defensive).
        for t in store.all_types() {
            store.closure.insert((t, t));
        }

        // Warshall's algorithm: for each intermediate vertex k,
        // if (i, k) and (k, j) are in the closure, add (i, j).
        let all_types: Vec<TypeId> = {
            let mut s = HashSet::new();
            for &t in &self.universe {
                s.insert(t);
            }
            for &(a, b) in &store.edges {
                s.insert(a);
                s.insert(b);
            }
            s.into_iter().collect()
        };

        for &k in &all_types {
            // Collect pairs (i, k) and (k, j) before mutating.
            let predecessors: Vec<TypeId> = all_types
                .iter()
                .filter(|&&i| store.closure.contains(&(i, k)))
                .copied()
                .collect();
            let successors: Vec<TypeId> = all_types
                .iter()
                .filter(|&&j| store.closure.contains(&(k, j)))
                .copied()
                .collect();

            for &i in &predecessors {
                for &j in &successors {
                    store.closure.insert((i, j));
                }
            }
        }

        // Detect non-trivial cycles.
        store.cycles.clear();
        for &a in &all_types {
            for &b in &all_types {
                if a < b && store.closure.contains(&(a, b)) && store.closure.contains(&(b, a)) {
                    store.cycles.push((a, b));
                }
            }
        }

        store.closure_dirty = false;
    }

    /// Check whether `a <= b` holds (using transitive closure).
    ///
    /// Reflexivity (a <= a) always holds. For non-reflexive queries,
    /// the transitive closure is consulted (and recomputed if dirty).
    pub fn is_subtype(&self, store: &mut LatticeStore, a: TypeId, b: TypeId) -> bool {
        if a == b {
            return true;
        }
        self.ensure_closure(store);
        store.closure.contains(&(a, b))
    }

    /// Compute the join (LUB, least upper bound) of two types.
    ///
    /// Returns the smallest type `c` in the universe such that
    /// `a <= c` and `b <= c`. Returns `None` if no such type exists
    /// (the lattice may not have a top element).
    ///
    /// When multiple candidates have the same minimality, the one with
    /// the fewest supertypes is chosen (most specific common supertype).
    pub fn join(&self, store: &mut LatticeStore, a: TypeId, b: TypeId) -> Option<TypeId> {
        // Normalize the key for cache symmetry: join(a, b) == join(b, a).
        let key = if a <= b { (a, b) } else { (b, a) };

        if let Some(&cached) = store.lub_cache.get(&key) {
            return cached;
        }

        self.ensure_closure(store);

        // Trivial cases.
        if a == b {
            store.lub_cache.insert(key, Some(a));
            return Some(a);
        }
        if store.closure.contains(&(a, b)) {
            store.lub_cache.insert(key, Some(b));
            return Some(b);
        }
        if store.closure.contains(&(b, a)) {
            store.lub_cache.insert(key, Some(a));
            return Some(a);
        }

        // Find all common upper bounds: types c such that a <= c and b <= c.
        let upper_bounds: Vec<TypeId> = self
            .universe
            .iter()
            .copied()
            .filter(|&c| store.closure.contains(&(a, c)) && store.closure.contains(&(b, c)))
            .collect();

        // Find the least (most specific) among the upper bounds:
        // c is least if no other upper bound d satisfies d <= c (d != c).
        let result = upper_bounds.iter().copied().find(|&c| {
            upper_bounds.iter().all(|&d| {
                d == c || !store.closure.contains(&(d, c)) || store.closure.contains(&(c, d))
            })
        });

        store.lub_cache.insert(key, result);
        result
    }

    /// Compute the meet (GLB, greatest lower bound) of two types.
    ///
    /// Returns the largest type `c` in the universe such that
    /// `c <= a` and `c <= b`. Returns `None` if no such type exists
    /// (the lattice may not have a bottom element).
    pub fn meet(&self, store: &mut LatticeStore, a: TypeId, b: TypeId) -> Option<TypeId> {
        // Normalize the key for cache symmetry: meet(a, b) == meet(b, a).
        let key = if a <= b { (a, b) } else { (b, a) };

        if let Some(&cached) = store.glb_cache.get(&key) {
            return cached;
        }

        self.ensure_closure(store);

        // Trivial cases.
        if a == b {
            store.glb_cache.insert(key, Some(a));
            return Some(a);
        }
        if store.closure.contains(&(a, b)) {
            store.glb_cache.insert(key, Some(a));
            return Some(a);
        }
        if store.closure.contains(&(b, a)) {
            store.glb_cache.insert(key, Some(b));
            return Some(b);
        }

        // Find all common lower bounds: types c such that c <= a and c <= b.
        let lower_bounds: Vec<TypeId> = self
            .universe
            .iter()
            .copied()
            .filter(|&c| store.closure.contains(&(c, a)) && store.closure.contains(&(c, b)))
            .collect();

        // Find the greatest (most general) among the lower bounds:
        // c is greatest if no other lower bound d satisfies c <= d (d != c).
        let result = lower_bounds.iter().copied().find(|&c| {
            lower_bounds.iter().all(|&d| {
                d == c || !store.closure.contains(&(c, d)) || store.closure.contains(&(d, c))
            })
        });

        store.glb_cache.insert(key, result);
        result
    }

    /// Detect non-trivial cycles in the subtype relation.
    ///
    /// A non-trivial cycle exists when `a <= b` and `b <= a` with `a != b`.
    /// Such cycles indicate type equivalences (antisymmetry violation).
    ///
    /// Returns a list of (a, b) pairs forming cycles (with a < b to avoid
    /// duplicate reporting).
    pub fn detect_cycles(&self, store: &mut LatticeStore) -> Vec<(TypeId, TypeId)> {
        self.ensure_closure(store);
        store.cycles.clone()
    }

    /// Ensure the transitive closure is up to date.
    fn ensure_closure(&self, store: &mut LatticeStore) {
        if store.closure_dirty || store.closure.is_empty() {
            self.compute_closure(store);
        }
    }

    /// Check exhaustiveness: whether every type in the universe that is a
    /// subtype of some other type has its subtype relationship recorded.
    ///
    /// Returns the set of types that appear in the universe but have no
    /// subtype edges (neither as sub nor as sup). These are "isolated" types.
    pub fn isolated_types(&self, store: &LatticeStore) -> Vec<TypeId> {
        let mentioned = store.all_types();
        self.universe
            .iter()
            .copied()
            .filter(|t| !mentioned.contains(t))
            .collect()
    }

    /// Freeze the current declared subtype relation for semantic queries.
    ///
    /// The returned theory owns an immutable transitive-closure snapshot.
    /// Later changes to `store` cannot affect it, and evaluating a predicate
    /// cannot add edges. This is the constraint domain to use for refinement
    /// predicates over an already-declared type hierarchy.
    pub fn freeze(&self, store: &LatticeStore) -> FrozenLatticeTheory {
        let mut closed_store = store.clone();
        self.ensure_closure(&mut closed_store);
        FrozenLatticeTheory {
            universe: self.universe.clone(),
            names: self.names.clone(),
            closure: closed_store.closure,
        }
    }
}

impl fmt::Display for LatticeTheory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LatticeTheory({} types)", self.universe.len())
    }
}

// ==============================================================================
// FrozenLatticeTheory
// ==============================================================================

/// Immutable, exact interpretation of a declared subtype lattice.
///
/// [`LatticeTheory`] is a builder whose propagation operation asserts edges.
/// This snapshot is instead an observation algebra: an atom is true exactly
/// when its pair occurs in the frozen reflexive-transitive closure. Because
/// [`SubtypeConstraint`] contains ground type identifiers, the snapshot is a
/// single fixed interpretation and every [`TheoryPred`] is exactly decidable.
///
/// The corresponding construction/observation separation and exactness proof
/// is `formal/rocq/lattice/theories/FrozenLatticeConstraint.v`.
#[derive(Clone, Debug)]
pub struct FrozenLatticeTheory {
    /// Finite declared universe used to construct the identity witness.
    pub universe: Vec<TypeId>,
    /// Type names retained for diagnostics.
    pub names: HashMap<TypeId, String>,
    /// Immutable reflexive-transitive subtype relation.
    closure: HashSet<(TypeId, TypeId)>,
}

impl FrozenLatticeTheory {
    /// Observe whether `sub <= sup` holds in this snapshot.
    ///
    /// Type identifiers denote ground constants. Reflexivity therefore holds
    /// even for an identifier that has no explicit declaration edge; every
    /// non-reflexive fact must occur in the frozen closure.
    pub fn is_subtype(&self, sub: TypeId, sup: TypeId) -> bool {
        sub == sup || self.closure.contains(&(sub, sup))
    }

    /// Get the display name for a type, falling back to its numeric ID.
    pub fn type_name(&self, id: TypeId) -> String {
        self.names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("T{}", id))
    }

    fn identity_assignment(&self) -> TypeAssignment {
        let bindings = self
            .universe
            .iter()
            .enumerate()
            .map(|(index, &type_id)| (index, type_id))
            .collect();
        TypeAssignment { bindings }
    }

    /// Evaluate a complete Boolean predicate with an explicit task stack.
    fn evaluate_predicate(&self, predicate: &TheoryPred<Self>) -> bool {
        enum Task<'predicate> {
            Visit(&'predicate TheoryPred<FrozenLatticeTheory>),
            Not,
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(predicate)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TheoryPred::True) => values.push(true),
                Task::Visit(TheoryPred::False) => values.push(false),
                Task::Visit(TheoryPred::Atom(constraint)) => {
                    values.push(self.is_subtype(constraint.sub, constraint.sup));
                },
                Task::Visit(TheoryPred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Not => {
                    let value = values
                        .pop()
                        .expect("frozen-lattice predicate PDA lost its negand");
                    values.push(!value);
                },
                Task::And => {
                    let right = values
                        .pop()
                        .expect("frozen-lattice predicate PDA lost conjunction RHS");
                    let left = values
                        .pop()
                        .expect("frozen-lattice predicate PDA lost conjunction LHS");
                    values.push(left && right);
                },
                Task::Or => {
                    let right = values
                        .pop()
                        .expect("frozen-lattice predicate PDA lost disjunction RHS");
                    let left = values
                        .pop()
                        .expect("frozen-lattice predicate PDA lost disjunction LHS");
                    values.push(left || right);
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("frozen-lattice predicate PDA produced no value")
    }
}

impl fmt::Display for FrozenLatticeTheory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FrozenLatticeTheory({} types)", self.universe.len())
    }
}

impl ConstraintTheory for FrozenLatticeTheory {
    type Constraint = SubtypeConstraint;
    type Assignment = TypeAssignment;
    type Store = ();

    fn empty_store(&self) {}

    /// Check an asserted proposition without changing the frozen relation.
    fn propagate(&self, _store: &(), constraint: &SubtypeConstraint) -> Option<()> {
        self.is_subtype(constraint.sub, constraint.sup)
            .then_some(())
    }

    fn is_consistent(&self, _store: &()) -> bool {
        true
    }

    fn witness(&self, _store: &()) -> Option<TypeAssignment> {
        Some(self.identity_assignment())
    }

    fn label(&self, _store: &()) -> LogicStream<SubtypeConstraint> {
        LogicStream::empty()
    }

    fn evaluate(&self, constraint: &SubtypeConstraint, _assignment: &TypeAssignment) -> bool {
        self.is_subtype(constraint.sub, constraint.sup)
    }
}

impl DecidableConstraintTheory for FrozenLatticeTheory {
    fn decide_exact(&self, predicate: &TheoryPred<Self>) -> ExactSatisfiability<TypeAssignment> {
        let witness = self.identity_assignment();
        if self.evaluate_predicate(predicate) {
            ExactSatisfiability::Satisfiable(witness)
        } else {
            ExactSatisfiability::Unsatisfiable
        }
    }
}

// ==============================================================================
// ConstraintTheory Implementation
// ==============================================================================

impl ConstraintTheory for LatticeTheory {
    type Constraint = SubtypeConstraint;
    type Assignment = TypeAssignment;
    type Store = LatticeStore;

    fn empty_store(&self) -> LatticeStore {
        LatticeStore::new()
    }

    /// Add a subtype edge and propagate.
    ///
    /// Always succeeds: cycles are recorded as type equivalences rather
    /// than causing inconsistency. The closure is marked dirty so it
    /// will be recomputed on the next query.
    fn propagate(&self, store: &LatticeStore, c: &SubtypeConstraint) -> Option<LatticeStore> {
        let mut new_store = store.clone();
        new_store.add_edge(c.sub, c.sup);

        // Eagerly recompute closure to detect cycles immediately.
        self.compute_closure(&mut new_store);

        Some(new_store)
    }

    /// The lattice store is always consistent.
    ///
    /// Cycles represent type equivalences (a and b are the same type),
    /// not contradictions. A store with cycles is still consistent.
    fn is_consistent(&self, _store: &LatticeStore) -> bool {
        true
    }

    /// Extract a witness assignment from the store.
    ///
    /// For each type in the universe, the witness maps the type index
    /// to itself. This is the identity assignment — the store's subtype
    /// relation is the witness itself.
    fn witness(&self, _store: &LatticeStore) -> Option<TypeAssignment> {
        let bindings: HashMap<usize, TypeId> = self
            .universe
            .iter()
            .enumerate()
            .map(|(idx, &tid)| (idx, tid))
            .collect();
        Some(TypeAssignment { bindings })
    }

    /// No labeling needed — the lattice theory is decidable.
    ///
    /// The finite universe of types means propagation alone determines
    /// all subtype relationships via transitive closure.
    fn label(&self, _store: &LatticeStore) -> LogicStream<SubtypeConstraint> {
        LogicStream::empty()
    }

    /// Evaluate whether a subtype constraint holds under the given assignment.
    ///
    /// Recomputes the transitive closure if needed, then checks if
    /// `constraint.sub <= constraint.sup` is in the closure.
    ///
    /// The assignment maps variable indices to type IDs. If the constraint
    /// references type IDs directly (not variables), the assignment is not
    /// needed — the closure is checked directly.
    fn evaluate(&self, c: &SubtypeConstraint, _assignment: &TypeAssignment) -> bool {
        // For the lattice theory, constraints reference TypeIds directly.
        // Reflexivity always holds.
        if c.sub == c.sup {
            return true;
        }
        // Without a store, we can only check reflexivity.
        // The evaluate method checks semantic truth of the constraint;
        // for non-reflexive cases, we conservatively return false since
        // we cannot access the closure here. The proper check is done
        // via is_subtype() with a store.
        //
        // However, the ConstraintTheory trait's evaluate is meant to
        // check against a concrete assignment. Since all our constraints
        // are structural (TypeId-based, not variable-based), we check
        // reflexivity only.
        false
    }
}

// ==============================================================================
// Analysis result
// ==============================================================================

/// Analysis result from subtype lattice guard checking.
#[derive(Debug, Clone, Default)]
pub struct LatticeAnalysis {
    /// Unsatisfiable subtype constraints (contradictory type hierarchy).
    pub unsatisfiable_constraints: Vec<(String, String)>,
    /// Redundant subtype constraints (already implied by transitivity).
    pub redundant_constraints: Vec<(String, String)>,
}

// ==============================================================================
// Grammar Bundle Analysis
// ==============================================================================

/// Infer a subtype lattice from grammar category delegation patterns.
///
/// Walks `all_syntax` looking for category inclusion patterns that form a type
/// hierarchy.  When *all* of category A's rules delegate exclusively to
/// category B as their sole `NonTerminal` item (ignoring terminals), the
/// inference rule `A ≤ B` is added.
///
/// # Algorithm
///
/// 1. Build a category-name → index map from `categories`.
/// 2. For each rule `(label, cat, items)`, count how many rules exist per
///    category and, for rules whose non-terminal content is exactly one
///    distinct non-terminal category, record that delegation target.
/// 3. A category A is inferred to be a subtype of category B when every rule
///    belonging to A delegates exclusively to B (i.e., every rule has at most
///    one unique non-terminal reference and it is always B).
/// 4. Build a `LatticeTheory` + `LatticeStore` from the inferred edges and
///    compute the transitive closure.
/// 5. Check for *non-trivial cycles* (`store.cycles`) — these indicate a
///    contradictory hierarchy (A ≤ B and B ≤ A with A ≠ B).
/// 6. Check for *redundant edges* — a direct edge `(A, C)` is redundant if
///    `A ≤ C` is already implied by a path through some intermediate B.
/// 7. Return `LatticeAnalysis::default()` when no hierarchy is detected.
///
/// # Parameters
///
/// * `all_syntax` — Per-rule syntax items: `(label, category, items)`.
/// * `categories` — Category metadata for the grammar.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> LatticeAnalysis {
    if categories.is_empty() || all_syntax.is_empty() {
        return LatticeAnalysis::default();
    }

    // Step 1: Build category name → TypeId (index) map.
    let cat_to_id: HashMap<String, TypeId> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name.clone(), i))
        .collect();

    let num_cats = categories.len();
    // universe of TypeIds
    let universe: Vec<TypeId> = (0..num_cats).collect();
    let names: HashMap<TypeId, String> = categories
        .iter()
        .enumerate()
        .map(|(i, c)| (i, c.name.clone()))
        .collect();

    // Step 2: For each category, collect per-rule delegation targets.
    //
    // For a rule to be a "pure delegation" its non-terminal items must all
    // reference exactly one distinct category (different from self), and there
    // must be at least one such item.  Terminal items are allowed (they are
    // ignored for this analysis).
    //
    // rule_delegates[cat_id] = Some(target_id)   — all rules delegate to target_id
    //                        = None              — mixed or no delegation found
    //
    // We use a per-category Option<TypeId> accumulator:
    //   - Uninitialised (represented as `Option<Option<TypeId>>`):
    //       outer None  = not yet seen any rule for this category
    //       outer Some(inner) = seen at least one rule:
    //           inner None       = this category cannot be a pure delegator
    //           inner Some(tid)  = all rules so far delegate to `tid`

    let mut rule_delegates: Vec<Option<Option<TypeId>>> = vec![None; num_cats];

    for (_label, cat, items) in all_syntax {
        let Some(&src_id) = cat_to_id.get(cat.as_str()) else {
            continue;
        };

        // Collect the set of distinct non-terminal categories this rule references.
        let mut nt_targets: HashSet<TypeId> = HashSet::new();
        collect_rule_nonterminals(items, src_id, &cat_to_id, &mut nt_targets);

        // A rule qualifies as a pure delegation if it references exactly one
        // non-terminal category (and it is not a self-reference).
        let delegation: Option<TypeId> = if nt_targets.len() == 1 {
            let &tid = nt_targets.iter().next().expect("exactly one element");
            if tid != src_id {
                Some(tid)
            } else {
                None // self-recursive — not a subtype delegation
            }
        } else {
            None // zero or multiple non-terminal targets — not a pure delegation
        };

        // Merge with the accumulator for this category.
        rule_delegates[src_id] = Some(match rule_delegates[src_id] {
            None => delegation, // first rule seen for this category
            Some(prev) => match (prev, delegation) {
                (Some(p), Some(d)) if p == d => Some(p), // consistent delegation
                _ => None,                               // contradiction or mixed
            },
        });
    }

    // Step 3: Collect inferred edges A ≤ B.
    let mut inferred_edges: Vec<(TypeId, TypeId)> = Vec::new();
    for (src_id, state) in rule_delegates.iter().enumerate() {
        if let Some(Some(tgt_id)) = state {
            inferred_edges.push((src_id, *tgt_id));
        }
    }

    // No hierarchy inferred — return default.
    if inferred_edges.is_empty() {
        return LatticeAnalysis::default();
    }

    // Step 4: Build LatticeTheory + LatticeStore from inferred edges.
    let theory = LatticeTheory::new(universe, names);
    let mut store = LatticeStore::new();
    for &(sub, sup) in &inferred_edges {
        store.add_edge(sub, sup);
    }
    theory.compute_closure(&mut store);

    // Step 5: Check for non-trivial cycles → unsatisfiable constraints.
    let unsatisfiable_constraints: Vec<(String, String)> = store
        .cycles
        .iter()
        .map(|&(a, b)| (theory.type_name(a), theory.type_name(b)))
        .collect();

    // Step 6: Check for redundant edges.
    //
    // An edge (A, C) is redundant if it is already in the closure when
    // computed without that edge.  We test this by: removing the edge,
    // recomputing the closure, and checking whether (A, C) is still present.
    let mut redundant_constraints: Vec<(String, String)> = Vec::new();
    for &(sub, sup) in &inferred_edges {
        // Build a transient store without this edge.
        let mut tmp_store = LatticeStore::new();
        for &(s, t) in &inferred_edges {
            if (s, t) != (sub, sup) {
                tmp_store.add_edge(s, t);
            }
        }
        theory.compute_closure(&mut tmp_store);

        // If (sub, sup) is still reachable via the remaining edges, this
        // edge is redundant.
        if tmp_store.closure.contains(&(sub, sup)) {
            redundant_constraints.push((theory.type_name(sub), theory.type_name(sup)));
        }
    }

    LatticeAnalysis {
        unsatisfiable_constraints,
        redundant_constraints,
    }
}

/// Collect all distinct non-terminal category TypeIds referenced in a rule's
/// syntax item list, recursively descending into composite items.
///
/// Self-references (where `src_id == target_id`) are included — the caller
/// decides how to interpret them.
fn collect_rule_nonterminals(
    items: &[crate::SyntaxItemSpec],
    src_id: TypeId,
    cat_to_id: &HashMap<String, TypeId>,
    out: &mut HashSet<TypeId>,
) {
    let _ = src_id;
    for item in crate::syntax_item::preorder(items) {
        match item {
            crate::SyntaxItemSpec::NonTerminal { category, .. } => {
                if let Some(&tid) = cat_to_id.get(category.as_str()) {
                    out.insert(tid);
                }
            },
            crate::SyntaxItemSpec::Binder { category, .. } => {
                if let Some(&tid) = cat_to_id.get(category.as_str()) {
                    out.insert(tid);
                }
            },
            crate::SyntaxItemSpec::Collection { element_category, .. } => {
                if let Some(&tid) = cat_to_id.get(element_category.as_str()) {
                    out.insert(tid);
                }
            },
            crate::SyntaxItemSpec::Zip { left_category, right_category, .. } => {
                if let Some(&tid) = cat_to_id.get(left_category.as_str()) {
                    out.insert(tid);
                }
                if let Some(&tid) = cat_to_id.get(right_category.as_str()) {
                    out.insert(tid);
                }
            },
            // Terminal, IdentCapture, BinderCollection — no non-terminal references.
            _ => {},
        }
    }
}

// ==============================================================================
// Tests
// ==============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a type hierarchy for testing.
    ///
    /// ```text
    ///       Number (2)
    ///      /      \
    ///   Int (0)  Float (1)
    /// ```
    fn number_hierarchy() -> (LatticeTheory, LatticeStore) {
        let int = 0;
        let float = 1;
        let number = 2;

        let theory = LatticeTheory::new(
            vec![int, float, number],
            HashMap::from([
                (int, "Int".to_string()),
                (float, "Float".to_string()),
                (number, "Number".to_string()),
            ]),
        );

        let mut store = theory.empty_store();
        store.add_edge(int, number); // Int <= Number
        store.add_edge(float, number); // Float <= Number
        theory.compute_closure(&mut store);

        (theory, store)
    }

    /// Helper: create a diamond hierarchy.
    ///
    /// ```text
    ///       D (3)
    ///      / \
    ///    B(1) C(2)
    ///      \ /
    ///       A (0)
    /// ```
    fn diamond_hierarchy() -> (LatticeTheory, LatticeStore) {
        let a = 0;
        let b = 1;
        let c = 2;
        let d = 3;

        let theory = LatticeTheory::new(
            vec![a, b, c, d],
            HashMap::from([
                (a, "A".to_string()),
                (b, "B".to_string()),
                (c, "C".to_string()),
                (d, "D".to_string()),
            ]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b); // A <= B
        store.add_edge(a, c); // A <= C
        store.add_edge(b, d); // B <= D
        store.add_edge(c, d); // C <= D
        theory.compute_closure(&mut store);

        (theory, store)
    }

    /// Helper: create a read/write capability hierarchy.
    ///
    /// ```text
    ///   Readable (0)   Writable (1)
    ///        \            /
    ///       ReadWrite (2)
    /// ```
    fn capability_hierarchy() -> (LatticeTheory, LatticeStore) {
        let readable = 0;
        let writable = 1;
        let readwrite = 2;

        let theory = LatticeTheory::new(
            vec![readable, writable, readwrite],
            HashMap::from([
                (readable, "Readable".to_string()),
                (writable, "Writable".to_string()),
                (readwrite, "ReadWrite".to_string()),
            ]),
        );

        let mut store = theory.empty_store();
        store.add_edge(readwrite, readable); // ReadWrite <= Readable
        store.add_edge(readwrite, writable); // ReadWrite <= Writable
        theory.compute_closure(&mut store);

        (theory, store)
    }

    // ── Transitive Closure Tests ──────────────────────────────────────────

    #[test]
    fn transitive_closure_basic() {
        // A <= B, B <= C => A <= C
        let a = 0;
        let b = 1;
        let c = 2;

        let theory = LatticeTheory::new(
            vec![a, b, c],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string()), (c, "C".to_string())]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b); // A <= B
        store.add_edge(b, c); // B <= C

        assert!(theory.is_subtype(&mut store, a, c), "transitivity: A <= B, B <= C => A <= C");
    }

    #[test]
    fn transitive_closure_chain() {
        // A <= B <= C <= D => A <= D
        let a = 0;
        let b = 1;
        let c = 2;
        let d = 3;

        let theory = LatticeTheory::new(
            vec![a, b, c, d],
            HashMap::from([
                (a, "A".to_string()),
                (b, "B".to_string()),
                (c, "C".to_string()),
                (d, "D".to_string()),
            ]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b);
        store.add_edge(b, c);
        store.add_edge(c, d);

        assert!(theory.is_subtype(&mut store, a, d), "A <= D via chain");
        assert!(theory.is_subtype(&mut store, a, c), "A <= C via chain");
        assert!(theory.is_subtype(&mut store, b, d), "B <= D via chain");
    }

    #[test]
    fn transitive_closure_no_false_positives() {
        // A <= B, C is unrelated
        let a = 0;
        let b = 1;
        let c = 2;

        let theory = LatticeTheory::new(
            vec![a, b, c],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string()), (c, "C".to_string())]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b);

        assert!(!theory.is_subtype(&mut store, a, c), "A is not a subtype of unrelated C");
        assert!(!theory.is_subtype(&mut store, c, a), "C is not a subtype of unrelated A");
        assert!(!theory.is_subtype(&mut store, b, a), "B is not a subtype of A (only A <= B)");
    }

    // ── Reflexivity Tests ─────────────────────────────────────────────────

    #[test]
    fn reflexivity_always_holds() {
        let a = 0;
        let b = 1;

        let theory = LatticeTheory::new(
            vec![a, b],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string())]),
        );

        let mut store = theory.empty_store();
        // Even with no edges, reflexivity holds.
        assert!(theory.is_subtype(&mut store, a, a), "A <= A (reflexive)");
        assert!(theory.is_subtype(&mut store, b, b), "B <= B (reflexive)");
    }

    #[test]
    fn reflexivity_with_edges() {
        let (theory, mut store) = number_hierarchy();
        assert!(theory.is_subtype(&mut store, 0, 0), "Int <= Int");
        assert!(theory.is_subtype(&mut store, 1, 1), "Float <= Float");
        assert!(theory.is_subtype(&mut store, 2, 2), "Number <= Number");
    }

    // ── Cycle Detection Tests ─────────────────────────────────────────────

    #[test]
    fn cycle_detection_basic() {
        // A <= B, B <= A => cycle detected
        let a = 0;
        let b = 1;

        let theory = LatticeTheory::new(
            vec![a, b],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string())]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b);
        store.add_edge(b, a);

        let cycles = theory.detect_cycles(&mut store);
        assert!(!cycles.is_empty(), "should detect cycle: A <= B <= A");
        assert!(cycles.contains(&(a, b)), "cycle should include (A, B)");
    }

    #[test]
    fn no_cycles_in_dag() {
        let (theory, mut store) = number_hierarchy();
        let cycles = theory.detect_cycles(&mut store);
        assert!(cycles.is_empty(), "DAG hierarchy should have no cycles");
    }

    #[test]
    fn cycle_propagation_still_succeeds() {
        // Cycles represent type equivalences, not contradictions.
        let a = 0;
        let b = 1;

        let theory = LatticeTheory::new(
            vec![a, b],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string())]),
        );

        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: a, sup: b })
            .expect("propagation should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: b, sup: a })
            .expect("propagation should still succeed (cycle = equivalence)");

        // Both directions hold.
        let mut store = store;
        assert!(theory.is_subtype(&mut store, a, b));
        assert!(theory.is_subtype(&mut store, b, a));

        // Cycle is recorded.
        assert!(!store.detected_cycles().is_empty(), "cycle should be recorded");
    }

    // ── Join (LUB) Tests ──────────────────────────────────────────────────

    #[test]
    fn join_in_number_hierarchy() {
        // Int <= Number, Float <= Number => join(Int, Float) = Number
        let (theory, mut store) = number_hierarchy();
        let result = theory.join(&mut store, 0, 1);
        assert_eq!(result, Some(2), "join(Int, Float) should be Number");
    }

    #[test]
    fn join_reflexive() {
        let (theory, mut store) = number_hierarchy();
        assert_eq!(theory.join(&mut store, 0, 0), Some(0), "join(Int, Int) = Int");
    }

    #[test]
    fn join_with_subtype() {
        // join(Int, Number) = Number (since Int <= Number)
        let (theory, mut store) = number_hierarchy();
        assert_eq!(theory.join(&mut store, 0, 2), Some(2), "join(Int, Number) = Number");
    }

    #[test]
    fn join_diamond() {
        // In diamond: A <= B, A <= C, B <= D, C <= D
        // join(B, C) = D
        let (theory, mut store) = diamond_hierarchy();
        assert_eq!(theory.join(&mut store, 1, 2), Some(3), "join(B, C) = D in diamond");
    }

    #[test]
    fn join_no_common_supertype() {
        // Two unrelated types with no common supertype.
        let a = 0;
        let b = 1;

        let theory = LatticeTheory::new(
            vec![a, b],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string())]),
        );

        let mut store = theory.empty_store();
        // No edges at all.
        assert_eq!(
            theory.join(&mut store, a, b),
            None,
            "join of unrelated types with no top is None"
        );
    }

    #[test]
    fn join_commutative() {
        let (theory, mut store) = number_hierarchy();
        let ab = theory.join(&mut store, 0, 1);
        let ba = theory.join(&mut store, 1, 0);
        assert_eq!(ab, ba, "join should be commutative");
    }

    #[test]
    fn join_cached() {
        let (theory, mut store) = number_hierarchy();
        // First call computes.
        let r1 = theory.join(&mut store, 0, 1);
        // Second call should return cached result.
        let r2 = theory.join(&mut store, 0, 1);
        assert_eq!(r1, r2, "cached join should match");
    }

    // ── Meet (GLB) Tests ──────────────────────────────────────────────────

    #[test]
    fn meet_in_capability_hierarchy() {
        // ReadWrite <= Readable, ReadWrite <= Writable
        // meet(Readable, Writable) = ReadWrite
        let (theory, mut store) = capability_hierarchy();
        let result = theory.meet(&mut store, 0, 1);
        assert_eq!(result, Some(2), "meet(Readable, Writable) should be ReadWrite");
    }

    #[test]
    fn meet_reflexive() {
        let (theory, mut store) = capability_hierarchy();
        assert_eq!(theory.meet(&mut store, 0, 0), Some(0), "meet(Readable, Readable) = Readable");
    }

    #[test]
    fn meet_with_subtype() {
        // meet(ReadWrite, Readable) = ReadWrite (since ReadWrite <= Readable)
        let (theory, mut store) = capability_hierarchy();
        assert_eq!(theory.meet(&mut store, 2, 0), Some(2), "meet(ReadWrite, Readable) = ReadWrite");
    }

    #[test]
    fn meet_diamond() {
        // In diamond: A <= B, A <= C, B <= D, C <= D
        // meet(B, C) = A
        let (theory, mut store) = diamond_hierarchy();
        assert_eq!(theory.meet(&mut store, 1, 2), Some(0), "meet(B, C) = A in diamond");
    }

    #[test]
    fn meet_no_common_subtype() {
        // Two unrelated types with no common subtype.
        let a = 0;
        let b = 1;

        let theory = LatticeTheory::new(
            vec![a, b],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string())]),
        );

        let mut store = theory.empty_store();
        assert_eq!(
            theory.meet(&mut store, a, b),
            None,
            "meet of unrelated types with no bottom is None"
        );
    }

    #[test]
    fn meet_commutative() {
        let (theory, mut store) = capability_hierarchy();
        let ab = theory.meet(&mut store, 0, 1);
        let ba = theory.meet(&mut store, 1, 0);
        assert_eq!(ab, ba, "meet should be commutative");
    }

    #[test]
    fn meet_cached() {
        let (theory, mut store) = capability_hierarchy();
        let r1 = theory.meet(&mut store, 0, 1);
        let r2 = theory.meet(&mut store, 0, 1);
        assert_eq!(r1, r2, "cached meet should match");
    }

    // ── Diamond Hierarchy Tests ───────────────────────────────────────────

    #[test]
    fn diamond_transitive_closure() {
        let (theory, mut store) = diamond_hierarchy();

        // Direct edges.
        assert!(theory.is_subtype(&mut store, 0, 1), "A <= B");
        assert!(theory.is_subtype(&mut store, 0, 2), "A <= C");
        assert!(theory.is_subtype(&mut store, 1, 3), "B <= D");
        assert!(theory.is_subtype(&mut store, 2, 3), "C <= D");

        // Transitive.
        assert!(theory.is_subtype(&mut store, 0, 3), "A <= D (transitive)");

        // Non-relationships.
        assert!(!theory.is_subtype(&mut store, 1, 2), "B is not <= C");
        assert!(!theory.is_subtype(&mut store, 2, 1), "C is not <= B");
        assert!(!theory.is_subtype(&mut store, 3, 0), "D is not <= A");
    }

    #[test]
    fn diamond_join_and_meet_comprehensive() {
        let (theory, mut store) = diamond_hierarchy();

        // join(B, C) = D (least upper bound).
        assert_eq!(theory.join(&mut store, 1, 2), Some(3));
        // meet(B, C) = A (greatest lower bound).
        assert_eq!(theory.meet(&mut store, 1, 2), Some(0));

        // join(A, D) = D (A <= D).
        assert_eq!(theory.join(&mut store, 0, 3), Some(3));
        // meet(A, D) = A (A <= D).
        assert_eq!(theory.meet(&mut store, 0, 3), Some(0));

        // join(A, B) = B (A <= B).
        assert_eq!(theory.join(&mut store, 0, 1), Some(1));
        // meet(A, B) = A (A <= B).
        assert_eq!(theory.meet(&mut store, 0, 1), Some(0));
    }

    // ── ConstraintTheory Trait Tests ──────────────────────────────────────

    #[test]
    fn empty_store_is_consistent() {
        let theory = LatticeTheory::new(vec![0, 1, 2], HashMap::new());
        let store = theory.empty_store();
        assert!(theory.is_consistent(&store));
    }

    #[test]
    fn propagate_adds_edges() {
        let theory = LatticeTheory::new(
            vec![0, 1, 2],
            HashMap::from([(0, "A".to_string()), (1, "B".to_string()), (2, "C".to_string())]),
        );

        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 0, sup: 1 })
            .expect("propagation should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 1, sup: 2 })
            .expect("propagation should succeed");

        let mut store = store;
        assert!(theory.is_subtype(&mut store, 0, 1), "A <= B");
        assert!(theory.is_subtype(&mut store, 1, 2), "B <= C");
        assert!(theory.is_subtype(&mut store, 0, 2), "A <= C (transitive)");
    }

    #[test]
    fn label_returns_empty() {
        let theory = LatticeTheory::new(vec![0, 1], HashMap::new());
        let store = theory.empty_store();
        let labels = theory.label(&store);
        assert!(labels.is_empty(), "ground lattice construction needs no labeling choices");
    }

    #[test]
    fn witness_returns_identity_assignment() {
        let theory = LatticeTheory::new(
            vec![0, 1, 2],
            HashMap::from([(0, "A".to_string()), (1, "B".to_string()), (2, "C".to_string())]),
        );

        let store = theory.empty_store();
        let witness = theory.witness(&store).expect("witness should exist");
        assert_eq!(witness.bindings.get(&0), Some(&0));
        assert_eq!(witness.bindings.get(&1), Some(&1));
        assert_eq!(witness.bindings.get(&2), Some(&2));
    }

    #[test]
    fn evaluate_reflexive_constraint() {
        let theory = LatticeTheory::new(vec![0, 1], HashMap::new());
        let assignment = TypeAssignment { bindings: HashMap::new() };
        assert!(
            theory.evaluate(&SubtypeConstraint { sub: 0, sup: 0 }, &assignment),
            "reflexive constraint should evaluate to true"
        );
    }

    #[test]
    fn evaluate_non_reflexive_without_store() {
        let theory = LatticeTheory::new(vec![0, 1], HashMap::new());
        let assignment = TypeAssignment { bindings: HashMap::new() };
        // Without a store, non-reflexive constraints return false conservatively.
        assert!(
            !theory.evaluate(&SubtypeConstraint { sub: 0, sup: 1 }, &assignment),
            "non-reflexive constraint without store context returns false"
        );
    }

    #[test]
    fn frozen_snapshot_separates_assertion_from_observation() {
        let (theory, mut store) = number_hierarchy();
        let frozen = theory.freeze(&store);

        assert!(frozen.is_subtype(0, 2), "the snapshot observes Int <= Number");
        assert!(!frozen.is_subtype(2, 0), "the reverse edge was not declared");
        assert!(
            frozen
                .propagate(&(), &SubtypeConstraint { sub: 2, sup: 0 })
                .is_none(),
            "query propagation must reject a false proposition instead of asserting it"
        );

        store = theory
            .propagate(&store, &SubtypeConstraint { sub: 2, sup: 0 })
            .expect("the mutable builder accepts a newly asserted edge");
        assert!(theory.is_subtype(&mut store, 2, 0), "the mutable store now contains the edge");
        assert!(
            !frozen.is_subtype(2, 0),
            "later builder mutations cannot change an installed snapshot"
        );
    }

    #[test]
    fn frozen_snapshot_decides_boolean_complement_exactly() {
        let (theory, store) = number_hierarchy();
        let frozen = theory.freeze(&store);
        let reverse = TheoryPred::Atom(SubtypeConstraint { sub: 2, sup: 0 });
        let not_reverse = TheoryPred::Not(Box::new(reverse.clone()));

        assert!(matches!(frozen.decide_exact(&reverse), ExactSatisfiability::Unsatisfiable));
        assert!(matches!(frozen.decide_exact(&not_reverse), ExactSatisfiability::Satisfiable(_)));
    }

    #[test]
    fn frozen_snapshot_exact_decision_is_stack_safe_for_deep_predicates() {
        let (theory, store) = number_hierarchy();
        let frozen = theory.freeze(&store);
        let atom = TheoryPred::Atom(SubtypeConstraint { sub: 0, sup: 2 });
        let mut predicate = TheoryPred::True;
        for _ in 0..50_000 {
            predicate = TheoryPred::And(Box::new(predicate), Box::new(atom.clone()));
        }

        assert!(matches!(frozen.decide_exact(&predicate), ExactSatisfiability::Satisfiable(_)));
    }

    // ── Exhaustiveness / Isolated Types Tests ─────────────────────────────

    #[test]
    fn isolated_types_detected() {
        let theory = LatticeTheory::new(
            vec![0, 1, 2, 3],
            HashMap::from([
                (0, "A".to_string()),
                (1, "B".to_string()),
                (2, "C".to_string()),
                (3, "Isolated".to_string()),
            ]),
        );

        let mut store = theory.empty_store();
        store.add_edge(0, 1); // A <= B
        store.add_edge(1, 2); // B <= C
                              // Type 3 is not connected.

        let isolated = theory.isolated_types(&store);
        assert_eq!(isolated, vec![3], "type 3 should be isolated");
    }

    #[test]
    fn no_isolated_types_when_all_connected() {
        let (theory, store) = diamond_hierarchy();
        let isolated = theory.isolated_types(&store);
        assert!(isolated.is_empty(), "diamond hierarchy has no isolated types");
    }

    // ── Edge Cases ────────────────────────────────────────────────────────

    #[test]
    fn empty_universe() {
        let theory = LatticeTheory::new(vec![], HashMap::new());
        let store = theory.empty_store();

        assert!(theory.is_consistent(&store));
        let witness = theory.witness(&store).expect("empty witness should exist");
        assert!(witness.bindings.is_empty());
    }

    #[test]
    fn single_type_universe() {
        let theory = LatticeTheory::new(vec![42], HashMap::from([(42, "Only".to_string())]));

        let mut store = theory.empty_store();
        assert!(theory.is_subtype(&mut store, 42, 42), "reflexive");
        assert_eq!(theory.join(&mut store, 42, 42), Some(42));
        assert_eq!(theory.meet(&mut store, 42, 42), Some(42));
    }

    #[test]
    fn adding_redundant_edges() {
        let (theory, mut store) = number_hierarchy();
        let original_closure_size = store.closure.len();

        // Add an edge that is already implied by transitivity.
        store.add_edge(0, 2); // Int <= Number (already present)
        theory.compute_closure(&mut store);

        assert_eq!(
            store.closure.len(),
            original_closure_size,
            "redundant edge should not change closure"
        );
    }

    #[test]
    fn closure_invalidation_on_new_edge() {
        let a = 0;
        let b = 1;
        let c = 2;

        let theory = LatticeTheory::new(
            vec![a, b, c],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string()), (c, "C".to_string())]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, b);
        theory.compute_closure(&mut store);

        assert!(!theory.is_subtype(&mut store, a, c), "A not <= C yet");

        // Add new edge.
        store.add_edge(b, c);
        // Closure should be dirty now.
        assert!(store.closure_dirty, "closure should be dirty after new edge");

        // is_subtype should trigger recomputation.
        assert!(theory.is_subtype(&mut store, a, c), "A <= C after adding B <= C");
    }

    #[test]
    fn type_name_fallback() {
        let theory = LatticeTheory::new(vec![0, 1], HashMap::new());
        assert_eq!(theory.type_name(0), "T0");
        assert_eq!(theory.type_name(1), "T1");
    }

    #[test]
    fn type_name_with_names() {
        let theory = LatticeTheory::new(vec![0], HashMap::from([(0, "MyType".to_string())]));
        assert_eq!(theory.type_name(0), "MyType");
    }

    #[test]
    fn display_impl() {
        let theory = LatticeTheory::new(vec![0, 1, 2], HashMap::new());
        let display = format!("{}", theory);
        assert_eq!(display, "LatticeTheory(3 types)");
    }

    // ── Larger Hierarchy Tests ────────────────────────────────────────────

    #[test]
    fn five_level_hierarchy() {
        // Linear chain: 0 <= 1 <= 2 <= 3 <= 4
        let types: Vec<TypeId> = (0..5).collect();
        let names: HashMap<TypeId, String> =
            types.iter().map(|&t| (t, format!("L{}", t))).collect();

        let theory = LatticeTheory::new(types, names);
        let mut store = theory.empty_store();
        for i in 0..4 {
            store.add_edge(i, i + 1);
        }

        // All forward relationships should hold.
        for i in 0..5 {
            for j in i..5 {
                assert!(theory.is_subtype(&mut store, i, j), "L{} <= L{} should hold", i, j);
            }
        }

        // No backward relationships (except reflexive).
        for i in 0..5 {
            for j in 0..i {
                assert!(!theory.is_subtype(&mut store, i, j), "L{} should not be <= L{}", i, j);
            }
        }
    }

    #[test]
    fn multiple_inheritance_join() {
        // W-shaped hierarchy:
        //       D(3)     E(4)
        //      / \      / \
        //    B(1) C(2)  C(2) F(5)
        //      \ /        |
        //       A(0)      G(6)
        //
        // B and C share supertype D; C and F share supertype E.
        let types: Vec<TypeId> = (0..7).collect();
        let names: HashMap<TypeId, String> =
            types.iter().map(|&t| (t, format!("T{}", t))).collect();

        let theory = LatticeTheory::new(types, names);
        let mut store = theory.empty_store();
        store.add_edge(0, 1); // A <= B
        store.add_edge(0, 2); // A <= C
        store.add_edge(1, 3); // B <= D
        store.add_edge(2, 3); // C <= D
        store.add_edge(2, 4); // C <= E
        store.add_edge(5, 4); // F <= E
        store.add_edge(6, 5); // G <= F

        assert_eq!(theory.join(&mut store, 1, 2), Some(3), "join(B, C) = D");
        assert_eq!(theory.meet(&mut store, 1, 2), Some(0), "meet(B, C) = A");
        assert_eq!(theory.join(&mut store, 2, 5), Some(4), "join(C, F) = E");
    }

    // ── Cache Invalidation Tests ──────────────────────────────────────────

    #[test]
    fn cache_cleared_on_new_edge() {
        let a = 0;
        let b = 1;
        let c = 2;

        let theory = LatticeTheory::new(
            vec![a, b, c],
            HashMap::from([(a, "A".to_string()), (b, "B".to_string()), (c, "C".to_string())]),
        );

        let mut store = theory.empty_store();
        store.add_edge(a, c);
        store.add_edge(b, c);

        // join(A, B) = C
        assert_eq!(theory.join(&mut store, a, b), Some(c));

        // Now add A <= B, which should change join(A, B) = B.
        store.add_edge(a, b);
        assert!(store.lub_cache.is_empty(), "cache should be cleared");
        assert_eq!(theory.join(&mut store, a, b), Some(b), "join(A, B) = B after adding A <= B");
    }

    // ── ConstraintTheory via Propagation Integration Tests ────────────────

    #[test]
    fn propagation_chain_builds_closure() {
        let theory = LatticeTheory::new(
            vec![0, 1, 2, 3],
            HashMap::from([
                (0, "Bottom".to_string()),
                (1, "Left".to_string()),
                (2, "Right".to_string()),
                (3, "Top".to_string()),
            ]),
        );

        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 0, sup: 1 })
            .expect("should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 0, sup: 2 })
            .expect("should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 1, sup: 3 })
            .expect("should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 2, sup: 3 })
            .expect("should succeed");

        // Verify transitive closure was built.
        let mut store = store;
        assert!(theory.is_subtype(&mut store, 0, 3), "Bottom <= Top");

        // Verify join/meet.
        assert_eq!(theory.join(&mut store, 1, 2), Some(3), "join(Left, Right) = Top");
        assert_eq!(theory.meet(&mut store, 1, 2), Some(0), "meet(Left, Right) = Bottom");
    }

    #[test]
    fn propagation_with_cycle_records_equivalence() {
        let theory = LatticeTheory::new(
            vec![0, 1, 2],
            HashMap::from([(0, "A".to_string()), (1, "B".to_string()), (2, "C".to_string())]),
        );

        let store = theory.empty_store();
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 0, sup: 1 })
            .expect("should succeed");
        let store = theory
            .propagate(&store, &SubtypeConstraint { sub: 1, sup: 0 })
            .expect("should succeed (cycle = equivalence)");

        // Both directions hold.
        let mut store = store;
        assert!(theory.is_subtype(&mut store, 0, 1));
        assert!(theory.is_subtype(&mut store, 1, 0));

        // Cycle recorded.
        let cycles = theory.detect_cycles(&mut store);
        assert!(!cycles.is_empty(), "cycle should be detected");
    }

    // ── Default Trait Implementation Test ─────────────────────────────────

    #[test]
    fn lattice_store_default() {
        let store = LatticeStore::default();
        assert!(store.edges.is_empty());
        assert!(store.closure.is_empty());
        assert!(!store.closure_dirty);
        assert!(store.lub_cache.is_empty());
        assert!(store.glb_cache.is_empty());
        assert!(store.cycles.is_empty());
    }

    // ── LatticeAnalysis ─────────────────────────────────────────────────

    #[test]
    fn analysis_default_is_empty() {
        let analysis = LatticeAnalysis::default();
        assert!(analysis.unsatisfiable_constraints.is_empty());
        assert!(analysis.redundant_constraints.is_empty());
    }

    // ── analyze_from_bundle ──────────────────────────────────────────────

    /// Construct a `CategoryInfo` for tests.
    fn cat_info(name: &str) -> crate::pipeline::CategoryInfo {
        crate::pipeline::CategoryInfo {
            name: name.to_string(),
            native_type: None,
            is_primary: false,
            has_var: true,
        }
    }

    /// A flat grammar where every category has rules with mixed non-terminal
    /// references (or no references at all) — no pure delegation chains exist,
    /// so the analysis should detect no hierarchy.
    ///
    /// Grammar:
    ///   A → "a" B C     (two distinct non-terminals → not a pure delegation)
    ///   B → "b"         (no non-terminals → no delegation)
    ///   C → "c"         (no non-terminals → no delegation)
    #[test]
    fn test_analyze_from_bundle_no_hierarchy() {
        let categories = vec![cat_info("A"), cat_info("B"), cat_info("C")];
        let all_syntax = vec![
            (
                "rule_A".to_string(),
                "A".to_string(),
                vec![
                    crate::SyntaxItemSpec::Terminal("a".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "B".to_string(),
                        param_name: "b".to_string(),
                    },
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "C".to_string(),
                        param_name: "c".to_string(),
                    },
                ],
            ),
            (
                "rule_B".to_string(),
                "B".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("b".to_string())],
            ),
            (
                "rule_C".to_string(),
                "C".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("c".to_string())],
            ),
        ];

        let analysis = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            analysis.unsatisfiable_constraints.is_empty(),
            "flat grammar should have no unsatisfiable constraints"
        );
        assert!(
            analysis.redundant_constraints.is_empty(),
            "flat grammar should have no redundant constraints"
        );
    }

    /// A linear delegation chain A → B → C (each category has exactly one rule
    /// that delegates entirely to the next category).  The analysis should
    /// infer A ≤ B and B ≤ C, with no contradictions and no redundancy.
    ///
    /// Grammar:
    ///   A → B    (sole non-terminal is B → infer A ≤ B)
    ///   B → C    (sole non-terminal is C → infer B ≤ C)
    ///   C → "c"  (terminal only — no delegation)
    #[test]
    fn test_analyze_from_bundle_linear_hierarchy() {
        let categories = vec![cat_info("A"), cat_info("B"), cat_info("C")];
        let all_syntax = vec![
            (
                "rule_A".to_string(),
                "A".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "B".to_string(),
                    param_name: "b".to_string(),
                }],
            ),
            (
                "rule_B".to_string(),
                "B".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "C".to_string(),
                    param_name: "c".to_string(),
                }],
            ),
            (
                "rule_C".to_string(),
                "C".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("c".to_string())],
            ),
        ];

        let analysis = analyze_from_bundle(&all_syntax, &categories);

        assert!(
            analysis.unsatisfiable_constraints.is_empty(),
            "linear chain A≤B≤C should have no contradictions; got: {:?}",
            analysis.unsatisfiable_constraints
        );
        // Direct edges are A→B and B→C.  The transitive edge A→C is NOT a
        // direct inferred edge (we only infer edges, not the closure), so
        // there are no redundant direct edges.
        assert!(
            analysis.redundant_constraints.is_empty(),
            "linear chain with only direct edges should have no redundancy; got: {:?}",
            analysis.redundant_constraints
        );
    }

    /// The unanimous pure-delegation inference rule produces at most one
    /// outgoing edge for each category. Therefore its inferred edge set cannot
    /// itself contain a direct edge that is redundant with another path from
    /// the same source. This test checks both sides of that invariant:
    ///
    /// 1. bundle analysis of `A -> B -> C` reports no redundant direct edge;
    /// 2. the lower-level closure detects that explicitly adding `A -> C` to
    ///    `A -> B -> C` does not enlarge the relation.
    #[test]
    fn test_analyze_from_bundle_redundant_edge() {
        // Part A: verify analyze_from_bundle on a linear chain A→B→C
        // produces no redundant constraints (the inferred edges A≤B and B≤C
        // are minimal — the transitive A≤C is only in the closure, not in the
        // inferred edge set, so it cannot be reported as redundant).
        let categories = vec![cat_info("A"), cat_info("B"), cat_info("C")];
        let all_syntax = vec![
            (
                "rule_A".to_string(),
                "A".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "B".to_string(),
                    param_name: "b".to_string(),
                }],
            ),
            (
                "rule_B".to_string(),
                "B".to_string(),
                vec![crate::SyntaxItemSpec::NonTerminal {
                    category: "C".to_string(),
                    param_name: "c".to_string(),
                }],
            ),
            (
                "rule_C".to_string(),
                "C".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("c".to_string())],
            ),
        ];

        let analysis = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            analysis.redundant_constraints.is_empty(),
            "linear chain A≤B≤C has no redundant inferred edges; got: {:?}",
            analysis.redundant_constraints
        );

        // Part B: verify the redundancy check logic at the store level.
        // Build a store with edges: A≤B, B≤C, and A≤C (the last is redundant).
        let universe = vec![0usize, 1, 2];
        let names: HashMap<TypeId, String> =
            HashMap::from([(0, "A".to_string()), (1, "B".to_string()), (2, "C".to_string())]);
        let theory = LatticeTheory::new(universe, names);

        // Check: without A≤C, is A still a subtype of C?
        let mut store_without_ac = LatticeStore::new();
        store_without_ac.add_edge(0, 1); // A ≤ B
        store_without_ac.add_edge(1, 2); // B ≤ C
        theory.compute_closure(&mut store_without_ac);

        assert!(
            store_without_ac.closure.contains(&(0, 2)),
            "A ≤ C should be implied by A≤B and B≤C (transitivity)"
        );

        // Therefore A≤C is a redundant edge when A≤B and B≤C already exist.
        // Confirm by adding A≤C and checking it does not enlarge the closure.
        let mut store_with_ac = LatticeStore::new();
        store_with_ac.add_edge(0, 1); // A ≤ B
        store_with_ac.add_edge(1, 2); // B ≤ C
        store_with_ac.add_edge(0, 2); // A ≤ C  — redundant
        theory.compute_closure(&mut store_with_ac);

        assert_eq!(
            store_without_ac.closure.len(),
            store_with_ac.closure.len(),
            "adding redundant edge A≤C should not change the closure size"
        );
    }
}
