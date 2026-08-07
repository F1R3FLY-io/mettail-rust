use super::*;

// ==============================================================================
// SetTheoreticTypeSystem (Sprint RT3)
// ==============================================================================

/// A set-theoretic type: union/intersection/negation over named base types.
///
/// Types are modeled as sets of values. Union (∪), intersection (∩), and
/// negation (¬) correspond to set operations. Subtyping is set inclusion:
/// `S <: T` iff every value of type S is also of type T.
///
/// For a term algebra with finitely many constructors, these sets form regular
/// tree languages. `SetTheoreticTypeSystem` uses `TreeAutomaton<BooleanWeight>`
/// to decide subtyping via language inclusion: `S <: T` iff `L(S) ∩ L(¬T) = ∅`.
///
/// References:
/// - Frisch, Castagna, & Benzaken (2008). "Semantic subtyping." JACM 55(4).
/// - Comon et al. (2007). "Tree Automata Techniques and Applications."
pub enum SetType {
    /// Named base type (atom, corresponds to a tree automaton state).
    Atom(String),
    /// Union: S ∪ T — values that are in S or T (or both).
    Union(Box<SetType>, Box<SetType>),
    /// Intersection: S ∩ T — values that are in both S and T.
    Intersection(Box<SetType>, Box<SetType>),
    /// Negation: ¬S — values that are NOT in S.
    Negation(Box<SetType>),
    /// Arrow type: S → T (function types). Covariant in T, contravariant in S.
    Arrow(Box<SetType>, Box<SetType>),
    /// Top type (all values).
    Top,
    /// Bottom type (no values / empty type).
    Bottom,
}

#[path = "settheoretic/set_type_lifecycle.rs"]
mod set_type_lifecycle;

#[cfg(test)]
#[path = "../../tests/support/settheoretic_complement_recursive_oracle.rs"]
mod complement_recursive_oracle;

/// Type environment for the set-theoretic type system.
#[derive(Clone, Debug)]
pub struct SetTypeEnv {
    /// Variable-to-type bindings.
    pub bindings: HashMap<String, SetType>,
}

/// Set-theoretic type system using tree automata for subtyping decisions.
///
/// Types are modeled as regular tree languages over a ranked alphabet of
/// constructors. Subtyping is decided by tree automaton language inclusion:
/// `S <: T` iff `L(A_S) ⊆ L(A_T)` iff `L(A_S ∩ ¬A_T) = ∅`.
///
/// All operations are **compile-time only** — they execute during `language!`
/// macro expansion to verify type relationships and emit lints. No tree
/// automata appear in the generated binary.
#[derive(Clone, Debug)]
pub struct SetTheoreticTypeSystem {
    /// Constructors with their arities (defines the term algebra).
    pub constructors: HashMap<String, usize>,
    /// Named type definitions: type name → tree automaton accepting the type's values.
    pub type_defs: HashMap<
        String,
        crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    >,
}

impl SetTheoreticTypeSystem {
    /// Create a new set-theoretic type system with the given constructors.
    pub fn new(constructors: HashMap<String, usize>) -> Self {
        SetTheoreticTypeSystem { constructors, type_defs: HashMap::new() }
    }

    /// Register a named type definition backed by a tree automaton.
    pub fn define_type(
        &mut self,
        name: impl Into<String>,
        automaton: crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) {
        self.type_defs.insert(name.into(), automaton);
    }

    /// Build a tree automaton for the given `SetType`.
    ///
    /// Each `SetType` variant maps to tree automaton operations:
    /// - `Atom(name)` → look up the named type's automaton (or build a single-state one)
    /// - `Union(a, b)` → union of automata (combined accepting states)
    /// - `Intersection(a, b)` → product construction
    /// - `Negation(a)` → complement (requires determinization; we use the
    ///   bottom-up completeness property of our automata)
    /// - `Top` → universal automaton (accepts all terms)
    /// - `Bottom` → empty automaton (rejects all terms)
    pub fn type_to_automaton(
        &self,
        ty: &SetType,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::tree_automaton::TreeAutomaton;

        enum Task<'ty> {
            Visit(&'ty SetType),
            Union,
            Intersection,
            Negation,
        }

        let mut tasks = vec![Task::Visit(ty)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SetType::Atom(name)) => values.push(
                    self.type_defs
                        .get(name)
                        .cloned()
                        .unwrap_or_else(TreeAutomaton::new),
                ),
                Task::Visit(SetType::Union(left, right)) => {
                    tasks.push(Task::Union);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SetType::Intersection(left, right)) => {
                    tasks.push(Task::Intersection);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SetType::Negation(inner)) => {
                    tasks.push(Task::Negation);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(SetType::Arrow(_, _)) => values.push(
                    self.type_defs
                        .get("__arrow")
                        .cloned()
                        .unwrap_or_else(TreeAutomaton::new),
                ),
                Task::Visit(SetType::Top) => values.push(self.universal_automaton()),
                Task::Visit(SetType::Bottom) => values.push(TreeAutomaton::new()),
                Task::Union | Task::Intersection => {
                    let right = values
                        .pop()
                        .expect("set-type automaton PDA lost its right operand");
                    let left = values
                        .pop()
                        .expect("set-type automaton PDA lost its left operand");
                    values.push(match task {
                        Task::Union => self.union_automata(&left, &right),
                        Task::Intersection => self.intersect_automata(&left, &right),
                        Task::Visit(_) | Task::Negation => unreachable!(),
                    });
                },
                Task::Negation => {
                    let inner = values
                        .pop()
                        .expect("set-type automaton PDA lost its negated operand");
                    values.push(self.complement_automaton(&inner));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("set-type automaton PDA produced no value")
    }

    fn universal_automaton(
        &self,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        let mut automaton = TreeAutomaton::new();
        let state = automaton.add_state(true);
        for (symbol, &arity) in &self.constructors {
            automaton.add_transition(TreeTransition {
                symbol: symbol.clone(),
                child_states: vec![state; arity],
                target_state: state,
                weight: BooleanWeight(true),
            });
        }
        automaton
    }

    /// Product construction for tree automata intersection.
    ///
    /// States in the product are pairs `(q_a, q_b)`. A product state is
    /// accepting iff both component states are accepting.
    ///
    /// Transition: `f((q_a1, q_b1), ..., (q_an, q_bn)) → (q_a, q_b)` exists
    /// iff `f(q_a1, ..., q_an) → q_a` in A and `f(q_b1, ..., q_bn) → q_b` in B.
    pub fn intersect_automata(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
        b: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        let na = a.num_states();
        let nb = b.num_states();
        if na == 0 || nb == 0 {
            return TreeAutomaton::new();
        }

        let mut product = TreeAutomaton::new();
        // State mapping: (qa, qb) → qa * nb + qb
        let pair_id = |qa: usize, qb: usize| -> usize { qa * nb + qb };

        // Create product states
        for qa in 0..na {
            for qb in 0..nb {
                let is_final = a.final_states.contains(&qa) && b.final_states.contains(&qb);
                let id = product.add_state(is_final);
                debug_assert_eq!(id, pair_id(qa, qb));
            }
        }

        // Create product transitions
        // For each symbol, collect transitions from A and B, then form products
        let mut a_by_sym: HashMap<&str, Vec<&TreeTransition<BooleanWeight>>> = HashMap::new();
        for t in &a.transitions {
            a_by_sym.entry(&t.symbol).or_default().push(t);
        }
        let mut b_by_sym: HashMap<&str, Vec<&TreeTransition<BooleanWeight>>> = HashMap::new();
        for t in &b.transitions {
            b_by_sym.entry(&t.symbol).or_default().push(t);
        }

        for (sym, a_trans) in &a_by_sym {
            let Some(b_trans) = b_by_sym.get(sym) else {
                continue;
            };
            for ta in a_trans {
                for tb in b_trans {
                    if ta.child_states.len() != tb.child_states.len() {
                        continue;
                    }
                    let product_children: Vec<usize> = ta
                        .child_states
                        .iter()
                        .zip(tb.child_states.iter())
                        .map(|(&qa, &qb)| pair_id(qa, qb))
                        .collect();
                    let product_target = pair_id(ta.target_state, tb.target_state);
                    let product_weight = BooleanWeight(ta.weight.0 && tb.weight.0);
                    product.add_transition(TreeTransition {
                        symbol: sym.to_string(),
                        child_states: product_children,
                        target_state: product_target,
                        weight: product_weight,
                    });
                }
            }
        }

        product
    }

    /// Union construction for tree automata.
    ///
    /// Creates a disjoint union of two automata. States are renumbered:
    /// A's states keep their IDs, B's states are offset by `|A.states|`.
    /// A state is accepting if it's accepting in either component.
    pub fn union_automata(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
        b: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        let mut result = TreeAutomaton::new();
        let offset = a.num_states();

        // Add A's states
        for state in &a.states {
            result.add_state(state.is_final);
        }
        // Add B's states (offset)
        for state in &b.states {
            result.add_state(state.is_final);
        }

        // Add A's transitions (no renumbering needed)
        for t in &a.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.clone(),
                target_state: t.target_state,
                weight: t.weight,
            });
        }
        // Add B's transitions (offset state IDs)
        for t in &b.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.iter().map(|&s| s + offset).collect(),
                target_state: t.target_state + offset,
                weight: t.weight,
            });
        }

        result
    }

    /// Complement construction for tree automata (bottom-up).
    ///
    /// For bottom-up tree automata, complementation requires:
    /// 1. The automaton must be **complete** (every symbol/state combination
    ///    has at least one transition — add a sink state if needed)
    /// 2. The automaton must be **deterministic** (at most one transition for
    ///    each symbol/state combination)
    /// 3. Swap accepting and non-accepting states
    ///
    /// Since our type automata are generally small (tens of states), we use
    /// a straightforward approach: complete the automaton, then swap finals.
    pub fn complement_automaton(
        &self,
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight> {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::{TreeAutomaton, TreeTransition};

        // Special case: empty automaton → universal automaton
        if a.num_states() == 0 {
            return self.universal_automaton();
        }

        let mut result = TreeAutomaton::new();
        let n = a.num_states();

        // Copy states, swapping accepting status
        for state in &a.states {
            result.add_state(!state.is_final);
        }

        // Add a sink state (non-accepting in the original → accepting in complement)
        let sink = result.add_state(true);

        // Copy existing transitions
        for t in &a.transitions {
            result.add_transition(TreeTransition {
                symbol: t.symbol.clone(),
                child_states: t.child_states.clone(),
                target_state: t.target_state,
                weight: t.weight,
            });
        }

        // Complete the automaton: for every constructor and state combination
        // that has no transition, add a transition to the sink state.
        // This is needed for correct complementation.
        let mut existing: HashSet<(String, Vec<usize>)> = HashSet::new();
        for t in &a.transitions {
            existing.insert((t.symbol.clone(), t.child_states.clone()));
        }

        for (sym, &arity) in &self.constructors {
            if arity == 0 {
                // Leaf constructor: check if there's a transition for it
                let key = (sym.clone(), vec![]);
                if !existing.contains(&key) {
                    result.add_transition(TreeTransition {
                        symbol: sym.clone(),
                        child_states: vec![],
                        target_state: sink,
                        weight: BooleanWeight(true),
                    });
                }
            } else {
                // For non-leaf constructors, add sink transitions for state
                // combinations that don't have transitions. We iterate over
                // all state combinations (including the sink state).
                // For small automata this is tractable; for large ones we'd
                // need a lazier approach.
                let all_states: Vec<usize> = (0..=n).collect(); // 0..n original + sink
                Self::enumerate_missing_transitions(
                    &existing,
                    sym,
                    arity,
                    &all_states,
                    sink,
                    &mut result,
                );
            }
        }

        result
    }

    /// Add transitions to `sink` for state combinations missing from `existing`.
    ///
    /// For tractability, we only enumerate combinations up to a reasonable limit.
    /// For type automata with ~tens of states and constructors with arity ≤ 3,
    /// this is practical.
    fn enumerate_missing_transitions(
        existing: &HashSet<(String, Vec<usize>)>,
        symbol: &str,
        arity: usize,
        states: &[usize],
        sink: usize,
        result: &mut crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) {
        use crate::automata::semiring::BooleanWeight;
        use crate::tree_automaton::TreeTransition;

        // For arity 1-3, enumerate explicitly
        match arity {
            1 => {
                for &q in states {
                    let key = (symbol.to_string(), vec![q]);
                    if !existing.contains(&key) {
                        result.add_transition(TreeTransition {
                            symbol: symbol.to_string(),
                            child_states: vec![q],
                            target_state: sink,
                            weight: BooleanWeight(true),
                        });
                    }
                }
            },
            2 => {
                for &q1 in states {
                    for &q2 in states {
                        let key = (symbol.to_string(), vec![q1, q2]);
                        if !existing.contains(&key) {
                            result.add_transition(TreeTransition {
                                symbol: symbol.to_string(),
                                child_states: vec![q1, q2],
                                target_state: sink,
                                weight: BooleanWeight(true),
                            });
                        }
                    }
                }
            },
            3 => {
                for &q1 in states {
                    for &q2 in states {
                        for &q3 in states {
                            let key = (symbol.to_string(), vec![q1, q2, q3]);
                            if !existing.contains(&key) {
                                result.add_transition(TreeTransition {
                                    symbol: symbol.to_string(),
                                    child_states: vec![q1, q2, q3],
                                    target_state: sink,
                                    weight: BooleanWeight(true),
                                });
                            }
                        }
                    }
                }
            },
            _ => {
                // For higher arities, only add the all-sink combination as a fallback.
                // Full enumeration would be |states|^arity which is infeasible.
                let key = (symbol.to_string(), vec![sink; arity]);
                if !existing.contains(&key) {
                    result.add_transition(TreeTransition {
                        symbol: symbol.to_string(),
                        child_states: vec![sink; arity],
                        target_state: sink,
                        weight: BooleanWeight(true),
                    });
                }
            },
        }
    }

    /// Check if a tree automaton's language is empty (no term is accepted).
    ///
    /// Uses bottom-up reachability: iteratively compute which states are
    /// reachable (have at least one term that reaches them). A state is
    /// reachable if there exists a transition `f(q1, ..., qn) → q` where
    /// all child states q1...qn are reachable (or n=0 for leaf transitions).
    ///
    /// The language is empty iff no accepting state is reachable.
    pub fn is_empty(
        a: &crate::tree_automaton::TreeAutomaton<crate::automata::semiring::BooleanWeight>,
    ) -> bool {
        if a.num_states() == 0 {
            return true;
        }
        if a.final_states.is_empty() {
            return true;
        }

        let mut reachable: HashSet<usize> = HashSet::new();
        let mut changed = true;

        while changed {
            changed = false;
            for t in &a.transitions {
                if !t.weight.0 {
                    continue; // zero-weight transitions don't count
                }
                if reachable.contains(&t.target_state) {
                    continue; // already reached
                }
                // Check if all children are reachable
                let all_children_reachable =
                    t.child_states.iter().all(|child| reachable.contains(child));
                if all_children_reachable {
                    reachable.insert(t.target_state);
                    changed = true;
                }
            }
        }

        // Empty iff no final state is reachable
        !a.final_states.iter().any(|f| reachable.contains(f))
    }
}

impl TypeSystem for SetTheoreticTypeSystem {
    type Type = SetType;
    type TypeEnv = SetTypeEnv;
    type Term = crate::tree_automaton::Term;

    fn empty_env(&self) -> Self::TypeEnv {
        SetTypeEnv { bindings: HashMap::new() }
    }

    fn check(
        &self,
        // SetTheoreticTypeSystem determines membership structurally via
        // tree-automaton acceptance, not via variable bindings — env is
        // unused. The trait signature retains the env param for other
        // impls (LatticeTypeSystem, RefinementTypeSystem) that do consult it.
        _env: &Self::TypeEnv,
        term: &Self::Term,
        ty: &Self::Type,
    ) -> bool {
        // Bottom-up evaluate the term through the type's automaton.
        // The term has type `ty` if it reaches an accepting state.
        let aut = self.type_to_automaton(ty);
        let state_map = crate::tree_automaton::bottom_up_evaluate(&aut, term);
        state_map
            .iter()
            .any(|(state, weight)| aut.final_states.contains(state) && weight.0)
    }

    fn infer(
        &self,
        // env unused — same reasoning as `check` above.
        _env: &Self::TypeEnv,
        term: &Self::Term,
    ) -> Vec<Self::Type> {
        // Check the term against each named type definition
        let mut result = Vec::new();
        for (name, aut) in &self.type_defs {
            let state_map = crate::tree_automaton::bottom_up_evaluate(aut, term);
            let accepted = state_map
                .iter()
                .any(|(state, weight)| aut.final_states.contains(state) && weight.0);
            if accepted {
                result.push(SetType::Atom(name.clone()));
            }
        }
        result
    }

    fn is_subtype(&self, _env: &Self::TypeEnv, sub: &Self::Type, sup: &Self::Type) -> bool {
        // S <: T iff L(S) ⊆ L(T) iff L(S) ∩ L(¬T) = ∅
        let aut_sub = self.type_to_automaton(sub);
        let aut_not_sup = self.type_to_automaton(&SetType::Negation(Box::new(sup.clone())));
        let intersection = self.intersect_automata(&aut_sub, &aut_not_sup);
        Self::is_empty(&intersection)
    }

    fn join(&self, _env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        // Join = union type
        Some(SetType::Union(Box::new(a.clone()), Box::new(b.clone())))
    }

    fn meet(&self, _env: &Self::TypeEnv, a: &Self::Type, b: &Self::Type) -> Option<Self::Type> {
        // Meet = intersection type
        Some(SetType::Intersection(Box::new(a.clone()), Box::new(b.clone())))
    }

    fn extend(&self, env: &Self::TypeEnv, var: &str, ty: &Self::Type) -> Self::TypeEnv {
        let mut bindings = env.bindings.clone();
        bindings.insert(var.to_string(), ty.clone());
        SetTypeEnv { bindings }
    }

    fn is_inhabited(&self, _env: &Self::TypeEnv, ty: &Self::Type) -> bool {
        let aut = self.type_to_automaton(ty);
        !Self::is_empty(&aut)
    }

    fn top(&self) -> Option<Self::Type> {
        Some(SetType::Top)
    }

    fn bottom(&self) -> Option<Self::Type> {
        Some(SetType::Bottom)
    }
}
