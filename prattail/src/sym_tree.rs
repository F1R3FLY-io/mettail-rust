//! Symbolic tree automata over ranked terms with **symbolic payload guards** —
//! the structural-recursion core that lifts symbolic *word* automata to
//! (recursive, algebraic) *tree* data.
//!
//! A [`SymTerm<D>`] is a ranked term: a constructor, an optional scalar payload
//! `D`, and child subterms. A [`SymbolicTreeAutomaton<A>`] is a **bottom-up**
//! automaton whose transitions
//! `(constructor, payload_guard: Option<A::Predicate>, child_states) → target`
//! fire at a node when the constructor and child states match and the node's
//! payload satisfies the guard (an effective-Boolean-algebra predicate, so the
//! payload alphabet may be infinite). This generalizes the finite-alphabet tree
//! automaton in `type_system.rs` to symbolic payloads.
//!
//! This module (M1.6a) provides the automaton with `run`/`accepts`/`is_empty`/
//! `witness`/`intersect`/`union`. Determinization + complement and the
//! `TreeAlgebra` Boolean-algebra wrapper are added in M1.6b.

use std::collections::{HashMap, HashSet};

use crate::symbolic::BooleanAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// SymTerm
// ══════════════════════════════════════════════════════════════════════════════

/// A ranked term with an optional scalar payload of type `D`.
///
/// Structural constructors (e.g. `Cons`, `Pair`) carry `payload = None`; scalar
/// leaf constructors (e.g. an integer literal `Lit`) carry `payload = Some(d)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymTerm<D> {
    /// The head constructor.
    pub constructor: String,
    /// An optional scalar payload (for leaf scalar constructors).
    pub payload: Option<D>,
    /// Child subterms.
    pub children: Vec<SymTerm<D>>,
}

impl<D> SymTerm<D> {
    /// A structural node `c(children)` with no payload.
    pub fn node(constructor: impl Into<String>, children: Vec<SymTerm<D>>) -> Self {
        SymTerm { constructor: constructor.into(), payload: None, children }
    }

    /// A scalar leaf `c[payload]`.
    pub fn leaf(constructor: impl Into<String>, payload: D) -> Self {
        SymTerm { constructor: constructor.into(), payload: Some(payload), children: Vec::new() }
    }

    /// A nullary structural constant `c`.
    pub fn constant(constructor: impl Into<String>) -> Self {
        SymTerm { constructor: constructor.into(), payload: None, children: Vec::new() }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// SymbolicTreeAutomaton
// ══════════════════════════════════════════════════════════════════════════════

/// A bottom-up transition: at a node with this `constructor`, whose children are
/// in `child_states` and whose payload satisfies `payload_guard`, move to
/// `target`. `payload_guard = None` matches a payload-less (structural) node;
/// `Some(g)` matches a scalar node whose payload satisfies `g`.
#[derive(Clone, Debug)]
pub struct TreeTrans<P> {
    /// Head constructor.
    pub constructor: String,
    /// Payload guard (`None` for structural constructors).
    pub payload_guard: Option<P>,
    /// Required state for each child (length = arity).
    pub child_states: Vec<usize>,
    /// Resulting state.
    pub target: usize,
}

/// A bottom-up symbolic tree automaton over element algebra `A`.
#[derive(Clone, Debug)]
pub struct SymbolicTreeAutomaton<A: BooleanAlgebra> {
    /// The element (payload) algebra.
    pub algebra: A,
    /// Number of states (ids `0..num_states`).
    pub num_states: usize,
    /// Transitions.
    pub transitions: Vec<TreeTrans<A::Predicate>>,
    /// Accepting (root) states.
    pub accepting: HashSet<usize>,
    /// Ranked alphabet: constructor → arity.
    pub arities: HashMap<String, usize>,
}

impl<A: BooleanAlgebra> SymbolicTreeAutomaton<A> {
    /// An empty automaton over the given algebra.
    pub fn new(algebra: A) -> Self {
        SymbolicTreeAutomaton {
            algebra,
            num_states: 0,
            transitions: Vec::new(),
            accepting: HashSet::new(),
            arities: HashMap::new(),
        }
    }

    /// Add a state, returning its id.
    pub fn add_state(&mut self) -> usize {
        let id = self.num_states;
        self.num_states += 1;
        id
    }

    /// Mark a state accepting.
    pub fn set_accepting(&mut self, state: usize) {
        self.accepting.insert(state);
    }

    /// Register a constructor's arity in the ranked alphabet.
    pub fn register(&mut self, constructor: impl Into<String>, arity: usize) {
        self.arities.insert(constructor.into(), arity);
    }

    /// Add a transition.
    pub fn add_transition(&mut self, trans: TreeTrans<A::Predicate>) {
        self.transitions.push(trans);
    }

    /// Whether a transition's payload guard accepts the node's payload.
    fn payload_matches(&self, guard: &Option<A::Predicate>, payload: &Option<A::Domain>) -> bool {
        match (guard, payload) {
            (None, None) => true,
            (Some(g), Some(v)) => self.algebra.evaluate(g, v),
            _ => false,
        }
    }

    /// Whether a transition's payload guard is satisfiable (for emptiness).
    fn guard_satisfiable(&self, guard: &Option<A::Predicate>) -> bool {
        match guard {
            None => true,
            Some(g) => self.algebra.is_satisfiable(g),
        }
    }

    /// Bottom-up: the set of states the automaton can reach at the root of `term`.
    pub fn run(&self, term: &SymTerm<A::Domain>) -> HashSet<usize> {
        let child_state_sets: Vec<HashSet<usize>> =
            term.children.iter().map(|c| self.run(c)).collect();
        let mut reached = HashSet::new();
        for trans in &self.transitions {
            if trans.constructor != term.constructor
                || trans.child_states.len() != term.children.len()
            {
                continue;
            }
            if !self.payload_matches(&trans.payload_guard, &term.payload) {
                continue;
            }
            let children_ok = trans
                .child_states
                .iter()
                .zip(&child_state_sets)
                .all(|(q, set)| set.contains(q));
            if children_ok {
                reached.insert(trans.target);
            }
        }
        reached
    }

    /// Whether `term` is accepted (some reachable root state is accepting).
    pub fn accepts(&self, term: &SymTerm<A::Domain>) -> bool {
        self.run(term).iter().any(|s| self.accepting.contains(s))
    }

    /// The set of *productive* states (a satisfiable derivation exists), via a
    /// bottom-up fixpoint.
    fn productive_states(&self) -> HashSet<usize> {
        let mut productive = HashSet::new();
        loop {
            let mut changed = false;
            for trans in &self.transitions {
                if productive.contains(&trans.target) {
                    continue;
                }
                if self.guard_satisfiable(&trans.payload_guard)
                    && trans.child_states.iter().all(|q| productive.contains(q))
                {
                    productive.insert(trans.target);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        productive
    }

    /// Whether the automaton's language is empty.
    pub fn is_empty(&self) -> bool {
        let productive = self.productive_states();
        !self.accepting.iter().any(|s| productive.contains(s))
    }

    /// A minimal accepted term, or `None` if the language is empty.
    pub fn witness(&self) -> Option<SymTerm<A::Domain>> {
        // Bottom-up: assign each state a smallest witness term.
        let mut wit: HashMap<usize, SymTerm<A::Domain>> = HashMap::new();
        loop {
            let mut changed = false;
            for trans in &self.transitions {
                if wit.contains_key(&trans.target) {
                    continue;
                }
                if !self.guard_satisfiable(&trans.payload_guard) {
                    continue;
                }
                if !trans.child_states.iter().all(|q| wit.contains_key(q)) {
                    continue;
                }
                let payload = match &trans.payload_guard {
                    None => None,
                    Some(g) => Some(self.algebra.witness(g)?),
                };
                let children: Vec<SymTerm<A::Domain>> =
                    trans.child_states.iter().map(|q| wit[q].clone()).collect();
                wit.insert(
                    trans.target,
                    SymTerm { constructor: trans.constructor.clone(), payload, children },
                );
                changed = true;
            }
            if !changed {
                break;
            }
        }
        self.accepting.iter().filter_map(|s| wit.get(s)).cloned().min_by_key(term_size)
    }

    /// Disjoint union: accepts `L(self) ∪ L(other)`.
    pub fn union(&self, other: &Self) -> Self {
        let off = self.num_states;
        let mut result = self.clone();
        result.num_states = self.num_states + other.num_states;
        for trans in &other.transitions {
            result.transitions.push(TreeTrans {
                constructor: trans.constructor.clone(),
                payload_guard: trans.payload_guard.clone(),
                child_states: trans.child_states.iter().map(|q| q + off).collect(),
                target: trans.target + off,
            });
        }
        for &acc in &other.accepting {
            result.accepting.insert(acc + off);
        }
        for (c, a) in &other.arities {
            result.arities.insert(c.clone(), *a);
        }
        result
    }

    /// Product construction: accepts `L(self) ∩ L(other)`.
    pub fn intersect(&self, other: &Self) -> Self {
        let mut result = SymbolicTreeAutomaton::new(self.algebra.clone());
        for (c, a) in &self.arities {
            result.arities.insert(c.clone(), *a);
        }
        for (c, a) in &other.arities {
            result.arities.insert(c.clone(), *a);
        }
        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();
        let mut get_state = |sa: usize, sb: usize, result: &mut Self| -> usize {
            *state_map.entry((sa, sb)).or_insert_with(|| {
                let id = result.num_states;
                result.num_states += 1;
                id
            })
        };
        for ta in &self.transitions {
            for tb in &other.transitions {
                if ta.constructor != tb.constructor
                    || ta.child_states.len() != tb.child_states.len()
                {
                    continue;
                }
                let guard = match (&ta.payload_guard, &tb.payload_guard) {
                    (None, None) => None,
                    (Some(ga), Some(gb)) => {
                        let g = self.algebra.and(ga, gb);
                        if !self.algebra.is_satisfiable(&g) {
                            continue;
                        }
                        Some(g)
                    },
                    _ => continue, // incompatible payload-ness
                };
                let child_states: Vec<usize> = ta
                    .child_states
                    .iter()
                    .zip(&tb.child_states)
                    .map(|(&a, &b)| get_state(a, b, &mut result))
                    .collect();
                let target = get_state(ta.target, tb.target, &mut result);
                result.transitions.push(TreeTrans {
                    constructor: ta.constructor.clone(),
                    payload_guard: guard,
                    child_states,
                    target,
                });
            }
        }
        for (&(sa, sb), &id) in &state_map {
            if self.accepting.contains(&sa) && other.accepting.contains(&sb) {
                result.accepting.insert(id);
            }
        }
        result
    }
}

fn term_size<D>(t: &SymTerm<D>) -> usize {
    1 + t.children.iter().map(term_size).sum::<usize>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    // A tiny term language: Lit[int] (scalar leaf) and Pair(a, b) (binary).
    fn lit(n: i64) -> SymTerm<i64> {
        SymTerm::leaf("Lit", n)
    }
    fn pair(a: SymTerm<i64>, b: SymTerm<i64>) -> SymTerm<i64> {
        SymTerm::node("Pair", vec![a, b])
    }

    /// Automaton: accepts Pair(Lit in [0,10), Lit in [0,10)).
    fn small_pair_automaton() -> SymbolicTreeAutomaton<IntervalAlgebra> {
        let mut a = SymbolicTreeAutomaton::new(IntervalAlgebra::new(0, 100));
        a.register("Lit", 0);
        a.register("Pair", 2);
        let q_lit = a.add_state(); // a small Lit
        let q_pair = a.add_state(); // a Pair of small Lits
        a.set_accepting(q_pair);
        a.add_transition(TreeTrans {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(0, 10)),
            child_states: vec![],
            target: q_lit,
        });
        a.add_transition(TreeTrans {
            constructor: "Pair".to_string(),
            payload_guard: None,
            child_states: vec![q_lit, q_lit],
            target: q_pair,
        });
        a
    }

    #[test]
    fn run_and_accepts() {
        let a = small_pair_automaton();
        assert!(a.accepts(&pair(lit(3), lit(7))));
        assert!(!a.accepts(&pair(lit(3), lit(50)))); // second lit too big
        assert!(!a.accepts(&lit(3))); // not a Pair at the root
        assert!(!a.accepts(&pair(lit(50), lit(3))));
    }

    #[test]
    fn emptiness_and_witness() {
        let a = small_pair_automaton();
        assert!(!a.is_empty());
        let w = a.witness().expect("nonempty");
        assert!(a.accepts(&w));
        assert_eq!(w.constructor, "Pair");

        // Make the Lit guard unsatisfiable → empty.
        let mut b = SymbolicTreeAutomaton::new(IntervalAlgebra::new(0, 100));
        b.register("Lit", 0);
        b.register("Pair", 2);
        let q_lit = b.add_state();
        let q_pair = b.add_state();
        b.set_accepting(q_pair);
        b.add_transition(TreeTrans {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(50, 50)), // empty range
            child_states: vec![],
            target: q_lit,
        });
        b.add_transition(TreeTrans {
            constructor: "Pair".to_string(),
            payload_guard: None,
            child_states: vec![q_lit, q_lit],
            target: q_pair,
        });
        assert!(b.is_empty());
        assert!(b.witness().is_none());
    }

    #[test]
    fn intersect_narrows() {
        // A: Pair(Lit[0,10), Lit[0,10)); B: Pair(Lit[5,100), Lit[5,100)).
        let a = small_pair_automaton();
        let mut b = SymbolicTreeAutomaton::new(IntervalAlgebra::new(0, 100));
        b.register("Lit", 0);
        b.register("Pair", 2);
        let q_lit = b.add_state();
        let q_pair = b.add_state();
        b.set_accepting(q_pair);
        b.add_transition(TreeTrans {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(5, 100)),
            child_states: vec![],
            target: q_lit,
        });
        b.add_transition(TreeTrans {
            constructor: "Pair".to_string(),
            payload_guard: None,
            child_states: vec![q_lit, q_lit],
            target: q_pair,
        });
        let inter = a.intersect(&b);
        // Intersection: both lits in [5,10).
        assert!(inter.accepts(&pair(lit(7), lit(8))));
        assert!(!inter.accepts(&pair(lit(3), lit(8)))); // 3 not in [5,10)
        assert!(!inter.accepts(&pair(lit(7), lit(50)))); // 50 not in [0,10)
        assert!(!inter.is_empty());
        assert!(inter.accepts(&inter.witness().unwrap()));
    }

    #[test]
    fn union_widens() {
        // A accepts small pairs; C accepts a bare Lit[90,100).
        let a = small_pair_automaton();
        let mut c = SymbolicTreeAutomaton::new(IntervalAlgebra::new(0, 100));
        c.register("Lit", 0);
        c.register("Pair", 2);
        let q = c.add_state();
        c.set_accepting(q);
        c.add_transition(TreeTrans {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(90, 100)),
            child_states: vec![],
            target: q,
        });
        let u = a.union(&c);
        assert!(u.accepts(&pair(lit(3), lit(4)))); // from A
        assert!(u.accepts(&lit(95))); // from C
        assert!(!u.accepts(&lit(50))); // neither
    }
}
