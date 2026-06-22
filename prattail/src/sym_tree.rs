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
        SymTerm {
            constructor: constructor.into(),
            payload: None,
            children,
        }
    }

    /// A scalar leaf `c[payload]`.
    pub fn leaf(constructor: impl Into<String>, payload: D) -> Self {
        SymTerm {
            constructor: constructor.into(),
            payload: Some(payload),
            children: Vec::new(),
        }
    }

    /// A nullary structural constant `c`.
    pub fn constant(constructor: impl Into<String>) -> Self {
        SymTerm {
            constructor: constructor.into(),
            payload: None,
            children: Vec::new(),
        }
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
                    SymTerm {
                        constructor: trans.constructor.clone(),
                        payload,
                        children,
                    },
                );
                changed = true;
            }
            if !changed {
                break;
            }
        }
        self.accepting
            .iter()
            .filter_map(|s| wit.get(s))
            .cloned()
            .min_by_key(term_size)
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

/// All `n^k` index tuples (k-fold cartesian product of `0..n`).
fn index_tuples(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = vec![Vec::new()];
    for _ in 0..k {
        let mut next = Vec::with_capacity(out.len() * n);
        for prefix in &out {
            for i in 0..n {
                let mut t = prefix.clone();
                t.push(i);
                next.push(t);
            }
        }
        out = next;
    }
    out
}

/// Cartesian product of per-slot choice lists.
fn cartesian(slots: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut out = vec![Vec::new()];
    for slot in slots {
        let mut next = Vec::new();
        for prefix in &out {
            for &choice in slot {
                let mut t = prefix.clone();
                t.push(choice);
                next.push(t);
            }
        }
        out = next;
    }
    out
}

// ══════════════════════════════════════════════════════════════════════════════
// Determinization + complement (symbolic bottom-up subset construction)
// ══════════════════════════════════════════════════════════════════════════════

impl<A: BooleanAlgebra> SymbolicTreeAutomaton<A> {
    /// Per-constructor payload minterms: `None` (a single structural "minterm")
    /// for payload-less constructors, or the satisfiable minterms of the
    /// constructor's payload guards for scalar constructors.
    fn constructor_minterms(&self) -> HashMap<String, Vec<Option<A::Predicate>>> {
        let mut map = HashMap::new();
        for c in self.arities.keys() {
            let trans_c: Vec<&TreeTrans<A::Predicate>> = self
                .transitions
                .iter()
                .filter(|t| &t.constructor == c)
                .collect();
            let scalar = trans_c.iter().any(|t| t.payload_guard.is_some());
            let mts = if scalar {
                let guards: Vec<A::Predicate> = trans_c
                    .iter()
                    .filter_map(|t| t.payload_guard.clone())
                    .collect();
                crate::collection_algebra::minterms(&self.algebra, &guards)
                    .into_iter()
                    .map(Some)
                    .collect()
            } else {
                vec![None]
            };
            map.insert(c.clone(), mts);
        }
        map
    }

    /// The determinized target state (set of original states) for a constructor
    /// `c` under payload minterm `m` and determinized child-state sets.
    fn det_target(
        &self,
        c: &str,
        m: &Option<A::Predicate>,
        child_dets: &[&std::collections::BTreeSet<usize>],
    ) -> std::collections::BTreeSet<usize> {
        let mut target = std::collections::BTreeSet::new();
        for t in &self.transitions {
            if t.constructor != c || t.child_states.len() != child_dets.len() {
                continue;
            }
            let compat = match (m, &t.payload_guard) {
                (None, None) => true,
                (Some(mm), Some(g)) => self.algebra.is_satisfiable(&self.algebra.and(mm, g)),
                _ => false,
            };
            if !compat {
                continue;
            }
            if t.child_states
                .iter()
                .zip(child_dets)
                .all(|(q, d)| d.contains(q))
            {
                target.insert(t.target);
            }
        }
        target
    }

    /// Determinize bottom-up (subset construction over payload minterms); if
    /// `complement` is set, the accepting set is flipped (det-states that do NOT
    /// meet an original accepting state).
    fn determinize_with(&self, complement: bool) -> Self {
        use std::collections::{BTreeSet, HashSet as Set};
        let ctor_minterms = self.constructor_minterms();

        // Phase 1 — discover all reachable determinized states (∅ = sink).
        let mut discovered: Vec<BTreeSet<usize>> = vec![BTreeSet::new()];
        let mut seen: Set<BTreeSet<usize>> = Set::new();
        seen.insert(BTreeSet::new());
        loop {
            let snapshot = discovered.clone();
            let before = discovered.len();
            for (c, &k) in &self.arities {
                let mts = &ctor_minterms[c];
                for tup in index_tuples(snapshot.len(), k) {
                    let child_dets: Vec<&BTreeSet<usize>> =
                        tup.iter().map(|&i| &snapshot[i]).collect();
                    for m in mts {
                        let target = self.det_target(c, m, &child_dets);
                        if seen.insert(target.clone()) {
                            discovered.push(target);
                        }
                    }
                }
            }
            if discovered.len() == before {
                break;
            }
        }

        // Phase 2 — build the deterministic, complete automaton.
        let id_of: HashMap<BTreeSet<usize>, usize> = discovered
            .iter()
            .enumerate()
            .map(|(i, d)| (d.clone(), i))
            .collect();
        let mut result = SymbolicTreeAutomaton::new(self.algebra.clone());
        result.num_states = discovered.len();
        result.arities = self.arities.clone();
        for (c, &k) in &self.arities {
            let mts = &ctor_minterms[c];
            for tup in index_tuples(discovered.len(), k) {
                let child_dets: Vec<&BTreeSet<usize>> =
                    tup.iter().map(|&i| &discovered[i]).collect();
                for m in mts {
                    let target = self.det_target(c, m, &child_dets);
                    let tid = id_of[&target];
                    result.transitions.push(TreeTrans {
                        constructor: c.clone(),
                        payload_guard: m.clone(),
                        child_states: tup.clone(),
                        target: tid,
                    });
                }
            }
        }
        for (d, &id) in &id_of {
            let intersects = d.iter().any(|s| self.accepting.contains(s));
            if intersects != complement {
                result.accepting.insert(id);
            }
        }
        result
    }

    /// A deterministic, complete automaton accepting the same language.
    pub fn determinize(&self) -> Self {
        self.determinize_with(false)
    }

    /// The complement automaton (accepts exactly the well-formed terms over this
    /// alphabet that `self` rejects).
    pub fn complement(&self) -> Self {
        self.determinize_with(true)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TreeAlgebra — effective Boolean algebra of symbolic tree patterns
// ══════════════════════════════════════════════════════════════════════════════

/// A symbolic tree predicate over element-predicate type `P`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TreePred<P> {
    /// Matches every well-formed term.
    True,
    /// Matches no term.
    False,
    /// Matches any subtree (a pattern variable / wildcard).
    Wild,
    /// Matches `constructor(children...)` whose payload satisfies `payload_guard`
    /// (`None` = structural) and whose children match the child patterns.
    Node {
        constructor: String,
        payload_guard: Option<P>,
        children: Vec<TreePred<P>>,
    },
    /// Conjunction.
    And(Box<TreePred<P>>, Box<TreePred<P>>),
    /// Disjunction.
    Or(Box<TreePred<P>>, Box<TreePred<P>>),
    /// Negation (relative to the ranked-alphabet universe).
    Not(Box<TreePred<P>>),
}

/// The effective Boolean algebra of symbolic tree predicates over a ranked
/// alphabet, with scalar payloads decided by an element algebra `A`.
#[derive(Clone, Debug)]
pub struct TreeAlgebra<A: BooleanAlgebra> {
    /// The element (payload) algebra.
    pub elem: A,
    /// Ranked alphabet: constructor → arity.
    pub arities: HashMap<String, usize>,
    /// Constructors that carry a scalar payload.
    pub payloaded: HashSet<String>,
}

impl<A: BooleanAlgebra> TreeAlgebra<A> {
    /// Construct a tree algebra over the given alphabet.
    pub fn new(elem: A, arities: HashMap<String, usize>, payloaded: HashSet<String>) -> Self {
        TreeAlgebra { elem, arities, payloaded }
    }

    /// The universal automaton accepting every well-formed term.
    fn universal(&self) -> SymbolicTreeAutomaton<A> {
        let mut a = SymbolicTreeAutomaton::new(self.elem.clone());
        a.arities = self.arities.clone();
        let u = a.add_state();
        a.set_accepting(u);
        for (c, &k) in &self.arities {
            let pg = if self.payloaded.contains(c) {
                Some(self.elem.true_pred())
            } else {
                None
            };
            a.add_transition(TreeTrans {
                constructor: c.clone(),
                payload_guard: pg,
                child_states: vec![u; k],
                target: u,
            });
        }
        a
    }

    /// The empty automaton (one non-accepting state).
    fn empty_automaton(&self) -> SymbolicTreeAutomaton<A> {
        let mut a = SymbolicTreeAutomaton::new(self.elem.clone());
        a.arities = self.arities.clone();
        a.add_state();
        a
    }

    /// Compile a node pattern into an automaton accepting
    /// `constructor(children...)` matching the child patterns.
    fn compile_node(
        &self,
        constructor: &str,
        payload_guard: &Option<A::Predicate>,
        children: &[TreePred<A::Predicate>],
    ) -> SymbolicTreeAutomaton<A> {
        let child_autos: Vec<SymbolicTreeAutomaton<A>> =
            children.iter().map(|ch| self.compile(ch)).collect();
        let mut result = SymbolicTreeAutomaton::new(self.elem.clone());
        result.arities = self.arities.clone();
        let mut child_accepts: Vec<Vec<usize>> = Vec::with_capacity(child_autos.len());
        for ca in &child_autos {
            for (cc, &aa) in &ca.arities {
                result.arities.insert(cc.clone(), aa);
            }
            let base = result.num_states;
            result.num_states += ca.num_states;
            for t in &ca.transitions {
                result.transitions.push(TreeTrans {
                    constructor: t.constructor.clone(),
                    payload_guard: t.payload_guard.clone(),
                    child_states: t.child_states.iter().map(|q| q + base).collect(),
                    target: t.target + base,
                });
            }
            child_accepts.push(ca.accepting.iter().map(|&q| q + base).collect());
        }
        let q = result.num_states;
        result.num_states += 1;
        result.set_accepting(q);
        for combo in cartesian(&child_accepts) {
            result.add_transition(TreeTrans {
                constructor: constructor.to_string(),
                payload_guard: payload_guard.clone(),
                child_states: combo,
                target: q,
            });
        }
        result
    }

    /// Compile a tree predicate into a symbolic tree automaton over this
    /// algebra's ranked alphabet.
    ///
    /// This is the public entry point the structural-type recognizer
    /// (`crate::structural_types`) uses to turn a parsed refinement pattern
    /// ([`TreePred`]) into a [`SymbolicTreeAutomaton`] so it can be intersected /
    /// complemented against a category automaton (`is_empty` then deciding
    /// disjointness / subtype). A `Wild` (or `True`) leaf compiles to the
    /// universal automaton over the alphabet, so intersecting a pattern automaton
    /// with a category automaton restricts a `Wild` slot to exactly the
    /// well-formed terms of that slot's category.
    pub fn pattern_to_automaton(&self, p: &TreePred<A::Predicate>) -> SymbolicTreeAutomaton<A> {
        self.compile(p)
    }

    /// Compile a tree predicate into a symbolic tree automaton.
    fn compile(&self, p: &TreePred<A::Predicate>) -> SymbolicTreeAutomaton<A> {
        match p {
            TreePred::True | TreePred::Wild => self.universal(),
            TreePred::False => self.empty_automaton(),
            TreePred::Node { constructor, payload_guard, children } => {
                self.compile_node(constructor, payload_guard, children)
            },
            TreePred::And(a, b) => self.compile(a).intersect(&self.compile(b)),
            TreePred::Or(a, b) => self.compile(a).union(&self.compile(b)),
            TreePred::Not(x) => self.compile(x).complement(),
        }
    }
}

impl<A: BooleanAlgebra> BooleanAlgebra for TreeAlgebra<A> {
    type Predicate = TreePred<A::Predicate>;
    type Domain = SymTerm<A::Domain>;

    fn true_pred(&self) -> Self::Predicate {
        TreePred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        TreePred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (TreePred::False, _) | (_, TreePred::False) => TreePred::False,
            (TreePred::True, x) | (x, TreePred::True) => x.clone(),
            _ => TreePred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (TreePred::True, _) | (_, TreePred::True) => TreePred::True,
            (TreePred::False, x) | (x, TreePred::False) => x.clone(),
            _ => TreePred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        TreePred::Not(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        !self.compile(a).is_empty()
    }

    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        self.compile(a).witness()
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        self.compile(pred).accepts(elem)
    }
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

#[cfg(test)]
mod tree_algebra_tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    fn lit(n: i64) -> SymTerm<i64> {
        SymTerm::leaf("Lit", n)
    }
    fn pair(a: SymTerm<i64>, b: SymTerm<i64>) -> SymTerm<i64> {
        SymTerm::node("Pair", vec![a, b])
    }

    // Term language: Lit[int] (scalar) and Pair(a, b).
    fn tree_alg() -> TreeAlgebra<IntervalAlgebra> {
        let arities: HashMap<String, usize> =
            [("Lit".to_string(), 0usize), ("Pair".to_string(), 2usize)]
                .into_iter()
                .collect();
        let payloaded: HashSet<String> = ["Lit".to_string()].into_iter().collect();
        TreeAlgebra::new(IntervalAlgebra::new(0, 100), arities, payloaded)
    }

    fn small_lit() -> TreePred<IntervalPred> {
        TreePred::Node {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(0, 10)),
            children: vec![],
        }
    }

    #[test]
    fn node_pattern_match() {
        let alg = tree_alg();
        let p = small_lit();
        assert!(alg.evaluate(&p, &lit(5)));
        assert!(!alg.evaluate(&p, &lit(50)));
        assert!(!alg.evaluate(&p, &pair(lit(1), lit(2))));
        assert!(alg.is_satisfiable(&p));
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
    }

    #[test]
    fn nested_pattern_with_wildcard() {
        let alg = tree_alg();
        // Pair(small Lit, anything)
        let p = TreePred::Node {
            constructor: "Pair".to_string(),
            payload_guard: None,
            children: vec![small_lit(), TreePred::Wild],
        };
        assert!(alg.evaluate(&p, &pair(lit(3), lit(99))));
        assert!(alg.evaluate(&p, &pair(lit(3), pair(lit(1), lit(2)))));
        assert!(!alg.evaluate(&p, &pair(lit(50), lit(1)))); // first not small
        assert!(!alg.evaluate(&p, &lit(3))); // not a Pair
        assert!(alg.is_satisfiable(&p));
        assert!(alg.evaluate(&p, &alg.witness(&p).unwrap()));
    }

    #[test]
    fn complement_over_alphabet() {
        let alg = tree_alg();
        let not_small_lit = alg.not(&small_lit());
        // A big Lit and any Pair are in the complement; a small Lit is not.
        assert!(!alg.evaluate(&not_small_lit, &lit(5)));
        assert!(alg.evaluate(&not_small_lit, &lit(50)));
        assert!(alg.evaluate(&not_small_lit, &pair(lit(1), lit(2))));
        assert!(alg.is_satisfiable(&not_small_lit));
        // Double negation ≡ original (semantically): a∧¬a unsat, ¬¬a accepts a.
        assert!(!alg.is_satisfiable(&alg.and(&small_lit(), &not_small_lit)));
        let dn = alg.not(&not_small_lit);
        assert!(alg.evaluate(&dn, &lit(5)));
        assert!(!alg.evaluate(&dn, &lit(50)));
    }

    #[test]
    fn and_or_combinations() {
        let alg = tree_alg();
        // Lit in [0,10) AND Lit in [5,100) = Lit in [5,10)
        let mid = alg.and(
            &small_lit(),
            &TreePred::Node {
                constructor: "Lit".to_string(),
                payload_guard: Some(IntervalPred::Range(5, 100)),
                children: vec![],
            },
        );
        assert!(alg.evaluate(&mid, &lit(7)));
        assert!(!alg.evaluate(&mid, &lit(3)));
        assert!(!alg.evaluate(&mid, &lit(50)));

        // small Lit OR any Pair
        let either = alg.or(
            &small_lit(),
            &TreePred::Node {
                constructor: "Pair".to_string(),
                payload_guard: None,
                children: vec![TreePred::Wild, TreePred::Wild],
            },
        );
        assert!(alg.evaluate(&either, &lit(3)));
        assert!(alg.evaluate(&either, &pair(lit(50), lit(50))));
        assert!(!alg.evaluate(&either, &lit(50)));
    }

    #[test]
    fn top_and_bottom() {
        let alg = tree_alg();
        assert!(alg.is_satisfiable(&alg.true_pred()));
        assert!(!alg.is_satisfiable(&alg.false_pred()));
        assert!(alg.evaluate(&alg.true_pred(), &pair(lit(1), lit(2))));
        // ¬True = False over the alphabet.
        assert!(!alg.is_satisfiable(&alg.not(&alg.true_pred())));
        // ¬False = True.
        assert!(alg.is_satisfiable(&alg.not(&alg.false_pred())));
    }
}
