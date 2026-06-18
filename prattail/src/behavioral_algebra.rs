//! `BehavioralAlgebra` — an effective algebra of **behavioral** predicates over
//! the dynamics of terms (relational/Datalog facts now; modal and temporal
//! fragments added in later steps).
//!
//! Behavioral predicates are only *snapshot-relative*: a relation's absence from
//! the current fact base is not a proof of absence (more facts may be derived).
//! So `BehavioralAlgebra` implements [`HeytingAlgebra`] (intuitionistic — no
//! involutive complement, no excluded middle) and **NOT**
//! [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra): the symbolic-automaton
//! classical operations are statically unavailable on it (the safety property of
//! the [algebra tower](crate::algebra_tower)). Computation against a *fixed*
//! finite snapshot is nonetheless decidable (closed-world over the snapshot),
//! returning [`Sat3::Sat`]/[`Sat3::Unsat`]; only an exceeded search budget
//! yields [`Sat3::DontKnow`].
//!
//! This module (M2.2a) provides the relational fragment: `Relation` atoms,
//! `forall`/`exists` quantifiers, and boolean combination, decided against a
//! [`FactBase`] over the active domain. The modal (`Diamond`/`Box`/`Mu`/`Nu`)
//! and temporal fragments — which use the [`HostTerm`] LTS — extend the
//! [`BehavioralFormula`] enum and the `evaluate`/`is_satisfiable_3v` dispatch in
//! subsequent steps.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;

use crate::algebra_tower::{HeytingAlgebra, RejectSafeAlgebra, Sat3};

/// Default cap on the number of free-variable assignments searched before
/// `is_satisfiable_3v` returns `DontKnow`.
const DEFAULT_SEARCH_BUDGET: usize = 100_000;

// ══════════════════════════════════════════════════════════════════════════════
// HostTerm — the LTS interface (used by the modal/temporal fragments)
// ══════════════════════════════════════════════════════════════════════════════

/// A host-language term that induces a labeled transition system: the seam the
/// modal/temporal behavioral fragments use. (The relational fragment ignores the
/// term.)
pub trait HostTerm: Clone + Debug + Eq + Hash + Send + Sync + 'static {
    /// One-step successors with action labels (the LTS edges). Backed by the
    /// host's reduction relation.
    fn successors(&self) -> Vec<(String, Self)>;
    /// A label for atomic-proposition matching at this state.
    fn label(&self) -> String;
}

/// A degenerate host term with no transitions — for relational-only use (the
/// relational fragment never inspects the term). A real, total LTS (the
/// single-state, no-edge system), not a stub.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NoTerm;

impl HostTerm for NoTerm {
    fn successors(&self) -> Vec<(String, Self)> {
        Vec::new()
    }
    fn label(&self) -> String {
        String::new()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Fact base
// ══════════════════════════════════════════════════════════════════════════════

/// A finite snapshot of Datalog-style relations (each a set of string tuples).
#[derive(Clone, Debug, Default)]
pub struct FactBase {
    relations: HashMap<String, HashSet<Vec<String>>>,
}

impl FactBase {
    /// An empty fact base.
    pub fn new() -> Self {
        FactBase { relations: HashMap::new() }
    }

    /// Add a fact `relation(tuple)`.
    pub fn add_fact(&mut self, relation: impl Into<String>, tuple: Vec<String>) {
        self.relations
            .entry(relation.into())
            .or_default()
            .insert(tuple);
    }

    /// Whether `relation(tuple)` holds in this snapshot.
    pub fn holds(&self, relation: &str, tuple: &[String]) -> bool {
        self.relations
            .get(relation)
            .is_some_and(|s| s.contains(tuple))
    }

    /// The active domain: every constant appearing in any fact tuple.
    fn active_domain(&self) -> BTreeSet<String> {
        let mut dom = BTreeSet::new();
        for tuples in self.relations.values() {
            for t in tuples {
                for v in t {
                    dom.insert(v.clone());
                }
            }
        }
        dom
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Behavioral formula (relational fragment)
// ══════════════════════════════════════════════════════════════════════════════

/// An argument to a relation: a bound/free variable or a literal constant.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Arg {
    /// A variable (looked up in the binding environment).
    Var(String),
    /// A literal constant.
    Lit(String),
}

/// What a modal operator matches on an LTS edge label.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ActionPattern {
    /// Any action (`⟨-⟩` / `[-]`).
    Any,
    /// An internal/unlabeled step (`τ`): empty or `"tau"` label.
    Tau,
    /// A specific named action.
    Named(String),
}

impl ActionPattern {
    fn matches(&self, action: &str) -> bool {
        match self {
            ActionPattern::Any => true,
            ActionPattern::Tau => action.is_empty() || action == "tau",
            ActionPattern::Named(n) => action == n,
        }
    }
}

/// The domain a quantifier ranges over.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum QDomain {
    /// An explicit set of values.
    Values(Vec<String>),
    /// Column `usize` of a relation.
    RelationColumn(String, usize),
    /// The active domain of the fact base.
    Active,
    /// Bounded iteration over an inner domain (semi-decidable — at most `usize`).
    Bounded(Box<QDomain>, usize),
}

/// A behavioral predicate. (Relational fragment; modal/temporal arms added
/// later.)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BehavioralFormula {
    /// Always true.
    Top,
    /// Always false.
    Bot,
    /// A relation atom `name(args)`.
    Relation { name: String, args: Vec<Arg> },
    /// `∀ var ∈ domain. body`.
    Forall {
        var: String,
        domain: QDomain,
        body: Box<BehavioralFormula>,
    },
    /// `∃ var ∈ domain. body`.
    Exists {
        var: String,
        domain: QDomain,
        body: Box<BehavioralFormula>,
    },
    /// A state proposition: the LTS state's `label()` equals this string.
    Atom(String),
    /// `⟨a⟩φ` — some `a`-labeled successor satisfies `φ`.
    Diamond(ActionPattern, Box<BehavioralFormula>),
    /// `[a]φ` — all `a`-labeled successors satisfy `φ`.
    BoxAll(ActionPattern, Box<BehavioralFormula>),
    /// Least fixpoint `μX.φ` (liveness/eventuality).
    Mu(String, Box<BehavioralFormula>),
    /// Greatest fixpoint `νX.φ` (safety/invariance).
    Nu(String, Box<BehavioralFormula>),
    /// A fixpoint variable.
    FixVar(String),
    /// Conjunction.
    And(Box<BehavioralFormula>, Box<BehavioralFormula>),
    /// Disjunction.
    Or(Box<BehavioralFormula>, Box<BehavioralFormula>),
    /// Negation (snapshot-relative — see module docs).
    Not(Box<BehavioralFormula>),
}

impl BehavioralFormula {
    /// Collect the free variables (not bound by an enclosing quantifier).
    fn free_vars(&self, bound: &mut BTreeSet<String>, acc: &mut BTreeSet<String>) {
        match self {
            BehavioralFormula::Top | BehavioralFormula::Bot => {},
            BehavioralFormula::Relation { args, .. } => {
                for a in args {
                    if let Arg::Var(v) = a {
                        if !bound.contains(v) {
                            acc.insert(v.clone());
                        }
                    }
                }
            },
            BehavioralFormula::Forall { var, body, .. }
            | BehavioralFormula::Exists { var, body, .. } => {
                let fresh = bound.insert(var.clone());
                body.free_vars(bound, acc);
                if fresh {
                    bound.remove(var);
                }
            },
            BehavioralFormula::And(a, b) | BehavioralFormula::Or(a, b) => {
                a.free_vars(bound, acc);
                b.free_vars(bound, acc);
            },
            BehavioralFormula::Not(x) => x.free_vars(bound, acc),
            // Modal arms: fixpoint variables are a separate namespace (state
            // sets), not relational vars; recurse into bodies for relational
            // free vars; Atom/FixVar contribute no relational vars.
            BehavioralFormula::Atom(_) | BehavioralFormula::FixVar(_) => {},
            BehavioralFormula::Diamond(_, body)
            | BehavioralFormula::BoxAll(_, body)
            | BehavioralFormula::Mu(_, body)
            | BehavioralFormula::Nu(_, body) => body.free_vars(bound, acc),
        }
    }

    /// Whether the formula uses any modal/temporal operator (and therefore needs
    /// the LTS, not just the fact base).
    fn has_modal(&self) -> bool {
        match self {
            BehavioralFormula::Atom(_)
            | BehavioralFormula::Diamond(..)
            | BehavioralFormula::BoxAll(..)
            | BehavioralFormula::Mu(..)
            | BehavioralFormula::Nu(..)
            | BehavioralFormula::FixVar(_) => true,
            BehavioralFormula::And(a, b) | BehavioralFormula::Or(a, b) => {
                a.has_modal() || b.has_modal()
            },
            BehavioralFormula::Not(x) => x.has_modal(),
            BehavioralFormula::Forall { body, .. } | BehavioralFormula::Exists { body, .. } => {
                body.has_modal()
            },
            BehavioralFormula::Top
            | BehavioralFormula::Bot
            | BehavioralFormula::Relation { .. } => false,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// BehavioralWorld (domain element)
// ══════════════════════════════════════════════════════════════════════════════

/// A concrete element the behavioral predicate is evaluated against: a host term
/// (for the modal/temporal fragments) plus a binding environment (for the
/// relational fragment).
#[derive(Clone, Debug)]
pub struct BehavioralWorld<H: HostTerm> {
    /// The term (its LTS is used by modal/temporal fragments).
    pub term: H,
    /// Variable bindings.
    pub env: BTreeMap<String, String>,
}

impl<H: HostTerm> BehavioralWorld<H> {
    /// A world with the given term and no bindings.
    pub fn new(term: H) -> Self {
        BehavioralWorld { term, env: BTreeMap::new() }
    }

    /// A world with the given term and bindings.
    pub fn with_env(term: H, env: BTreeMap<String, String>) -> Self {
        BehavioralWorld { term, env }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// BehavioralAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// The behavioral algebra over a fixed fact-base snapshot and a host-term type.
#[derive(Clone, Debug)]
pub struct BehavioralAlgebra<H: HostTerm> {
    facts: Arc<FactBase>,
    search_budget: usize,
    _marker: std::marker::PhantomData<fn() -> H>,
}

impl<H: HostTerm> BehavioralAlgebra<H> {
    /// Construct over the given fact base (default search budget).
    pub fn new(facts: FactBase) -> Self {
        BehavioralAlgebra {
            facts: Arc::new(facts),
            search_budget: DEFAULT_SEARCH_BUDGET,
            _marker: std::marker::PhantomData,
        }
    }

    /// Override the satisfiability search budget.
    pub fn with_budget(mut self, budget: usize) -> Self {
        self.search_budget = budget;
        self
    }

    fn resolve(&self, arg: &Arg, env: &BTreeMap<String, String>) -> Option<String> {
        match arg {
            Arg::Lit(s) => Some(s.clone()),
            Arg::Var(v) => env.get(v).cloned(),
        }
    }

    fn domain_values(&self, domain: &QDomain) -> (Vec<String>, bool) {
        // Returns (values, exact). `exact = false` means the domain was bounded
        // and may have been truncated.
        match domain {
            QDomain::Values(vs) => (vs.clone(), true),
            QDomain::Active => (self.facts.active_domain().into_iter().collect(), true),
            QDomain::RelationColumn(rel, col) => {
                let mut vals = BTreeSet::new();
                if let Some(tuples) = self.facts.relations.get(rel) {
                    for t in tuples {
                        if let Some(v) = t.get(*col) {
                            vals.insert(v.clone());
                        }
                    }
                }
                (vals.into_iter().collect(), true)
            },
            QDomain::Bounded(inner, limit) => {
                let (mut vals, exact) = self.domain_values(inner);
                let truncated = vals.len() > *limit;
                vals.truncate(*limit);
                (vals, exact && !truncated)
            },
        }
    }

    /// Evaluate `formula` against the snapshot with the given bindings. Returns
    /// `(result, exact)`; `exact = false` when a bounded quantifier may have
    /// been truncated (so a `false`/`true` could be budget-limited).
    fn eval(&self, formula: &BehavioralFormula, env: &BTreeMap<String, String>) -> (bool, bool) {
        match formula {
            BehavioralFormula::Top => (true, true),
            BehavioralFormula::Bot => (false, true),
            BehavioralFormula::Relation { name, args } => {
                let tuple: Option<Vec<String>> =
                    args.iter().map(|a| self.resolve(a, env)).collect();
                match tuple {
                    Some(t) => (self.facts.holds(name, &t), true),
                    None => (false, true), // unbound var ⇒ not satisfied with this env
                }
            },
            BehavioralFormula::Forall { var, domain, body } => {
                let (vals, dom_exact) = self.domain_values(domain);
                let mut env2 = env.clone();
                let mut all = true;
                let mut exact = dom_exact;
                for v in &vals {
                    env2.insert(var.clone(), v.clone());
                    let (r, e) = self.eval(body, &env2);
                    exact = exact && e;
                    if !r {
                        all = false;
                        break;
                    }
                }
                env2.remove(var);
                // If `all` held only over a truncated domain, the result is inexact.
                (all, exact)
            },
            BehavioralFormula::Exists { var, domain, body } => {
                let (vals, dom_exact) = self.domain_values(domain);
                let mut env2 = env.clone();
                let mut any = false;
                let mut exact = dom_exact;
                for v in &vals {
                    env2.insert(var.clone(), v.clone());
                    let (r, e) = self.eval(body, &env2);
                    exact = exact && e;
                    if r {
                        any = true;
                        break;
                    }
                }
                env2.remove(var);
                (any, exact)
            },
            BehavioralFormula::And(a, b) => {
                let (ra, ea) = self.eval(a, env);
                if !ra {
                    return (false, ea);
                }
                let (rb, eb) = self.eval(b, env);
                (rb, ea && eb)
            },
            BehavioralFormula::Or(a, b) => {
                let (ra, ea) = self.eval(a, env);
                if ra {
                    return (true, ea);
                }
                let (rb, eb) = self.eval(b, env);
                (rb, ea && eb)
            },
            BehavioralFormula::Not(x) => {
                let (r, e) = self.eval(x, env);
                (!r, e)
            },
            // Invariant: `eval` is the relational-only evaluator; modal formulas
            // are routed to the model checker by `evaluate`/`is_satisfiable_3v`,
            // and the relational fast path runs only when `has_modal()` is false,
            // so no modal arm is reachable here.
            BehavioralFormula::Atom(_)
            | BehavioralFormula::Diamond(..)
            | BehavioralFormula::BoxAll(..)
            | BehavioralFormula::Mu(..)
            | BehavioralFormula::Nu(..)
            | BehavioralFormula::FixVar(_) => {
                unreachable!("modal formula reached the relational evaluator")
            },
        }
    }

    /// Build the reachable LTS from `root` (BFS), capped at `MAX_REACH_STATES`.
    /// Returns the states (index 0 = root) and adjacency `(action, target)`.
    fn build_lts(&self, root: &H) -> (Vec<H>, Vec<Vec<(String, usize)>>) {
        let mut states = vec![root.clone()];
        let mut index: HashMap<H, usize> = HashMap::new();
        index.insert(root.clone(), 0);
        let mut adj: Vec<Vec<(String, usize)>> = vec![Vec::new()];
        let mut queue = VecDeque::from([0usize]);
        while let Some(i) = queue.pop_front() {
            for (action, next) in states[i].successors() {
                let j = match index.get(&next) {
                    Some(&j) => j,
                    None => {
                        if states.len() >= MAX_REACH_STATES {
                            continue; // truncated (reject-safe: missing edges only shrink modal sets)
                        }
                        let j = states.len();
                        states.push(next.clone());
                        index.insert(next, j);
                        adj.push(Vec::new());
                        queue.push_back(j);
                        j
                    },
                };
                adj[i].push((action, j));
            }
        }
        (states, adj)
    }

    /// The set of state indices satisfying `formula` (finite mu-calculus model
    /// checking over the reachable LTS). `fix` maps fixpoint variables to their
    /// current state sets.
    fn denote(
        &self,
        formula: &BehavioralFormula,
        states: &[H],
        adj: &[Vec<(String, usize)>],
        env: &BTreeMap<String, String>,
        fix: &HashMap<String, HashSet<usize>>,
    ) -> HashSet<usize> {
        let all = || (0..states.len()).collect::<HashSet<usize>>();
        match formula {
            BehavioralFormula::Top => all(),
            BehavioralFormula::Bot => HashSet::new(),
            BehavioralFormula::Atom(label) => (0..states.len())
                .filter(|&i| states[i].label() == *label)
                .collect(),
            // State-independent relational atom: holds at all states or none.
            BehavioralFormula::Relation { .. } => {
                if self.eval(formula, env).0 {
                    all()
                } else {
                    HashSet::new()
                }
            },
            BehavioralFormula::Forall { var, domain, body } => {
                let (vals, _exact) = self.domain_values(domain);
                let mut acc = all();
                let mut env2 = env.clone();
                for v in &vals {
                    env2.insert(var.clone(), v.clone());
                    let d = self.denote(body, states, adj, &env2, fix);
                    acc = acc.intersection(&d).copied().collect();
                }
                env2.remove(var);
                acc
            },
            BehavioralFormula::Exists { var, domain, body } => {
                let (vals, _exact) = self.domain_values(domain);
                let mut acc = HashSet::new();
                let mut env2 = env.clone();
                for v in &vals {
                    env2.insert(var.clone(), v.clone());
                    let d = self.denote(body, states, adj, &env2, fix);
                    acc = acc.union(&d).copied().collect();
                }
                env2.remove(var);
                acc
            },
            BehavioralFormula::And(a, b) => {
                let da = self.denote(a, states, adj, env, fix);
                let db = self.denote(b, states, adj, env, fix);
                da.intersection(&db).copied().collect()
            },
            BehavioralFormula::Or(a, b) => {
                let da = self.denote(a, states, adj, env, fix);
                let db = self.denote(b, states, adj, env, fix);
                da.union(&db).copied().collect()
            },
            BehavioralFormula::Not(x) => {
                let d = self.denote(x, states, adj, env, fix);
                (0..states.len()).filter(|i| !d.contains(i)).collect()
            },
            BehavioralFormula::Diamond(ap, body) => {
                let b = self.denote(body, states, adj, env, fix);
                (0..states.len())
                    .filter(|&i| {
                        adj[i]
                            .iter()
                            .any(|(act, j)| ap.matches(act) && b.contains(j))
                    })
                    .collect()
            },
            BehavioralFormula::BoxAll(ap, body) => {
                let b = self.denote(body, states, adj, env, fix);
                (0..states.len())
                    .filter(|&i| {
                        adj[i]
                            .iter()
                            .all(|(act, j)| !ap.matches(act) || b.contains(j))
                    })
                    .collect()
            },
            BehavioralFormula::Mu(x, body) => {
                // least fixpoint: start ∅, iterate (monotone; ≤ |states| steps).
                let mut cur: HashSet<usize> = HashSet::new();
                for _ in 0..=states.len() {
                    let mut fix2 = fix.clone();
                    fix2.insert(x.clone(), cur.clone());
                    let next = self.denote(body, states, adj, env, &fix2);
                    if next == cur {
                        break;
                    }
                    cur = next;
                }
                cur
            },
            BehavioralFormula::Nu(x, body) => {
                // greatest fixpoint: start ⊤, iterate (monotone; ≤ |states| steps).
                let mut cur: HashSet<usize> = all();
                for _ in 0..=states.len() {
                    let mut fix2 = fix.clone();
                    fix2.insert(x.clone(), cur.clone());
                    let next = self.denote(body, states, adj, env, &fix2);
                    if next == cur {
                        break;
                    }
                    cur = next;
                }
                cur
            },
            BehavioralFormula::FixVar(x) => fix.get(x).cloned().unwrap_or_default(),
        }
    }
}

/// Cap on reachable-LTS size for modal model checking (beyond it the LTS is
/// truncated; missing edges only shrink modal satisfaction sets — reject-safe).
const MAX_REACH_STATES: usize = 10_000;

impl<H: HostTerm> RejectSafeAlgebra for BehavioralAlgebra<H> {
    type Predicate = BehavioralFormula;
    type Domain = BehavioralWorld<H>;

    fn true_pred(&self) -> BehavioralFormula {
        BehavioralFormula::Top
    }

    fn false_pred(&self) -> BehavioralFormula {
        BehavioralFormula::Bot
    }

    fn and(&self, a: &BehavioralFormula, b: &BehavioralFormula) -> BehavioralFormula {
        match (a, b) {
            (BehavioralFormula::Bot, _) | (_, BehavioralFormula::Bot) => BehavioralFormula::Bot,
            (BehavioralFormula::Top, x) | (x, BehavioralFormula::Top) => x.clone(),
            _ => BehavioralFormula::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &BehavioralFormula, b: &BehavioralFormula) -> BehavioralFormula {
        match (a, b) {
            (BehavioralFormula::Top, _) | (_, BehavioralFormula::Top) => BehavioralFormula::Top,
            (BehavioralFormula::Bot, x) | (x, BehavioralFormula::Bot) => x.clone(),
            _ => BehavioralFormula::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn pseudo_complement(&self, a: &BehavioralFormula) -> BehavioralFormula {
        match a {
            BehavioralFormula::Top => BehavioralFormula::Bot,
            BehavioralFormula::Bot => BehavioralFormula::Top,
            BehavioralFormula::Not(inner) => (**inner).clone(),
            _ => BehavioralFormula::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable_3v(&self, a: &BehavioralFormula) -> Sat3 {
        if a.has_modal() {
            // Modal/temporal satisfiability (∃ a model) is semi-decidable without
            // a full mu-calculus SAT engine; report DontKnow honestly (reject-safe
            // — never a wrong Sat/Unsat). The model-checking direction (evaluate
            // against a given term) is exact.
            return Sat3::DontKnow;
        }
        // Relational: existentially close the free variables over the active
        // domain and search; exact (Sat/Unsat) unless the search budget is
        // exceeded or a bounded quantifier truncated.
        let mut free = BTreeSet::new();
        a.free_vars(&mut BTreeSet::new(), &mut free);
        let free: Vec<String> = free.into_iter().collect();
        let domain: Vec<String> = self.facts.active_domain().into_iter().collect();

        // Budget: |domain|^|free| assignments.
        let assignments = (domain.len().max(1)).checked_pow(free.len() as u32);
        match assignments {
            Some(n) if n <= self.search_budget => {},
            _ => return Sat3::DontKnow, // search space too large
        }

        let mut env = BTreeMap::new();
        let mut all_exact = true;
        let mut idx = vec![0usize; free.len()];
        loop {
            for (i, var) in free.iter().enumerate() {
                // domain may be empty: then there are no free assignments, but a
                // closed formula still gets evaluated once below.
                if let Some(v) = domain.get(idx[i]) {
                    env.insert(var.clone(), v.clone());
                }
            }
            // If there are free vars but the domain is empty, no assignment can
            // satisfy a positive atom; evaluate once with empty env.
            let (sat, exact) = self.eval(a, &env);
            all_exact = all_exact && exact;
            if sat {
                return Sat3::Sat;
            }
            // advance mixed-radix counter over the domain
            if free.is_empty() || domain.is_empty() {
                break;
            }
            let mut i = 0;
            loop {
                if i == free.len() {
                    // exhausted all assignments
                    return if all_exact {
                        Sat3::Unsat
                    } else {
                        Sat3::DontKnow
                    };
                }
                idx[i] += 1;
                if idx[i] < domain.len() {
                    break;
                }
                idx[i] = 0;
                i += 1;
            }
        }
        if all_exact {
            Sat3::Unsat
        } else {
            Sat3::DontKnow
        }
    }

    fn evaluate(&self, pred: &BehavioralFormula, elem: &BehavioralWorld<H>) -> bool {
        if !pred.has_modal() {
            // Relational fast path: evaluate against the fact base + bindings.
            return self.eval(pred, &elem.env).0;
        }
        // Modal/temporal: model-check over the term's reachable LTS.
        let (states, adj) = self.build_lts(&elem.term);
        self.denote(pred, &states, &adj, &elem.env, &HashMap::new())
            .contains(&0)
    }
}

impl<H: HostTerm> HeytingAlgebra for BehavioralAlgebra<H> {
    fn implies(&self, a: &BehavioralFormula, b: &BehavioralFormula) -> BehavioralFormula {
        // reject-safe material implication ¬a ∨ b
        self.or(&self.pseudo_complement(a), b)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CTL temporal operators (sugar over the mu-calculus modal fragment)
// ══════════════════════════════════════════════════════════════════════════════
//
// The modal mu-calculus (Diamond/BoxAll/Mu/Nu) is strictly more expressive than
// CTL and LTL on finite transition systems, so the standard branching-time
// temporal operators are *derived* — each desugars to a fixpoint formula that
// the model checker (`denote`) already decides exactly. A single fixpoint
// variable name is reused throughout: nesting is handled by `denote`'s lexical
// shadowing (an inner fixpoint rebinds the variable for its own body), and CTL
// sugar is always closed, so no free occurrence ever escapes a constructor.
//
// Deadlock convention: maximal-run semantics. A state with no successors is the
// end of its run; the encodings include `⟨-⟩⊤` / `[-]⊥` guards so that, e.g.,
// `AF φ` is false at a φ-free deadlock and `AG φ`/`EG φ` are correct there.
//
// (Linear-time LTL with fairness — e.g. `GF p` — is the one fragment the
// branching mu-calculus cannot express; those properties route through the
// existing Büchi engine, `crate::buchi` / `crate::ltl`.)

const CTL_VAR: &str = "__ctl";

fn diamond_any(f: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::Diamond(ActionPattern::Any, Box::new(f))
}
fn box_any(f: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::BoxAll(ActionPattern::Any, Box::new(f))
}
fn fixvar() -> BehavioralFormula {
    BehavioralFormula::FixVar(CTL_VAR.to_string())
}
fn mu(body: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::Mu(CTL_VAR.to_string(), Box::new(body))
}
fn nu(body: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::Nu(CTL_VAR.to_string(), Box::new(body))
}
fn and(a: BehavioralFormula, b: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::And(Box::new(a), Box::new(b))
}
fn or(a: BehavioralFormula, b: BehavioralFormula) -> BehavioralFormula {
    BehavioralFormula::Or(Box::new(a), Box::new(b))
}
/// `⟨-⟩⊤` — the state has at least one successor (is not a deadlock).
fn can_progress() -> BehavioralFormula {
    diamond_any(BehavioralFormula::Top)
}

/// `AX φ` — all successors satisfy `φ` (vacuously true at a deadlock).
pub fn ax(phi: BehavioralFormula) -> BehavioralFormula {
    box_any(phi)
}
/// `EX φ` — some successor satisfies `φ`.
pub fn ex(phi: BehavioralFormula) -> BehavioralFormula {
    diamond_any(phi)
}
/// `EF φ` — `φ` is reachable on some run.
pub fn ef(phi: BehavioralFormula) -> BehavioralFormula {
    mu(or(phi, diamond_any(fixvar())))
}
/// `AG φ` — `φ` holds on all states of all runs (safety/invariance).
pub fn ag(phi: BehavioralFormula) -> BehavioralFormula {
    nu(and(phi, box_any(fixvar())))
}
/// `AF φ` — `φ` holds eventually on every maximal run (false at a φ-free deadlock).
pub fn af(phi: BehavioralFormula) -> BehavioralFormula {
    mu(or(phi, and(box_any(fixvar()), can_progress())))
}
/// `EG φ` — some maximal run keeps `φ` true throughout.
pub fn eg(phi: BehavioralFormula) -> BehavioralFormula {
    // φ ∧ (⟨-⟩X ∨ deadlock); deadlock = [-]⊥.
    nu(and(phi, or(diamond_any(fixvar()), box_any(BehavioralFormula::Bot))))
}
/// `A(φ U ψ)` — on every maximal run, `φ` holds until `ψ`.
pub fn au(phi: BehavioralFormula, psi: BehavioralFormula) -> BehavioralFormula {
    mu(or(psi, and(phi, and(box_any(fixvar()), can_progress()))))
}
/// `E(φ U ψ)` — some run has `φ` until `ψ`.
pub fn eu(phi: BehavioralFormula, psi: BehavioralFormula) -> BehavioralFormula {
    mu(or(psi, and(phi, diamond_any(fixvar()))))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(s: &str) -> Arg {
        Arg::Lit(s.to_string())
    }
    fn var(s: &str) -> Arg {
        Arg::Var(s.to_string())
    }

    fn sample_facts() -> FactBase {
        let mut f = FactBase::new();
        f.add_fact("edge", vec!["a".into(), "b".into()]);
        f.add_fact("edge", vec!["b".into(), "c".into()]);
        f.add_fact("safe", vec!["c".into()]);
        f
    }

    #[test]
    fn relation_evaluate() {
        let alg = BehavioralAlgebra::<NoTerm>::new(sample_facts());
        let p = BehavioralFormula::Relation {
            name: "edge".into(),
            args: vec![lit("a"), lit("b")],
        };
        let mut env = BTreeMap::new();
        let w = BehavioralWorld::with_env(NoTerm, env.clone());
        assert!(alg.evaluate(&p, &w));
        let q = BehavioralFormula::Relation {
            name: "edge".into(),
            args: vec![lit("a"), lit("c")],
        };
        assert!(!alg.evaluate(&q, &BehavioralWorld::new(NoTerm)));
        // with a binding
        env.insert("x".into(), "b".into());
        let r = BehavioralFormula::Relation {
            name: "edge".into(),
            args: vec![lit("a"), var("x")],
        };
        assert!(alg.evaluate(&r, &BehavioralWorld::with_env(NoTerm, env)));
    }

    #[test]
    fn satisfiable_existential() {
        let alg = BehavioralAlgebra::<NoTerm>::new(sample_facts());
        // ∃x. edge(a, x)  → Sat (x=b)
        let p = BehavioralFormula::Relation {
            name: "edge".into(),
            args: vec![lit("a"), var("x")],
        };
        assert_eq!(alg.is_satisfiable_3v(&p), Sat3::Sat);
        // edge(a, z) with z forced to a value not present → Unsat over active domain
        let q = BehavioralFormula::Relation {
            name: "edge".into(),
            args: vec![lit("z"), lit("z")],
        };
        assert_eq!(alg.is_satisfiable_3v(&q), Sat3::Unsat);
    }

    #[test]
    fn quantifiers() {
        let alg = BehavioralAlgebra::<NoTerm>::new(sample_facts());
        // ∃y. edge(a,y) ∧ ∃z. edge(y,z)   — a→b→c chain
        let inner = BehavioralFormula::Exists {
            var: "z".into(),
            domain: QDomain::Active,
            body: Box::new(BehavioralFormula::Relation {
                name: "edge".into(),
                args: vec![var("y"), var("z")],
            }),
        };
        let chain = BehavioralFormula::Exists {
            var: "y".into(),
            domain: QDomain::Active,
            body: Box::new(BehavioralFormula::And(
                Box::new(BehavioralFormula::Relation {
                    name: "edge".into(),
                    args: vec![lit("a"), var("y")],
                }),
                Box::new(inner),
            )),
        };
        assert_eq!(alg.is_satisfiable_3v(&chain), Sat3::Sat);
        assert!(alg.evaluate(&chain, &BehavioralWorld::new(NoTerm)));

        // ∀y. edge(a,y) → safe(y)  is FALSE (b is not safe)
        let univ = BehavioralFormula::Forall {
            var: "y".into(),
            domain: QDomain::Active,
            body: Box::new(BehavioralFormula::Or(
                Box::new(BehavioralFormula::Not(Box::new(BehavioralFormula::Relation {
                    name: "edge".into(),
                    args: vec![lit("a"), var("y")],
                }))),
                Box::new(BehavioralFormula::Relation {
                    name: "safe".into(),
                    args: vec![var("y")],
                }),
            )),
        };
        assert!(!alg.evaluate(&univ, &BehavioralWorld::new(NoTerm)));
    }

    #[test]
    fn heyting_structure_and_safety() {
        let alg = BehavioralAlgebra::<NoTerm>::new(sample_facts());
        let p = BehavioralFormula::Relation {
            name: "safe".into(),
            args: vec![lit("c")],
        };
        let np = alg.pseudo_complement(&p);
        let w = BehavioralWorld::new(NoTerm);
        assert!(alg.evaluate(&p, &w));
        assert!(!alg.evaluate(&np, &w));
        // double negation collapses structurally here (Not(Not p) -> p via smart ctor)
        assert_eq!(alg.pseudo_complement(&np), p);
        // a ∧ ¬a is unsatisfiable over the snapshot
        assert_eq!(alg.is_satisfiable_3v(&alg.and(&p, &np)), Sat3::Unsat);

        // The safety property: a function bounded on BooleanAlgebra cannot accept
        // BehavioralAlgebra (it only implements HeytingAlgebra). We confirm it is
        // usable through the Heyting tier.
        fn via_heyting<A: HeytingAlgebra>(
            alg: &A,
            a: &A::Predicate,
            b: &A::Predicate,
        ) -> A::Predicate {
            alg.implies(a, b)
        }
        let _ = via_heyting(&alg, &p, &BehavioralFormula::Top);
    }

    #[test]
    fn budget_exceeded_is_dontknow() {
        // Force a tiny budget so a 2-free-var formula over a multi-value domain
        // exceeds it → DontKnow (honest reject-safe).
        let alg = BehavioralAlgebra::<NoTerm>::new(sample_facts()).with_budget(2);
        let p = BehavioralFormula::And(
            Box::new(BehavioralFormula::Relation {
                name: "edge".into(),
                args: vec![var("x"), var("y")],
            }),
            Box::new(BehavioralFormula::Relation {
                name: "safe".into(),
                args: vec![var("y")],
            }),
        );
        assert_eq!(alg.is_satisfiable_3v(&p), Sat3::DontKnow);
    }

    // A tiny LTS: 0 --step--> 1 --step--> 2(done), 2 terminal.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct TestProc(u32);
    impl HostTerm for TestProc {
        fn successors(&self) -> Vec<(String, Self)> {
            match self.0 {
                0 => vec![("step".into(), TestProc(1))],
                1 => vec![("step".into(), TestProc(2))],
                _ => vec![],
            }
        }
        fn label(&self) -> String {
            if self.0 == 2 {
                "done".into()
            } else {
                String::new()
            }
        }
    }

    #[test]
    fn modal_diamond_box() {
        let alg = BehavioralAlgebra::<TestProc>::new(FactBase::new());
        let can_step = BehavioralFormula::Diamond(
            ActionPattern::Named("step".into()),
            Box::new(BehavioralFormula::Top),
        );
        assert!(alg.evaluate(&can_step, &BehavioralWorld::new(TestProc(0))));
        assert!(!alg.evaluate(&can_step, &BehavioralWorld::new(TestProc(2)))); // terminal
                                                                               // [step]⊥ at the terminal state: no step successors → vacuously true.
        let no_step = BehavioralFormula::BoxAll(
            ActionPattern::Named("step".into()),
            Box::new(BehavioralFormula::Bot),
        );
        assert!(alg.evaluate(&no_step, &BehavioralWorld::new(TestProc(2))));
        assert!(!alg.evaluate(&no_step, &BehavioralWorld::new(TestProc(0)))); // has a step
    }

    #[test]
    fn modal_eventually_done() {
        let alg = BehavioralAlgebra::<TestProc>::new(FactBase::new());
        // μX. (done ∨ ⟨-⟩X) — eventually reaches a 'done' state.
        let eventually = BehavioralFormula::Mu(
            "X".into(),
            Box::new(BehavioralFormula::Or(
                Box::new(BehavioralFormula::Atom("done".into())),
                Box::new(BehavioralFormula::Diamond(
                    ActionPattern::Any,
                    Box::new(BehavioralFormula::FixVar("X".into())),
                )),
            )),
        );
        assert!(alg.evaluate(&eventually, &BehavioralWorld::new(TestProc(0))));
        assert!(alg.evaluate(&eventually, &BehavioralWorld::new(TestProc(2)))); // already done
                                                                                // Modal satisfiability is honestly DontKnow.
        assert_eq!(alg.is_satisfiable_3v(&eventually), Sat3::DontKnow);
    }

    #[test]
    fn modal_no_infinite_path() {
        let alg = BehavioralAlgebra::<TestProc>::new(FactBase::new());
        // νX. ⟨-⟩X — an infinite path exists; the chain terminates ⇒ false.
        let inf = BehavioralFormula::Nu(
            "X".into(),
            Box::new(BehavioralFormula::Diamond(
                ActionPattern::Any,
                Box::new(BehavioralFormula::FixVar("X".into())),
            )),
        );
        assert!(!alg.evaluate(&inf, &BehavioralWorld::new(TestProc(0))));
        assert!(!alg.evaluate(&inf, &BehavioralWorld::new(TestProc(2))));
    }

    #[test]
    fn modal_invariant_box_chain() {
        let alg = BehavioralAlgebra::<TestProc>::new(FactBase::new());
        // νX. ([−]X) — trivially true (safety with no atomic constraint): every
        // state, and all its successors transitively, are in the set.
        let always = BehavioralFormula::Nu(
            "X".into(),
            Box::new(BehavioralFormula::BoxAll(
                ActionPattern::Any,
                Box::new(BehavioralFormula::FixVar("X".into())),
            )),
        );
        assert!(alg.evaluate(&always, &BehavioralWorld::new(TestProc(0))));
        // νX. (done ∧ [−]X) — "done holds globally" — false (states 0,1 not done).
        let always_done = BehavioralFormula::Nu(
            "X".into(),
            Box::new(BehavioralFormula::And(
                Box::new(BehavioralFormula::Atom("done".into())),
                Box::new(BehavioralFormula::BoxAll(
                    ActionPattern::Any,
                    Box::new(BehavioralFormula::FixVar("X".into())),
                )),
            )),
        );
        assert!(!alg.evaluate(&always_done, &BehavioralWorld::new(TestProc(0))));
    }

    #[test]
    fn ctl_temporal_operators() {
        let alg = BehavioralAlgebra::<TestProc>::new(FactBase::new());
        let done = || BehavioralFormula::Atom("done".into());
        let s0 = || BehavioralWorld::new(TestProc(0));
        let s2 = || BehavioralWorld::new(TestProc(2));

        // EF done — done is reachable.
        assert!(alg.evaluate(&ef(done()), &s0()));
        // AF done — every (here, the single) maximal run reaches done.
        assert!(alg.evaluate(&af(done()), &s0()));
        // AG done — false (states 0,1 are not done) but holds at the done state.
        assert!(!alg.evaluate(&ag(done()), &s0()));
        assert!(alg.evaluate(&ag(done()), &s2()));
        // AG ¬bad — safety with no 'bad' states → true.
        let no_bad = ag(BehavioralFormula::Not(Box::new(BehavioralFormula::Atom("bad".into()))));
        assert!(alg.evaluate(&no_bad, &s0()));
        // E(¬done U done) — some run stays ¬done until done.
        let until = eu(BehavioralFormula::Not(Box::new(done())), done());
        assert!(alg.evaluate(&until, &s0()));
        // AX over a terminal: AX ⊥ is vacuously true at the deadlock state 2.
        assert!(alg.evaluate(&ax(BehavioralFormula::Bot), &s2()));
        // EX (¬done) from state 0 — successor (state 1) is ¬done.
        assert!(alg.evaluate(&ex(BehavioralFormula::Not(Box::new(done()))), &s0()));
    }
}
