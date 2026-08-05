//! `BehavioralAlgebra` — an effective algebra of **behavioral** predicates over
//! the dynamics of terms: a relational/Datalog fragment plus a modal/temporal
//! (μ-calculus) fragment over a labeled transition system.
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
//! This module provides both fragments. The **relational** fragment — `Relation`
//! atoms, `forall`/`exists` quantifiers, and boolean combination — is decided
//! against a [`FactBase`] over the active domain. The **modal/temporal**
//! fragment (`Diamond`/`BoxAll`/`Mu`/`Nu`, with the CTL operators derived below)
//! uses the [`HostTerm`] LTS and is model-checked by `denote`; the
//! `evaluate`/`is_satisfiable_3v` dispatch routes between them via `has_modal`.

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

mod lifecycle;

impl BehavioralFormula {
    /// Collect the free variables (not bound by an enclosing quantifier).
    fn free_variables(&self) -> BTreeSet<String> {
        lifecycle::free_variables(self)
    }

    /// Whether the formula uses any modal/temporal operator (and therefore needs
    /// the LTS, not just the fact base).
    fn has_modal(&self) -> bool {
        lifecycle::has_modal(self)
    }

    /// Classify this behavioral predicate into a decidability tier — the
    /// `algebra_tower`-backed behavioral classifier (OSLF Phase 3).
    ///
    /// The tier is derived from the formula *shape*, not from evaluating it:
    /// - `Top`/`Bot` are ground constants ⇒ compile-time decidable (`T1`).
    /// - Any modal/temporal operator (`Diamond`/`BoxAll`/`Mu`/`Nu`/`Atom`/
    ///   `FixVar`, anywhere in the formula) makes satisfiability only
    ///   *semi-decidable*: [`BehavioralAlgebra::is_satisfiable_3v`] returns
    ///   [`Sat3::DontKnow`] for a modal formula (the *model-checking* direction
    ///   against a given term is exact, but the *type* is only reject-safe) ⇒
    ///   semi-decidable (`T3`).
    /// - Otherwise the formula is purely **relational** — decided closed-world
    ///   over the fact snapshot ⇒ runtime-decidable (`T2`): decidable once the
    ///   relation snapshot is populated, reject-safe under stratified negation.
    ///
    /// This is a **sound over-approximation**: it never under-reports a tier (a
    /// modal guard is never classified below `T3`), and — the load-bearing
    /// property — anything it classifies at `≤ T2` is non-modal, hence handled
    /// completely by the relational runtime evaluator
    /// (`evaluate_pred_with_bindings`). It never routes a modal guard to the
    /// relational-only path. Proven in
    /// `formal/rocq/symbolic_algebra/theories/BehavioralTierClassificationSound.v`.
    pub fn decidability_tier(&self) -> crate::symbolic::DecidabilityTier {
        use crate::symbolic::DecidabilityTier;
        match self {
            BehavioralFormula::Top | BehavioralFormula::Bot => {
                DecidabilityTier::CompileTimeDecidable
            },
            _ if self.has_modal() => DecidabilityTier::SemiDecidable,
            _ => DecidabilityTier::RuntimeDecidable,
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

fn restore_binding(
    environment: &mut BTreeMap<String, String>,
    variable: &str,
    previous: Option<String>,
) {
    if let Some(value) = previous {
        environment.insert(variable.to_owned(), value);
    } else {
        environment.remove(variable);
    }
}

fn restore_fixpoint(
    fixpoints: &mut HashMap<String, HashSet<usize>>,
    variable: &str,
    previous: Option<HashSet<usize>>,
) {
    if let Some(value) = previous {
        fixpoints.insert(variable.to_owned(), value);
    } else {
        fixpoints.remove(variable);
    }
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
        let mut limits = Vec::new();
        let mut cursor = domain;
        while let QDomain::Bounded(inner, limit) = cursor {
            limits.push(*limit);
            cursor = inner;
        }
        let (mut values, mut exact) = match cursor {
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
            QDomain::Bounded(..) => unreachable!("QDomain spine scan stopped on a wrapper"),
        };
        for limit in limits.into_iter().rev() {
            let truncated = values.len() > limit;
            values.truncate(limit);
            exact = exact && !truncated;
        }
        (values, exact)
    }

    /// Evaluate `formula` against the snapshot with the given bindings. Returns
    /// `(result, exact)`; `exact = false` when a bounded quantifier may have
    /// been truncated (so a `false`/`true` could be budget-limited).
    fn eval(&self, formula: &BehavioralFormula, env: &BTreeMap<String, String>) -> (bool, bool) {
        struct QuantFrame<'formula> {
            forall: bool,
            var: &'formula str,
            body: &'formula BehavioralFormula,
            values: Vec<String>,
            next: usize,
            result: bool,
            exact: bool,
            previous: Option<String>,
        }
        enum Task<'formula> {
            Visit(&'formula BehavioralFormula),
            Not,
            AndLeft(&'formula BehavioralFormula),
            AndRight(bool),
            OrLeft(&'formula BehavioralFormula),
            OrRight(bool),
            QuantNext(QuantFrame<'formula>),
            QuantAfter(QuantFrame<'formula>),
        }

        let mut environment = env.clone();
        let mut tasks = vec![Task::Visit(formula)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(BehavioralFormula::Top) => values.push((true, true)),
                Task::Visit(BehavioralFormula::Bot) => values.push((false, true)),
                Task::Visit(BehavioralFormula::Relation { name, args }) => {
                    let tuple: Option<Vec<String>> = args
                        .iter()
                        .map(|arg| self.resolve(arg, &environment))
                        .collect();
                    values.push((tuple.is_some_and(|tuple| self.facts.holds(name, &tuple)), true));
                },
                Task::Visit(BehavioralFormula::Forall { var, domain, body }) => {
                    let (domain_values, exact) = self.domain_values(domain);
                    let previous = environment.get(var).cloned();
                    tasks.push(Task::QuantNext(QuantFrame {
                        forall: true,
                        var,
                        body,
                        values: domain_values,
                        next: 0,
                        result: true,
                        exact,
                        previous,
                    }));
                },
                Task::Visit(BehavioralFormula::Exists { var, domain, body }) => {
                    let (domain_values, exact) = self.domain_values(domain);
                    let previous = environment.get(var).cloned();
                    tasks.push(Task::QuantNext(QuantFrame {
                        forall: false,
                        var,
                        body,
                        values: domain_values,
                        next: 0,
                        result: false,
                        exact,
                        previous,
                    }));
                },
                Task::Visit(BehavioralFormula::And(left, right)) => {
                    tasks.push(Task::AndLeft(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(BehavioralFormula::Or(left, right)) => {
                    tasks.push(Task::OrLeft(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(BehavioralFormula::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(
                    BehavioralFormula::Atom(_)
                    | BehavioralFormula::Diamond(..)
                    | BehavioralFormula::BoxAll(..)
                    | BehavioralFormula::Mu(..)
                    | BehavioralFormula::Nu(..)
                    | BehavioralFormula::FixVar(_),
                ) => unreachable!("modal formula reached the relational evaluator"),
                Task::Not => {
                    let (result, exact) = values.pop().expect("relational PDA lost a Not operand");
                    values.push((!result, exact));
                },
                Task::AndLeft(right) => {
                    let (left, exact) = values
                        .pop()
                        .expect("relational PDA lost an And left operand");
                    if left {
                        tasks.push(Task::AndRight(exact));
                        tasks.push(Task::Visit(right));
                    } else {
                        values.push((false, exact));
                    }
                },
                Task::AndRight(left_exact) => {
                    let (right, right_exact) = values
                        .pop()
                        .expect("relational PDA lost an And right operand");
                    values.push((right, left_exact && right_exact));
                },
                Task::OrLeft(right) => {
                    let (left, exact) = values
                        .pop()
                        .expect("relational PDA lost an Or left operand");
                    if left {
                        values.push((true, exact));
                    } else {
                        tasks.push(Task::OrRight(exact));
                        tasks.push(Task::Visit(right));
                    }
                },
                Task::OrRight(left_exact) => {
                    let (right, right_exact) = values
                        .pop()
                        .expect("relational PDA lost an Or right operand");
                    values.push((right, left_exact && right_exact));
                },
                Task::QuantNext(frame) if frame.next == frame.values.len() => {
                    restore_binding(&mut environment, frame.var, frame.previous);
                    values.push((frame.result, frame.exact));
                },
                Task::QuantNext(frame) => {
                    environment.insert(frame.var.to_owned(), frame.values[frame.next].clone());
                    let body = frame.body;
                    tasks.push(Task::QuantAfter(frame));
                    tasks.push(Task::Visit(body));
                },
                Task::QuantAfter(mut frame) => {
                    let (result, exact) = values
                        .pop()
                        .expect("relational PDA lost a quantifier body result");
                    frame.exact = frame.exact && exact;
                    if (frame.forall && !result) || (!frame.forall && result) {
                        frame.result = result;
                        restore_binding(&mut environment, frame.var, frame.previous);
                        values.push((frame.result, frame.exact));
                    } else {
                        frame.next += 1;
                        tasks.push(Task::QuantNext(frame));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("relational PDA produced no result")
    }

    /// Build the finite reachable LTS from `root` (BFS).
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
        struct QuantFrame<'formula> {
            forall: bool,
            var: &'formula str,
            body: &'formula BehavioralFormula,
            values: Vec<String>,
            next: usize,
            accumulator: HashSet<usize>,
            previous: Option<String>,
        }
        struct FixFrame<'formula> {
            var: &'formula str,
            body: &'formula BehavioralFormula,
            current: HashSet<usize>,
            remaining: usize,
            previous: Option<HashSet<usize>>,
        }
        enum Task<'formula> {
            Visit(&'formula BehavioralFormula),
            And,
            Or,
            Not,
            Diamond(&'formula ActionPattern),
            BoxAll(&'formula ActionPattern),
            QuantNext(QuantFrame<'formula>),
            QuantAfter(QuantFrame<'formula>),
            FixNext(FixFrame<'formula>),
            FixAfter(FixFrame<'formula>),
        }

        let all_states = || (0..states.len()).collect::<HashSet<usize>>();
        let mut environment = env.clone();
        let mut fixpoints = fix.clone();
        let mut tasks = vec![Task::Visit(formula)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(BehavioralFormula::Top) => values.push(all_states()),
                Task::Visit(BehavioralFormula::Bot) => values.push(HashSet::new()),
                Task::Visit(BehavioralFormula::Atom(label)) => values.push(
                    (0..states.len())
                        .filter(|&index| states[index].label() == *label)
                        .collect(),
                ),
                Task::Visit(formula @ BehavioralFormula::Relation { .. }) => {
                    values.push(if self.eval(formula, &environment).0 {
                        all_states()
                    } else {
                        HashSet::new()
                    });
                },
                Task::Visit(BehavioralFormula::Forall { var, domain, body }) => {
                    let (domain_values, _) = self.domain_values(domain);
                    tasks.push(Task::QuantNext(QuantFrame {
                        forall: true,
                        var,
                        body,
                        values: domain_values,
                        next: 0,
                        accumulator: all_states(),
                        previous: environment.get(var).cloned(),
                    }));
                },
                Task::Visit(BehavioralFormula::Exists { var, domain, body }) => {
                    let (domain_values, _) = self.domain_values(domain);
                    tasks.push(Task::QuantNext(QuantFrame {
                        forall: false,
                        var,
                        body,
                        values: domain_values,
                        next: 0,
                        accumulator: HashSet::new(),
                        previous: environment.get(var).cloned(),
                    }));
                },
                Task::Visit(BehavioralFormula::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(BehavioralFormula::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(BehavioralFormula::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(BehavioralFormula::Diamond(action, body)) => {
                    tasks.push(Task::Diamond(action));
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(BehavioralFormula::BoxAll(action, body)) => {
                    tasks.push(Task::BoxAll(action));
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(BehavioralFormula::Mu(var, body)) => {
                    tasks.push(Task::FixNext(FixFrame {
                        var,
                        body,
                        current: HashSet::new(),
                        remaining: states.len() + 1,
                        previous: fixpoints.get(var).cloned(),
                    }));
                },
                Task::Visit(BehavioralFormula::Nu(var, body)) => {
                    tasks.push(Task::FixNext(FixFrame {
                        var,
                        body,
                        current: all_states(),
                        remaining: states.len() + 1,
                        previous: fixpoints.get(var).cloned(),
                    }));
                },
                Task::Visit(BehavioralFormula::FixVar(var)) => {
                    values.push(fixpoints.get(var).cloned().unwrap_or_default());
                },
                Task::And => {
                    let right = values
                        .pop()
                        .expect("denotation PDA lost an And right operand");
                    let left = values
                        .pop()
                        .expect("denotation PDA lost an And left operand");
                    values.push(left.intersection(&right).copied().collect());
                },
                Task::Or => {
                    let right = values
                        .pop()
                        .expect("denotation PDA lost an Or right operand");
                    let left = values
                        .pop()
                        .expect("denotation PDA lost an Or left operand");
                    values.push(left.union(&right).copied().collect());
                },
                Task::Not => {
                    let inner = values.pop().expect("denotation PDA lost a Not operand");
                    values.push(
                        (0..states.len())
                            .filter(|index| !inner.contains(index))
                            .collect(),
                    );
                },
                Task::Diamond(action) => {
                    let body = values.pop().expect("denotation PDA lost a Diamond body");
                    values.push(
                        (0..states.len())
                            .filter(|&index| {
                                adj[index].iter().any(|(label, target)| {
                                    action.matches(label) && body.contains(target)
                                })
                            })
                            .collect(),
                    );
                },
                Task::BoxAll(action) => {
                    let body = values.pop().expect("denotation PDA lost a BoxAll body");
                    values.push(
                        (0..states.len())
                            .filter(|&index| {
                                adj[index].iter().all(|(label, target)| {
                                    !action.matches(label) || body.contains(target)
                                })
                            })
                            .collect(),
                    );
                },
                Task::QuantNext(frame) if frame.next == frame.values.len() => {
                    restore_binding(&mut environment, frame.var, frame.previous);
                    values.push(frame.accumulator);
                },
                Task::QuantNext(frame) => {
                    environment.insert(frame.var.to_owned(), frame.values[frame.next].clone());
                    let body = frame.body;
                    tasks.push(Task::QuantAfter(frame));
                    tasks.push(Task::Visit(body));
                },
                Task::QuantAfter(mut frame) => {
                    let body = values.pop().expect("denotation PDA lost a quantifier body");
                    frame.accumulator = if frame.forall {
                        frame.accumulator.intersection(&body).copied().collect()
                    } else {
                        frame.accumulator.union(&body).copied().collect()
                    };
                    frame.next += 1;
                    tasks.push(Task::QuantNext(frame));
                },
                Task::FixNext(frame) if frame.remaining == 0 => {
                    restore_fixpoint(&mut fixpoints, frame.var, frame.previous);
                    values.push(frame.current);
                },
                Task::FixNext(frame) => {
                    fixpoints.insert(frame.var.to_owned(), frame.current.clone());
                    let body = frame.body;
                    tasks.push(Task::FixAfter(frame));
                    tasks.push(Task::Visit(body));
                },
                Task::FixAfter(mut frame) => {
                    let next = values.pop().expect("denotation PDA lost a fixpoint body");
                    if next == frame.current {
                        restore_fixpoint(&mut fixpoints, frame.var, frame.previous);
                        values.push(frame.current);
                    } else {
                        frame.current = next;
                        frame.remaining -= 1;
                        tasks.push(Task::FixNext(frame));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("denotation PDA produced no result")
    }
}

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
        let free: Vec<String> = a.free_variables().into_iter().collect();
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

    // ── decidability_tier: the algebra_tower-backed behavioral classifier ──────
    use crate::symbolic::DecidabilityTier;

    #[test]
    fn decidability_tier_ground_is_t1() {
        assert_eq!(
            BehavioralFormula::Top.decidability_tier(),
            DecidabilityTier::CompileTimeDecidable
        );
        assert_eq!(
            BehavioralFormula::Bot.decidability_tier(),
            DecidabilityTier::CompileTimeDecidable
        );
    }

    #[test]
    fn decidability_tier_relational_is_t2() {
        // A purely relational guard is runtime-decidable (closed-world over the
        // snapshot once populated).
        let rel = BehavioralFormula::Relation {
            name: "halts".into(),
            args: vec![var("x")],
        };
        assert_eq!(rel.decidability_tier(), DecidabilityTier::RuntimeDecidable);
        // ∀/∃ + boolean combination over relational atoms stays T2.
        let quant = BehavioralFormula::Forall {
            var: "y".into(),
            domain: QDomain::Active,
            body: Box::new(BehavioralFormula::Or(
                Box::new(BehavioralFormula::Not(Box::new(rel.clone()))),
                Box::new(BehavioralFormula::Relation {
                    name: "safe".into(),
                    args: vec![var("y")],
                }),
            )),
        };
        assert_eq!(quant.decidability_tier(), DecidabilityTier::RuntimeDecidable);
    }

    #[test]
    fn decidability_tier_modal_is_t3() {
        // A modal/temporal guard is only semi-decidable (is_satisfiable_3v ⇒
        // DontKnow), so it must be classified T3 — never routed to the
        // relational-only runtime evaluator.
        let modal = BehavioralFormula::Diamond(
            ActionPattern::Named("step".into()),
            Box::new(BehavioralFormula::Atom("done".into())),
        );
        assert_eq!(modal.decidability_tier(), DecidabilityTier::SemiDecidable);
        let fixpoint = ef(BehavioralFormula::Atom("done".into()));
        assert_eq!(fixpoint.decidability_tier(), DecidabilityTier::SemiDecidable);
    }

    #[test]
    fn decidability_tier_mixed_modal_is_t3() {
        // A guard mixing a relational atom with a modal one is semi-decidable
        // (the modal subformula dominates) — the load-bearing case for the
        // mixed structural×behavioral guard rail.
        let mixed = BehavioralFormula::And(
            Box::new(BehavioralFormula::Relation {
                name: "safe".into(),
                args: vec![var("x")],
            }),
            Box::new(BehavioralFormula::Diamond(
                ActionPattern::Any,
                Box::new(BehavioralFormula::Atom("done".into())),
            )),
        );
        assert_eq!(mixed.decidability_tier(), DecidabilityTier::SemiDecidable);
    }
}
