//! `SymbolicTreeTransducer<A, B>` — a bottom-up symbolic tree transducer,
//! generalizing the word transducer (`sft.rs`) to ranked terms.
//!
//! It reads an input [`SymTerm<A::Domain>`] bottom-up; each transition
//! `(constructor, payload_guard, child_states) → (target, output)` fires when the
//! input node's constructor/children/payload match, and an [`OutputBuilder`]
//! constructs the output node from the input payload and the already-transduced
//! children. The result is the set of output terms producible at an accepting
//! root state.
//!
//! Operations provided here (all exact): [`transduce`](SymbolicTreeTransducer::transduce),
//! [`domain_sta`](SymbolicTreeTransducer::domain_sta) (the underlying input tree
//! automaton), [`is_total`](SymbolicTreeTransducer::is_total) (every input has an
//! output — decided by complementing the domain), and
//! [`compose_transduce`] (exact sequential composition of two transductions).
//! The composition/functionality *algebraic laws* are established at the FV
//! layer (M4: `StftComposition.v` / `StftFunctionality.v`), which model the
//! abstract bottom-up transduction `f : SymTerm A → list (SymTerm B)`.

use std::collections::HashMap;
use std::sync::Arc;

use crate::symbolic::BooleanAlgebra;
use crate::sym_tree::{SymTerm, SymbolicTreeAutomaton, TreeTrans};

// ══════════════════════════════════════════════════════════════════════════════
// Output builders
// ══════════════════════════════════════════════════════════════════════════════

/// How a transition produces the output node's payload.
#[derive(Clone)]
pub enum PayloadOut<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Structural output node — no payload.
    Structural,
    /// A fixed output payload.
    Const(B::Domain),
    /// The output payload computed from the input node's payload.
    Map(Arc<dyn Fn(&A::Domain) -> B::Domain + Send + Sync>),
}

/// How a transition builds the output term from the transduced children.
#[derive(Clone)]
pub enum OutputBuilder<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Emit `constructor` with `payload` and the transduced children selected
    /// (and reordered) by `children` (indices into the input node's children).
    Build { constructor: String, payload: PayloadOut<A, B>, children: Vec<usize> },
    /// Emit the `i`-th transduced child directly (delete this node).
    Project(usize),
}

/// A bottom-up transition with an attached output builder.
#[derive(Clone)]
pub struct TransducerRule<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Input head constructor.
    pub constructor: String,
    /// Input payload guard (`None` for structural input nodes).
    pub payload_guard: Option<A::Predicate>,
    /// Required state for each input child.
    pub child_states: Vec<usize>,
    /// Resulting state.
    pub target: usize,
    /// How to build the output.
    pub output: OutputBuilder<A, B>,
}

// ══════════════════════════════════════════════════════════════════════════════
// SymbolicTreeTransducer
// ══════════════════════════════════════════════════════════════════════════════

/// A bottom-up symbolic tree transducer from terms over `A` to terms over `B`.
#[derive(Clone)]
pub struct SymbolicTreeTransducer<A: BooleanAlgebra, B: BooleanAlgebra> {
    /// Input element algebra.
    pub input_algebra: A,
    /// Output element algebra.
    pub output_algebra: B,
    /// Number of states.
    pub num_states: usize,
    /// Transition rules.
    pub rules: Vec<TransducerRule<A, B>>,
    /// Accepting (root) states.
    pub accepting: std::collections::HashSet<usize>,
    /// Ranked input alphabet: constructor → arity.
    pub arities: HashMap<String, usize>,
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> SymbolicTreeTransducer<A, B> {
    /// An empty transducer.
    pub fn new(input_algebra: A, output_algebra: B) -> Self {
        SymbolicTreeTransducer {
            input_algebra,
            output_algebra,
            num_states: 0,
            rules: Vec::new(),
            accepting: std::collections::HashSet::new(),
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

    /// Register a constructor's arity.
    pub fn register(&mut self, constructor: impl Into<String>, arity: usize) {
        self.arities.insert(constructor.into(), arity);
    }

    /// Add a transition rule.
    pub fn add_rule(&mut self, rule: TransducerRule<A, B>) {
        self.rules.push(rule);
    }

    fn payload_matches(&self, guard: &Option<A::Predicate>, payload: &Option<A::Domain>) -> bool {
        match (guard, payload) {
            (None, None) => true,
            (Some(g), Some(v)) => self.input_algebra.evaluate(g, v),
            _ => false,
        }
    }

    fn build_output(
        &self,
        builder: &OutputBuilder<A, B>,
        input_payload: &Option<A::Domain>,
        child_outputs: &[SymTerm<B::Domain>],
    ) -> Option<SymTerm<B::Domain>> {
        match builder {
            OutputBuilder::Project(i) => child_outputs.get(*i).cloned(),
            OutputBuilder::Build { constructor, payload, children } => {
                let pl = match payload {
                    PayloadOut::Structural => None,
                    PayloadOut::Const(d) => Some(d.clone()),
                    PayloadOut::Map(f) => Some(f(input_payload.as_ref()?)),
                };
                let kids: Option<Vec<SymTerm<B::Domain>>> =
                    children.iter().map(|&i| child_outputs.get(i).cloned()).collect();
                Some(SymTerm { constructor: constructor.clone(), payload: pl, children: kids? })
            },
        }
    }

    /// Bottom-up: state → output terms producible at this node in that state.
    fn run_outputs(
        &self,
        node: &SymTerm<A::Domain>,
    ) -> HashMap<usize, Vec<SymTerm<B::Domain>>> {
        let child_maps: Vec<HashMap<usize, Vec<SymTerm<B::Domain>>>> =
            node.children.iter().map(|c| self.run_outputs(c)).collect();
        let mut result: HashMap<usize, Vec<SymTerm<B::Domain>>> = HashMap::new();
        for rule in &self.rules {
            if rule.constructor != node.constructor
                || rule.child_states.len() != node.children.len()
            {
                continue;
            }
            if !self.payload_matches(&rule.payload_guard, &node.payload) {
                continue;
            }
            // Each child must be in its required state with some output(s).
            let per_child: Option<Vec<&Vec<SymTerm<B::Domain>>>> = rule
                .child_states
                .iter()
                .enumerate()
                .map(|(i, &q)| child_maps[i].get(&q))
                .collect();
            let Some(per_child) = per_child else { continue };
            for combo in cartesian_terms(&per_child) {
                if let Some(out) = self.build_output(&rule.output, &node.payload, &combo) {
                    result.entry(rule.target).or_default().push(out);
                }
            }
        }
        result
    }

    /// The set of output terms produced for `input`.
    pub fn transduce(&self, input: &SymTerm<A::Domain>) -> Vec<SymTerm<B::Domain>> {
        let outs = self.run_outputs(input);
        let mut result = Vec::new();
        for (state, terms) in outs {
            if self.accepting.contains(&state) {
                result.extend(terms);
            }
        }
        result
    }

    /// The underlying input tree automaton (outputs dropped): accepts exactly the
    /// terms in this transducer's domain.
    pub fn domain_sta(&self) -> SymbolicTreeAutomaton<A> {
        let mut sta = SymbolicTreeAutomaton::new(self.input_algebra.clone());
        sta.num_states = self.num_states;
        sta.arities = self.arities.clone();
        sta.accepting = self.accepting.clone();
        for rule in &self.rules {
            sta.add_transition(TreeTrans {
                constructor: rule.constructor.clone(),
                payload_guard: rule.payload_guard.clone(),
                child_states: rule.child_states.clone(),
                target: rule.target,
            });
        }
        sta
    }

    /// Whether every well-formed input term (over the registered alphabet) has at
    /// least one output — i.e. the domain accepts all terms.
    pub fn is_total(&self) -> bool {
        self.domain_sta().complement().is_empty()
    }
}

/// All ways to pick one output per child (cartesian product).
fn cartesian_terms<D: Clone>(per_child: &[&Vec<SymTerm<D>>]) -> Vec<Vec<SymTerm<D>>> {
    let mut out = vec![Vec::new()];
    for child in per_child {
        let mut next = Vec::new();
        for prefix in &out {
            for term in child.iter() {
                let mut t = prefix.clone();
                t.push(term.clone());
                next.push(t);
            }
        }
        out = next;
    }
    out
}

/// Exact sequential composition of two transductions: `(t1 ; t2)(input)` is the
/// set of final terms obtained by transducing `input` with `t1` then each
/// intermediate with `t2`.
pub fn compose_transduce<A, B, C>(
    t1: &SymbolicTreeTransducer<A, B>,
    t2: &SymbolicTreeTransducer<B, C>,
    input: &SymTerm<A::Domain>,
) -> Vec<SymTerm<C::Domain>>
where
    A: BooleanAlgebra,
    B: BooleanAlgebra,
    C: BooleanAlgebra,
{
    t1.transduce(input).iter().flat_map(|mid| t2.transduce(mid)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    fn lit(n: i64) -> SymTerm<i64> {
        SymTerm::leaf("Lit", n)
    }
    fn pair(a: SymTerm<i64>, b: SymTerm<i64>) -> SymTerm<i64> {
        SymTerm::node("Pair", vec![a, b])
    }

    /// A transducer that doubles every Lit payload and rebuilds Pairs.
    fn doubler() -> SymbolicTreeTransducer<IntervalAlgebra, IntervalAlgebra> {
        let mut t =
            SymbolicTreeTransducer::new(IntervalAlgebra::new(0, 1000), IntervalAlgebra::new(0, 1000));
        t.register("Lit", 0);
        t.register("Pair", 2);
        // A single recursive "term" state so the transducer handles arbitrary
        // nesting (and is total over all Lit/Pair terms).
        let q = t.add_state();
        t.set_accepting(q);
        t.add_rule(TransducerRule {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::True),
            child_states: vec![],
            target: q,
            output: OutputBuilder::Build {
                constructor: "Lit".to_string(),
                payload: PayloadOut::Map(Arc::new(|x: &i64| x * 2)),
                children: vec![],
            },
        });
        t.add_rule(TransducerRule {
            constructor: "Pair".to_string(),
            payload_guard: None,
            child_states: vec![q, q],
            target: q,
            output: OutputBuilder::Build {
                constructor: "Pair".to_string(),
                payload: PayloadOut::Structural,
                children: vec![0, 1],
            },
        });
        t
    }

    #[test]
    fn transduce_doubles_payloads() {
        let t = doubler();
        let out = t.transduce(&pair(lit(3), lit(4)));
        assert_eq!(out, vec![pair(lit(6), lit(8))]);
        let out_lit = t.transduce(&lit(5));
        assert_eq!(out_lit, vec![lit(10)]);
    }

    #[test]
    fn project_deletes_node() {
        // A transducer that projects Pair(a, b) to its first child.
        let mut t =
            SymbolicTreeTransducer::new(IntervalAlgebra::new(0, 1000), IntervalAlgebra::new(0, 1000));
        t.register("Lit", 0);
        t.register("Pair", 2);
        let q = t.add_state();
        t.set_accepting(q);
        t.add_rule(TransducerRule {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::True),
            child_states: vec![],
            target: q,
            output: OutputBuilder::Build {
                constructor: "Lit".to_string(),
                payload: PayloadOut::Map(Arc::new(|x: &i64| *x)),
                children: vec![],
            },
        });
        t.add_rule(TransducerRule {
            constructor: "Pair".to_string(),
            payload_guard: None,
            child_states: vec![q, q],
            target: q,
            output: OutputBuilder::Project(0),
        });
        assert_eq!(t.transduce(&pair(lit(7), lit(9))), vec![lit(7)]);
    }

    #[test]
    fn domain_and_totality() {
        let t = doubler();
        let dom = t.domain_sta();
        assert!(dom.accepts(&pair(lit(1), lit(2))));
        assert!(dom.accepts(&lit(5)));
        // The doubler accepts every well-formed Lit/Pair term → total.
        assert!(t.is_total());
    }

    #[test]
    fn not_total_when_guard_restricts() {
        // Only transduces Lits in [0,10); larger Lits have no output.
        let mut t =
            SymbolicTreeTransducer::new(IntervalAlgebra::new(0, 1000), IntervalAlgebra::new(0, 1000));
        t.register("Lit", 0);
        let q = t.add_state();
        t.set_accepting(q);
        t.add_rule(TransducerRule {
            constructor: "Lit".to_string(),
            payload_guard: Some(IntervalPred::Range(0, 10)),
            child_states: vec![],
            target: q,
            output: OutputBuilder::Build {
                constructor: "Lit".to_string(),
                payload: PayloadOut::Map(Arc::new(|x: &i64| *x)),
                children: vec![],
            },
        });
        assert!(t.transduce(&lit(5)).len() == 1);
        assert!(t.transduce(&lit(50)).is_empty());
        assert!(!t.is_total()); // Lit[10,1000) has no output
    }

    #[test]
    fn composition_sequences_transductions() {
        let t = doubler();
        // double then double = quadruple
        let out = compose_transduce(&t, &t, &pair(lit(3), lit(4)));
        assert_eq!(out, vec![pair(lit(12), lit(16))]);
    }
}
