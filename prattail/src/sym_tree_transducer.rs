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

use crate::sym_tree::{SymTerm, SymbolicTreeAutomaton, TreeTrans};
use crate::symbolic::BooleanAlgebra;

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
    Build {
        constructor: String,
        payload: PayloadOut<A, B>,
        children: Vec<usize>,
    },
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
                let kids: Option<Vec<SymTerm<B::Domain>>> = children
                    .iter()
                    .map(|&i| child_outputs.get(i).cloned())
                    .collect();
                Some(SymTerm {
                    constructor: constructor.clone(),
                    payload: pl,
                    children: kids?,
                })
            },
        }
    }

    /// Bottom-up: state → output terms producible at this node in that state.
    fn run_outputs(&self, node: &SymTerm<A::Domain>) -> HashMap<usize, Vec<SymTerm<B::Domain>>> {
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
    t1.transduce(input)
        .iter()
        .flat_map(|mid| t2.transduce(mid))
        .collect()
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge (OSLF substrate, Phase 4 — `.0` introduced inert; `.1` live:
// `dead_casts` is consumed by `analyze_refinement_types` and surfaced as the
// RT07 dead-cast note when `oslf-transducer` is on)
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level cast-transduction analysis result.
///
/// Two diagnostics derived from realizing each grammar cast `r : src → tgt` as a
/// [`SymbolicTreeTransducer`] over the grammar's ranked alphabet:
///   - `non_total_casts` — `(src, tgt)` for each cast whose transduction is **not
///     total** (some well-formed term over the alphabet has no image), via
///     [`SymbolicTreeTransducer::is_total`];
///   - `dead_casts` — the rule label of each cast whose pre-image
///     ([`SymbolicTreeTransducer::domain_sta`]) **intersected with** the Phase-2
///     `structural_types::category_automaton` of `src` is empty (no source term is
///     cast-reachable).
#[cfg(feature = "oslf-transducer")]
#[derive(Debug, Clone, Default)]
pub struct TransducerAnalysis {
    /// `(source_category, target_category)` for each non-total cast.
    pub non_total_casts: Vec<(String, String)>,
    /// Rule labels of casts with an empty (dead) pre-image over the source
    /// category.
    pub dead_casts: Vec<String>,
}

/// Analyze a grammar's cast / refinement rules via bottom-up symbolic tree
/// transduction.
///
/// For each cast rule `r : src → tgt` (classified from its body by
/// [`crate::classify::classify_rule`], the single source of truth for
/// `is_cast` / `cast_source_category`), a [`SymbolicTreeTransducer`] over the
/// grammar's ranked alphabet (reusing the Phase-2
/// [`structural_types::ranked_alphabet`](crate::structural_types::ranked_alphabet)
/// / [`structural_types::build_tree_algebra`](crate::structural_types::build_tree_algebra)
/// builders) is constructed whose **domain is the source category's term
/// language** and whose output is the cast image. Then:
///   - [`is_total`](SymbolicTreeTransducer::is_total) decides whether every
///     well-formed term has an image; a non-total cast records `(src, tgt)`;
///   - the pre-image [`domain_sta`](SymbolicTreeTransducer::domain_sta) is
///     intersected with the Phase-2
///     [`structural_types::category_automaton`](crate::structural_types::category_automaton)
///     of `src`; an empty intersection records the rule label in `dead_casts`.
///
/// `refinement_types` supplies the declared refinement bases so a *refinement*
/// downcast (a cast whose owning category is a refinement type over `src`) is
/// recognized; ordinary casts are analyzed too. Introduced inert at `.0`; at
/// `.1` this is the live dead-cast entrypoint — `analyze_refinement_types`
/// calls it under `oslf-transducer` and surfaces `dead_casts` as RT07 notes.
/// The agreement gate (`prattail/tests/transducer_preimage_snapshot.rs`) proves
/// the transducer pre-image accept-set agrees, category-for-category, with the
/// Phase-2 source `category_automaton`.
///
/// # Arguments
///
/// * `all_syntax` — `(rule_label, category, items)` triples from the parser
///   bundle.
/// * `categories` — the grammar's [`CategoryInfo`](crate::pipeline::CategoryInfo)
///   list (declaration order preserved for the output).
/// * `refinement_types` — declared refinement types (`name → base_category`),
///   used to recognize refinement downcasts.
#[cfg(feature = "oslf-transducer")]
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
    refinement_types: &[crate::RefinementTypeSpec],
) -> TransducerAnalysis {
    use crate::any_algebra::AnyAlgebra;
    use crate::structural_types::{build_tree_algebra, category_automaton, ranked_alphabet};
    use crate::sym_tree::SymbolicTreeAutomaton;

    // Refinement types referenced only for documentation parity with
    // `collect_refinement_downcast_rule_labels`; every cast (refinement or
    // ordinary) is analyzed, so the base map need not gate the scan. It is
    // consulted to keep the entrypoint symmetric with the `.1` refinement path.
    let _refinement_bases: std::collections::HashMap<&str, &str> = refinement_types
        .iter()
        .map(|r| (r.name.as_str(), r.base_category.as_str()))
        .collect();

    let category_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();
    let alpha = ranked_alphabet(all_syntax, categories);
    let elem = build_tree_algebra(&alpha);

    // Preallocate to the (over-)bound of one cast per rule.
    let mut non_total_casts: Vec<(String, String)> = Vec::with_capacity(all_syntax.len());
    let mut dead_casts: Vec<String> = Vec::with_capacity(all_syntax.len());

    for (label, category, items) in all_syntax {
        // Classify the rule from its structure (the single source of truth).
        let classification = crate::classify::classify_rule(items, category, &category_names);
        let src = match (classification.is_cast, classification.cast_source_category.as_deref()) {
            (true, Some(src)) => src,
            // Not a cast rule — nothing to transduce.
            _ => continue,
        };

        // Build the cast transducer over the ranked alphabet. Its domain is the
        // source category's term language; its image is the `tgt` cast term.
        let transducer = build_cast_transducer(label, src, &alpha, &elem);

        // Totality: does every well-formed term over the alphabet have an image?
        if !transducer.is_total() {
            non_total_casts.push((src.to_string(), category.clone()));
        }

        // Cast-reachability: pre-image ∩ source-category automaton. An empty
        // intersection means no source term is cast-reachable ⇒ a dead cast.
        let preimage: SymbolicTreeAutomaton<AnyAlgebra> = transducer.domain_sta();
        let source_auto = category_automaton(src, &alpha, &elem);
        if preimage.intersect(&source_auto).is_empty() {
            dead_casts.push(label.clone());
        }
    }

    TransducerAnalysis { non_total_casts, dead_casts }
}

/// The transducer **pre-image** automaton for a single cast rule `r : src → tgt`
/// — i.e. [`SymbolicTreeTransducer::domain_sta`] of the cast transducer built
/// over the grammar's ranked alphabet — or `None` when `r` (identified by
/// `cast_label`) is not a cast rule.
///
/// Exposed (`pub`) so the agreement gate
/// (`prattail/tests/transducer_preimage_snapshot.rs`) can compare the pre-image's
/// accepted language, category-for-category, against the Phase-2
/// [`structural_types::category_automaton`](crate::structural_types::category_automaton)
/// of `src` — the agreement is only meaningful if the test sees the *same*
/// pre-image the analysis derived. At `.1` the dispatch consumes this directly.
#[cfg(feature = "oslf-transducer")]
pub fn cast_preimage_automaton(
    cast_label: &str,
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> Option<crate::sym_tree::SymbolicTreeAutomaton<crate::any_algebra::AnyAlgebra>> {
    use crate::structural_types::{build_tree_algebra, ranked_alphabet};

    let category_names: Vec<String> = categories.iter().map(|c| c.name.clone()).collect();
    let alpha = ranked_alphabet(all_syntax, categories);
    let elem = build_tree_algebra(&alpha);

    for (label, category, items) in all_syntax {
        if label != cast_label {
            continue;
        }
        let classification = crate::classify::classify_rule(items, category, &category_names);
        return match (classification.is_cast, classification.cast_source_category.as_deref()) {
            (true, Some(src)) => Some(build_cast_transducer(label, src, &alpha, &elem).domain_sta()),
            _ => None,
        };
    }
    None
}

/// Build the [`SymbolicTreeTransducer`] realizing a cast `r : src → tgt` over the
/// grammar's ranked alphabet.
///
/// The transducer's **input domain** mirrors
/// [`structural_types::category_automaton`](crate::structural_types::category_automaton)
/// of `src` transition-for-transition (so its
/// [`domain_sta`](SymbolicTreeTransducer::domain_sta) accepts *exactly* the
/// source category's terms — the property the agreement gate checks), and the
/// `src`-accepting state's transitions additionally emit the cast image. Output
/// builders are immaterial to `domain_sta` / `is_total` / the pre-image (those
/// drop outputs), so each rule carries a structure-preserving identity builder;
/// the cast image is a single-child `tgt` wrapper at the accepting state.
///
/// Reuses the Phase-2 ranked alphabet rather than re-deriving tree-automaton
/// machinery.
#[cfg(feature = "oslf-transducer")]
fn build_cast_transducer(
    cast_label: &str,
    src_cat: &str,
    alpha: &crate::structural_types::RankedAlphabet,
    elem: &crate::any_algebra::AnyAlgebra,
) -> SymbolicTreeTransducer<crate::any_algebra::AnyAlgebra, crate::any_algebra::AnyAlgebra> {
    use crate::structural_types::category_automaton;

    // Mirror the source category automaton's states/transitions. `domain_sta`
    // reconstructs precisely these (constructor / payload_guard / child_states /
    // target), so the transducer's domain equals `category_automaton(src)`.
    let source_auto = category_automaton(src_cat, alpha, elem);

    let mut t = SymbolicTreeTransducer::new(elem.clone(), elem.clone());
    t.num_states = source_auto.num_states;
    t.arities = source_auto.arities.clone();
    t.accepting = source_auto.accepting.clone();

    for trans in &source_auto.transitions {
        let arity = trans.child_states.len();
        // Identity-shaped output: re-emit the same constructor with the same
        // payload disposition (`Const`-free: a structural node when no guard, a
        // mapped payload when guarded) over the transduced children in order.
        let payload = match &trans.payload_guard {
            None => PayloadOut::Structural,
            Some(_) => PayloadOut::Map(std::sync::Arc::new(|d: &crate::any_algebra::AnyDomain| {
                d.clone()
            })),
        };
        t.add_rule(TransducerRule {
            constructor: trans.constructor.clone(),
            payload_guard: trans.payload_guard.clone(),
            child_states: trans.child_states.clone(),
            target: trans.target,
            output: OutputBuilder::Build {
                constructor: trans.constructor.clone(),
                payload,
                children: (0..arity).collect(),
            },
        });
    }

    // The cast image: the cast constructor `cast_label` wraps a single source
    // term (arity 1). Registering it keeps the output alphabet well-formed
    // without affecting the (input-side) domain automaton that `domain_sta`
    // reconstructs.
    t.register(cast_label.to_string(), 1);

    t
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
        let mut t = SymbolicTreeTransducer::new(
            IntervalAlgebra::new(0, 1000),
            IntervalAlgebra::new(0, 1000),
        );
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
        let mut t = SymbolicTreeTransducer::new(
            IntervalAlgebra::new(0, 1000),
            IntervalAlgebra::new(0, 1000),
        );
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
        let mut t = SymbolicTreeTransducer::new(
            IntervalAlgebra::new(0, 1000),
            IntervalAlgebra::new(0, 1000),
        );
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
