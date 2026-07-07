//! Set-automaton matching for positional Dovetail patterns.
//!
//! This module is the first shared matching substrate for the Rho-native
//! runtime plan: compile a set of left-hand-side patterns once, scan the
//! subject e-graph once at the root level, and dispatch only the candidate
//! patterns whose root symbol and arity can match the inspected e-node.
//! Associative-commutative (`AcApp`) patterns remain on the existing lazy AC
//! path because matching them may materialize budget-gated rest complements.

use crate::hash::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

use crate::egraph::{EClassId, EGraph};
use crate::rules::{Pattern, Subst};

/// Stable identifier assigned by the caller to a compiled pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PatternId(pub usize);

/// One match produced by a compiled set automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetAutomatonMatch {
    pub pattern: PatternId,
    pub root: EClassId,
    pub subst: Subst,
}

/// Cheap observability for tests, benchmarks, and later RhoNet cost models.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SetAutomatonStats {
    /// Canonical e-classes considered as potential redex roots.
    pub root_classes: usize,
    /// E-nodes inspected while scanning potential redex roots.
    pub root_nodes: usize,
    /// Candidate root-pattern checks after symbol/arity indexing.
    pub candidate_evaluations: usize,
    /// Cache misses for compiled pattern states at canonical e-classes.
    pub state_evaluations: usize,
    /// Cache hits for compiled pattern states at canonical e-classes.
    pub state_cache_hits: usize,
}

/// Result of one set-automaton scan.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SetAutomatonRun {
    pub matches: Vec<SetAutomatonMatch>,
    pub stats: SetAutomatonStats,
}

impl SetAutomatonRun {
    pub fn into_matches(self) -> Vec<SetAutomatonMatch> {
        self.matches
    }
}

type CachedSubsts = Rc<[Subst]>;

fn cached_substs(substs: Vec<Subst>) -> CachedSubsts {
    Rc::from(substs.into_boxed_slice())
}

/// Why a pattern set could not be compiled into the positional automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetAutomatonError {
    unsupported: Vec<PatternId>,
}

impl SetAutomatonError {
    pub fn unsupported_patterns(&self) -> &[PatternId] {
        &self.unsupported
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RootKey<L> {
    op: L,
    arity: usize,
}

#[derive(Clone, Debug)]
struct PatternEntry<L> {
    id: PatternId,
    root_state: StateId,
    _marker: std::marker::PhantomData<L>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StateId(usize);

impl StateId {
    /// The dense index of this interned automaton state (`0..state_count`). The
    /// in-Rho lowering keys a state's `sa:` receiver by this index — structurally
    /// equal sub-patterns share one `StateId` (the `[optimal]` O1/O3 quotient the
    /// interner already computes), so they will share one receiver.
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StateKey<L> {
    Var(String),
    App { op: L, args: Vec<StateId> },
}

#[derive(Clone, Debug)]
enum PatternState<L> {
    Var(String),
    App { op: L, args: Vec<StateId> },
}

#[derive(Clone, Debug)]
struct PatternCompiler<L> {
    states: Vec<PatternState<L>>,
    interned: HashMap<StateKey<L>, StateId>,
}

impl<L> Default for PatternCompiler<L> {
    fn default() -> Self {
        Self {
            states: Vec::new(),
            interned: HashMap::default(),
        }
    }
}

impl<L: Clone + Eq + Hash> PatternCompiler<L> {
    fn compile(&mut self, pattern: &Pattern<L>) -> StateId {
        match pattern {
            Pattern::Var(name) => self.intern(StateKey::Var(name.clone())),
            Pattern::App { op, args } => {
                let args = args.iter().map(|arg| self.compile(arg)).collect();
                self.intern(StateKey::App { op: op.clone(), args })
            },
            Pattern::AcApp { .. } => unreachable!("AcApp rejected before state compilation"),
        }
    }

    fn intern(&mut self, key: StateKey<L>) -> StateId {
        if let Some(&id) = self.interned.get(&key) {
            return id;
        }

        let id = StateId(self.states.len());
        let state = match &key {
            StateKey::Var(name) => PatternState::Var(name.clone()),
            StateKey::App { op, args } => PatternState::App { op: op.clone(), args: args.clone() },
        };
        self.states.push(state);
        self.interned.insert(key, id);
        id
    }
}

/// Compiled positional set automaton for one or more patterns.
#[derive(Clone, Debug)]
pub struct SetAutomaton<L> {
    entries: Vec<PatternEntry<L>>,
    states: Vec<PatternState<L>>,
    variable_roots: Vec<usize>,
    app_roots: HashMap<RootKey<L>, Vec<usize>>,
}

/// A read-only view over a compiled [`SetAutomaton`]'s interned pattern DAG, for
/// serializing it into an in-Rho `sa:`-receiver network (Stage 1). Additive: it
/// exposes the automaton's structure without changing any matching behavior.
pub struct SetAutomatonView<'a, L> {
    automaton: &'a SetAutomaton<L>,
}

/// One interned automaton state seen through a [`SetAutomatonView`]: a pattern
/// variable (an accept/bind leaf) or a constructor application that dispatches on
/// `op`/arity into its argument states.
pub enum AutomatonNode<'a, L> {
    Var(&'a str),
    App { op: &'a L, args: &'a [StateId] },
}

impl<L> SetAutomaton<L> {
    /// A read-only view over the interned pattern DAG — the Stage 1 in-Rho lowering
    /// input.
    pub fn view(&self) -> SetAutomatonView<'_, L> {
        SetAutomatonView { automaton: self }
    }
}

impl<'a, L> SetAutomatonView<'a, L> {
    /// The number of compiled pattern entries (one per LHS pattern).
    pub fn entry_count(&self) -> usize {
        self.automaton.entries.len()
    }

    /// The root state of the `entry`-th compiled pattern.
    pub fn entry_root_state(&self, entry: usize) -> StateId {
        self.automaton.entries[entry].root_state
    }

    /// The interned node at `state` — the `Var`/`App` shape the serializer walks.
    pub fn node(&self, state: StateId) -> AutomatonNode<'a, L> {
        let automaton = self.automaton;
        match &automaton.states[state.0] {
            PatternState::Var(name) => AutomatonNode::Var(name.as_str()),
            PatternState::App { op, args } => AutomatonNode::App { op, args: args.as_slice() },
        }
    }

    /// The entry indices whose root pattern is a bare variable (match-anything).
    pub fn variable_root_entries(&self) -> &'a [usize] {
        self.automaton.variable_roots.as_slice()
    }
}

impl<L: Clone + Eq + Hash> SetAutomaton<L> {
    /// Compile a set of positional patterns.
    ///
    /// The compiler rejects any pattern containing [`Pattern::AcApp`] so callers
    /// cannot accidentally bypass the existing AC rest-complement budget logic.
    pub fn compile_structural<I>(patterns: I) -> Result<Self, SetAutomatonError>
    where
        I: IntoIterator<Item = (PatternId, Pattern<L>)>,
    {
        let mut entries = Vec::new();
        let mut variable_roots = Vec::new();
        let mut app_roots: HashMap<RootKey<L>, Vec<usize>> = HashMap::default();
        let mut unsupported = Vec::new();
        let mut compiler = PatternCompiler::default();

        for (id, pattern) in patterns {
            if contains_ac(&pattern) {
                unsupported.push(id);
                continue;
            }

            let entry_idx = entries.len();
            let root_state = compiler.compile(&pattern);
            match &pattern {
                Pattern::Var(_) => variable_roots.push(entry_idx),
                Pattern::App { op, args } => {
                    let key = RootKey { op: op.clone(), arity: args.len() };
                    app_roots.entry(key).or_default().push(entry_idx);
                },
                Pattern::AcApp { .. } => unreachable!("AcApp rejected by contains_ac"),
            }
            entries.push(PatternEntry {
                id,
                root_state,
                _marker: std::marker::PhantomData,
            });
        }

        if unsupported.is_empty() {
            Ok(SetAutomaton {
                entries,
                states: compiler.states,
                variable_roots,
                app_roots,
            })
        } else {
            Err(SetAutomatonError { unsupported })
        }
    }

    /// Scan the e-graph once at candidate redex roots and return every match.
    pub fn search_egraph(&self, eg: &EGraph<L>) -> SetAutomatonRun {
        let mut run = SetAutomatonRun::default();
        let mut cache = HashMap::<(StateId, EClassId), CachedSubsts>::default();
        let mut visited_roots = HashSet::default();
        for class in eg.classes() {
            let root = eg.find(class);
            if !visited_roots.insert(root) {
                continue;
            }
            run.stats.root_classes += 1;

            for &entry_idx in &self.variable_roots {
                self.extend_entry_matches(eg, entry_idx, root, &mut cache, &mut run);
            }

            let mut dispatched_keys = HashSet::default();
            for node in eg.nodes(root) {
                run.stats.root_nodes += 1;
                let key = RootKey {
                    op: node.op.clone(),
                    arity: node.children.len(),
                };
                let Some(candidate_entries) = self.app_roots.get(&key) else {
                    continue;
                };
                if !dispatched_keys.insert(key) {
                    continue;
                }
                for &entry_idx in candidate_entries {
                    run.stats.candidate_evaluations += 1;
                    self.extend_entry_matches(eg, entry_idx, root, &mut cache, &mut run);
                }
            }
        }
        run
    }

    fn extend_entry_matches(
        &self,
        eg: &EGraph<L>,
        entry_idx: usize,
        root: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        run: &mut SetAutomatonRun,
    ) {
        let entry = &self.entries[entry_idx];
        let matches = self.eval_state(eg, entry.root_state, root, cache, &mut run.stats);
        run.matches
            .extend(matches.iter().cloned().map(|subst| SetAutomatonMatch {
                pattern: entry.id,
                root,
                subst,
            }));
    }

    fn eval_state(
        &self,
        eg: &EGraph<L>,
        state_id: StateId,
        class: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        stats: &mut SetAutomatonStats,
    ) -> CachedSubsts {
        let class = eg.find(class);
        let key = (state_id, class);
        if let Some(matches) = cache.get(&key) {
            stats.state_cache_hits += 1;
            return Rc::clone(matches);
        }

        stats.state_evaluations += 1;
        let matches = match &self.states[state_id.0] {
            PatternState::Var(name) => {
                let mut subst = Subst::default();
                subst.insert(name.clone(), class);
                cached_substs(vec![subst])
            },
            PatternState::App { op, args } => {
                self.eval_app_state(eg, op, args, class, cache, stats)
            },
        };
        cache.insert(key, Rc::clone(&matches));
        matches
    }

    fn eval_app_state(
        &self,
        eg: &EGraph<L>,
        op: &L,
        args: &[StateId],
        class: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        stats: &mut SetAutomatonStats,
    ) -> CachedSubsts {
        let mut out = Vec::new();
        for node in eg
            .nodes(class)
            .iter()
            .filter(|node| node.op == *op && node.children.len() == args.len())
        {
            let mut partial = vec![Subst::default()];
            for (&arg_state, &child) in args.iter().zip(&node.children) {
                let child_matches = self.eval_state(eg, arg_state, child, cache, stats);
                if child_matches.is_empty() {
                    partial.clear();
                    break;
                }

                let mut next = Vec::new();
                for left in &partial {
                    for right in child_matches.iter() {
                        if let Some(merged) = merge_substs(eg, left, right) {
                            next.push(merged);
                        }
                    }
                }
                partial = next;
                if partial.is_empty() {
                    break;
                }
            }
            out.extend(partial);
        }
        cached_substs(out)
    }
}

fn contains_ac<L>(pattern: &Pattern<L>) -> bool {
    match pattern {
        Pattern::Var(_) => false,
        Pattern::App { args, .. } => args.iter().any(contains_ac),
        Pattern::AcApp { .. } => true,
    }
}

fn merge_substs<L: Clone + Eq + Hash>(
    eg: &EGraph<L>,
    left: &Subst,
    right: &Subst,
) -> Option<Subst> {
    let mut merged = left.clone();
    for (name, &right_class) in right {
        let right_class = eg.find(right_class);
        match merged.get(name).copied() {
            Some(left_class) if eg.find(left_class) == right_class => {},
            Some(_) => return None,
            None => {
                merged.insert(name.clone(), right_class);
            },
        }
    }
    Some(merged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::ENode;

    fn leaf(eg: &mut EGraph<String>, op: &str) -> EClassId {
        eg.add(ENode::leaf(op.to_string()))
    }

    #[test]
    fn rejects_ac_patterns_without_partial_compilation() {
        let compiled = SetAutomaton::compile_structural([(
            PatternId(7),
            Pattern::ac("par".to_string(), vec![Pattern::var("x")], Some("rest".to_string())),
        )]);

        let err = compiled.expect_err("AC patterns must stay on the lazy AC path");
        assert_eq!(err.unsupported_patterns(), &[PatternId(7)]);
    }

    #[test]
    fn view_exposes_the_interned_pattern_dag() {
        // Swap(x, y): one App-rooted entry over two distinct Var leaves.
        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("a linear App pattern compiles");
        let view = automaton.view();

        assert_eq!(view.entry_count(), 1);
        assert!(view.variable_root_entries().is_empty(), "an App-rooted pattern has no variable root");

        let root = view.entry_root_state(0);
        match view.node(root) {
            AutomatonNode::App { op, args } => {
                assert_eq!(op, "Swap");
                assert_eq!(args.len(), 2, "Swap is binary");
                assert!(matches!(view.node(args[0]), AutomatonNode::Var("x")));
                assert!(matches!(view.node(args[1]), AutomatonNode::Var("y")));
            },
            AutomatonNode::Var(_) => panic!("Swap(x, y) root must be an App state"),
        }
    }

    #[test]
    fn view_shares_one_state_for_structurally_equal_subpatterns() {
        // `pair(x, y)` occurs both as entry 1 and as `wrap`'s child in entry 0. The
        // interner is the [optimal] O1/O3 quotient: both share ONE StateId, so the
        // in-Rho lowering (which keys sa: receivers by StateId) shares one receiver.
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app(
                    "wrap".to_string(),
                    vec![Pattern::app(
                        "pair".to_string(),
                        vec![Pattern::var("x"), Pattern::var("y")],
                    )],
                ),
            ),
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
        ])
        .expect("patterns compile");
        let view = automaton.view();
        assert_eq!(view.entry_count(), 2);

        let entry1_root = view.entry_root_state(1);
        let entry0_child = match view.node(view.entry_root_state(0)) {
            AutomatonNode::App { op, args } => {
                assert_eq!(op, "wrap");
                args[0]
            },
            AutomatonNode::Var(_) => panic!("wrap(...) root must be an App state"),
        };
        assert_eq!(
            entry0_child, entry1_root,
            "the shared pair(x, y) sub-pattern interns to one StateId"
        );
    }

    #[test]
    fn scans_roots_once_and_matches_multiple_patterns() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let pair = eg.add(ENode::new("pair".to_string(), vec![a, b]));
        let wrap = eg.add(ENode::new("wrap".to_string(), vec![pair]));

        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(2),
                Pattern::app(
                    "wrap".to_string(),
                    vec![Pattern::app(
                        "pair".to_string(),
                        vec![Pattern::var("x"), Pattern::var("y")],
                    )],
                ),
            ),
        ])
        .expect("positional patterns compile");

        let run = automaton.search_egraph(&eg);

        assert_eq!(run.stats.root_classes, 4);
        assert_eq!(run.stats.root_nodes, 4);
        assert_eq!(run.stats.candidate_evaluations, 2);
        assert_eq!(run.matches.len(), 2);
        assert!(run
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(1) && m.root == pair));
        assert!(run
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(2) && m.root == wrap));
    }

    #[test]
    fn enforces_non_linear_variable_consistency() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let same = eg.add(ENode::new("pair".to_string(), vec![a, a]));
        let different = eg.add(ENode::new("pair".to_string(), vec![a, b]));

        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("x")]),
        )])
        .expect("positional pattern compiles");

        let run = automaton.search_egraph(&eg);

        assert_eq!(run.matches.len(), 1);
        assert_eq!(run.matches[0].root, same);
        assert_ne!(run.matches[0].root, different);
    }

    #[test]
    fn shares_nested_state_matches_across_patterns() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let pair = eg.add(ENode::new("pair".to_string(), vec![a, b]));
        let wrap = eg.add(ENode::new("wrap".to_string(), vec![pair]));
        let boxed = eg.add(ENode::new("box".to_string(), vec![pair]));

        let shared_pair =
            Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]);
        let automaton = SetAutomaton::compile_structural([
            (PatternId(1), Pattern::app("wrap".to_string(), vec![shared_pair.clone()])),
            (PatternId(2), Pattern::app("box".to_string(), vec![shared_pair])),
        ])
        .expect("positional patterns compile");

        let run = automaton.search_egraph(&eg);

        assert_eq!(run.matches.len(), 2);
        assert!(run
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(1) && m.root == wrap));
        assert!(run
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(2) && m.root == boxed));
        assert!(
            run.stats.state_cache_hits >= 1,
            "shared nested pair state should be reused across root patterns"
        );
    }

    #[test]
    fn evaluates_duplicate_root_key_once_per_class() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let c = leaf(&mut eg, "c");
        let d = leaf(&mut eg, "d");
        let pair_ab = eg.add(ENode::new("pair".to_string(), vec![a, b]));
        let pair_cd = eg.add(ENode::new("pair".to_string(), vec![c, d]));
        eg.merge(pair_ab, pair_cd);
        eg.rebuild();
        let root = eg.find(pair_ab);

        let automaton = SetAutomaton::compile_structural([(
            PatternId(0),
            Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
        )])
        .expect("positional pattern compiles");

        let run = automaton.search_egraph(&eg);
        let root_matches = run.matches.iter().filter(|m| m.root == root).count();

        assert_eq!(run.stats.root_classes, eg.class_count());
        assert_eq!(root_matches, 2);
        assert_eq!(run.stats.candidate_evaluations, 1);
    }

    #[test]
    fn scans_each_canonical_root_once_after_merges() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let c = leaf(&mut eg, "c");
        eg.merge(a, b);
        eg.rebuild();

        let automaton = SetAutomaton::compile_structural([(PatternId(0), Pattern::var("x"))])
            .expect("root variable pattern compiles");

        let run = automaton.search_egraph(&eg);
        let mut roots = HashSet::default();
        for matched in &run.matches {
            roots.insert(matched.root);
        }

        assert_eq!(run.stats.root_classes, eg.class_count());
        assert_eq!(roots.len(), eg.class_count());
        assert!(roots.contains(&eg.find(a)));
        assert!(roots.contains(&eg.find(c)));
    }
}
