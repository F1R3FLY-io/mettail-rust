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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
enum PatternState<L> {
    Var(String),
    App { op: L, args: Vec<StateId> },
}

/// The append-only state interner. E-3 T-INCR: retained INSIDE the compiled
/// [`SetAutomaton`] (it was previously consumed and dropped by
/// [`SetAutomaton::compile_structural`]) so [`SetAutomaton::extend`] can keep
/// interning against the SAME `interned` map — the freshless append-only bound:
/// an extension adds only genuinely unshared sub-patterns, and every existing
/// [`StateId`] stays put (prefix stability). The retained map costs one
/// `StateKey` clone per interned state — the deliberate T-INCR memory trade.
#[derive(Clone, Debug)]
struct PatternCompiler<L> {
    states: Vec<PatternState<L>>,
    interned: HashMap<StateKey<L>, StateId>,
}

// Manual (not derived): the `interned` map's own `PartialEq` requires `L: Eq + Hash`
// (its keys), which a derive would not add to the bounds.
impl<L: Eq + Hash> PartialEq for PatternCompiler<L> {
    fn eq(&self, other: &Self) -> bool {
        self.states == other.states && self.interned == other.interned
    }
}

impl<L: Eq + Hash> Eq for PatternCompiler<L> {}

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
        enum Task<'a, L> {
            Visit(&'a Pattern<L>),
            Assemble { op: L, child_count: usize },
        }

        let mut tasks = vec![Task::Visit(pattern)];
        let mut states = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(name)) => {
                    states.push(self.intern(StateKey::Var(name.clone())));
                },
                Task::Visit(Pattern::App { op, args }) => {
                    tasks.push(Task::Assemble { op: op.clone(), child_count: args.len() });
                    tasks.extend(args.iter().rev().map(Task::Visit));
                },
                Task::Visit(Pattern::AcApp { .. }) => {
                    unreachable!("AcApp rejected before state compilation")
                },
                Task::Assemble { op, child_count } => {
                    let first_child = states
                        .len()
                        .checked_sub(child_count)
                        .expect("pattern-compiler PDA lost a child state");
                    let args = states.split_off(first_child);
                    states.push(self.intern(StateKey::App { op, args }));
                },
            }
        }
        debug_assert_eq!(states.len(), 1);
        states
            .pop()
            .expect("pattern-compiler PDA produced no root state")
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
///
/// E-3 T-INCR: the automaton retains its [`PatternCompiler`] (the append-only
/// state interner) so [`extend`](Self::extend) can append new pattern entries with
/// **StateId prefix stability** — extending never moves or renumbers an existing
/// state, and `compile_structural(P₁ ++ P₂)` equals
/// `compile_structural(P₁)` + `extend(P₂)` field-for-field (the T-INCR
/// batch-equivalence invariant, tested below).
#[derive(Clone, Debug)]
pub struct SetAutomaton<L> {
    entries: Vec<PatternEntry<L>>,
    compiler: PatternCompiler<L>,
    variable_roots: Vec<usize>,
    app_roots: HashMap<RootKey<L>, Vec<usize>>,
}

// Manual (not derived): the `app_roots` map's `PartialEq` requires `L: Eq + Hash`
// (its `RootKey<L>` keys), which a derive would not add to the bounds.
impl<L: Eq + Hash> PartialEq for SetAutomaton<L> {
    fn eq(&self, other: &Self) -> bool {
        self.entries == other.entries
            && self.compiler == other.compiler
            && self.variable_roots == other.variable_roots
            && self.app_roots == other.app_roots
    }
}

impl<L: Eq + Hash> Eq for SetAutomaton<L> {}

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
        match &automaton.compiler.states[state.0] {
            PatternState::Var(name) => AutomatonNode::Var(name.as_str()),
            PatternState::App { op, args } => AutomatonNode::App { op, args: args.as_slice() },
        }
    }

    /// The entry indices whose root pattern is a bare variable (match-anything).
    pub fn variable_root_entries(&self) -> &'a [usize] {
        self.automaton.variable_roots.as_slice()
    }

    /// The [`PatternId`] of the `entry`-th compiled pattern — which rewrite rule it
    /// is. A multi-pattern serializer routes each accepting match to the correct
    /// rule's σ-receiver channel by this id.
    pub fn entry_id(&self, entry: usize) -> PatternId {
        self.automaton.entries[entry].id
    }

    /// The number of interned states. Because structurally-equal sub-patterns share
    /// one state (the `[optimal]` O1/O3 quotient the interner computes), this is the
    /// count of distinct `sa:` receivers a full multi-pattern serialization emits.
    pub fn state_count(&self) -> usize {
        self.automaton.compiler.states.len()
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
                compiler,
                variable_roots,
                app_roots,
            })
        } else {
            Err(SetAutomatonError { unsupported })
        }
    }

    /// E-3 T-INCR: append additional pattern entries to this compiled automaton,
    /// interning against the retained state interner.
    ///
    /// **Batch-equivalence invariant** (the T-INCR correctness anchor, tested below
    /// including by property): for any pattern sequences `P₁`, `P₂`,
    ///
    /// ```text
    /// { let mut a = compile_structural(P₁)?; a.extend(P₂)?; a }
    ///   == compile_structural(P₁ ++ P₂)?
    /// ```
    ///
    /// field-for-field — in particular every `StateId` assigned while compiling `P₁`
    /// is PREFIX-STABLE (never moved or renumbered by an extension; the interner only
    /// appends, `intern`), and an extension interns only the genuinely unshared
    /// sub-patterns of `P₂` (the freshless append-only bound).
    ///
    /// **Atomicity**: like [`compile_structural`](Self::compile_structural) this
    /// rejects any [`Pattern::AcApp`]-containing pattern — but ALL patterns are
    /// validated BEFORE any state is touched, so a rejected extension leaves the
    /// automaton exactly as it was (no partial append).
    ///
    /// **Caller contract**: `PatternId`s are caller-assigned; callers who need
    /// distinct entries (every current caller) must not reuse an existing id —
    /// exactly the same contract `compile_structural` places on its input sequence.
    pub fn extend<I>(&mut self, patterns: I) -> Result<(), SetAutomatonError>
    where
        I: IntoIterator<Item = (PatternId, Pattern<L>)>,
    {
        let patterns: Vec<(PatternId, Pattern<L>)> = patterns.into_iter().collect();
        let unsupported: Vec<PatternId> = patterns
            .iter()
            .filter(|(_, pattern)| contains_ac(pattern))
            .map(|(id, _)| *id)
            .collect();
        if !unsupported.is_empty() {
            return Err(SetAutomatonError { unsupported });
        }

        for (id, pattern) in patterns {
            let entry_idx = self.entries.len();
            let root_state = self.compiler.compile(&pattern);
            match &pattern {
                Pattern::Var(_) => self.variable_roots.push(entry_idx),
                Pattern::App { op, args } => {
                    let key = RootKey { op: op.clone(), arity: args.len() };
                    self.app_roots.entry(key).or_default().push(entry_idx);
                },
                Pattern::AcApp { .. } => unreachable!("AcApp rejected by the pre-validation"),
            }
            self.entries.push(PatternEntry {
                id,
                root_state,
                _marker: std::marker::PhantomData,
            });
        }
        Ok(())
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
        let matches = match &self.compiler.states[state_id.0] {
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
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern {
            Pattern::Var(_) => {},
            Pattern::App { args, .. } => pending.extend(args.iter().rev()),
            Pattern::AcApp { .. } => return true,
        }
    }
    false
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
#[path = "../tests/support/set_automaton_compile_recursive_oracle.rs"]
mod compile_recursive_oracle;

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
        assert!(
            view.variable_root_entries().is_empty(),
            "an App-rooted pattern has no variable root"
        );

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
    fn view_exposes_entry_ids_and_state_count() {
        // entry_id round-trips the PatternId (which rewrite rule an entry is), so a
        // multi-pattern serializer can route each accept to the right rule; state_count
        // reports the interned-DAG size it walks. Swap(x, y) and Pair(a, b) share no
        // sub-structure (distinct ops AND distinct var names), so each contributes one
        // App + two Var states = 6.
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(7),
                Pattern::app("Swap".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(3),
                Pattern::app("Pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
        ])
        .expect("patterns compile");
        let view = automaton.view();
        assert_eq!(view.entry_count(), 2);
        assert_eq!(view.entry_id(0), PatternId(7), "entry_id returns the id, not the index");
        assert_eq!(view.entry_id(1), PatternId(3));
        assert_eq!(view.state_count(), 6, "2 App roots + 4 distinct Var leaves");
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

    // ─── E-3 T-INCR: extend-vs-batch equivalence ──────────────────────────────

    /// A deterministic ladder-shaped pattern: `R{i}(S(S(…s deep…(x))))`.
    fn chain_pattern(root: usize, depth: usize) -> Pattern<String> {
        let mut pattern = Pattern::var("x");
        for _ in 0..depth {
            pattern = Pattern::app("S".to_string(), vec![pattern]);
        }
        Pattern::app(format!("R{root}"), vec![pattern])
    }

    #[test]
    fn extend_equals_batch_on_the_concatenated_sequence() {
        // The T-INCR invariant, field-for-field (PartialEq covers entries, the
        // retained interner, variable_roots, and app_roots).
        let base: Vec<(PatternId, Pattern<String>)> = (0..8)
            .map(|i| (PatternId(i), chain_pattern(i, 1)))
            .collect();
        let appended: Vec<(PatternId, Pattern<String>)> = (0..3)
            .map(|i| (PatternId(8 + i), chain_pattern(i, 2)))
            .collect();

        let mut incremental =
            SetAutomaton::compile_structural(base.clone()).expect("the base ladder compiles");
        let base_state_count = incremental.view().state_count();
        incremental
            .extend(appended.clone())
            .expect("the extension compiles");

        let batch = SetAutomaton::compile_structural(base.into_iter().chain(appended))
            .expect("the concatenated ladder compiles");
        assert_eq!(incremental, batch, "extend must equal batch on the concatenated sequence");
        assert!(
            incremental.view().state_count() > base_state_count,
            "the deeper chains intern new states"
        );
    }

    #[test]
    fn extend_is_stateid_prefix_stable_and_appends_only_unshared_states() {
        let base: Vec<(PatternId, Pattern<String>)> = (0..4)
            .map(|i| (PatternId(i), chain_pattern(i, 1)))
            .collect();
        let mut automaton =
            SetAutomaton::compile_structural(base).expect("the base ladder compiles");
        let before: Vec<StateId> = (0..automaton.view().entry_count())
            .map(|e| automaton.view().entry_root_state(e))
            .collect();
        let before_states = automaton.view().state_count();

        // `R0(S(x))` again under a NEW id: fully shared — zero new states, and the
        // new entry's root state IS the existing root state (the O1/O3 quotient).
        automaton
            .extend([(PatternId(100), chain_pattern(0, 1))])
            .expect("a fully-shared extension compiles");
        assert_eq!(automaton.view().state_count(), before_states, "nothing new interned");
        assert_eq!(
            automaton
                .view()
                .entry_root_state(automaton.view().entry_count() - 1),
            before[0],
            "the duplicate pattern shares the existing root state"
        );

        // A deeper chain: exactly the unshared suffix interns (S(S(x)) exists up to
        // depth 1; depth 2 adds ONE S-state, plus the new root App).
        automaton
            .extend([(PatternId(101), chain_pattern(0, 2))])
            .expect("the deeper chain compiles");
        assert_eq!(
            automaton.view().state_count(),
            before_states + 2,
            "only the unshared sub-patterns intern (freshless append-only bound)"
        );
        for (entry, &state) in before.iter().enumerate() {
            assert_eq!(
                automaton.view().entry_root_state(entry),
                state,
                "existing StateIds never move (prefix stability)"
            );
        }
    }

    #[test]
    fn diagonal_one_pattern_at_a_time_equals_batch() {
        // The design §4.5 diagonal worst case: N single-pattern extensions must equal
        // the one-shot batch compile, and the interned-state count stays bounded by
        // the total pattern nodes (the size-optimality bound `states ≤ raw nodes`).
        let patterns: Vec<(PatternId, Pattern<String>)> = (0..16)
            .map(|i| (PatternId(i), chain_pattern(i % 5, 1 + i / 5)))
            .collect();
        let raw_nodes: usize = patterns
            .iter()
            .map(|(_, p)| {
                fn nodes(p: &Pattern<String>) -> usize {
                    match p {
                        Pattern::Var(_) => 1,
                        Pattern::App { args, .. } => 1 + args.iter().map(nodes).sum::<usize>(),
                        Pattern::AcApp { .. } => unreachable!("no AC in the diagonal"),
                    }
                }
                nodes(p)
            })
            .sum();

        let mut diagonal = SetAutomaton::compile_structural(patterns[..1].to_vec())
            .expect("the first pattern compiles");
        for pattern in &patterns[1..] {
            diagonal
                .extend([pattern.clone()])
                .expect("each diagonal step compiles");
        }
        let batch =
            SetAutomaton::compile_structural(patterns).expect("the batch sequence compiles");
        assert_eq!(diagonal, batch, "the diagonal equals the batch compile");
        assert!(
            diagonal.view().state_count() <= raw_nodes,
            "interned states stay within the raw pattern-node bound"
        );
    }

    #[test]
    fn extend_rejects_ac_atomically() {
        let mut automaton = SetAutomaton::compile_structural([(PatternId(0), chain_pattern(0, 1))])
            .expect("the base compiles");
        let before = automaton.clone();
        let err = automaton
            .extend([
                (PatternId(1), chain_pattern(1, 1)),
                (
                    PatternId(2),
                    Pattern::ac(
                        "par".to_string(),
                        vec![Pattern::var("x")],
                        Some("rest".to_string()),
                    ),
                ),
            ])
            .expect_err("an AC pattern in the extension must fail closed");
        assert_eq!(err.unsupported_patterns(), &[PatternId(2)]);
        assert_eq!(automaton, before, "a rejected extension mutates NOTHING (atomicity)");
    }

    #[test]
    fn extended_automaton_matches_like_the_batch_automaton() {
        // search_egraph equality (the design §4.3 invariant's behavioral half): the
        // extended automaton and the batch automaton produce identical runs.
        let mut eg = EGraph::new();
        let leaf_a = leaf(&mut eg, "a");
        let s1 = eg.add(ENode::new("S".to_string(), vec![leaf_a]));
        let s2 = eg.add(ENode::new("S".to_string(), vec![s1]));
        let r0_shallow = eg.add(ENode::new("R0".to_string(), vec![s1]));
        let r0_deep = eg.add(ENode::new("R0".to_string(), vec![s2]));

        let mut incremental =
            SetAutomaton::compile_structural([(PatternId(0), chain_pattern(0, 1))])
                .expect("the base compiles");
        incremental
            .extend([(PatternId(1), chain_pattern(0, 2))])
            .expect("the extension compiles");
        let batch = SetAutomaton::compile_structural([
            (PatternId(0), chain_pattern(0, 1)),
            (PatternId(1), chain_pattern(0, 2)),
        ])
        .expect("the batch compiles");

        let run_incremental = incremental.search_egraph(&eg);
        let run_batch = batch.search_egraph(&eg);
        assert_eq!(run_incremental, run_batch, "identical matches AND stats");
        assert!(run_incremental
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(0) && m.root == r0_shallow));
        assert!(run_incremental
            .matches
            .iter()
            .any(|m| m.pattern == PatternId(1) && m.root == r0_deep));
    }

    proptest::proptest! {
        /// Property: for ARBITRARY splits of an arbitrary ladder-shaped pattern
        /// sequence, compile(P₁) + extend(P₂) == compile(P₁ ++ P₂). Shapes cover
        /// shared chains (few roots, varying depth), bare-variable roots, and
        /// duplicate structures under distinct ids.
        #[test]
        fn prop_extend_equals_batch(
            roots in proptest::collection::vec(0usize..6, 1..24),
            depths in proptest::collection::vec(0usize..5, 1..24),
            split_seed in 0usize..24,
        ) {
            let count = roots.len().min(depths.len());
            let patterns: Vec<(PatternId, Pattern<String>)> = (0..count)
                .map(|i| {
                    // depth 0 with root 0 degenerates to a bare Var root — the
                    // variable_roots arm is exercised too.
                    let pattern = if depths[i] == 0 && roots[i] == 0 {
                        Pattern::var("x")
                    } else {
                        chain_pattern(roots[i], depths[i])
                    };
                    (PatternId(i), pattern)
                })
                .collect();
            let split = split_seed % (count + 1);

            let mut incremental = SetAutomaton::compile_structural(patterns[..split].to_vec())
                .expect("the prefix compiles (AC-free by construction)");
            incremental
                .extend(patterns[split..].to_vec())
                .expect("the suffix extension compiles (AC-free by construction)");
            let batch = SetAutomaton::compile_structural(patterns)
                .expect("the full sequence compiles");
            proptest::prop_assert_eq!(incremental, batch);
        }
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
