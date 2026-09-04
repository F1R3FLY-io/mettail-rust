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

/// One node in a stack-safe positional pattern DAG.  Child indices must point
/// backward, and the root must be the final node.  This is the source-neutral
/// entrypoint for runtime-compiled grammars whose canonical rule arenas are
/// already flat; it avoids materializing a recursive [`Pattern`] first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatPatternNode<L> {
    Var(String),
    App { op: L, args: Vec<usize> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatPattern<L> {
    pub nodes: Vec<FlatPatternNode<L>>,
    pub root: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatPatternError {
    Empty,
    Root { root: usize, nodes: usize },
    RootNotLast { root: usize, nodes: usize },
    ForwardReference { owner: usize, target: usize },
    UnreachableNode { node: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatSetAutomatonError {
    pub pattern: PatternId,
    pub error: FlatPatternError,
}

/// One match produced by a compiled set automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetAutomatonMatch {
    pub pattern: PatternId,
    pub root: EClassId,
    pub subst: Subst,
}

/// One substitution obtained by matching a caller-owned application view.
///
/// Unlike [`SetAutomatonMatch`], this result has no root [`EClassId`]: the
/// application itself is virtual and is never inserted into the subject
/// e-graph. Its children remain ordinary canonical e-classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetAutomatonApplicationMatch {
    pub pattern: PatternId,
    pub subst: Subst,
}

/// Cheap observability for tests, benchmarks, and later RhoNet cost models.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SetAutomatonStats {
    /// Canonical e-classes considered as potential redex roots.
    pub root_classes: usize,
    /// E-nodes inspected while scanning potential redex roots.
    pub root_nodes: usize,
    /// Caller-owned application views considered without e-graph insertion.
    pub application_roots: usize,
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

/// Result of matching one virtual application root.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SetAutomatonApplicationRun {
    pub matches: Vec<SetAutomatonApplicationMatch>,
    pub stats: SetAutomatonStats,
}

/// Consensus-visible reason a bounded set-automaton scan did not complete.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetAutomatonSearchStop {
    WorkBudgetExhausted,
    Cancelled,
    /// A checked allocation required by a private result frontier failed.
    AllocationFailed,
}

/// Complete bounded scan.  `work` is the exact number of abstract evaluator
/// units charged by this version of the automaton ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedSetAutomatonRun {
    pub run: SetAutomatonRun,
    pub work: u64,
}

/// Complete bounded virtual-application match.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedSetAutomatonApplicationRun {
    pub run: SetAutomatonApplicationRun,
    pub work: u64,
}

/// Fail-closed bounded scan result.  Partial matches are intentionally absent;
/// only non-semantic diagnostics and the exact consumed work may escape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetAutomatonSearchFailure {
    pub reason: SetAutomatonSearchStop,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

trait SearchGovernor {
    fn charge(&mut self, work: usize) -> Result<(), SetAutomatonSearchStop>;
}

struct UnboundedGovernor;

impl SearchGovernor for UnboundedGovernor {
    #[inline(always)]
    fn charge(&mut self, _work: usize) -> Result<(), SetAutomatonSearchStop> {
        Ok(())
    }
}

struct BoundedGovernor<C> {
    remaining: u64,
    spent: u64,
    is_cancelled: C,
}

impl<C> BoundedGovernor<C>
where
    C: FnMut() -> bool,
{
    fn new(work_limit: u64, is_cancelled: C) -> Self {
        Self {
            remaining: work_limit,
            spent: 0,
            is_cancelled,
        }
    }

    fn spent(&self) -> u64 {
        self.spent
    }
}

impl<C> SearchGovernor for BoundedGovernor<C>
where
    C: FnMut() -> bool,
{
    #[inline]
    fn charge(&mut self, work: usize) -> Result<(), SetAutomatonSearchStop> {
        if (self.is_cancelled)() {
            return Err(SetAutomatonSearchStop::Cancelled);
        }
        let work = u64::try_from(work).map_err(|_| SetAutomatonSearchStop::WorkBudgetExhausted)?;
        if work > self.remaining {
            return Err(SetAutomatonSearchStop::WorkBudgetExhausted);
        }
        self.remaining -= work;
        self.spent += work;
        Ok(())
    }
}

type SlotSubst = Box<[EClassId]>;
type PartialSlotSubst = Box<[Option<EClassId>]>;
type CachedSubsts = Rc<[SlotSubst]>;

fn cached_substs(substs: Vec<SlotSubst>) -> CachedSubsts {
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
    slot_names: Vec<String>,
    _marker: std::marker::PhantomData<L>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StateId(usize);

impl StateId {
    /// The dense index of this interned automaton state (`0..state_count`).
    /// Structurally equal sub-patterns share one `StateId` (the `[optimal]`
    /// O1/O3 quotient the interner computes), so an append-only runtime
    /// serializer can emit each canonical state exactly once.
    pub fn index(self) -> usize {
        self.0
    }
}

/// A dense variable-interface position local to one canonical automaton state.
///
/// Slot identities are assigned in first-occurrence order. They deliberately do
/// not contain source variable names: alpha-renamed patterns therefore share the
/// same state while each pattern entry retains its own slot-to-name boundary map.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SlotId(usize);

impl SlotId {
    pub fn from_index(index: usize) -> Self {
        Self(index)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SlotMap {
    Identity(usize),
    Explicit(Box<[SlotId]>),
}

impl SlotMap {
    fn from_slots(slots: Vec<SlotId>) -> Self {
        if slots
            .iter()
            .enumerate()
            .all(|(index, slot)| slot.0 == index)
        {
            SlotMap::Identity(slots.len())
        } else {
            SlotMap::Explicit(slots.into_boxed_slice())
        }
    }

    fn len(&self) -> usize {
        match self {
            SlotMap::Identity(len) => *len,
            SlotMap::Explicit(slots) => slots.len(),
        }
    }

    fn get(&self, local: SlotId) -> SlotId {
        match self {
            SlotMap::Identity(len) => {
                assert!(local.0 < *len, "local slot lies outside the identity map");
                local
            },
            SlotMap::Explicit(slots) => slots[local.0],
        }
    }
}

/// One child-state invocation and the renaming from its local slot interface to
/// its parent state's local slot interface.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StateInvocation {
    state: StateId,
    slots: SlotMap,
}

impl StateInvocation {
    fn new(state: StateId, slots: Vec<SlotId>) -> Self {
        Self { state, slots: SlotMap::from_slots(slots) }
    }

    pub fn state(&self) -> StateId {
        self.state
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn parent_slot(&self, local: SlotId) -> SlotId {
        self.slots.get(local)
    }

    pub fn parent_slots(&self) -> impl ExactSizeIterator<Item = SlotId> + '_ {
        (0..self.slot_count()).map(|local| self.parent_slot(SlotId(local)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum StateKey<L> {
    Var,
    App { op: L, args: Vec<StateInvocation> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum PatternState<L> {
    Var,
    App {
        op: L,
        args: Vec<StateInvocation>,
        slot_count: usize,
    },
}

impl<L> PatternState<L> {
    fn slot_count(&self) -> usize {
        match self {
            PatternState::Var => 1,
            PatternState::App { slot_count, .. } => *slot_count,
        }
    }
}

#[derive(Clone)]
struct CompiledSubpattern {
    state: StateId,
    slot_names: Vec<Rc<str>>,
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
    fn compile(&mut self, pattern: &Pattern<L>) -> (StateId, Vec<String>) {
        enum Task<'a, L> {
            Visit(&'a Pattern<L>),
            Assemble { op: L, child_count: usize },
        }

        let mut tasks = vec![Task::Visit(pattern)];
        let mut states: Vec<CompiledSubpattern> = Vec::new();
        let mut names: HashMap<&str, Rc<str>> = HashMap::default();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Pattern::Var(name)) => {
                    let slot_name = match names.get(name.as_str()) {
                        Some(name) => Rc::clone(name),
                        None => {
                            let shared: Rc<str> = Rc::from(name.as_str());
                            names.insert(name.as_str(), Rc::clone(&shared));
                            shared
                        },
                    };
                    states.push(CompiledSubpattern {
                        state: self.intern(StateKey::Var, 1),
                        slot_names: vec![slot_name],
                    });
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
                    let children = states.split_off(first_child);
                    states.push(self.assemble(op, children));
                },
            }
        }
        debug_assert_eq!(states.len(), 1);
        let root = states
            .pop()
            .expect("pattern-compiler PDA produced no root state");
        (
            root.state,
            root.slot_names
                .into_iter()
                .map(|name| name.to_string())
                .collect(),
        )
    }

    fn compile_flat(
        &mut self,
        pattern: &FlatPattern<L>,
    ) -> Result<(StateId, Vec<String>), FlatPatternError> {
        if pattern.nodes.is_empty() {
            return Err(FlatPatternError::Empty);
        }
        if pattern.root >= pattern.nodes.len() {
            return Err(FlatPatternError::Root {
                root: pattern.root,
                nodes: pattern.nodes.len(),
            });
        }
        if pattern.root + 1 != pattern.nodes.len() {
            return Err(FlatPatternError::RootNotLast {
                root: pattern.root,
                nodes: pattern.nodes.len(),
            });
        }

        let mut reachable = vec![false; pattern.nodes.len()];
        let mut pending = vec![pattern.root];
        while let Some(index) = pending.pop() {
            if reachable[index] {
                continue;
            }
            reachable[index] = true;
            if let FlatPatternNode::App { args, .. } = &pattern.nodes[index] {
                for target in args {
                    if *target >= index {
                        return Err(FlatPatternError::ForwardReference {
                            owner: index,
                            target: *target,
                        });
                    }
                    pending.push(*target);
                }
            }
        }
        if let Some(node) = reachable.iter().position(|reachable| !reachable) {
            return Err(FlatPatternError::UnreachableNode { node });
        }

        let mut compiled = Vec::with_capacity(pattern.nodes.len());
        let mut names: HashMap<&str, Rc<str>> = HashMap::default();
        for node in &pattern.nodes {
            match node {
                FlatPatternNode::Var(name) => {
                    let slot_name = match names.get(name.as_str()) {
                        Some(name) => Rc::clone(name),
                        None => {
                            let shared: Rc<str> = Rc::from(name.as_str());
                            names.insert(name.as_str(), Rc::clone(&shared));
                            shared
                        },
                    };
                    compiled.push(CompiledSubpattern {
                        state: self.intern(StateKey::Var, 1),
                        slot_names: vec![slot_name],
                    });
                },
                FlatPatternNode::App { op, args } => {
                    let children = args.iter().map(|index| compiled[*index].clone()).collect();
                    compiled.push(self.assemble(op.clone(), children));
                },
            }
        }
        let root = compiled.pop().ok_or(FlatPatternError::Empty)?;
        Ok((
            root.state,
            root.slot_names
                .into_iter()
                .map(|name| name.to_string())
                .collect(),
        ))
    }

    fn assemble(&mut self, op: L, mut children: Vec<CompiledSubpattern>) -> CompiledSubpattern {
        let child_count = children.len();
        let (args, parent_names) = if children.len() == 1 {
            let child = children.pop().expect("the unary child exists");
            let slots = (0..child.slot_names.len()).map(SlotId).collect();
            (vec![StateInvocation::new(child.state, slots)], child.slot_names)
        } else {
            let mut args = Vec::with_capacity(child_count);
            let mut parent_names: Vec<Rc<str>> = Vec::new();
            let mut parent_slots: HashMap<Rc<str>, SlotId> = HashMap::default();

            for child in children {
                let mut slots = Vec::with_capacity(child.slot_names.len());
                for name in child.slot_names {
                    let slot = match parent_slots.get(&name).copied() {
                        Some(slot) => slot,
                        None => {
                            let slot = SlotId(parent_names.len());
                            parent_names.push(Rc::clone(&name));
                            parent_slots.insert(name, slot);
                            slot
                        },
                    };
                    slots.push(slot);
                }
                args.push(StateInvocation::new(child.state, slots));
            }
            (args, parent_names)
        };

        let slot_count = parent_names.len();
        CompiledSubpattern {
            state: self.intern(StateKey::App { op, args }, slot_count),
            slot_names: parent_names,
        }
    }

    fn intern(&mut self, key: StateKey<L>, slot_count: usize) -> StateId {
        if let Some(&id) = self.interned.get(&key) {
            debug_assert_eq!(self.states[id.0].slot_count(), slot_count);
            return id;
        }

        let id = StateId(self.states.len());
        let state = match &key {
            StateKey::Var => PatternState::Var,
            StateKey::App { op, args } => PatternState::App {
                op: op.clone(),
                args: args.clone(),
                slot_count,
            },
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

/// A read-only view over a compiled [`SetAutomaton`]'s interned pattern DAG.
///
/// Serializers use this view to lower the append-only state prefix into their
/// own execution representation without exposing a public [`StateId`]
/// constructor. The view is additive: it exposes structure without changing
/// matching behavior.
pub struct SetAutomatonView<'a, L> {
    automaton: &'a SetAutomaton<L>,
}

/// One interned automaton state seen through a [`SetAutomatonView`]: a pattern
/// variable (an accept/bind leaf) or a constructor application that dispatches on
/// `op`/arity into its argument states.
pub enum AutomatonNode<'a, L> {
    Var,
    App { op: &'a L, args: &'a [StateInvocation] },
}

/// Closed, source-neutral representation of one already-interned positional
/// automaton state.  Cache/image adapters use this to restore the exact state
/// quotient without rebuilding source patterns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatAutomatonNodeImage<L> {
    Var,
    App {
        op: L,
        args: Vec<FlatAutomatonInvocationImage>,
    },
}

/// One child-state call in a [`FlatAutomatonNodeImage`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatAutomatonInvocationImage {
    pub state: usize,
    /// Child-local slot to parent-local slot.
    pub parent_slots: Vec<usize>,
}

/// One dense state in a serialized/restored set automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatAutomatonStateImage<L> {
    pub slot_count: usize,
    pub node: FlatAutomatonNodeImage<L>,
}

/// One pattern entry in a serialized/restored set automaton.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatAutomatonEntryImage {
    pub id: PatternId,
    pub root_state: usize,
    pub slot_names: Vec<String>,
}

/// Canonical flat image accepted by [`SetAutomaton::restore_flat_image`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatAutomatonImage<L> {
    pub states: Vec<FlatAutomatonStateImage<L>>,
    pub entries: Vec<FlatAutomatonEntryImage>,
}

/// Structural reason an untrusted flat automaton image cannot be restored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatAutomatonRestoreError {
    Allocation,
    StateReference {
        owner: usize,
        target: usize,
    },
    StateSlotCount {
        state: usize,
        expected: usize,
        actual: usize,
    },
    InvocationSlotCount {
        state: usize,
        child: usize,
        expected: usize,
        actual: usize,
    },
    ParentSlot {
        state: usize,
        slot: usize,
        slot_count: usize,
    },
    NonCanonicalParentSlot {
        state: usize,
        expected: usize,
        actual: usize,
    },
    NonInjectiveInvocation {
        state: usize,
        slot: usize,
    },
    DuplicateState {
        state: usize,
        previous: usize,
    },
    EntryRoot {
        entry: usize,
        root: usize,
    },
    EntrySlotCount {
        entry: usize,
        expected: usize,
        actual: usize,
    },
    DuplicateEntryId(PatternId),
    DuplicateEntrySlot {
        entry: usize,
        name: String,
    },
}

impl<L> SetAutomaton<L> {
    /// A read-only view over the interned pattern DAG — the Stage 1 in-Rho lowering
    /// input.
    pub fn view(&self) -> SetAutomatonView<'_, L> {
        SetAutomatonView { automaton: self }
    }
}

impl<L: Clone> SetAutomaton<L> {
    /// Serialize the already-interned state quotient without reconstructing
    /// source [`Pattern`] trees.  Dense state and entry order is preserved.
    pub fn flat_image(&self) -> FlatAutomatonImage<L> {
        let view = self.view();
        let states = view
            .state_ids()
            .map(|state| FlatAutomatonStateImage {
                slot_count: view.state_slot_count(state),
                node: match view.node(state) {
                    AutomatonNode::Var => FlatAutomatonNodeImage::Var,
                    AutomatonNode::App { op, args } => FlatAutomatonNodeImage::App {
                        op: op.clone(),
                        args: args
                            .iter()
                            .map(|invocation| FlatAutomatonInvocationImage {
                                state: invocation.state().index(),
                                parent_slots: invocation
                                    .parent_slots()
                                    .map(SlotId::index)
                                    .collect(),
                            })
                            .collect(),
                    },
                },
            })
            .collect();
        let entries = (0..view.entry_count())
            .map(|entry| FlatAutomatonEntryImage {
                id: view.entry_id(entry),
                root_state: view.entry_root_state(entry).index(),
                slot_names: view.entry_slot_names(entry).to_vec(),
            })
            .collect();
        FlatAutomatonImage { states, entries }
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

    /// Original source variable names for an entry's canonical root slots, in
    /// dense [`SlotId`] order. Names live only at this entry boundary and never
    /// participate in state identity or evaluator-cache keys.
    pub fn entry_slot_names(&self, entry: usize) -> &'a [String] {
        self.automaton.entries[entry].slot_names.as_slice()
    }

    /// The interned node at `state` — the `Var`/`App` shape the serializer walks.
    pub fn node(&self, state: StateId) -> AutomatonNode<'a, L> {
        let automaton = self.automaton;
        match &automaton.compiler.states[state.0] {
            PatternState::Var => AutomatonNode::Var,
            PatternState::App { op, args, .. } => AutomatonNode::App { op, args: args.as_slice() },
        }
    }

    /// Number of canonical slots in `state`'s local variable interface.
    pub fn state_slot_count(&self, state: StateId) -> usize {
        self.automaton.compiler.states[state.0].slot_count()
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

    /// Every interned state identifier in dense serialization order.
    ///
    /// [`SetAutomaton::extend`] is prefix-stable, so a retained serializer can
    /// remember its previous length and consume only
    /// `view.state_ids().skip(previous_len)`. Returning identifiers rather than
    /// accepting raw indices preserves the invariant that every visible
    /// [`StateId`] names a state owned by this automaton.
    pub fn state_ids(&self) -> impl ExactSizeIterator<Item = StateId> + '_ {
        (0..self.state_count()).map(StateId)
    }
}

impl<L: Clone + Eq + Hash> SetAutomaton<L> {
    /// Restore a previously interned canonical automaton image without
    /// reconstructing source [`Pattern`] trees.
    ///
    /// State references must point backward and the image must already be the
    /// quotient produced by this module's state interner: duplicate structural
    /// states are rejected rather than silently re-numbered.  The method
    /// validates the complete image before returning, so no partially restored
    /// dispatch table can escape.
    pub fn restore_flat_image(
        image: FlatAutomatonImage<L>,
    ) -> Result<Self, FlatAutomatonRestoreError> {
        let mut compiler = PatternCompiler::default();
        for (state_index, state) in image.states.into_iter().enumerate() {
            let key = match state.node {
                FlatAutomatonNodeImage::Var => {
                    if state.slot_count != 1 {
                        return Err(FlatAutomatonRestoreError::StateSlotCount {
                            state: state_index,
                            expected: 1,
                            actual: state.slot_count,
                        });
                    }
                    StateKey::Var
                },
                FlatAutomatonNodeImage::App { op, args } => {
                    let mut invocations = Vec::new();
                    invocations
                        .try_reserve_exact(args.len())
                        .map_err(|_| FlatAutomatonRestoreError::Allocation)?;
                    for invocation in args {
                        let child = compiler.states.get(invocation.state).ok_or(
                            FlatAutomatonRestoreError::StateReference {
                                owner: state_index,
                                target: invocation.state,
                            },
                        )?;
                        let expected = child.slot_count();
                        if invocation.parent_slots.len() != expected {
                            return Err(FlatAutomatonRestoreError::InvocationSlotCount {
                                state: state_index,
                                child: invocation.state,
                                expected,
                                actual: invocation.parent_slots.len(),
                            });
                        }
                        let mut parent_slots = Vec::new();
                        parent_slots
                            .try_reserve_exact(expected)
                            .map_err(|_| FlatAutomatonRestoreError::Allocation)?;
                        let mut local_slots = HashSet::default();
                        for slot in invocation.parent_slots {
                            if slot >= state.slot_count {
                                return Err(FlatAutomatonRestoreError::ParentSlot {
                                    state: state_index,
                                    slot,
                                    slot_count: state.slot_count,
                                });
                            }
                            if !local_slots.insert(slot) {
                                return Err(FlatAutomatonRestoreError::NonInjectiveInvocation {
                                    state: state_index,
                                    slot,
                                });
                            }
                            parent_slots.push(SlotId(slot));
                        }
                        invocations
                            .push(StateInvocation::new(StateId(invocation.state), parent_slots));
                    }
                    let mut next_slot = 0usize;
                    for invocation in &invocations {
                        for slot in invocation.parent_slots() {
                            let slot = slot.index();
                            if slot > next_slot {
                                return Err(FlatAutomatonRestoreError::NonCanonicalParentSlot {
                                    state: state_index,
                                    expected: next_slot,
                                    actual: slot,
                                });
                            }
                            if slot == next_slot {
                                next_slot += 1;
                            }
                        }
                    }
                    if next_slot != state.slot_count {
                        return Err(FlatAutomatonRestoreError::StateSlotCount {
                            state: state_index,
                            expected: next_slot,
                            actual: state.slot_count,
                        });
                    }
                    StateKey::App { op, args: invocations }
                },
            };
            if let Some(previous) = compiler.interned.get(&key) {
                return Err(FlatAutomatonRestoreError::DuplicateState {
                    state: state_index,
                    previous: previous.0,
                });
            }
            let actual = compiler.intern(key, state.slot_count);
            debug_assert_eq!(actual.0, state_index);
        }

        let mut entries = Vec::new();
        entries
            .try_reserve_exact(image.entries.len())
            .map_err(|_| FlatAutomatonRestoreError::Allocation)?;
        let mut variable_roots = Vec::new();
        let mut app_roots: HashMap<RootKey<L>, Vec<usize>> = HashMap::default();
        let mut entry_ids = HashSet::default();
        for (entry_index, entry) in image.entries.into_iter().enumerate() {
            let state = compiler.states.get(entry.root_state).ok_or(
                FlatAutomatonRestoreError::EntryRoot {
                    entry: entry_index,
                    root: entry.root_state,
                },
            )?;
            if entry.slot_names.len() != state.slot_count() {
                return Err(FlatAutomatonRestoreError::EntrySlotCount {
                    entry: entry_index,
                    expected: state.slot_count(),
                    actual: entry.slot_names.len(),
                });
            }
            let mut names = HashSet::default();
            for name in &entry.slot_names {
                if !names.insert(name.as_str()) {
                    return Err(FlatAutomatonRestoreError::DuplicateEntrySlot {
                        entry: entry_index,
                        name: name.clone(),
                    });
                }
            }
            if !entry_ids.insert(entry.id) {
                return Err(FlatAutomatonRestoreError::DuplicateEntryId(entry.id));
            }
            match state {
                PatternState::Var => variable_roots.push(entry_index),
                PatternState::App { op, args, .. } => {
                    app_roots
                        .entry(RootKey { op: op.clone(), arity: args.len() })
                        .or_default()
                        .push(entry_index);
                },
            }
            entries.push(PatternEntry {
                id: entry.id,
                root_state: StateId(entry.root_state),
                slot_names: entry.slot_names,
                _marker: std::marker::PhantomData,
            });
        }

        Ok(Self {
            entries,
            compiler,
            variable_roots,
            app_roots,
        })
    }

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
            let (root_state, slot_names) = compiler.compile(&pattern);
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
                slot_names,
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

    /// Compile canonical backward-referencing pattern DAGs directly.
    ///
    /// This produces the same interned state algebra as
    /// [`compile_structural`](Self::compile_structural), while keeping native
    /// stack use constant and preserving subterm sharing in the input.  Any
    /// malformed DAG rejects the whole batch; no partial automaton escapes.
    pub fn compile_structural_flat<I>(patterns: I) -> Result<Self, FlatSetAutomatonError>
    where
        I: IntoIterator<Item = (PatternId, FlatPattern<L>)>,
    {
        let mut entries = Vec::new();
        let mut variable_roots = Vec::new();
        let mut app_roots: HashMap<RootKey<L>, Vec<usize>> = HashMap::default();
        let mut compiler = PatternCompiler::default();

        for (id, pattern) in patterns {
            let root_shape = match pattern.nodes.get(pattern.root) {
                Some(FlatPatternNode::Var(_)) => None,
                Some(FlatPatternNode::App { op, args }) => Some((op.clone(), args.len())),
                None if pattern.nodes.is_empty() => {
                    return Err(FlatSetAutomatonError {
                        pattern: id,
                        error: FlatPatternError::Empty,
                    });
                },
                None => {
                    return Err(FlatSetAutomatonError {
                        pattern: id,
                        error: FlatPatternError::Root {
                            root: pattern.root,
                            nodes: pattern.nodes.len(),
                        },
                    });
                },
            };
            let (root_state, slot_names) = compiler
                .compile_flat(&pattern)
                .map_err(|error| FlatSetAutomatonError { pattern: id, error })?;
            let entry_idx = entries.len();
            match root_shape {
                None => variable_roots.push(entry_idx),
                Some((op, arity)) => {
                    app_roots
                        .entry(RootKey { op, arity })
                        .or_default()
                        .push(entry_idx);
                },
            }
            entries.push(PatternEntry {
                id,
                root_state,
                slot_names,
                _marker: std::marker::PhantomData,
            });
        }

        Ok(SetAutomaton {
            entries,
            compiler,
            variable_roots,
            app_roots,
        })
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
            let (root_state, slot_names) = self.compiler.compile(&pattern);
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
                slot_names,
                _marker: std::marker::PhantomData,
            });
        }
        Ok(())
    }

    /// Scan the e-graph once at candidate redex roots and return every match.
    pub fn search_egraph(&self, eg: &EGraph<L>) -> SetAutomatonRun {
        let mut governor = UnboundedGovernor;
        match self.search_egraph_governed(eg, &mut governor) {
            Ok(run) => run,
            Err(_) => unreachable!("the unbounded set-automaton governor cannot stop"),
        }
    }

    /// Scan the e-graph with explicit work accounting and cooperative
    /// cancellation.
    ///
    /// The callback is sampled before every charged operation.  Every loop that
    /// can grow with the subject, pattern interface, substitution cross-product,
    /// or output passes through the governor.  If either bound stops the scan,
    /// all matches accumulated so far remain private and are discarded; the
    /// returned failure contains only diagnostics and consumed work.
    ///
    /// [`search_egraph`](Self::search_egraph) remains the unbounded generated
    /// path.  Both entrypoints monomorphize the same evaluator, so bounded
    /// execution cannot drift into a second matcher and the no-op governor is
    /// optimized out of the existing path.
    pub fn search_egraph_bounded<C>(
        &self,
        eg: &EGraph<L>,
        work_limit: u64,
        is_cancelled: C,
    ) -> Result<BoundedSetAutomatonRun, SetAutomatonSearchFailure>
    where
        C: FnMut() -> bool,
    {
        let mut governor = BoundedGovernor::new(work_limit, is_cancelled);
        match self.search_egraph_governed(eg, &mut governor) {
            Ok(run) => Ok(BoundedSetAutomatonRun { run, work: governor.spent() }),
            Err((reason, run)) => Err(SetAutomatonSearchFailure {
                reason,
                work: governor.spent(),
                stats: run.stats,
            }),
        }
    }

    /// Match only one canonical e-class root under the same bounded evaluator
    /// used by [`search_egraph_bounded`](Self::search_egraph_bounded).
    ///
    /// This is the semantic-transition path: premise expansion supplies an
    /// exact redex root, so scanning unrelated classes would make proof-search
    /// cost depend on private intermediate terms. State evaluation, slot
    /// merging, work accounting, cancellation, and result publication remain
    /// identical to the whole-graph path.
    pub fn search_eclass_bounded<C>(
        &self,
        eg: &EGraph<L>,
        root: EClassId,
        work_limit: u64,
        is_cancelled: C,
    ) -> Result<BoundedSetAutomatonRun, SetAutomatonSearchFailure>
    where
        C: FnMut() -> bool,
    {
        let mut governor = BoundedGovernor::new(work_limit, is_cancelled);
        let mut run = SetAutomatonRun::default();
        if let Err(reason) = governor.charge(0) {
            return Err(SetAutomatonSearchFailure {
                reason,
                work: governor.spent(),
                stats: run.stats,
            });
        }
        let mut cache = HashMap::<(StateId, EClassId), CachedSubsts>::default();
        match governor
            .charge(1)
            .and_then(|()| self.search_root_governed(eg, root, &mut cache, &mut run, &mut governor))
        {
            Ok(()) => Ok(BoundedSetAutomatonRun { run, work: governor.spent() }),
            Err(reason) => Err(SetAutomatonSearchFailure {
                reason,
                work: governor.spent(),
                stats: run.stats,
            }),
        }
    }

    /// Match one application without inserting a synthetic root into `eg`.
    ///
    /// This is the Horn-judgment path: a checked judgment identifier supplies
    /// the operator and the query supplies canonical argument e-classes. Only
    /// application-root entries participate; a root variable cannot bind the
    /// virtual application because no fabricated [`EClassId`] exists for it.
    /// Child states are evaluated by [`Self::eval_state`], so compiled-state
    /// semantics, slot consistency, caching, cancellation, and work charging
    /// are shared with physical-root matching.
    pub fn search_application_bounded<C>(
        &self,
        eg: &EGraph<L>,
        op: &L,
        arguments: &[EClassId],
        work_limit: u64,
        is_cancelled: C,
    ) -> Result<BoundedSetAutomatonApplicationRun, SetAutomatonSearchFailure>
    where
        C: FnMut() -> bool,
    {
        let mut governor = BoundedGovernor::new(work_limit, is_cancelled);
        let mut run = SetAutomatonApplicationRun::default();
        if let Err(reason) = governor.charge(0) {
            return Err(SetAutomatonSearchFailure {
                reason,
                work: governor.spent(),
                stats: run.stats,
            });
        }
        match governor.charge(1).and_then(|()| {
            self.search_application_governed(eg, op, arguments, &mut run, &mut governor)
        }) {
            Ok(()) => Ok(BoundedSetAutomatonApplicationRun { run, work: governor.spent() }),
            Err(reason) => Err(SetAutomatonSearchFailure {
                reason,
                work: governor.spent(),
                stats: run.stats,
            }),
        }
    }

    fn search_application_governed<G>(
        &self,
        eg: &EGraph<L>,
        op: &L,
        arguments: &[EClassId],
        run: &mut SetAutomatonApplicationRun,
        governor: &mut G,
    ) -> Result<(), SetAutomatonSearchStop>
    where
        G: SearchGovernor,
    {
        governor.charge(1)?;
        run.stats.application_roots += 1;
        let key = RootKey { op: op.clone(), arity: arguments.len() };
        let Some(candidate_entries) = self.app_roots.get(&key) else {
            return Ok(());
        };
        let mut cache = HashMap::<(StateId, EClassId), CachedSubsts>::default();
        for &entry_index in candidate_entries {
            governor.charge(1)?;
            run.stats.candidate_evaluations += 1;
            self.extend_application_matches(eg, entry_index, arguments, &mut cache, run, governor)?;
        }
        Ok(())
    }

    fn extend_application_matches<G>(
        &self,
        eg: &EGraph<L>,
        entry_index: usize,
        arguments: &[EClassId],
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        run: &mut SetAutomatonApplicationRun,
        governor: &mut G,
    ) -> Result<(), SetAutomatonSearchStop>
    where
        G: SearchGovernor,
    {
        let entry = &self.entries[entry_index];
        let PatternState::App { op: _, args: state_arguments, slot_count } =
            &self.compiler.states[entry.root_state.0]
        else {
            unreachable!("the application root index cannot contain a variable state")
        };
        debug_assert_eq!(state_arguments.len(), arguments.len());

        governor.charge(charged_width(*slot_count)?)?;
        let mut partial = Vec::new();
        partial
            .try_reserve_exact(1)
            .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
        partial.push(empty_partial_slot_subst(*slot_count)?);

        for (invocation, &argument) in state_arguments.iter().zip(arguments) {
            let child_matches =
                self.eval_state(eg, invocation.state(), argument, cache, &mut run.stats, governor)?;
            if child_matches.is_empty() {
                partial.clear();
                break;
            }
            let mut next = Vec::new();
            for left in &partial {
                for right in child_matches.iter() {
                    governor.charge(charged_width(right.len())?)?;
                    if let Some(merged) = merge_slot_substs(eg, left, invocation, right)? {
                        next.try_reserve(1)
                            .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
                        next.push(merged);
                    }
                }
            }
            partial = next;
            if partial.is_empty() {
                break;
            }
        }

        let mut complete = Vec::new();
        finish_slot_substs_governed(&mut partial, &mut complete, governor)?;
        for slots in complete {
            governor.charge(charged_width(slots.len())?)?;
            debug_assert_eq!(slots.len(), entry.slot_names.len());
            let mut subst = Subst::default();
            subst
                .try_reserve(entry.slot_names.len())
                .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
            for (name, class) in entry.slot_names.iter().zip(slots.iter().copied()) {
                subst.insert(name.clone(), class);
            }
            run.matches
                .try_reserve(1)
                .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
            run.matches
                .push(SetAutomatonApplicationMatch { pattern: entry.id, subst });
        }
        Ok(())
    }

    fn search_egraph_governed<G>(
        &self,
        eg: &EGraph<L>,
        governor: &mut G,
    ) -> Result<SetAutomatonRun, (SetAutomatonSearchStop, SetAutomatonRun)>
    where
        G: SearchGovernor,
    {
        let mut run = SetAutomatonRun::default();
        if let Err(reason) = governor.charge(0) {
            return Err((reason, run));
        }
        let mut cache = HashMap::<(StateId, EClassId), CachedSubsts>::default();
        let mut visited_roots = HashSet::default();
        for class in eg.classes() {
            if let Err(reason) = governor.charge(1) {
                return Err((reason, run));
            }
            let root = eg.find(class);
            if !visited_roots.insert(root) {
                continue;
            }
            if let Err(reason) = self.search_root_governed(eg, root, &mut cache, &mut run, governor)
            {
                return Err((reason, run));
            }
        }
        Ok(run)
    }

    fn search_root_governed<G>(
        &self,
        eg: &EGraph<L>,
        root: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        run: &mut SetAutomatonRun,
        governor: &mut G,
    ) -> Result<(), SetAutomatonSearchStop>
    where
        G: SearchGovernor,
    {
        let root = eg.find(root);
        if eg.nodes(root).is_empty() {
            return Ok(());
        }
        run.stats.root_classes += 1;

        for &entry_idx in &self.variable_roots {
            governor.charge(1)?;
            self.extend_entry_matches(eg, entry_idx, root, cache, run, governor)?;
        }

        let mut dispatched_keys = HashSet::default();
        for node in eg.nodes(root) {
            governor.charge(1)?;
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
                governor.charge(1)?;
                run.stats.candidate_evaluations += 1;
                self.extend_entry_matches(eg, entry_idx, root, cache, run, governor)?;
            }
        }
        Ok(())
    }

    fn extend_entry_matches<G>(
        &self,
        eg: &EGraph<L>,
        entry_idx: usize,
        root: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        run: &mut SetAutomatonRun,
        governor: &mut G,
    ) -> Result<(), SetAutomatonSearchStop>
    where
        G: SearchGovernor,
    {
        let entry = &self.entries[entry_idx];
        let matches =
            self.eval_state(eg, entry.root_state, root, cache, &mut run.stats, governor)?;
        for slots in matches.iter() {
            governor.charge(charged_width(slots.len())?)?;
            debug_assert_eq!(slots.len(), entry.slot_names.len());
            let mut subst = Subst::default();
            for (name, &class) in entry.slot_names.iter().zip(slots.iter()) {
                subst.insert(name.clone(), class);
            }
            run.matches
                .push(SetAutomatonMatch { pattern: entry.id, root, subst });
        }
        Ok(())
    }

    fn eval_state<G>(
        &self,
        eg: &EGraph<L>,
        state_id: StateId,
        class: EClassId,
        cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
        stats: &mut SetAutomatonStats,
        governor: &mut G,
    ) -> Result<CachedSubsts, SetAutomatonSearchStop>
    where
        G: SearchGovernor,
    {
        struct AppFrame {
            state_id: StateId,
            class: EClassId,
            next_node: usize,
            active_node: Option<usize>,
            next_arg: usize,
            partial: Vec<PartialSlotSubst>,
            out: Vec<SlotSubst>,
        }

        enum Job {
            Evaluate { state_id: StateId, class: EClassId },
            ContinueApp(AppFrame),
            MergeArg(AppFrame),
        }

        let mut jobs = vec![Job::Evaluate { state_id, class }];
        let mut values = Vec::<CachedSubsts>::new();
        while let Some(job) = jobs.pop() {
            governor.charge(1)?;
            match job {
                Job::Evaluate { state_id, class } => {
                    let class = eg.find(class);
                    let key = (state_id, class);
                    if let Some(matches) = cache.get(&key) {
                        stats.state_cache_hits += 1;
                        values.push(Rc::clone(matches));
                        continue;
                    }

                    stats.state_evaluations += 1;
                    match &self.compiler.states[state_id.0] {
                        PatternState::Var => {
                            governor.charge(1)?;
                            let matches = cached_substs(vec![vec![class].into_boxed_slice()]);
                            cache.insert(key, Rc::clone(&matches));
                            values.push(matches);
                        },
                        PatternState::App { .. } => jobs.push(Job::ContinueApp(AppFrame {
                            state_id,
                            class,
                            next_node: 0,
                            active_node: None,
                            next_arg: 0,
                            partial: Vec::new(),
                            out: Vec::new(),
                        })),
                    }
                },
                Job::ContinueApp(mut frame) => {
                    let PatternState::App { op, args, slot_count } =
                        &self.compiler.states[frame.state_id.0]
                    else {
                        unreachable!("only App states create application evaluation frames")
                    };

                    if frame.active_node.is_none() {
                        let nodes = eg.nodes(frame.class);
                        let mut node_index = None;
                        while frame.next_node < nodes.len() {
                            governor.charge(1)?;
                            let current = frame.next_node;
                            frame.next_node += 1;
                            if nodes[current].op == *op
                                && nodes[current].children.len() == args.len()
                            {
                                node_index = Some(current);
                                break;
                            }
                        }
                        let Some(node_index) = node_index else {
                            let matches = cached_substs(frame.out);
                            cache.insert((frame.state_id, frame.class), Rc::clone(&matches));
                            values.push(matches);
                            continue;
                        };
                        frame.active_node = Some(node_index);
                        frame.next_arg = 0;
                        governor.charge(charged_width(*slot_count)?)?;
                        frame
                            .partial
                            .try_reserve(1)
                            .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
                        frame.partial.push(empty_partial_slot_subst(*slot_count)?);

                        if args.is_empty() {
                            finish_slot_substs_governed(
                                &mut frame.partial,
                                &mut frame.out,
                                governor,
                            )?;
                            frame.active_node = None;
                            jobs.push(Job::ContinueApp(frame));
                            continue;
                        }
                    }

                    let node_index = frame
                        .active_node
                        .expect("an active application node was just selected");
                    let arg_state = args[frame.next_arg].state();
                    let child = eg.nodes(frame.class)[node_index].children[frame.next_arg];
                    jobs.push(Job::MergeArg(frame));
                    jobs.push(Job::Evaluate { state_id: arg_state, class: child });
                },
                Job::MergeArg(mut frame) => {
                    let child_matches = values
                        .pop()
                        .expect("application evaluator lost a child-state result");
                    if child_matches.is_empty() {
                        frame.partial.clear();
                        frame.active_node = None;
                        jobs.push(Job::ContinueApp(frame));
                        continue;
                    }

                    let mut next = Vec::new();
                    let PatternState::App { args, .. } = &self.compiler.states[frame.state_id.0]
                    else {
                        unreachable!("only App states create application evaluation frames")
                    };
                    let invocation = &args[frame.next_arg];
                    for left in &frame.partial {
                        for right in child_matches.iter() {
                            governor.charge(charged_width(right.len())?)?;
                            if let Some(merged) = merge_slot_substs(eg, left, invocation, right)? {
                                next.try_reserve(1)
                                    .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
                                next.push(merged);
                            }
                        }
                    }
                    frame.partial = next;
                    if frame.partial.is_empty() {
                        frame.active_node = None;
                    } else {
                        frame.next_arg += 1;
                        if frame.next_arg == args.len() {
                            finish_slot_substs_governed(
                                &mut frame.partial,
                                &mut frame.out,
                                governor,
                            )?;
                            frame.active_node = None;
                        }
                    }
                    jobs.push(Job::ContinueApp(frame));
                },
            }
        }

        debug_assert_eq!(values.len(), 1);
        Ok(values
            .pop()
            .expect("set-automaton evaluator produced no root-state result"))
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

fn charged_width(width: usize) -> Result<usize, SetAutomatonSearchStop> {
    width
        .checked_add(1)
        .ok_or(SetAutomatonSearchStop::WorkBudgetExhausted)
}

fn empty_partial_slot_subst(slot_count: usize) -> Result<PartialSlotSubst, SetAutomatonSearchStop> {
    let mut slots = Vec::new();
    slots
        .try_reserve_exact(slot_count)
        .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
    slots.resize(slot_count, None);
    Ok(slots.into_boxed_slice())
}

fn merge_slot_substs<L: Clone + Eq + Hash>(
    eg: &EGraph<L>,
    left: &PartialSlotSubst,
    invocation: &StateInvocation,
    right: &SlotSubst,
) -> Result<Option<PartialSlotSubst>, SetAutomatonSearchStop> {
    debug_assert_eq!(invocation.slot_count(), right.len());
    let mut merged = Vec::new();
    merged
        .try_reserve_exact(left.len())
        .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
    merged.extend_from_slice(left);
    for (local_index, &right_class) in right.iter().enumerate() {
        let right_class = eg.find(right_class);
        let parent = invocation.parent_slot(SlotId(local_index)).0;
        match merged[parent] {
            Some(left_class) if eg.find(left_class) == right_class => {},
            Some(_) => return Ok(None),
            None => merged[parent] = Some(right_class),
        }
    }
    Ok(Some(merged.into_boxed_slice()))
}

fn finish_slot_substs_governed<G>(
    partial: &mut Vec<PartialSlotSubst>,
    out: &mut Vec<SlotSubst>,
    governor: &mut G,
) -> Result<(), SetAutomatonSearchStop>
where
    G: SearchGovernor,
{
    for slots in partial.iter() {
        governor.charge(charged_width(slots.len())?)?;
    }
    out.try_reserve(partial.len())
        .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
    for slots in partial.drain(..) {
        let slots = slots.into_vec();
        let mut complete = Vec::new();
        complete
            .try_reserve_exact(slots.len())
            .map_err(|_| SetAutomatonSearchStop::AllocationFailed)?;
        for slot in slots {
            complete.push(slot.expect("every canonical state slot is bound by an occurrence"));
        }
        out.push(complete.into_boxed_slice());
    }
    Ok(())
}

#[cfg(test)]
fn finish_slot_substs(partial: &mut Vec<PartialSlotSubst>, out: &mut Vec<SlotSubst>) {
    let mut governor = UnboundedGovernor;
    finish_slot_substs_governed(partial, out, &mut governor)
        .expect("the unbounded search governor cannot stop evaluation");
}

#[cfg(test)]
#[path = "../tests/support/set_automaton_compile_recursive_oracle.rs"]
mod compile_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/set_automaton_eval_recursive_oracle.rs"]
mod eval_recursive_oracle;

#[cfg(test)]
#[path = "../tests/support/set_automaton_nominal_recursive_oracle.rs"]
mod nominal_recursive_oracle;

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
    fn flat_pattern_compilation_is_identical_to_recursive_compilation() {
        let recursive = SetAutomaton::compile_structural([(
            PatternId(7),
            Pattern::app(
                "pair".to_string(),
                vec![Pattern::var("x"), Pattern::app("wrap".to_string(), vec![Pattern::var("x")])],
            ),
        )])
        .expect("recursive pattern compiles");
        let flat = SetAutomaton::compile_structural_flat([(
            PatternId(7),
            FlatPattern {
                nodes: vec![
                    FlatPatternNode::Var("x".to_string()),
                    FlatPatternNode::Var("x".to_string()),
                    FlatPatternNode::App { op: "wrap".to_string(), args: vec![1] },
                    FlatPatternNode::App { op: "pair".to_string(), args: vec![0, 2] },
                ],
                root: 3,
            },
        )])
        .expect("flat pattern compiles");

        assert_eq!(flat, recursive);
    }

    #[test]
    fn flat_automaton_image_round_trips_the_exact_interned_quotient() {
        let compiled = SetAutomaton::compile_structural([
            (
                PatternId(7),
                Pattern::app(
                    "pair".to_string(),
                    vec![
                        Pattern::var("x"),
                        Pattern::app("wrap".to_string(), vec![Pattern::var("x")]),
                    ],
                ),
            ),
            (PatternId(11), Pattern::app("wrap".to_string(), vec![Pattern::var("value")])),
        ])
        .expect("recursive patterns compile");

        let restored = SetAutomaton::restore_flat_image(compiled.flat_image())
            .expect("the compiler's canonical image restores");

        assert_eq!(restored, compiled);

        let mut eg = EGraph::new();
        let leaf = leaf(&mut eg, "leaf");
        let wrapped = eg.add(ENode::new("wrap".to_string(), vec![leaf]));
        let _pair = eg.add(ENode::new("pair".to_string(), vec![leaf, wrapped]));
        assert_eq!(restored.search_egraph(&eg), compiled.search_egraph(&eg));
    }

    #[test]
    fn empty_flat_automaton_image_is_the_canonical_empty_automaton() {
        let compiled = SetAutomaton::<String>::compile_structural(std::iter::empty())
            .expect("the empty pattern set compiles");
        let image = compiled.flat_image();
        assert!(image.states.is_empty());
        assert!(image.entries.is_empty());

        let restored =
            SetAutomaton::restore_flat_image(image).expect("the canonical empty image restores");
        assert_eq!(restored, compiled);
    }

    #[test]
    fn bounded_scan_is_exact_at_its_reported_work_boundary() {
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (PatternId(2), Pattern::app("wrap".to_string(), vec![Pattern::var("value")])),
        ])
        .expect("the pattern set compiles");
        let mut eg = EGraph::new();
        let left = leaf(&mut eg, "left");
        let right = leaf(&mut eg, "right");
        let pair = eg.add(ENode::new("pair".to_string(), vec![left, right]));
        let _wrapped = eg.add(ENode::new("wrap".to_string(), vec![pair]));

        let unbounded = automaton.search_egraph(&eg);
        let generous = automaton
            .search_egraph_bounded(&eg, u64::MAX, || false)
            .expect("the generous bounded scan completes");
        assert_eq!(generous.run, unbounded);
        assert!(generous.work > 0);

        let exact = automaton
            .search_egraph_bounded(&eg, generous.work, || false)
            .expect("the exact reported work is sufficient");
        assert_eq!(exact, generous);

        let failure = automaton
            .search_egraph_bounded(&eg, generous.work - 1, || false)
            .expect_err("one unit below the exact work must fail closed");
        assert_eq!(failure.reason, SetAutomatonSearchStop::WorkBudgetExhausted);
        assert!(failure.work <= generous.work - 1);
        assert!(failure.work < generous.work);
    }

    #[test]
    fn bounded_single_root_uses_the_shared_evaluator_without_scanning_unrelated_classes() {
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (PatternId(2), Pattern::app("wrap".to_string(), vec![Pattern::var("value")])),
        ])
        .expect("the pattern set compiles");
        let mut eg = EGraph::new();
        let left = leaf(&mut eg, "left");
        let right = leaf(&mut eg, "right");
        let pair = eg.add(ENode::new("pair".to_string(), vec![left, right]));
        let wrapped = eg.add(ENode::new("wrap".to_string(), vec![pair]));
        for index in 0..128 {
            let _ = leaf(&mut eg, &format!("unrelated-{index}"));
        }

        let whole = automaton
            .search_egraph_bounded(&eg, u64::MAX, || false)
            .expect("whole-graph scan completes");
        let root = automaton
            .search_eclass_bounded(&eg, wrapped, u64::MAX, || false)
            .expect("single-root scan completes");
        let expected = whole
            .run
            .matches
            .iter()
            .filter(|matched| eg.equiv(matched.root, wrapped))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(root.run.matches, expected);
        assert_eq!(root.run.stats.root_classes, 1);
        assert!(root.work < whole.work);

        let exact = automaton
            .search_eclass_bounded(&eg, wrapped, root.work, || false)
            .expect("the reported single-root work is exact");
        assert_eq!(exact, root);
        assert_eq!(
            automaton
                .search_eclass_bounded(&eg, wrapped, root.work - 1, || false)
                .expect_err("one unit below the exact root work must fail closed")
                .reason,
            SetAutomatonSearchStop::WorkBudgetExhausted
        );
    }

    #[test]
    fn bounded_virtual_application_is_equivalent_to_a_singleton_physical_root() {
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(1),
                Pattern::app(
                    "pair".to_string(),
                    vec![
                        Pattern::var("x"),
                        Pattern::app("wrap".to_string(), vec![Pattern::var("x")]),
                    ],
                ),
            ),
            (
                PatternId(2),
                Pattern::app("pair".to_string(), vec![Pattern::var("left"), Pattern::var("right")]),
            ),
            (PatternId(3), Pattern::var("synthetic-root")),
        ])
        .expect("the pattern set compiles");
        let mut eg = EGraph::new();
        let leaf = leaf(&mut eg, "leaf");
        let wrapped = eg.add(ENode::new("wrap".to_string(), vec![leaf]));
        let physical = eg.add(ENode::new("pair".to_string(), vec![leaf, wrapped]));
        let nodes_before = eg.node_count();

        let physical_run = automaton
            .search_eclass_bounded(&eg, physical, u64::MAX, || false)
            .expect("the singleton physical root matches");
        let expected = physical_run
            .run
            .matches
            .into_iter()
            .filter(|matched| matched.pattern != PatternId(3))
            .map(|matched| SetAutomatonApplicationMatch {
                pattern: matched.pattern,
                subst: matched.subst,
            })
            .collect::<Vec<_>>();

        let virtual_run = automaton
            .search_application_bounded(
                &eg,
                &"pair".to_string(),
                &[leaf, wrapped],
                u64::MAX,
                || false,
            )
            .expect("the virtual application matches");
        assert_eq!(virtual_run.run.matches, expected);
        assert_eq!(virtual_run.run.stats.application_roots, 1);
        assert_eq!(virtual_run.run.stats.root_classes, 0);
        assert_eq!(virtual_run.run.stats.root_nodes, 0);
        assert_eq!(eg.node_count(), nodes_before, "virtual matching is read-only");

        let exact = automaton
            .search_application_bounded(
                &eg,
                &"pair".to_string(),
                &[leaf, wrapped],
                virtual_run.work,
                || false,
            )
            .expect("the reported virtual-root work is exact");
        assert_eq!(exact, virtual_run);
        assert_eq!(
            automaton
                .search_application_bounded(
                    &eg,
                    &"pair".to_string(),
                    &[leaf, wrapped],
                    virtual_run.work - 1,
                    || false,
                )
                .expect_err("one unit below exact virtual-root work must fail closed")
                .reason,
            SetAutomatonSearchStop::WorkBudgetExhausted
        );
    }

    #[test]
    fn virtual_application_cancellation_discards_private_matches() {
        let automaton = SetAutomaton::compile_structural([(
            PatternId(1),
            Pattern::app("pair".to_string(), vec![Pattern::var("left"), Pattern::var("right")]),
        )])
        .expect("the pattern compiles");
        let mut eg = EGraph::new();
        let left = leaf(&mut eg, "left");
        let right = leaf(&mut eg, "right");

        let failure = automaton
            .search_application_bounded(&eg, &"pair".to_string(), &[left, right], u64::MAX, || true)
            .expect_err("initial cancellation must fail before publication");
        assert_eq!(failure.reason, SetAutomatonSearchStop::Cancelled);
        assert_eq!(failure.work, 0);
        assert_eq!(failure.stats, SetAutomatonStats::default());
    }

    #[test]
    fn bounded_scan_cancellation_discards_private_matches() {
        let automaton =
            SetAutomaton::compile_structural([(PatternId(1), Pattern::var("everything"))])
                .expect("the variable pattern compiles");
        let mut eg = EGraph::new();
        for index in 0..32 {
            let _ = leaf(&mut eg, &format!("leaf-{index}"));
        }

        let polls = std::cell::Cell::new(0usize);
        let failure = automaton
            .search_egraph_bounded(&eg, u64::MAX, || {
                let poll = polls.get();
                polls.set(poll + 1);
                poll >= 12
            })
            .expect_err("mid-scan cancellation must stop the evaluator");
        assert_eq!(failure.reason, SetAutomatonSearchStop::Cancelled);
        assert!(failure.work > 0, "the cancellation occurred after useful work");

        let immediate = automaton
            .search_egraph_bounded(&eg, u64::MAX, || true)
            .expect_err("initial cancellation must stop before any work");
        assert_eq!(immediate.reason, SetAutomatonSearchStop::Cancelled);
        assert_eq!(immediate.work, 0);
        assert_eq!(immediate.stats, SetAutomatonStats::default());
    }

    #[test]
    fn zero_work_accepts_only_an_empty_scan() {
        let empty = SetAutomaton::<String>::compile_structural(std::iter::empty())
            .expect("the empty automaton compiles");
        let empty_graph = EGraph::<String>::new();
        assert_eq!(
            empty
                .search_egraph_bounded(&empty_graph, 0, || false)
                .expect("empty work completes"),
            BoundedSetAutomatonRun { run: SetAutomatonRun::default(), work: 0 }
        );

        let automaton = SetAutomaton::compile_structural([(PatternId(0), Pattern::var("value"))])
            .expect("the pattern compiles");
        let mut graph = EGraph::new();
        let _ = leaf(&mut graph, "value");
        let failure = automaton
            .search_egraph_bounded(&graph, 0, || false)
            .expect_err("the first charged operation exceeds zero work");
        assert_eq!(
            failure,
            SetAutomatonSearchFailure {
                reason: SetAutomatonSearchStop::WorkBudgetExhausted,
                work: 0,
                stats: SetAutomatonStats::default(),
            }
        );
    }

    #[test]
    fn flat_automaton_image_rejects_noncanonical_slot_interfaces() {
        let skipped_first_slot = FlatAutomatonImage {
            states: vec![
                FlatAutomatonStateImage {
                    slot_count: 1,
                    node: FlatAutomatonNodeImage::Var,
                },
                FlatAutomatonStateImage {
                    slot_count: 2,
                    node: FlatAutomatonNodeImage::App {
                        op: "wrap".to_string(),
                        args: vec![FlatAutomatonInvocationImage {
                            state: 0,
                            parent_slots: vec![1],
                        }],
                    },
                },
            ],
            entries: Vec::new(),
        };
        assert_eq!(
            SetAutomaton::restore_flat_image(skipped_first_slot),
            Err(FlatAutomatonRestoreError::NonCanonicalParentSlot {
                state: 1,
                expected: 0,
                actual: 1,
            })
        );

        let collapsed_child_slots = FlatAutomatonImage {
            states: vec![
                FlatAutomatonStateImage {
                    slot_count: 1,
                    node: FlatAutomatonNodeImage::Var,
                },
                FlatAutomatonStateImage {
                    slot_count: 2,
                    node: FlatAutomatonNodeImage::App {
                        op: "pair".to_string(),
                        args: vec![
                            FlatAutomatonInvocationImage { state: 0, parent_slots: vec![0] },
                            FlatAutomatonInvocationImage { state: 0, parent_slots: vec![1] },
                        ],
                    },
                },
                FlatAutomatonStateImage {
                    slot_count: 1,
                    node: FlatAutomatonNodeImage::App {
                        op: "wrap".to_string(),
                        args: vec![FlatAutomatonInvocationImage {
                            state: 1,
                            parent_slots: vec![0, 0],
                        }],
                    },
                },
            ],
            entries: Vec::new(),
        };
        assert_eq!(
            SetAutomaton::restore_flat_image(collapsed_child_slots),
            Err(FlatAutomatonRestoreError::NonInjectiveInvocation { state: 2, slot: 0 })
        );
    }

    #[test]
    fn flat_pattern_rejects_forward_and_unreachable_nodes() {
        let forward = SetAutomaton::compile_structural_flat([(
            PatternId(2),
            FlatPattern {
                nodes: vec![
                    FlatPatternNode::Var("x".to_string()),
                    FlatPatternNode::App { op: "bad".to_string(), args: vec![1] },
                ],
                root: 1,
            },
        )])
        .expect_err("a forward edge rejects the entire batch");
        assert_eq!(
            forward,
            FlatSetAutomatonError {
                pattern: PatternId(2),
                error: FlatPatternError::ForwardReference { owner: 1, target: 1 },
            }
        );

        let unreachable = SetAutomaton::compile_structural_flat([(
            PatternId(3),
            FlatPattern {
                nodes: vec![
                    FlatPatternNode::Var("unused".to_string()),
                    FlatPatternNode::Var("x".to_string()),
                    FlatPatternNode::App { op: "id".to_string(), args: vec![1] },
                ],
                root: 2,
            },
        )])
        .expect_err("unreachable nodes are non-canonical");
        assert_eq!(unreachable.error, FlatPatternError::UnreachableNode { node: 0 });
    }

    #[test]
    fn flat_pattern_compiler_is_stack_safe_for_deep_chains() {
        let depth = 20_000usize;
        let mut nodes = Vec::with_capacity(depth + 1);
        nodes.push(FlatPatternNode::Var("x".to_string()));
        for index in 1..=depth {
            nodes.push(FlatPatternNode::App {
                op: "step".to_string(),
                args: vec![index - 1],
            });
        }
        let automaton = SetAutomaton::compile_structural_flat([(
            PatternId(0),
            FlatPattern { nodes, root: depth },
        )])
        .expect("a deep flat pattern compiles without native recursion");
        assert_eq!(automaton.view().state_count(), depth + 1);

        let restored = SetAutomaton::restore_flat_image(automaton.flat_image())
            .expect("the deep canonical quotient restores without native recursion");
        assert_eq!(restored, automaton);
    }

    #[test]
    fn view_exposes_the_interned_pattern_dag() {
        // Swap(x, y): one App-rooted entry with two source occurrences sharing
        // the universal Var state; their invocation slot maps remain distinct.
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
                assert!(matches!(view.node(args[0].state()), AutomatonNode::Var));
                assert!(matches!(view.node(args[1].state()), AutomatonNode::Var));
                assert_eq!(args[0].parent_slot(SlotId(0)), SlotId(0));
                assert_eq!(args[1].parent_slot(SlotId(0)), SlotId(1));
            },
            AutomatonNode::Var => panic!("Swap(x, y) root must be an App state"),
        }
        assert_eq!(view.entry_slot_names(0), ["x", "y"]);
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
                args[0].state()
            },
            AutomatonNode::Var => panic!("wrap(...) root must be an App state"),
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
        // reports the interned-DAG size it walks. Variable leaves share one universal
        // state, while the two distinct constructors retain distinct App states.
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
        assert_eq!(view.state_count(), 3, "2 App roots + 1 universal Var state");
    }

    #[test]
    fn alpha_renamed_patterns_share_slot_shaped_states_without_merging_specificity() {
        let mut automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
        ])
        .expect("alpha and specificity corpus compiles");
        assert_eq!(
            automaton.view().state_count(),
            2,
            "the frozen alpha-pair treatment has one Var and one pair state"
        );
        automaton
            .extend([(
                PatternId(2),
                Pattern::app("pair".to_string(), vec![Pattern::var("same"), Pattern::var("same")]),
            )])
            .expect("the specificity control extends atomically");
        let view = automaton.view();

        assert_eq!(view.entry_root_state(0), view.entry_root_state(1));
        assert_ne!(view.entry_root_state(0), view.entry_root_state(2));
        assert_eq!(view.entry_slot_names(0), ["x", "y"]);
        assert_eq!(view.entry_slot_names(1), ["a", "b"]);
        assert_eq!(view.entry_slot_names(2), ["same"]);
        assert_eq!(view.state_slot_count(view.entry_root_state(0)), 2);
        assert_eq!(view.state_slot_count(view.entry_root_state(2)), 1);
        assert_eq!(view.state_count(), 3, "one Var plus linear and diagonal pair states");
    }

    #[test]
    fn alpha_shared_cache_restores_each_entrys_exact_substitution_names() {
        let mut eg = EGraph::new();
        let left = leaf(&mut eg, "left");
        let right = leaf(&mut eg, "right");
        let pair = eg.add(ENode::new("pair".to_string(), vec![left, right]));
        let automaton = SetAutomaton::compile_structural([
            (
                PatternId(0),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
            (
                PatternId(2),
                Pattern::app("pair".to_string(), vec![Pattern::var("same"), Pattern::var("same")]),
            ),
        ])
        .expect("the alpha-sharing match corpus compiles");

        let run = automaton.search_egraph(&eg);
        let at_pair: Vec<&SetAutomatonMatch> = run
            .matches
            .iter()
            .filter(|matched| matched.root == pair)
            .collect();
        assert_eq!(at_pair.len(), 2, "the nonlinear specificity control must reject");
        assert_eq!(at_pair[0].pattern, PatternId(0));
        assert_eq!(at_pair[0].subst.get("x"), Some(&left));
        assert_eq!(at_pair[0].subst.get("y"), Some(&right));
        assert_eq!(at_pair[1].pattern, PatternId(1));
        assert_eq!(at_pair[1].subst.get("a"), Some(&left));
        assert_eq!(at_pair[1].subst.get("b"), Some(&right));
        assert_eq!(run.stats.state_evaluations, 4, "linear root + two Var classes + diagonal root");
        assert!(run.stats.state_cache_hits >= 1, "the second alpha entry reuses the root result");
    }

    #[test]
    fn nominal_name_bearing_control_has_six_states_while_slot_quotient_has_two() {
        let patterns = vec![
            (
                PatternId(0),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
        ];
        assert_eq!(
            nominal_recursive_oracle::state_count(&patterns),
            6,
            "the independent pre-D-E5 name-bearing model allocates four Vars and two Apps"
        );
        assert_eq!(
            SetAutomaton::compile_structural(patterns)
                .expect("the frozen alpha corpus compiles")
                .view()
                .state_count(),
            2,
            "the slot quotient allocates one Var interface and one pair state"
        );
    }

    #[test]
    fn slot_quotient_matches_independent_nominal_equations_exactly() {
        let patterns = vec![
            (PatternId(0), Pattern::var("whole")),
            (
                PatternId(1),
                Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]),
            ),
            (
                PatternId(2),
                Pattern::app("pair".to_string(), vec![Pattern::var("a"), Pattern::var("b")]),
            ),
            (
                PatternId(3),
                Pattern::app("pair".to_string(), vec![Pattern::var("same"), Pattern::var("same")]),
            ),
            (
                PatternId(4),
                Pattern::app(
                    "wrap".to_string(),
                    vec![Pattern::app(
                        "pair".to_string(),
                        vec![Pattern::var("deep"), Pattern::var("deep")],
                    )],
                ),
            ),
        ];
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let pair_aa = eg.add(ENode::new("pair".to_string(), vec![a, a]));
        let pair_ab = eg.add(ENode::new("pair".to_string(), vec![a, b]));
        let _wrap_aa = eg.add(ENode::new("wrap".to_string(), vec![pair_aa]));
        let _wrap_ab = eg.add(ENode::new("wrap".to_string(), vec![pair_ab]));

        let actual = SetAutomaton::compile_structural(patterns.clone())
            .expect("the bounded nominal-equivalence corpus compiles")
            .search_egraph(&eg)
            .matches;
        let expected = nominal_recursive_oracle::search_egraph(&patterns, &eg);
        assert_eq!(
            actual, expected,
            "slot caching, nonlinear partitions, alpha sharing, output names, and match order"
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
    fn evaluator_pda_matches_bounded_recursive_equations_exactly() {
        let mut eg = EGraph::new();
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let pair_ab = eg.add(ENode::new("pair".to_string(), vec![a, b]));
        let pair_ba = eg.add(ENode::new("pair".to_string(), vec![b, a]));
        eg.merge(pair_ab, pair_ba);
        eg.rebuild();
        let pair = eg.find(pair_ab);
        let _wrap = eg.add(ENode::new("wrap".to_string(), vec![pair]));

        let shared_pair =
            Pattern::app("pair".to_string(), vec![Pattern::var("x"), Pattern::var("y")]);
        let automaton = SetAutomaton::compile_structural([
            (PatternId(0), Pattern::var("root")),
            (PatternId(1), shared_pair.clone()),
            (PatternId(2), Pattern::app("wrap".to_string(), vec![shared_pair])),
            (
                PatternId(3),
                Pattern::app("pair".to_string(), vec![Pattern::var("same"), Pattern::var("same")]),
            ),
            (PatternId(4), Pattern::app("a".to_string(), Vec::new())),
        ])
        .expect("the bounded positional corpus compiles");

        assert_eq!(
            automaton.search_egraph(&eg),
            eval_recursive_oracle::search_egraph(&automaton, &eg),
            "the PDA preserves match ordering, substitutions, and cache statistics"
        );
    }

    #[test]
    fn evaluator_pda_is_stack_safe_at_twenty_thousand_levels() {
        std::thread::Builder::new()
            .name("set-automaton-deep-pda".to_string())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 20_000;

                let mut eg = EGraph::new();
                let mut subject = leaf(&mut eg, "leaf");
                for _ in 0..DEPTH {
                    subject = eg.add(ENode::new("S".to_string(), vec![subject]));
                }
                let root = eg.add(ENode::new("Root".to_string(), vec![subject]));

                let mut pattern = Pattern::var("x");
                for _ in 0..DEPTH {
                    pattern = Pattern::app("S".to_string(), vec![pattern]);
                }
                pattern = Pattern::app("Root".to_string(), vec![pattern]);
                let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                    .expect("the deep positional pattern compiles");

                let run = automaton.search_egraph(&eg);
                assert_eq!(run.matches.len(), 1);
                assert_eq!(run.matches[0].root, root);
                assert_eq!(run.stats.candidate_evaluations, 1);
                assert_eq!(run.stats.state_evaluations, DEPTH + 2);
            })
            .expect("the bounded-stack worker starts")
            .join()
            .expect("the evaluator PDA completes without stack overflow");
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

        /// Bounded independent differential: the slot quotient must return the
        /// exact ordered name-bearing substitutions of the pre-quotient equations.
        #[test]
        fn prop_slot_quotient_matches_nominal_equations(
            names in proptest::collection::vec(0usize..4, 1..18),
            shapes in proptest::collection::vec(0usize..5, 1..18),
        ) {
            let count = names.len().min(shapes.len());
            let patterns: Vec<(PatternId, Pattern<String>)> = (0..count)
                .map(|index| {
                    let left = format!("v{}", names[index]);
                    let right = format!("v{}", (names[index] + 1) % 4);
                    let pattern = match shapes[index] {
                        0 => Pattern::var(left),
                        1 => Pattern::app(
                            "pair".to_string(),
                            vec![Pattern::var(left.clone()), Pattern::var(left)],
                        ),
                        2 => Pattern::app(
                            "pair".to_string(),
                            vec![Pattern::var(left), Pattern::var(right)],
                        ),
                        3 => Pattern::app(
                            "wrap".to_string(),
                            vec![Pattern::app(
                                "pair".to_string(),
                                vec![Pattern::var(left), Pattern::var(right)],
                            )],
                        ),
                        _ => Pattern::app("unary".to_string(), vec![Pattern::var(left)]),
                    };
                    (PatternId(index), pattern)
                })
                .collect();

            let mut eg = EGraph::new();
            let leaves: Vec<EClassId> = (0..4)
                .map(|index| leaf(&mut eg, &format!("leaf{index}")))
                .collect();
            for &left in &leaves {
                for &right in &leaves {
                    let pair = eg.add(ENode::new("pair".to_string(), vec![left, right]));
                    let _ = eg.add(ENode::new("wrap".to_string(), vec![pair]));
                }
                let _ = eg.add(ENode::new("unary".to_string(), vec![left]));
            }

            let actual = SetAutomaton::compile_structural(patterns.clone())
                .expect("the generated corpus is positional")
                .search_egraph(&eg)
                .matches;
            let expected = nominal_recursive_oracle::search_egraph(&patterns, &eg);
            proptest::prop_assert_eq!(actual, expected);
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
