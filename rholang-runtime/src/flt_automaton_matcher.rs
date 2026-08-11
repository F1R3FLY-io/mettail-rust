//! Retained set-automaton matching for reflected Foreign Language Term receives.
//!
//! The RSpace matcher boundary is the only production seam that can accelerate
//! an FLT receive without changing RSpace candidate selection or receive
//! atomicity. This module therefore retains one Dovetail [`SetAutomaton`] per
//! matcher, interns eligible reflected positional patterns in canonical order,
//! and lowers only newly interned [`StateId`]s into a compact matcher-owned PDA.
//! Patterns outside the proved positional envelope are declined; the caller
//! delegates them to f1r3node's spatial matcher unchanged.
//!
//! No `Par` is serialized on the matching hot path. Reflected operators are
//! identified by the exact private-name bytes already present in the model, and
//! successful matching clones only the actual free-variable captures.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, RwLock};

use dovetail::rules::Pattern;
use dovetail::set_automaton::{AutomatonNode, PatternId, SetAutomaton, SlotId, StateInvocation};
use mettail_rholang_codegen::parse_reflected_tag;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{BindPattern, EList, ListParWithRandom, Par};
use models::rust::rholang::par_children::visit_canonical_par_tree;
use prost::Message;

/// Observable state of the retained FLT matcher.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FltAutomatonStats {
    /// Exact eligible bind patterns retained by this matcher.
    pub registered_patterns: usize,
    /// Canonical Dovetail states after structural interning.
    pub automaton_states: usize,
    /// States serialized into the matcher-owned PDA.
    pub serialized_states: usize,
    /// Calls to `SetAutomaton::extend` after the initial compilation.
    pub extensions: usize,
    /// Patterns first registered by whole-program preparation.
    pub prepared_registrations: usize,
    /// Patterns first encountered through the defensive lazy path.
    pub lazy_registrations: usize,
    /// Eligible matches completed by the PDA.
    pub fast_matches: usize,
    /// Eligible patterns for which the PDA proved no match.
    pub fast_misses: usize,
    /// Patterns outside the eligibility envelope and delegated unchanged.
    pub spatial_fallbacks: usize,
}

#[derive(Default)]
struct MatchCounters {
    fast_matches: AtomicUsize,
    fast_misses: AtomicUsize,
    spatial_fallbacks: AtomicUsize,
}

/// The outcome of asking the retained matcher to handle one RSpace candidate.
pub(crate) enum FltMatchDecision {
    /// The pattern is outside the proved envelope; use the spatial matcher.
    Declined,
    /// The pattern is eligible and the candidate does not match it.
    Miss,
    /// The eligible pattern matched and produced its ordered captures.
    Match(ListParWithRandom),
}

/// Exact operator labels for the reflected positional subset.
///
/// A list and a private-name leaf with the same `GPrivate.id` are distinct
/// symbols. Concrete lists retain the metadata that f1r3node's concrete
/// `match_pars` path compares; dynamic lists deliberately omit that metadata
/// because its structural matcher omits it once a nested binder is present.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ReflectedOp {
    DynamicList {
        private_id: Box<[u8]>,
    },
    ConcreteList {
        private_id: Box<[u8]>,
        par_connective_used: bool,
        list_locally_free: Box<[u8]>,
        list_connective_used: bool,
    },
    Private {
        private_id: Box<[u8]>,
        par_connective_used: bool,
    },
    /// A Dovetail nullary application used as a zero-slot match-any state.
    /// Free variables remain `Pattern::Var`; separating the two preserves the
    /// spatial matcher's rule that only a wildcard may match an open target.
    Wildcard,
}

#[derive(Clone, Debug)]
struct SerializedInvocation {
    state: usize,
    parent_slots: Box<[usize]>,
}

#[derive(Clone, Debug)]
enum SerializedState {
    Var,
    App {
        op: ReflectedOp,
        args: Box<[SerializedInvocation]>,
        slot_count: usize,
    },
}

#[derive(Clone, Debug)]
struct RegisteredEntry {
    root_state: usize,
    /// Root slot to Rholang `FreeVar` level. Wildcards have no slots.
    free_levels: Box<[usize]>,
    free_count: usize,
}

#[derive(Default)]
struct MatcherState {
    automaton: Option<SetAutomaton<ReflectedOp>>,
    program: Vec<SerializedState>,
    entries: Vec<RegisteredEntry>,
    lookup: BTreeMap<BindPattern, usize>,
    extensions: usize,
    prepared_registrations: usize,
    lazy_registrations: usize,
}

struct MatcherInner {
    state: RwLock<MatcherState>,
    counters: MatchCounters,
}

/// Cloneable handle on the retained automaton and its append-only serializer.
#[derive(Clone)]
pub struct FltAutomatonMatcher {
    inner: Arc<MatcherInner>,
}

impl Default for FltAutomatonMatcher {
    fn default() -> Self {
        Self {
            inner: Arc::new(MatcherInner {
                state: RwLock::new(MatcherState::default()),
                counters: MatchCounters::default(),
            }),
        }
    }
}

impl FltAutomatonMatcher {
    /// Register every eligible receive pattern reachable from `program`.
    ///
    /// Patterns are sorted by their exact model ordering before registration,
    /// so equivalent whole programs produce the same entry and StateId order
    /// regardless of receive discovery order. Ineligible patterns are ignored
    /// here and remain on the spatial path when RSpace later presents them.
    pub fn prepare(&self, program: &Par) -> Result<usize, String> {
        let mut candidates = Vec::<(BindPattern, ConvertedPattern)>::new();
        visit_canonical_par_tree(program, |par| {
            for receive in &par.receives {
                for bind in &receive.binds {
                    let pattern = BindPattern {
                        patterns: bind.patterns.clone(),
                        remainder: bind.remainder.clone(),
                        free_count: bind.free_count,
                    };
                    if let Ok(converted) = convert_pattern(&pattern) {
                        candidates.push((pattern, converted));
                    }
                }
            }
        })
        .map_err(|error| {
            format!("cannot traverse program while preparing FLT patterns: {error}")
        })?;

        candidates.sort_by(|left, right| left.0.cmp(&right.0));
        candidates.dedup_by(|left, right| left.0 == right.0);

        let mut state = self
            .inner
            .state
            .write()
            .expect("the retained FLT matcher lock is not poisoned");
        candidates.retain(|(pattern, _)| !state.lookup.contains_key(pattern));
        let inserted = candidates.len();
        state.register_many(candidates);
        state.prepared_registrations += inserted;
        Ok(inserted)
    }

    /// Snapshot the retained structure and diagnostic counters.
    #[must_use]
    pub fn stats(&self) -> FltAutomatonStats {
        let state = self
            .inner
            .state
            .read()
            .expect("the retained FLT matcher lock is not poisoned");
        let automaton_states = state
            .automaton
            .as_ref()
            .map_or(0, |automaton| automaton.view().state_count());
        FltAutomatonStats {
            registered_patterns: state.entries.len(),
            automaton_states,
            serialized_states: state.program.len(),
            extensions: state.extensions,
            prepared_registrations: state.prepared_registrations,
            lazy_registrations: state.lazy_registrations,
            fast_matches: self.inner.counters.fast_matches.load(Ordering::Relaxed),
            fast_misses: self.inner.counters.fast_misses.load(Ordering::Relaxed),
            spatial_fallbacks: self
                .inner
                .counters
                .spatial_fallbacks
                .load(Ordering::Relaxed),
        }
    }

    /// Stable diagnostic fingerprint of the retained matcher layout.
    ///
    /// The fingerprint covers the exact-pattern lookup order, every serialized
    /// state and child-slot renaming, and every entry-root/free-level boundary.
    /// It is deliberately not a consensus value: its purpose is to make the
    /// canonical-registration and suffix-only-serialization invariants directly
    /// testable without exposing mutable automaton internals.
    #[must_use]
    pub fn layout_fingerprint(&self) -> [u8; 32] {
        let state = self
            .inner
            .state
            .read()
            .expect("the retained FLT matcher lock is not poisoned");
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"mettail.flt-automaton-layout.v1\0");

        append_len(&mut bytes, state.lookup.len());
        for (pattern, entry) in &state.lookup {
            append_len(&mut bytes, *entry);
            let encoded = pattern.encode_to_vec();
            append_slice(&mut bytes, &encoded);
        }

        append_len(&mut bytes, state.program.len());
        for serialized in &state.program {
            match serialized {
                SerializedState::Var => bytes.push(0),
                SerializedState::App { op, args, slot_count } => {
                    bytes.push(1);
                    append_reflected_op(&mut bytes, op);
                    append_len(&mut bytes, *slot_count);
                    append_len(&mut bytes, args.len());
                    for invocation in args.iter() {
                        append_len(&mut bytes, invocation.state);
                        append_len(&mut bytes, invocation.parent_slots.len());
                        for slot in invocation.parent_slots.iter() {
                            append_len(&mut bytes, *slot);
                        }
                    }
                },
            }
        }

        append_len(&mut bytes, state.entries.len());
        for entry in &state.entries {
            append_len(&mut bytes, entry.root_state);
            append_len(&mut bytes, entry.free_count);
            append_len(&mut bytes, entry.free_levels.len());
            for level in entry.free_levels.iter() {
                append_len(&mut bytes, *level);
            }
        }

        rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash::new(&bytes)
            .bytes()
            .try_into()
            .expect("Blake2b-256 always produces 32 bytes")
    }

    pub(crate) fn get(&self, pattern: &BindPattern, data: &ListParWithRandom) -> FltMatchDecision {
        let entry_index = {
            let state = self
                .inner
                .state
                .read()
                .expect("the retained FLT matcher lock is not poisoned");
            state.lookup.get(pattern).copied()
        };

        let entry_index = match entry_index {
            Some(entry) => entry,
            None => {
                let converted = match convert_pattern(pattern) {
                    Ok(converted) => converted,
                    Err(_) => {
                        self.inner
                            .counters
                            .spatial_fallbacks
                            .fetch_add(1, Ordering::Relaxed);
                        return FltMatchDecision::Declined;
                    },
                };
                let mut state = self
                    .inner
                    .state
                    .write()
                    .expect("the retained FLT matcher lock is not poisoned");
                match state.lookup.get(pattern).copied() {
                    Some(entry) => entry,
                    None => {
                        let entry = state.register(pattern.clone(), converted);
                        state.lazy_registrations += 1;
                        entry
                    },
                }
            },
        };

        let Some(target) = data.pars.first().filter(|_| data.pars.len() == 1) else {
            self.inner
                .counters
                .spatial_fallbacks
                .fetch_add(1, Ordering::Relaxed);
            return FltMatchDecision::Declined;
        };

        let matched = {
            let state = self
                .inner
                .state
                .read()
                .expect("the retained FLT matcher lock is not poisoned");
            let entry = &state.entries[entry_index];
            execute_program(&state.program, entry, target).map(|captures| ListParWithRandom {
                pars: captures,
                random_state: data.random_state.clone(),
            })
        };

        match matched {
            Some(matched) => {
                self.inner
                    .counters
                    .fast_matches
                    .fetch_add(1, Ordering::Relaxed);
                FltMatchDecision::Match(matched)
            },
            None => {
                self.inner
                    .counters
                    .fast_misses
                    .fetch_add(1, Ordering::Relaxed);
                FltMatchDecision::Miss
            },
        }
    }
}

fn append_len(bytes: &mut Vec<u8>, value: usize) {
    bytes.extend_from_slice(
        &u64::try_from(value)
            .expect("a Rust collection length fits in u64")
            .to_le_bytes(),
    );
}

fn append_slice(bytes: &mut Vec<u8>, value: &[u8]) {
    append_len(bytes, value.len());
    bytes.extend_from_slice(value);
}

fn append_reflected_op(bytes: &mut Vec<u8>, op: &ReflectedOp) {
    match op {
        ReflectedOp::DynamicList { private_id } => {
            bytes.push(0);
            append_slice(bytes, private_id);
        },
        ReflectedOp::ConcreteList {
            private_id,
            par_connective_used,
            list_locally_free,
            list_connective_used,
        } => {
            bytes.push(1);
            append_slice(bytes, private_id);
            bytes.push(u8::from(*par_connective_used));
            append_slice(bytes, list_locally_free);
            bytes.push(u8::from(*list_connective_used));
        },
        ReflectedOp::Private { private_id, par_connective_used } => {
            bytes.push(2);
            append_slice(bytes, private_id);
            bytes.push(u8::from(*par_connective_used));
        },
        ReflectedOp::Wildcard => bytes.push(3),
    }
}

impl MatcherState {
    fn register(&mut self, pattern: BindPattern, converted: ConvertedPattern) -> usize {
        let entry_index = self.entries.len();
        self.register_many(vec![(pattern, converted)]);
        entry_index
    }

    /// Compile or extend one canonical batch, then serialize its shared state
    /// suffix exactly once.  Whole-program preparation therefore pays one
    /// automaton pass and one view pass rather than repeating both per receive.
    fn register_many(&mut self, patterns: Vec<(BindPattern, ConvertedPattern)>) {
        if patterns.is_empty() {
            return;
        }

        let first_entry = self.entries.len();
        let mut metadata = Vec::with_capacity(patterns.len());
        let mut automaton_patterns = Vec::with_capacity(patterns.len());
        for (offset, (pattern, converted)) in patterns.into_iter().enumerate() {
            let entry_index = first_entry + offset;
            metadata.push((pattern, converted.free_count));
            automaton_patterns.push((PatternId(entry_index), converted.pattern));
        }

        match self.automaton.as_mut() {
            Some(automaton) => {
                automaton
                    .extend(automaton_patterns)
                    .expect("the FLT converter emits no associative-commutative pattern");
                self.extensions += 1;
            },
            None => {
                self.automaton = Some(
                    SetAutomaton::compile_structural(automaton_patterns)
                        .expect("the FLT converter emits no associative-commutative pattern"),
                );
            },
        }

        self.serialize_new_states();
        let automaton = self
            .automaton
            .as_ref()
            .expect("registration creates the retained automaton");
        let view = automaton.view();
        debug_assert_eq!(view.entry_count(), first_entry + metadata.len());
        for (offset, (pattern, free_count)) in metadata.into_iter().enumerate() {
            let automaton_entry = first_entry + offset;
            debug_assert_eq!(view.entry_id(automaton_entry), PatternId(automaton_entry));

            let mut free_levels = Vec::with_capacity(view.entry_slot_names(automaton_entry).len());
            for name in view.entry_slot_names(automaton_entry) {
                let level = name
                    .strip_prefix("free:")
                    .and_then(|level| level.parse::<usize>().ok())
                    .expect("only free-variable names occupy an FLT root slot");
                free_levels.push(level);
            }
            debug_assert_eq!(free_levels.len(), free_count);

            self.entries.push(RegisteredEntry {
                root_state: view.entry_root_state(automaton_entry).index(),
                free_levels: free_levels.into_boxed_slice(),
                free_count,
            });
            self.lookup.insert(pattern, automaton_entry);
        }
    }

    fn serialize_new_states(&mut self) {
        let first_new = self.program.len();
        let automaton = self
            .automaton
            .as_ref()
            .expect("state serialization follows automaton creation");
        let view = automaton.view();
        let mut suffix = Vec::with_capacity(view.state_count() - first_new);
        for state in view.state_ids().skip(first_new) {
            debug_assert_eq!(state.index(), first_new + suffix.len());
            suffix.push(match view.node(state) {
                AutomatonNode::Var => SerializedState::Var,
                AutomatonNode::App { op, args } => SerializedState::App {
                    op: op.clone(),
                    args: args.iter().map(serialize_invocation).collect(),
                    slot_count: view.state_slot_count(state),
                },
            });
        }
        self.program.extend(suffix);
        debug_assert_eq!(self.program.len(), view.state_count());
    }
}

fn serialize_invocation(invocation: &StateInvocation) -> SerializedInvocation {
    SerializedInvocation {
        state: invocation.state().index(),
        parent_slots: invocation.parent_slots().map(SlotId::index).collect(),
    }
}

struct ConvertedPattern {
    pattern: Pattern<ReflectedOp>,
    free_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConversionError {
    Envelope,
    Shape,
    ForeignFingerprint,
    FreeVariable,
}

fn convert_pattern(pattern: &BindPattern) -> Result<ConvertedPattern, ConversionError> {
    let free_count = usize::try_from(pattern.free_count).map_err(|_| ConversionError::Envelope)?;
    let [root] = pattern.patterns.as_slice() else {
        return Err(ConversionError::Envelope);
    };
    if pattern.remainder.is_some() || reflected_list(root).is_none() {
        return Err(ConversionError::Envelope);
    }

    enum Task<'a> {
        Visit(&'a Par),
        Assemble {
            par: &'a Par,
            list: &'a EList,
            private_id: Box<[u8]>,
            child_count: usize,
        },
    }

    let mut tasks = vec![Task::Visit(root)];
    let mut values = Vec::<(Pattern<ReflectedOp>, bool)>::new();
    let mut fingerprint: Option<String> = None;
    let mut seen_free = vec![false; free_count];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(par) => {
                if let Some(var) = pattern_var(par) {
                    match var {
                        VarInstance::FreeVar(level) => {
                            let level = usize::try_from(*level)
                                .map_err(|_| ConversionError::FreeVariable)?;
                            let Some(seen) = seen_free.get_mut(level) else {
                                return Err(ConversionError::FreeVariable);
                            };
                            if std::mem::replace(seen, true) {
                                return Err(ConversionError::FreeVariable);
                            }
                            values.push((Pattern::Var(format!("free:{level}")), true));
                        },
                        VarInstance::Wildcard(_) => values.push((
                            Pattern::App {
                                op: ReflectedOp::Wildcard,
                                args: Vec::new(),
                            },
                            true,
                        )),
                        VarInstance::BoundVar(_) => return Err(ConversionError::Shape),
                    }
                    continue;
                }

                if let Some(list) = reflected_list(par) {
                    let Some(head) = list.ps.first() else {
                        return Err(ConversionError::Shape);
                    };
                    let private_id = validated_private_id(head, &mut fingerprint)?;
                    tasks.push(Task::Assemble {
                        par,
                        list,
                        private_id,
                        child_count: list.ps.len() - 1,
                    });
                    tasks.extend(list.ps[1..].iter().rev().map(Task::Visit));
                    continue;
                }

                if let Some(private_id) = private_id(par) {
                    validate_fingerprint(private_id, &mut fingerprint)?;
                    values.push((
                        Pattern::App {
                            op: ReflectedOp::Private {
                                private_id: private_id.into(),
                                par_connective_used: par.connective_used,
                            },
                            args: Vec::new(),
                        },
                        false,
                    ));
                    continue;
                }
                return Err(ConversionError::Shape);
            },
            Task::Assemble { par, list, private_id, child_count } => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("the FLT conversion PDA retains every child result");
                let children = values.split_off(first_child);
                let dynamic = children.iter().any(|(_, dynamic)| *dynamic);
                if dynamic && (!par.connective_used || !list.connective_used) {
                    return Err(ConversionError::Shape);
                }
                let op = if dynamic {
                    ReflectedOp::DynamicList { private_id }
                } else {
                    ReflectedOp::ConcreteList {
                        private_id,
                        par_connective_used: par.connective_used,
                        list_locally_free: list.locally_free.clone().into_boxed_slice(),
                        list_connective_used: list.connective_used,
                    }
                };
                values.push((
                    Pattern::App {
                        op,
                        args: children.into_iter().map(|(pattern, _)| pattern).collect(),
                    },
                    dynamic,
                ));
            },
        }
    }

    if !seen_free.into_iter().all(|seen| seen) || values.len() != 1 {
        return Err(ConversionError::FreeVariable);
    }
    let (pattern, _) = values
        .pop()
        .expect("the FLT conversion PDA produces one root");
    Ok(ConvertedPattern { pattern, free_count })
}

fn validate_fingerprint(
    private_id: &[u8],
    expected: &mut Option<String>,
) -> Result<(), ConversionError> {
    let tag = String::decode(private_id).map_err(|_| ConversionError::Shape)?;
    let (fingerprint, _) = parse_reflected_tag(&tag).ok_or(ConversionError::Shape)?;
    match expected {
        Some(expected) if expected != fingerprint => Err(ConversionError::ForeignFingerprint),
        Some(_) => Ok(()),
        None => {
            *expected = Some(fingerprint.to_string());
            Ok(())
        },
    }
}

fn validated_private_id(
    par: &Par,
    fingerprint: &mut Option<String>,
) -> Result<Box<[u8]>, ConversionError> {
    let id = private_id(par).ok_or(ConversionError::Shape)?;
    validate_fingerprint(id, fingerprint)?;
    Ok(id.into())
}

fn par_has_no_process_fields(par: &Par) -> bool {
    par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
}

fn reflected_list(par: &Par) -> Option<&EList> {
    if !par_has_no_process_fields(par) || !par.unforgeables.is_empty() {
        return None;
    }
    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    match expr.expr_instance.as_ref()? {
        ExprInstance::EListBody(list) if list.remainder.is_none() => Some(list),
        _ => None,
    }
}

fn pattern_var(par: &Par) -> Option<&VarInstance> {
    if !par_has_no_process_fields(par) || !par.unforgeables.is_empty() || !par.connective_used {
        return None;
    }
    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    let ExprInstance::EVarBody(var) = expr.expr_instance.as_ref()? else {
        return None;
    };
    var.v.as_ref()?.var_instance.as_ref()
}

fn private_id(par: &Par) -> Option<&[u8]> {
    if !par_has_no_process_fields(par) || !par.exprs.is_empty() {
        return None;
    }
    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(private) => Some(private.id.as_slice()),
        _ => None,
    }
}

enum TargetArgs<'a> {
    Empty,
    List(&'a [Par]),
}

impl<'a> TargetArgs<'a> {
    fn len(&self) -> usize {
        match self {
            TargetArgs::Empty => 0,
            TargetArgs::List(args) => args.len(),
        }
    }
}

impl ReflectedOp {
    fn target_args<'a>(&self, target: &'a Par) -> Option<TargetArgs<'a>> {
        match self {
            ReflectedOp::Wildcard => Some(TargetArgs::Empty),
            ReflectedOp::Private {
                private_id: expected,
                par_connective_used,
            } => (target.connective_used == *par_connective_used
                && private_id(target) == Some(expected.as_ref()))
            .then_some(TargetArgs::Empty),
            ReflectedOp::DynamicList { private_id: expected } => {
                let list = reflected_list(target)?;
                (private_id(list.ps.first()?) == Some(expected.as_ref()))
                    .then(|| TargetArgs::List(&list.ps[1..]))
            },
            ReflectedOp::ConcreteList {
                private_id: expected,
                par_connective_used,
                list_locally_free,
                list_connective_used,
            } => {
                let list = reflected_list(target)?;
                (target.connective_used == *par_connective_used
                    && list.locally_free.as_slice() == list_locally_free.as_ref()
                    && list.connective_used == *list_connective_used
                    && private_id(list.ps.first()?) == Some(expected.as_ref()))
                .then(|| TargetArgs::List(&list.ps[1..]))
            },
        }
    }
}

fn execute_program(
    program: &[SerializedState],
    entry: &RegisteredEntry,
    target: &Par,
) -> Option<Vec<Par>> {
    /// One suspended application.  Four machine words are sufficient: the
    /// state identifies its serialized invocations, `target_args` borrows the
    /// reflected children, and the other two indices select the next child and
    /// this frame's region in the shared slot arena.
    struct Frame<'a> {
        state: usize,
        target_args: &'a [Par],
        next_arg: usize,
        slot_base: usize,
    }

    /// A completed child result.  Application captures already occupy a
    /// contiguous region of `slots`; variables and nullary applications need
    /// no temporary allocation at all.
    enum ChildResult<'a> {
        Empty,
        Var(&'a Par),
        Slots { base: usize, len: usize },
    }

    let mut frames = Vec::<Frame<'_>>::new();
    let mut slots = Vec::<Option<&Par>>::new();
    let mut current_state = entry.root_state;
    let mut current_target = target;

    let root = 'evaluate: loop {
        let mut child = match &program[current_state] {
            SerializedState::Var => {
                if !current_target.locally_free.is_empty() {
                    return None;
                }
                ChildResult::Var(current_target)
            },
            SerializedState::App { op, args, slot_count } => {
                let target_args = op.target_args(current_target)?;
                if target_args.len() != args.len() {
                    return None;
                }
                if args.is_empty() {
                    ChildResult::Empty
                } else {
                    let TargetArgs::List(target_args) = target_args else {
                        unreachable!("only reflected lists have child states")
                    };
                    let slot_base = slots.len();
                    slots.resize(slot_base + *slot_count, None);
                    frames.push(Frame {
                        state: current_state,
                        target_args,
                        next_arg: 0,
                        slot_base,
                    });
                    current_state = args[0].state;
                    current_target = &target_args[0];
                    continue 'evaluate;
                }
            },
        };

        loop {
            let Some(frame) = frames.last_mut() else {
                break 'evaluate child;
            };
            let SerializedState::App { args, slot_count, .. } = &program[frame.state] else {
                unreachable!("only application states create FLT continuation frames")
            };
            let invocation = &args[frame.next_arg];
            let child_len = match child {
                ChildResult::Empty => 0,
                ChildResult::Var(_) => 1,
                ChildResult::Slots { len, .. } => len,
            };
            debug_assert_eq!(child_len, invocation.parent_slots.len());

            for (child_slot, &parent_slot) in invocation.parent_slots.iter().enumerate() {
                let captured = match child {
                    ChildResult::Empty => unreachable!("an empty result has no slot mapping"),
                    ChildResult::Var(captured) => {
                        debug_assert_eq!(child_slot, 0);
                        captured
                    },
                    ChildResult::Slots { base, .. } => {
                        slots[base + child_slot].expect("every canonical child slot is assigned")
                    },
                };
                let parent = &mut slots[frame.slot_base + parent_slot];
                match *parent {
                    Some(existing) if existing != captured => return None,
                    Some(_) => {},
                    None => *parent = Some(captured),
                }
            }

            if let ChildResult::Slots { base, .. } = child {
                debug_assert!(base >= frame.slot_base + *slot_count);
                slots.truncate(base);
            }

            frame.next_arg += 1;
            if frame.next_arg < args.len() {
                current_state = args[frame.next_arg].state;
                current_target = &frame.target_args[frame.next_arg];
                continue 'evaluate;
            }

            child = ChildResult::Slots { base: frame.slot_base, len: *slot_count };
            frames.pop();
        }
    };

    let capture = |slot: usize| match root {
        ChildResult::Empty => None,
        ChildResult::Var(captured) => (slot == 0).then_some(captured),
        ChildResult::Slots { base, len } => (slot < len).then(|| slots[base + slot]).flatten(),
    };
    let mut bound = vec![None; entry.free_count];
    for (slot, &level) in entry.free_levels.iter().enumerate() {
        bound[level] = Some(capture(slot)?.clone());
    }
    bound.into_iter().collect::<Option<Vec<_>>>()
}
