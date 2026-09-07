//! Grammar-derived, stack-safe admission of reflected run-time syntax values.
//!
//! A reflected private constructor tag proves only language identity.  It does
//! not prove that an attacker-reassembled `Par` is a well-formed member of a
//! guest category.  This module compiles GrammarCore's declarative reductions
//! into a finite family of structural type states and checks the complete Rho
//! image with an explicit proof-search worklist.  Construction and negative FLT
//! capture therefore share one fail-closed category boundary.

use crate::dynamic_reflection::{
    BAG_LABEL, BOOLEAN_LABEL, INTEGER_LABEL, LIST_LABEL, PATHMAP_LABEL, SEQUENCE_LABEL, TEXT_LABEL,
    UNIT_LABEL,
};
use crate::rho_net_lower::BYTES_REFLECT_LABEL;
use crate::{ac_soup_channel, is_ground_marker_par, is_marked_object_label, parse_reflected_tag};
use mettail_grammar_core::{
    runtime_token_output_contract, BuiltinCarrier, Carrier, CategoryId, CollectionKind,
    FieldSource, GrammarCoreV1, RuntimeNativeValueKind, RuntimeTokenOutputContract, SyntaxItem,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::Par;
use prost::Message;
use std::collections::{BTreeMap, HashMap};

type StateId = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DynamicAdmissionCompileError {
    MissingIdentifierToken,
    MissingReduction(u32),
    MissingInput { reduction: u32, input: u16 },
    UnsupportedSyntax(&'static str),
    InvalidMappedLayout,
    TooManyStates,
}

impl std::fmt::Display for DynamicAdmissionCompileError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingIdentifierToken => {
                formatter.write_str("capture-ident syntax has no identifier token")
            },
            Self::MissingReduction(index) => write!(formatter, "missing reduction {index}"),
            Self::MissingInput { reduction, input } => {
                write!(formatter, "reduction {reduction} names missing semantic input {input}")
            },
            Self::UnsupportedSyntax(kind) => {
                write!(formatter, "{kind} is valid only inside separated mapped syntax")
            },
            Self::InvalidMappedLayout => {
                formatter.write_str("mapped separated syntax has incompatible slot layout")
            },
            Self::TooManyStates => formatter.write_str("dynamic admission automaton exceeds u32"),
        }
    }
}

impl std::error::Error for DynamicAdmissionCompileError {}

/// Why structural category membership could not be established or refuted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynamicAdmissionUnknown {
    WorkLimit,
    UnavailableContract,
}

/// A failed proof is not necessarily a proof of non-membership. Existing
/// boolean consumers accept only `Admitted`; semantic services can retain the
/// distinction between a malformed term and an unavailable judgment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynamicAdmissionDecision {
    Admitted,
    Rejected,
    Undetermined(DynamicAdmissionUnknown),
}

impl From<bool> for DynamicAdmissionDecision {
    fn from(value: bool) -> Self {
        if value {
            Self::Admitted
        } else {
            Self::Rejected
        }
    }
}

impl DynamicAdmissionDecision {
    fn conjunction(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rejected, _) | (_, Self::Rejected) => Self::Rejected,
            (Self::Undetermined(reason), _) | (_, Self::Undetermined(reason)) => {
                Self::Undetermined(reason)
            },
            (Self::Admitted, Self::Admitted) => Self::Admitted,
        }
    }

    fn alternative(self, other: Self) -> Self {
        match (self, other) {
            (Self::Admitted, _) | (_, Self::Admitted) => Self::Admitted,
            (Self::Undetermined(reason), _) | (_, Self::Undetermined(reason)) => {
                Self::Undetermined(reason)
            },
            (Self::Rejected, Self::Rejected) => Self::Rejected,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Shape {
    Any,
    Never,
    Unavailable,
    Category(CategoryId),
    Text,
    Integer,
    Boolean,
    Bytes,
    Unit,
    Sequence(Vec<StateId>),
    OptionalSequence(StateId),
    Collection {
        kind: CollectionKind,
        entry: Vec<StateId>,
    },
}

#[derive(Clone, Debug)]
struct ProductionShape {
    label: String,
    fields: Vec<StateId>,
}

/// A finite structural type automaton compiled once from an admitted GrammarCore.
#[derive(Clone, Debug)]
pub struct DynamicSyntaxAdmission {
    states: Vec<Shape>,
    category_states: Vec<StateId>,
    productions: Vec<Vec<ProductionShape>>,
    category_native_states: Vec<Vec<StateId>>,
    productions_by_label: BTreeMap<String, Vec<Vec<StateId>>>,
    any: StateId,
    any_pair: StateId,
    max_steps: usize,
}

enum MatchTask<'a> {
    Eval(&'a Par, StateId),
    Store((usize, StateId)),
    And(usize),
    Or(usize),
    Unavailable,
}

enum HashTask<'a> {
    Eval(&'a Par),
    FinishOrdered { label: String, child_count: usize },
    FinishUnordered { label: &'static str, child_count: usize },
    FinishMap { pair_count: usize },
}

impl DynamicSyntaxAdmission {
    pub fn compile(core: &GrammarCoreV1) -> Result<Self, DynamicAdmissionCompileError> {
        let mut builder = AdmissionBuilder::new(core)?;
        let mut productions = vec![Vec::new(); core.categories.len()];
        let mut productions_by_label: BTreeMap<String, Vec<Vec<StateId>>> = BTreeMap::new();
        for production in &core.productions {
            let slots = builder.lower_items(&production.syntax)?;
            let reduction = core
                .reductions
                .get(production.reduction as usize)
                .ok_or(DynamicAdmissionCompileError::MissingReduction(production.reduction))?;
            let mut fields = Vec::with_capacity(reduction.fields.len());
            for source in &reduction.fields {
                fields.push(match *source {
                    FieldSource::Input(input) => *slots.get(input as usize).ok_or(
                        DynamicAdmissionCompileError::MissingInput {
                            reduction: production.reduction,
                            input,
                        },
                    )?,
                    FieldSource::Text(_) => builder.text,
                    FieldSource::EmptySequence => builder.empty_sequence,
                    FieldSource::Unit => builder.unit,
                });
            }
            productions[production.result.0 as usize].push(ProductionShape {
                label: production.label.clone(),
                fields: fields.clone(),
            });
            productions_by_label
                .entry(production.label.clone())
                .or_default()
                .push(fields);
        }
        for alternatives in &mut productions {
            alternatives.sort_by(|left, right| {
                (&left.label, &left.fields).cmp(&(&right.label, &right.fields))
            });
            alternatives
                .dedup_by(|left, right| left.label == right.label && left.fields == right.fields);
        }
        for alternatives in productions_by_label.values_mut() {
            alternatives.sort();
            alternatives.dedup();
        }
        let mut category_native_states = Vec::with_capacity(core.categories.len());
        for category in &core.categories {
            let mut states = match &category.carrier {
                Carrier::Dynamic => core
                    .tokens
                    .iter()
                    .filter(|token| token.category == Some(category.id))
                    .map(|token| builder.token_state(token))
                    .filter(|state| *state != builder.never)
                    .collect::<Vec<_>>(),
                // The declared semantic carrier is not widened by a token
                // with an incompatible evaluator output. It also exists
                // when the grammar has no lexical token for that category.
                Carrier::Builtin(BuiltinCarrier::String) => vec![builder.text],
                Carrier::Builtin(BuiltinCarrier::Integer) => vec![builder.integer],
                Carrier::Builtin(BuiltinCarrier::Boolean) => vec![builder.boolean],
                Carrier::Builtin(BuiltinCarrier::Bytes) => vec![builder.bytes],
                Carrier::Builtin(
                    BuiltinCarrier::Rational | BuiltinCarrier::FixedPoint | BuiltinCarrier::Float,
                )
                | Carrier::Collection(_)
                | Carrier::Extern { .. }
                | Carrier::HostOpaque { .. } => vec![builder.unavailable],
            };
            states.sort_unstable();
            states.dedup();
            category_native_states.push(states);
        }
        Ok(Self {
            states: builder.states,
            category_states: builder.category_states,
            productions,
            category_native_states,
            productions_by_label,
            any: builder.any,
            any_pair: builder.any_pair,
            max_steps: usize::try_from(core.limits.max_forest_nodes).unwrap_or(usize::MAX),
        })
    }

    /// Fail-closed compatibility wrapper: only established membership passes.
    pub fn admits_category(&self, value: &Par, fingerprint: &str, category: CategoryId) -> bool {
        let mut budget = self.max_steps;
        self.check_category_with_budget(value, fingerprint, category, &mut budget)
            == DynamicAdmissionDecision::Admitted
    }

    /// Check one category under a caller-owned logical-work allowance. The
    /// automaton's own limit also applies; unused caller work is not discarded
    /// or replenished. Exhaustion is `Undetermined`, never an empty alternative.
    /// Work counts evaluated structural states, not bytes or allocation size.
    pub fn check_category_with_budget(
        &self,
        value: &Par,
        fingerprint: &str,
        category: CategoryId,
        remaining: &mut usize,
    ) -> DynamicAdmissionDecision {
        let Some(state) = self.category_states.get(category.0 as usize).copied() else {
            return DynamicAdmissionDecision::Rejected;
        };
        let allowance = (*remaining).min(self.max_steps);
        let mut budget = allowance;
        let result = self.check_state(value, fingerprint, state, &mut budget);
        *remaining -= allowance - budget;
        result
    }

    /// Return the canonical structural hash only when `value` is a complete
    /// member of `category`.  The hash traversal is an explicit bottom-up
    /// machine; it never invokes recursive protobuf encoding.  Set, map, and
    /// bag children are sorted by their child hashes, matching their semantic
    /// rather than incidental storage order.
    pub fn admitted_term_hash(
        &self,
        value: &Par,
        fingerprint: &str,
        category: CategoryId,
    ) -> Option<[u8; 32]> {
        if !self.admits_category(value, fingerprint, category) {
            return None;
        }
        let mut budget = self.max_steps;
        let mut tasks = vec![HashTask::Eval(value)];
        let mut values = Vec::<[u8; 32]>::new();
        while let Some(task) = tasks.pop() {
            match task {
                HashTask::Eval(par) => {
                    if budget == 0 {
                        return None;
                    }
                    budget -= 1;
                    if let Some((label, children)) = positional(par, fingerprint) {
                        tasks.push(HashTask::FinishOrdered { label, child_count: children.len() });
                        tasks.extend(children.iter().rev().map(HashTask::Eval));
                        continue;
                    }
                    if let Some(ExprInstance::ESetBody(set)) = exact_expr(par) {
                        tasks.push(HashTask::FinishUnordered {
                            label: "set",
                            child_count: set.ps.len(),
                        });
                        tasks.extend(set.ps.iter().rev().map(HashTask::Eval));
                        continue;
                    }
                    if let Some(ExprInstance::EMapBody(map)) = exact_expr(par) {
                        tasks.push(HashTask::FinishMap { pair_count: map.kvs.len() });
                        for pair in map.kvs.iter().rev() {
                            tasks.push(HashTask::Eval(pair.value.as_ref()?));
                            tasks.push(HashTask::Eval(pair.key.as_ref()?));
                        }
                        continue;
                    }
                    if let Some(sends) = exact_sends(par) {
                        tasks.push(HashTask::FinishUnordered {
                            label: "bag",
                            child_count: sends.len(),
                        });
                        for send in sends.iter().rev() {
                            tasks.push(HashTask::Eval(send.data.first()?));
                        }
                        continue;
                    }
                    return None;
                },
                HashTask::FinishOrdered { label, child_count } => {
                    let first = hash_child_start(&values, child_count)?;
                    let hash = hash_structural_node(
                        b"ordered",
                        fingerprint,
                        label.as_bytes(),
                        &values[first..],
                    );
                    values.truncate(first);
                    values.push(hash);
                },
                HashTask::FinishUnordered { label, child_count } => {
                    let first = hash_child_start(&values, child_count)?;
                    let mut children = values[first..].to_vec();
                    children.sort_unstable();
                    let hash = hash_structural_node(
                        b"unordered",
                        fingerprint,
                        label.as_bytes(),
                        &children,
                    );
                    values.truncate(first);
                    values.push(hash);
                },
                HashTask::FinishMap { pair_count } => {
                    let first = hash_child_start(&values, pair_count.checked_mul(2)?)?;
                    let mut pairs = Vec::with_capacity(pair_count);
                    for pair in values[first..].chunks_exact(2) {
                        let mut hasher = blake3::Hasher::new();
                        hasher.update(b"mettail-reflected-map-pair/1\0");
                        hasher.update(&pair[0]);
                        hasher.update(&pair[1]);
                        pairs.push(*hasher.finalize().as_bytes());
                    }
                    pairs.sort_unstable();
                    let hash = hash_structural_node(b"map", fingerprint, b"map", &pairs);
                    values.truncate(first);
                    values.push(hash);
                },
            }
        }
        (values.len() == 1).then(|| values[0])
    }

    /// Check an entire capture telescope under one shared logical-work budget.
    pub fn admits_captures(
        &self,
        values: &[Par],
        fingerprint: &str,
        categories: &[CategoryId],
    ) -> bool {
        if values.len() != categories.len() {
            return false;
        }
        let mut budget = self.max_steps;
        values.iter().zip(categories).all(|(value, category)| {
            self.category_states
                .get(category.0 as usize)
                .copied()
                .is_some_and(|state| {
                    self.check_state(value, fingerprint, state, &mut budget)
                        == DynamicAdmissionDecision::Admitted
                })
        })
    }

    fn check_state(
        &self,
        value: &Par,
        fingerprint: &str,
        state: StateId,
        budget: &mut usize,
    ) -> DynamicAdmissionDecision {
        let mut tasks = vec![MatchTask::Eval(value, state)];
        let mut values = Vec::new();
        let mut memo: HashMap<(usize, StateId), DynamicAdmissionDecision> = HashMap::new();
        while let Some(task) = tasks.pop() {
            match task {
                MatchTask::Eval(par, state) => {
                    if *budget == 0 {
                        return DynamicAdmissionDecision::Undetermined(
                            DynamicAdmissionUnknown::WorkLimit,
                        );
                    }
                    *budget -= 1;
                    let key = (par as *const Par as usize, state);
                    if let Some(result) = memo.get(&key) {
                        values.push(*result);
                        continue;
                    }
                    tasks.push(MatchTask::Store(key));
                    self.schedule_shape(par, fingerprint, state, &mut tasks, &mut values);
                },
                MatchTask::Store(key) => {
                    let result = *values.last().expect("admission task produced no result");
                    memo.insert(key, result);
                },
                MatchTask::And(count) => {
                    let first = values
                        .len()
                        .checked_sub(count)
                        .expect("admission conjunction lost an operand");
                    let result = values[first..].iter().copied().fold(
                        DynamicAdmissionDecision::Admitted,
                        DynamicAdmissionDecision::conjunction,
                    );
                    values.truncate(first);
                    values.push(result);
                },
                MatchTask::Or(count) => {
                    let first = values
                        .len()
                        .checked_sub(count)
                        .expect("admission disjunction lost an operand");
                    let result = values[first..].iter().copied().fold(
                        DynamicAdmissionDecision::Rejected,
                        DynamicAdmissionDecision::alternative,
                    );
                    values.truncate(first);
                    values.push(result);
                },
                MatchTask::Unavailable => {
                    let envelope = values.pop().expect("unavailable contract lost envelope");
                    values.push(match envelope {
                        DynamicAdmissionDecision::Rejected => DynamicAdmissionDecision::Rejected,
                        _ => DynamicAdmissionDecision::Undetermined(
                            DynamicAdmissionUnknown::UnavailableContract,
                        ),
                    });
                },
            }
        }
        match values.as_slice() {
            [result] => *result,
            _ => DynamicAdmissionDecision::Rejected,
        }
    }

    fn schedule_shape<'a>(
        &'a self,
        par: &'a Par,
        fingerprint: &str,
        state: StateId,
        tasks: &mut Vec<MatchTask<'a>>,
        values: &mut Vec<DynamicAdmissionDecision>,
    ) {
        let Some(shape) = self.states.get(state as usize) else {
            values.push(DynamicAdmissionDecision::Rejected);
            return;
        };
        match shape {
            Shape::Any => self.schedule_any(par, fingerprint, tasks, values),
            Shape::Never => values.push(DynamicAdmissionDecision::Rejected),
            Shape::Unavailable => {
                // A callback without an output contract may return a valid
                // nonnullary value. Validate its existing structural envelope
                // first; this is never positive evidence of category membership.
                tasks.push(MatchTask::Unavailable);
                tasks.push(MatchTask::Eval(par, self.any));
            },
            Shape::Category(category) => {
                let positional = positional(par, fingerprint);
                let alternatives =
                    positional
                        .as_ref()
                        .map_or_else(Vec::new, |(label, children)| {
                            self.productions[category.0 as usize]
                                .iter()
                                .filter(|production| {
                                    production.label == *label
                                        && production.fields.len() == children.len()
                                })
                                .map(|production| production.fields.as_slice())
                                .collect::<Vec<_>>()
                        });
                let natives = &self.category_native_states[category.0 as usize];
                tasks.push(MatchTask::Or(alternatives.len() + natives.len()));
                tasks.extend(
                    natives
                        .iter()
                        .rev()
                        .map(|state| MatchTask::Eval(par, *state)),
                );
                if let Some((_, children)) = positional {
                    for states in alternatives.into_iter().rev() {
                        schedule_conjunction(children, states, tasks);
                    }
                }
            },
            Shape::Text => values.push(native_leaf(par, fingerprint, valid_text_label).into()),
            Shape::Integer => {
                values.push(native_leaf(par, fingerprint, valid_integer_label).into())
            },
            Shape::Boolean => values.push(
                native_leaf(par, fingerprint, |label| {
                    matches!(label.strip_prefix(BOOLEAN_LABEL), Some("true" | "false"))
                })
                .into(),
            ),
            Shape::Bytes => values.push(
                native_leaf(par, fingerprint, |label| {
                    label
                        .strip_prefix(BYTES_REFLECT_LABEL)
                        .is_some_and(valid_hex)
                })
                .into(),
            ),
            Shape::Unit => {
                values.push(native_leaf(par, fingerprint, |label| label == UNIT_LABEL).into())
            },
            Shape::Sequence(states) => {
                let Some((label, children)) = positional(par, fingerprint) else {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                };
                if label != SEQUENCE_LABEL || children.len() != states.len() {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                }
                schedule_conjunction(children, states, tasks);
            },
            Shape::OptionalSequence(state) => {
                let Some((label, children)) = positional(par, fingerprint) else {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                };
                if label != SEQUENCE_LABEL || children.len() > 1 {
                    values.push(DynamicAdmissionDecision::Rejected);
                } else if let Some(child) = children.first() {
                    tasks.push(MatchTask::Eval(child, *state));
                } else {
                    values.push(DynamicAdmissionDecision::Admitted);
                }
            },
            Shape::Collection { kind, entry } => {
                self.schedule_collection(par, fingerprint, *kind, entry, tasks, values);
            },
        }
    }

    fn schedule_any<'a>(
        &'a self,
        par: &'a Par,
        fingerprint: &str,
        tasks: &mut Vec<MatchTask<'a>>,
        values: &mut Vec<DynamicAdmissionDecision>,
    ) {
        if let Some((label, children)) = positional(par, fingerprint) {
            let leaf = (label.starts_with(TEXT_LABEL) && valid_text_label(&label))
                || (label.starts_with(INTEGER_LABEL) && valid_integer_label(&label))
                || matches!(label.strip_prefix(BOOLEAN_LABEL), Some("true" | "false"))
                || label
                    .strip_prefix(BYTES_REFLECT_LABEL)
                    .is_some_and(valid_hex)
                || label == UNIT_LABEL;
            if leaf {
                values.push(children.is_empty().into());
                return;
            }
            if matches!(label.as_str(), SEQUENCE_LABEL | LIST_LABEL) {
                tasks.push(MatchTask::And(children.len()));
                tasks.extend(
                    children
                        .iter()
                        .rev()
                        .map(|child| MatchTask::Eval(child, self.any)),
                );
                return;
            }
            if label == PATHMAP_LABEL {
                tasks.push(MatchTask::And(children.len()));
                tasks.extend(
                    children
                        .iter()
                        .rev()
                        .map(|child| MatchTask::Eval(child, self.any_pair)),
                );
                return;
            }
            let alternatives = self
                .productions_by_label
                .get(&label)
                .into_iter()
                .flatten()
                .map(Vec::as_slice)
                .collect::<Vec<_>>();
            schedule_alternatives(children, &alternatives, tasks, values);
            return;
        }
        if let Some(ExprInstance::ESetBody(set)) = exact_expr(par) {
            if set.remainder.is_some() || set.connective_used {
                values.push(DynamicAdmissionDecision::Rejected);
                return;
            }
            tasks.push(MatchTask::And(set.ps.len()));
            tasks.extend(
                set.ps
                    .iter()
                    .rev()
                    .map(|child| MatchTask::Eval(child, self.any)),
            );
            return;
        }
        if let Some(ExprInstance::EMapBody(map)) = exact_expr(par) {
            if map.remainder.is_some()
                || map.connective_used
                || map
                    .kvs
                    .iter()
                    .any(|pair| pair.key.is_none() || pair.value.is_none())
            {
                values.push(DynamicAdmissionDecision::Rejected);
                return;
            }
            tasks.push(MatchTask::And(map.kvs.len() * 2));
            for pair in map.kvs.iter().rev() {
                tasks
                    .push(MatchTask::Eval(pair.value.as_ref().expect("validated value"), self.any));
                tasks.push(MatchTask::Eval(pair.key.as_ref().expect("validated key"), self.any));
            }
            return;
        }
        self.schedule_bag(par, fingerprint, self.any, tasks, values);
    }

    fn schedule_collection<'a>(
        &'a self,
        par: &'a Par,
        fingerprint: &str,
        kind: CollectionKind,
        entry: &[StateId],
        tasks: &mut Vec<MatchTask<'a>>,
        values: &mut Vec<DynamicAdmissionDecision>,
    ) {
        match kind {
            CollectionKind::List | CollectionKind::PathMap => {
                let expected_label = if kind == CollectionKind::List {
                    LIST_LABEL
                } else {
                    PATHMAP_LABEL
                };
                let Some((label, children)) = positional(par, fingerprint) else {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                };
                if label != expected_label || entry.len() != 1 {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                }
                tasks.push(MatchTask::And(children.len()));
                tasks.extend(
                    children
                        .iter()
                        .rev()
                        .map(|child| MatchTask::Eval(child, entry[0])),
                );
            },
            CollectionKind::Bag => {
                if entry.len() != 1 {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                }
                self.schedule_bag(par, fingerprint, entry[0], tasks, values);
            },
            CollectionKind::Set => {
                let Some(ExprInstance::ESetBody(set)) = exact_expr(par) else {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                };
                if entry.len() != 1 || set.remainder.is_some() || set.connective_used {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                }
                tasks.push(MatchTask::And(set.ps.len()));
                tasks.extend(
                    set.ps
                        .iter()
                        .rev()
                        .map(|child| MatchTask::Eval(child, entry[0])),
                );
            },
            CollectionKind::Map => {
                let Some(ExprInstance::EMapBody(map)) = exact_expr(par) else {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                };
                if entry.len() != 2
                    || map.remainder.is_some()
                    || map.connective_used
                    || map
                        .kvs
                        .iter()
                        .any(|pair| pair.key.is_none() || pair.value.is_none())
                {
                    values.push(DynamicAdmissionDecision::Rejected);
                    return;
                }
                tasks.push(MatchTask::And(map.kvs.len() * 2));
                for pair in map.kvs.iter().rev() {
                    tasks.push(MatchTask::Eval(
                        pair.value.as_ref().expect("validated value"),
                        entry[1],
                    ));
                    tasks
                        .push(MatchTask::Eval(pair.key.as_ref().expect("validated key"), entry[0]));
                }
            },
        }
    }

    fn schedule_bag<'a>(
        &'a self,
        par: &'a Par,
        fingerprint: &str,
        entry: StateId,
        tasks: &mut Vec<MatchTask<'a>>,
        values: &mut Vec<DynamicAdmissionDecision>,
    ) {
        let Some(sends) = exact_sends(par) else {
            values.push(DynamicAdmissionDecision::Rejected);
            return;
        };
        let channel = ac_soup_channel(fingerprint, BAG_LABEL);
        if sends.iter().any(|send| {
            send.persistent
                || send.connective_used
                || send.data.len() != 1
                || send.chan.as_ref().and_then(exact_string) != Some(channel.as_str())
        }) {
            values.push(DynamicAdmissionDecision::Rejected);
            return;
        }
        tasks.push(MatchTask::And(sends.len()));
        tasks.extend(
            sends
                .iter()
                .rev()
                .map(|send| MatchTask::Eval(&send.data[0], entry)),
        );
    }
}

fn hash_child_start(values: &[[u8; 32]], child_count: usize) -> Option<usize> {
    values.len().checked_sub(child_count)
}

fn hash_structural_node(
    kind: &[u8],
    fingerprint: &str,
    label: &[u8],
    children: &[[u8; 32]],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"mettail-reflected-flt/1\0");
    hash_bytes(&mut hasher, kind);
    hash_bytes(&mut hasher, fingerprint.as_bytes());
    hash_bytes(&mut hasher, label);
    hasher.update(&(children.len() as u64).to_be_bytes());
    for child in children {
        hasher.update(child);
    }
    *hasher.finalize().as_bytes()
}

fn hash_bytes(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn schedule_conjunction<'a>(
    children: &'a [Par],
    states: &[StateId],
    tasks: &mut Vec<MatchTask<'a>>,
) {
    debug_assert_eq!(children.len(), states.len());
    tasks.push(MatchTask::And(children.len()));
    for (child, state) in children.iter().zip(states).rev() {
        tasks.push(MatchTask::Eval(child, *state));
    }
}

fn schedule_alternatives<'a>(
    children: &'a [Par],
    alternatives: &[&[StateId]],
    tasks: &mut Vec<MatchTask<'a>>,
    values: &mut Vec<DynamicAdmissionDecision>,
) {
    let alternatives = alternatives
        .iter()
        .copied()
        .filter(|states| states.len() == children.len())
        .collect::<Vec<_>>();
    if alternatives.is_empty() {
        values.push(DynamicAdmissionDecision::Rejected);
        return;
    }
    tasks.push(MatchTask::Or(alternatives.len()));
    for states in alternatives.into_iter().rev() {
        schedule_conjunction(children, states, tasks);
    }
}

fn native_leaf(par: &Par, fingerprint: &str, predicate: impl FnOnce(&str) -> bool) -> bool {
    positional(par, fingerprint)
        .is_some_and(|(label, children)| children.is_empty() && predicate(&label))
}

struct AdmissionBuilder<'a> {
    core: &'a GrammarCoreV1,
    states: Vec<Shape>,
    interned: HashMap<Shape, StateId>,
    category_states: Vec<StateId>,
    any: StateId,
    any_pair: StateId,
    never: StateId,
    unavailable: StateId,
    text: StateId,
    integer: StateId,
    boolean: StateId,
    bytes: StateId,
    unit: StateId,
    empty_sequence: StateId,
}

impl<'a> AdmissionBuilder<'a> {
    fn new(core: &'a GrammarCoreV1) -> Result<Self, DynamicAdmissionCompileError> {
        let mut builder = Self {
            core,
            states: Vec::new(),
            interned: HashMap::new(),
            category_states: Vec::new(),
            any: 0,
            any_pair: 0,
            never: 0,
            unavailable: 0,
            text: 0,
            integer: 0,
            boolean: 0,
            bytes: 0,
            unit: 0,
            empty_sequence: 0,
        };
        builder.any = builder.intern(Shape::Any)?;
        builder.never = builder.intern(Shape::Never)?;
        builder.unavailable = builder.intern(Shape::Unavailable)?;
        let any = builder.any;
        builder.any_pair = builder.intern(Shape::Sequence(vec![any, any]))?;
        builder.text = builder.intern(Shape::Text)?;
        builder.integer = builder.intern(Shape::Integer)?;
        builder.boolean = builder.intern(Shape::Boolean)?;
        builder.bytes = builder.intern(Shape::Bytes)?;
        builder.unit = builder.intern(Shape::Unit)?;
        builder.empty_sequence = builder.intern(Shape::Sequence(Vec::new()))?;
        for category in &core.categories {
            let state = builder.intern(Shape::Category(category.id))?;
            builder.category_states.push(state);
        }
        Ok(builder)
    }

    fn intern(&mut self, shape: Shape) -> Result<StateId, DynamicAdmissionCompileError> {
        if let Some(state) = self.interned.get(&shape) {
            return Ok(*state);
        }
        let state = StateId::try_from(self.states.len())
            .map_err(|_| DynamicAdmissionCompileError::TooManyStates)?;
        self.states.push(shape.clone());
        self.interned.insert(shape, state);
        Ok(state)
    }

    fn collection(
        &mut self,
        kind: CollectionKind,
        entry: Vec<StateId>,
    ) -> Result<StateId, DynamicAdmissionCompileError> {
        self.intern(Shape::Collection { kind, entry })
    }

    fn lower_items(
        &mut self,
        items: &'a [SyntaxItem],
    ) -> Result<Vec<StateId>, DynamicAdmissionCompileError> {
        enum Task<'a> {
            Items(&'a [SyntaxItem]),
            Item(&'a SyntaxItem),
            Flatten(usize),
            Optional,
            Collections(CollectionKind),
            MappedCollections(Vec<CollectionKind>),
        }

        let mut tasks = vec![Task::Items(items)];
        let mut values: Vec<Vec<StateId>> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Items(items) => {
                    tasks.push(Task::Flatten(items.len()));
                    tasks.extend(items.iter().rev().map(Task::Item));
                },
                Task::Item(item) => match item {
                    SyntaxItem::Token(_) => values.push(Vec::new()),
                    SyntaxItem::Category { category, .. } | SyntaxItem::Binder { category, .. } => {
                        values.push(vec![self.category_states[category.0 as usize]]);
                    },
                    SyntaxItem::CaptureIdent { .. } => {
                        let token = self
                            .core
                            .tokens
                            .iter()
                            .find(|token| {
                                matches!(
                                    token.pattern,
                                    mettail_grammar_core::TokenPattern::Builtin(
                                        mettail_grammar_core::BuiltinToken::Identifier
                                    )
                                )
                            })
                            .ok_or(DynamicAdmissionCompileError::MissingIdentifierToken)?;
                        values.push(vec![self.token_state(token)]);
                    },
                    SyntaxItem::CaptureToken { token, .. } => {
                        values.push(vec![self.token_state(&self.core.tokens[token.0 as usize])]);
                    },
                    SyntaxItem::Collection { key, element, kind, .. } => {
                        let element = self.category_states[element.0 as usize];
                        let entry = if *kind == CollectionKind::Map {
                            vec![
                                self.category_states[key.expect("validated map key").0 as usize],
                                element,
                            ]
                        } else if *kind == CollectionKind::PathMap {
                            let pair = self.intern(Shape::Sequence(vec![
                                self.category_states
                                    [key.expect("validated path-map key").0 as usize],
                                element,
                            ]))?;
                            vec![pair]
                        } else {
                            vec![element]
                        };
                        values.push(vec![self.collection(*kind, entry)?]);
                    },
                    SyntaxItem::Repeat { body, kind, .. } => {
                        tasks.push(Task::Collections(*kind));
                        tasks.push(Task::Items(body));
                    },
                    SyntaxItem::Sequence(body) => tasks.push(Task::Items(body)),
                    SyntaxItem::Optional(body) => {
                        tasks.push(Task::Optional);
                        tasks.push(Task::Items(body));
                    },
                    SyntaxItem::Separated { source, .. } => match source.as_ref() {
                        SyntaxItem::Mapped { source, body, .. } => {
                            let kinds = match source.as_ref() {
                                SyntaxItem::Collection { kind, .. } => vec![*kind],
                                SyntaxItem::Binder { multiple: true, .. } => {
                                    vec![CollectionKind::List]
                                },
                                SyntaxItem::Zip { left_kind, right_kind, .. } => {
                                    vec![*left_kind, *right_kind]
                                },
                                _ => return Err(DynamicAdmissionCompileError::InvalidMappedLayout),
                            };
                            tasks.push(Task::MappedCollections(kinds));
                            tasks.push(Task::Items(body));
                        },
                        SyntaxItem::Collection { .. } => tasks.push(Task::Item(source)),
                        _ => {
                            tasks.push(Task::Collections(CollectionKind::List));
                            tasks.push(Task::Item(source));
                        },
                    },
                    SyntaxItem::Mapped { .. } => {
                        return Err(DynamicAdmissionCompileError::UnsupportedSyntax(
                            "mapped syntax",
                        ))
                    },
                    SyntaxItem::Zip { .. } => {
                        return Err(DynamicAdmissionCompileError::UnsupportedSyntax("zip syntax"))
                    },
                    SyntaxItem::ForeignLanguage { .. } => values.push(vec![self.any]),
                    SyntaxItem::Guard { .. } => values.push(vec![self.unit]),
                },
                Task::Flatten(count) => {
                    let first = values
                        .len()
                        .checked_sub(count)
                        .expect("syntax admission PDA lost an item result");
                    let nested = values.split_off(first);
                    values.push(nested.into_iter().flatten().collect());
                },
                Task::Optional => {
                    let slots = values.pop().expect("optional admission lost its body");
                    let mut wrapped = Vec::with_capacity(slots.len());
                    for slot in slots {
                        wrapped.push(self.intern(Shape::OptionalSequence(slot))?);
                    }
                    values.push(wrapped);
                },
                Task::Collections(kind) => {
                    let slots = values.pop().expect("collection admission lost its body");
                    let mut wrapped = Vec::with_capacity(slots.len());
                    for slot in slots {
                        wrapped.push(self.collection(kind, vec![slot])?);
                    }
                    values.push(wrapped);
                },
                Task::MappedCollections(kinds) => {
                    let slots = values.pop().expect("mapped admission lost its body");
                    if slots.len() != kinds.len() {
                        return Err(DynamicAdmissionCompileError::InvalidMappedLayout);
                    }
                    let mut wrapped = Vec::with_capacity(slots.len());
                    for (slot, kind) in slots.into_iter().zip(kinds) {
                        wrapped.push(self.collection(kind, vec![slot])?);
                    }
                    values.push(wrapped);
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        Ok(values.pop().unwrap_or_default())
    }

    fn token_state(&self, token: &mettail_grammar_core::TokenDefinition) -> StateId {
        match runtime_token_output_contract(&token.decoder, token.evaluation.as_ref()) {
            RuntimeTokenOutputContract::Known(kind) => match kind {
                RuntimeNativeValueKind::Text => self.text,
                RuntimeNativeValueKind::Integer => self.integer,
                RuntimeNativeValueKind::Boolean => self.boolean,
                RuntimeNativeValueKind::Bytes => self.bytes,
                RuntimeNativeValueKind::Unit => self.unit,
            },
            RuntimeTokenOutputContract::NoSuccessfulOutput => self.never,
            RuntimeTokenOutputContract::UnavailableContract => self.unavailable,
        }
    }
}

fn exact_expr(par: &Par) -> Option<&ExprInstance> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.unforgeables.is_empty()
    {
        return None;
    }
    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

fn private_tag(par: &Par) -> Option<String> {
    if !par.exprs.is_empty()
        || !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
    {
        return None;
    }
    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    let UnfInstance::GPrivateBody(private) = unforgeable.unf_instance.as_ref()? else {
        return None;
    };
    String::decode(private.id.as_slice()).ok()
}

fn positional<'a>(par: &'a Par, fingerprint: &str) -> Option<(String, &'a [Par])> {
    let ExprInstance::EListBody(list) = exact_expr(par)? else {
        return None;
    };
    if list.remainder.is_some() || list.connective_used {
        return None;
    }
    let (head, raw_children) = list.ps.split_first()?;
    let tag = private_tag(head)?;
    let (actual, label) = parse_reflected_tag(&tag)?;
    if actual != fingerprint {
        return None;
    }
    let children = if is_marked_object_label(label) {
        let (marker, children) = raw_children.split_first()?;
        if !is_ground_marker_par(marker, fingerprint) {
            return None;
        }
        children
    } else {
        raw_children
    };
    Some((label.to_string(), children))
}

fn exact_sends(par: &Par) -> Option<&[models::rhoapi::Send]> {
    if !par.exprs.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.connectives.is_empty()
        || !par.unforgeables.is_empty()
    {
        return None;
    }
    Some(&par.sends)
}

fn exact_string(par: &Par) -> Option<&str> {
    let ExprInstance::GString(value) = exact_expr(par)? else {
        return None;
    };
    Some(value)
}

fn valid_hex(value: &str) -> bool {
    value.len() % 2 == 0
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn valid_text_label(label: &str) -> bool {
    let Some(hex) = label.strip_prefix(TEXT_LABEL) else {
        return false;
    };
    if !valid_hex(hex) {
        return false;
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    for pair in hex.as_bytes().chunks_exact(2) {
        let high = (pair[0] as char).to_digit(16).expect("validated hex");
        let low = (pair[1] as char).to_digit(16).expect("validated hex");
        bytes.push(((high << 4) | low) as u8);
    }
    String::from_utf8(bytes).is_ok()
}

fn valid_integer_label(label: &str) -> bool {
    label
        .strip_prefix(INTEGER_LABEL)
        .and_then(|value| value.parse::<i128>().ok().map(|parsed| (value, parsed)))
        .is_some_and(|(value, parsed)| parsed.to_string() == value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{reflect_ground_term_par, GroundTerm};
    use mettail_grammar_core::{
        Category, ConstructorId, ModeId, ModeTransition, NativeEvaluation, Precedence, Production,
        ProductionClass, ProductionId, ReductionPlan, Reservation, TokenDecoder, TokenDefinition,
        TokenId, TokenPattern,
    };

    const FP: &str = "dynamic-admission-test";

    fn grammar() -> GrammarCoreV1 {
        let mut core = GrammarCoreV1::new("Admission");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Expr".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        core.reductions = vec![
            ReductionPlan {
                output_category: CategoryId(0),
                constructor: ConstructorId(0),
                input_arity: 0,
                fields: Vec::new(),
                evaluation: None,
                evaluation_mode: None,
                tier: None,
            },
            ReductionPlan {
                output_category: CategoryId(0),
                constructor: ConstructorId(1),
                input_arity: 1,
                fields: vec![FieldSource::Input(0)],
                evaluation: None,
                evaluation_mode: None,
                tier: None,
            },
            ReductionPlan {
                output_category: CategoryId(0),
                constructor: ConstructorId(2),
                input_arity: 0,
                fields: Vec::new(),
                evaluation: None,
                evaluation_mode: None,
                tier: None,
            },
        ];
        core.productions = vec![
            Production {
                id: ProductionId(0),
                constructor: ConstructorId(0),
                label: "Zero".into(),
                result: CategoryId(0),
                syntax: Vec::new(),
                precedence: Precedence::default(),
                classification: ProductionClass::default(),
                reduction: 0,
                provenance: None,
            },
            Production {
                id: ProductionId(1),
                constructor: ConstructorId(1),
                label: "Wrap".into(),
                result: CategoryId(0),
                syntax: vec![SyntaxItem::Category {
                    category: CategoryId(0),
                    slot: "inner".into(),
                }],
                precedence: Precedence::default(),
                classification: ProductionClass::default(),
                reduction: 1,
                provenance: None,
            },
            Production {
                id: ProductionId(2),
                constructor: ConstructorId(2),
                label: "One".into(),
                result: CategoryId(0),
                syntax: Vec::new(),
                precedence: Precedence::default(),
                classification: ProductionClass::default(),
                reduction: 2,
                provenance: None,
            },
        ];
        core
    }

    #[test]
    fn category_admission_checks_the_complete_recursive_shape_and_fingerprint() {
        let admission = DynamicSyntaxAdmission::compile(&grammar()).expect("grammar compiles");
        let valid = reflect_ground_term_par(
            &GroundTerm::new("Wrap", vec![GroundTerm::nullary("Zero")]),
            FP,
        );
        assert!(admission.admits_category(&valid, FP, CategoryId(0)));
        assert!(!admission.admits_category(&valid, "other", CategoryId(0)));

        let forged = reflect_ground_term_par(
            &GroundTerm::new("Wrap", vec![GroundTerm::nullary(format!("{TEXT_LABEL}61"))]),
            FP,
        );
        let child = forged
            .exprs
            .first()
            .and_then(|expr| match expr.expr_instance.as_ref() {
                Some(ExprInstance::EListBody(list)) => list.ps.last(),
                _ => None,
            })
            .expect("forged child");
        assert!(native_leaf(child, FP, valid_text_label));
        assert!(!admission.admits_category(&forged, FP, CategoryId(0)));
    }

    fn add_token(
        core: &mut GrammarCoreV1,
        category: CategoryId,
        decoder: TokenDecoder,
        evaluation: Option<NativeEvaluation>,
    ) {
        let id = core.tokens.len() as u32;
        core.tokens.push(TokenDefinition {
            id: TokenId(id),
            name: format!("token{id}"),
            pattern: TokenPattern::Regex(".+".into()),
            category: Some(category),
            evaluation,
            priority: 0,
            mode: ModeId(0),
            channel: "main".into(),
            transition: ModeTransition::default(),
            decoder,
            reservation: Reservation::None,
        });
    }

    fn decision(
        admission: &DynamicSyntaxAdmission,
        value: &GroundTerm,
        category: u32,
    ) -> DynamicAdmissionDecision {
        let value = reflect_ground_term_par(value, FP);
        let mut budget = 1_000_000;
        admission.check_category_with_budget(&value, FP, CategoryId(category), &mut budget)
    }

    #[test]
    fn mixed_category_keeps_constructors_and_only_its_own_token_outputs() {
        let mut core = grammar();
        core.categories.push(Category {
            id: CategoryId(1),
            name: "Other".into(),
            carrier: Carrier::Dynamic,
            primary: false,
            admits_variables: false,
        });
        add_token(
            &mut core,
            CategoryId(0),
            TokenDecoder::Text,
            Some(NativeEvaluation::Carrier {
                kind: "str".into(),
                parameters: BTreeMap::new(),
            }),
        );
        add_token(&mut core, CategoryId(1), TokenDecoder::Integer { radix: None }, None);
        let admission = DynamicSyntaxAdmission::compile(&core).expect("mixed grammar compiles");
        let text = GroundTerm::nullary(format!("{TEXT_LABEL}61"));
        let integer = GroundTerm::nullary(format!("{INTEGER_LABEL}7"));
        for value in [
            GroundTerm::nullary("Zero"),
            text.clone(),
            GroundTerm::new("Wrap", vec![text.clone()]),
        ] {
            assert_eq!(decision(&admission, &value, 0), DynamicAdmissionDecision::Admitted);
        }
        assert_eq!(decision(&admission, &integer, 0), DynamicAdmissionDecision::Rejected);
        assert_eq!(decision(&admission, &integer, 1), DynamicAdmissionDecision::Admitted);
        for value in [text, GroundTerm::nullary("Zero")] {
            assert_eq!(decision(&admission, &value, 1), DynamicAdmissionDecision::Rejected);
        }
    }

    #[test]
    fn declared_native_carrier_exists_without_tokens_and_cannot_be_widened() {
        let mut core = grammar();
        core.categories[0].carrier = Carrier::Builtin(BuiltinCarrier::Integer);
        let integer = GroundTerm::nullary(format!("{INTEGER_LABEL}7"));
        let text = GroundTerm::nullary(format!("{TEXT_LABEL}37"));
        let admission = DynamicSyntaxAdmission::compile(&core).expect("native grammar compiles");
        assert_eq!(decision(&admission, &integer, 0), DynamicAdmissionDecision::Admitted);
        add_token(&mut core, CategoryId(0), TokenDecoder::Text, None);
        let admission = DynamicSyntaxAdmission::compile(&core).expect("native grammar compiles");
        assert_eq!(decision(&admission, &text, 0), DynamicAdmissionDecision::Rejected);
        assert_eq!(decision(&admission, &integer, 0), DynamicAdmissionDecision::Admitted);
        assert_eq!(
            decision(&admission, &GroundTerm::nullary("Zero"), 0),
            DynamicAdmissionDecision::Admitted
        );
    }

    #[test]
    fn captured_token_uses_its_evaluator_output_not_the_category_carrier() {
        let mut core = grammar();
        core.categories[0].carrier = Carrier::Builtin(BuiltinCarrier::Float);
        add_token(
            &mut core,
            CategoryId(0),
            TokenDecoder::Text,
            Some(NativeEvaluation::Carrier {
                kind: "float".into(),
                parameters: BTreeMap::new(),
            }),
        );
        core.productions[1].syntax = vec![SyntaxItem::CaptureToken {
            token: TokenId(0),
            slot: "numeric_text".into(),
        }];
        let admission = DynamicSyntaxAdmission::compile(&core).expect("captured grammar compiles");
        let text = GroundTerm::nullary(format!("{TEXT_LABEL}312e30"));
        assert_eq!(
            decision(&admission, &text, 0),
            DynamicAdmissionDecision::Undetermined(DynamicAdmissionUnknown::UnavailableContract)
        );
        assert_eq!(
            decision(&admission, &GroundTerm::new("Wrap", vec![text]), 0),
            DynamicAdmissionDecision::Admitted
        );
        assert_eq!(
            decision(
                &admission,
                &GroundTerm::new("Wrap", vec![GroundTerm::nullary(format!("{INTEGER_LABEL}1"))]),
                0
            ),
            DynamicAdmissionDecision::Rejected
        );
    }

    #[test]
    fn unavailable_output_is_unknown_without_erasing_valid_constructor_evidence() {
        for (decoder, evaluation) in [
            (TokenDecoder::Capability("decoder".into()), None),
            (TokenDecoder::Text, Some(NativeEvaluation::Handler("evaluator".into()))),
        ] {
            let mut core = grammar();
            add_token(&mut core, CategoryId(0), decoder, evaluation);
            let admission =
                DynamicSyntaxAdmission::compile(&core).expect("callback grammar compiles");
            let text = GroundTerm::nullary(format!("{TEXT_LABEL}61"));
            for value in [text.clone(), GroundTerm::new(SEQUENCE_LABEL, vec![text])] {
                assert_eq!(
                    decision(&admission, &value, 0),
                    DynamicAdmissionDecision::Undetermined(
                        DynamicAdmissionUnknown::UnavailableContract
                    )
                );
                let reflected = reflect_ground_term_par(&value, FP);
                assert!(!admission.admits_category(&reflected, FP, CategoryId(0)));
                let mut budget = 100;
                assert_eq!(
                    admission.check_category_with_budget(
                        &reflected,
                        "foreign",
                        CategoryId(0),
                        &mut budget
                    ),
                    DynamicAdmissionDecision::Rejected
                );
            }
            for malformed in [
                GroundTerm::nullary(format!("{TEXT_LABEL}ff")),
                GroundTerm::nullary("undeclared"),
            ] {
                assert_eq!(decision(&admission, &malformed, 0), DynamicAdmissionDecision::Rejected);
            }
            assert_eq!(
                decision(&admission, &GroundTerm::nullary("Zero"), 0),
                DynamicAdmissionDecision::Admitted
            );
        }
    }

    #[test]
    fn native_admission_rejects_wrong_kind_noncanonical_payload_and_extra_children() {
        let mut core = grammar();
        add_token(&mut core, CategoryId(0), TokenDecoder::Integer { radix: None }, None);
        let admission = DynamicSyntaxAdmission::compile(&core).expect("integer grammar compiles");
        for value in [
            GroundTerm::nullary(format!("{INTEGER_LABEL}01")),
            GroundTerm::nullary(format!("{INTEGER_LABEL}+1")),
            GroundTerm::nullary(format!("{INTEGER_LABEL}170141183460469231731687303715884105728")),
            GroundTerm::nullary(format!("{TEXT_LABEL}31")),
            GroundTerm::new(format!("{INTEGER_LABEL}1"), vec![GroundTerm::nullary("Zero")]),
        ] {
            assert_eq!(decision(&admission, &value, 0), DynamicAdmissionDecision::Rejected);
        }
        let valid = GroundTerm::nullary(format!("{INTEGER_LABEL}-1"));
        assert_eq!(decision(&admission, &valid, 0), DynamicAdmissionDecision::Admitted);
    }

    #[test]
    fn admission_budget_is_shared_and_exhaustion_is_not_refutation() {
        let mut core = grammar();
        add_token(&mut core, CategoryId(0), TokenDecoder::Text, None);
        let admission = DynamicSyntaxAdmission::compile(&core).expect("grammar compiles");
        let value = reflect_ground_term_par(&GroundTerm::nullary(format!("{TEXT_LABEL}61")), FP);
        let mut budget = 1;
        assert_eq!(
            admission.check_category_with_budget(&value, FP, CategoryId(0), &mut budget),
            DynamicAdmissionDecision::Undetermined(DynamicAdmissionUnknown::WorkLimit)
        );
        assert_eq!(budget, 0);
        budget = 3;
        assert_eq!(
            admission.check_category_with_budget(&value, FP, CategoryId(0), &mut budget),
            DynamicAdmissionDecision::Admitted
        );
        assert_eq!(budget, 1);
        assert_eq!(
            admission.check_category_with_budget(&value, FP, CategoryId(0), &mut budget),
            DynamicAdmissionDecision::Undetermined(DynamicAdmissionUnknown::WorkLimit)
        );
        assert_eq!(budget, 0);
        core.limits.max_forest_nodes = 1;
        let admission = DynamicSyntaxAdmission::compile(&core).expect("limited grammar compiles");
        budget = 20;
        assert_eq!(
            admission.check_category_with_budget(&value, FP, CategoryId(0), &mut budget),
            DynamicAdmissionDecision::Undetermined(DynamicAdmissionUnknown::WorkLimit)
        );
        assert_eq!(budget, 19);
    }

    #[test]
    fn literal_category_admission_uses_a_worklist_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut core = grammar();
                add_token(&mut core, CategoryId(0), TokenDecoder::Text, None);
                let admission = DynamicSyntaxAdmission::compile(&core).expect("grammar compiles");
                let mut ground = GroundTerm::nullary(format!("{TEXT_LABEL}61"));
                for _ in 0..20_000 {
                    ground = GroundTerm::new("Wrap", vec![ground]);
                }
                let value = reflect_ground_term_par(&ground, FP);
                assert!(admission.admits_category(&value, FP, CategoryId(0)));
                let mut budget = 10;
                assert_eq!(
                    admission.check_category_with_budget(&value, FP, CategoryId(0), &mut budget),
                    DynamicAdmissionDecision::Undetermined(DynamicAdmissionUnknown::WorkLimit)
                );
                assert_eq!(budget, 0);
            })
            .expect("small-stack literal thread")
            .join()
            .expect("literal traversal and cleanup are stack-safe");
    }

    #[test]
    fn recursive_category_admission_is_stack_safe_at_extreme_depth() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let admission =
                    DynamicSyntaxAdmission::compile(&grammar()).expect("grammar compiles");
                let mut ground = GroundTerm::nullary("Zero");
                for _ in 0..20_000 {
                    ground = GroundTerm::new("Wrap", vec![ground]);
                }
                let reflected = reflect_ground_term_par(&ground, FP);
                assert!(admission.admits_category(&reflected, FP, CategoryId(0)));
                assert!(admission
                    .admitted_term_hash(&reflected, FP, CategoryId(0))
                    .is_some());
            })
            .expect("small-stack admission thread")
            .join()
            .expect("admission uses its heap worklist");
    }

    #[test]
    fn canonical_hash_descends_to_a_deepest_leaf_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let admission =
                    DynamicSyntaxAdmission::compile(&grammar()).expect("grammar compiles");
                let mut left = GroundTerm::nullary("Zero");
                let mut right = GroundTerm::nullary("One");
                for _ in 0..20_000 {
                    left = GroundTerm::new("Wrap", vec![left]);
                    right = GroundTerm::new("Wrap", vec![right]);
                }
                let left = reflect_ground_term_par(&left, FP);
                let right = reflect_ground_term_par(&right, FP);
                let left_hash = admission
                    .admitted_term_hash(&left, FP, CategoryId(0))
                    .expect("left term is admitted");
                let right_hash = admission
                    .admitted_term_hash(&right, FP, CategoryId(0))
                    .expect("right term is admitted");
                assert_ne!(
                    left_hash, right_hash,
                    "the canonical hash must reach the only differing leaf",
                );
            })
            .expect("small-stack hash thread")
            .join()
            .expect("canonical hashing uses its heap worklist");
    }
}
