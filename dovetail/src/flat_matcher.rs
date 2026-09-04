//! Bounded stack-safe matching for the complete flat Dovetail pattern algebra.
//!
//! The positional [`SetAutomaton`](crate::set_automaton::SetAutomaton) remains
//! the compiled fast path. This evaluator covers the same positional nodes plus
//! exact ordered and unordered collection patterns without converting a flat
//! arena into a recursive Rust value. Unordered selection reuses
//! [`LazyAcSelect`](crate::rules::LazyAcSelect), so the executable enumeration
//! is the one proved by `CollectionAcLowering.v`.

use crate::egraph::{EClassId, EGraph, ENode};
use crate::hash::HashMap;
use crate::key::SemanticHash;
use crate::rules::{LazyAcSelect, Subst};
use crate::set_automaton::{
    validate_flat_pattern, FlatPattern, FlatPatternError, FlatPatternNode, SetAutomatonStats,
};
use std::hash::Hash;

/// Independent bounds for one generalized flat-pattern transaction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FlatMatchLimits {
    /// Maximum abstract-machine transitions.
    pub work: u64,
    /// Maximum complete alternatives retained for publication.
    pub outputs: usize,
    /// Maximum suspended machine states.
    pub frontier: usize,
}

/// Why a complete generalized match could not be decided within its contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatMatchStop {
    InvalidPattern(FlatPatternError),
    WorkBudgetExhausted,
    Cancelled,
    OutputLimitExceeded,
    FrontierLimitExceeded,
    EGraphNodeBudgetExhausted,
    AllocationFailed,
}

/// A failed transaction never publishes a prefix of its alternatives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatMatchFailure {
    pub reason: FlatMatchStop,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

/// One complete match against the requested canonical root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatPatternMatch {
    pub root: EClassId,
    pub subst: Subst,
}

/// Complete generalized-match result and deterministic work evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatMatchRun {
    pub matches: Vec<FlatPatternMatch>,
    pub work: u64,
    pub stats: SetAutomatonStats,
}

#[derive(Debug)]
enum Goal {
    Match {
        pattern: usize,
        class: EClassId,
    },
    BindOrderedRemainder {
        pattern: usize,
        complement: Vec<EClassId>,
    },
    ContinueUnorderedPairing {
        pattern: usize,
        selection: Vec<EClassId>,
        complement: Vec<EClassId>,
        used: Vec<bool>,
        depth: usize,
    },
}

enum Work {
    Run {
        goals: Vec<Goal>,
        subst: Subst,
    },
    NodeCandidates {
        pattern: usize,
        class: EClassId,
        next_node: usize,
        goals: Vec<Goal>,
        subst: Subst,
    },
    Selections {
        pattern: usize,
        selections: LazyAcSelect,
        goals: Vec<Goal>,
        subst: Subst,
    },
    PairChoices {
        pattern: usize,
        selection: Vec<EClassId>,
        complement: Vec<EClassId>,
        used: Vec<bool>,
        depth: usize,
        next_index: usize,
        goals: Vec<Goal>,
        subst: Subst,
    },
}

/// Match one complete flat pattern at one e-class.
///
/// The supplied e-graph must be private to the enclosing semantic transaction:
/// a successful collection-rest binding is represented by a canonical e-node
/// in that graph. If this function fails, no result prefix escapes; callers
/// discard the private graph together with the failure.
pub fn match_flat_eclass_bounded<L, C>(
    egraph: &mut EGraph<L>,
    pattern: &FlatPattern<L>,
    root: EClassId,
    limits: FlatMatchLimits,
    mut is_cancelled: C,
) -> Result<FlatMatchRun, FlatMatchFailure>
where
    L: Clone + Eq + Hash + SemanticHash,
    C: FnMut() -> bool,
{
    if let Err(error) = validate_flat_pattern(pattern) {
        return Err(FlatMatchFailure {
            reason: FlatMatchStop::InvalidPattern(error),
            work: 0,
            stats: SetAutomatonStats::default(),
        });
    }

    let root = egraph.find(root);
    let mut stats = SetAutomatonStats {
        root_classes: usize::from(!egraph.nodes(root).is_empty()),
        ..SetAutomatonStats::default()
    };
    let mut work_count = 0u64;
    let mut frontier = Vec::new();
    if frontier.try_reserve_exact(1).is_err() {
        return failure(FlatMatchStop::AllocationFailed, work_count, stats);
    }
    let mut initial_goals = Vec::new();
    if initial_goals.try_reserve_exact(1).is_err() {
        return failure(FlatMatchStop::AllocationFailed, work_count, stats);
    }
    initial_goals.push(Goal::Match { pattern: pattern.root, class: root });
    if let Err(reason) = push_work(
        &mut frontier,
        Work::Run {
            goals: initial_goals,
            subst: Subst::default(),
        },
        limits.frontier,
    ) {
        return failure(reason, work_count, stats);
    }

    let mut matches = Vec::new();
    while let Some(task) = frontier.pop() {
        if let Err(reason) = charge(&mut work_count, limits.work, &mut is_cancelled) {
            return failure(reason, work_count, stats);
        }
        match task {
            Work::Run { mut goals, mut subst } => {
                let Some(goal) = goals.pop() else {
                    if matches.len() == limits.outputs {
                        return failure(FlatMatchStop::OutputLimitExceeded, work_count, stats);
                    }
                    if matches.try_reserve(1).is_err() {
                        return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                    }
                    matches.push(FlatPatternMatch { root, subst });
                    continue;
                };
                match goal {
                    Goal::Match { pattern: pattern_index, class } => {
                        stats.state_evaluations = stats.state_evaluations.saturating_add(1);
                        let class = egraph.find(class);
                        match &pattern.nodes[pattern_index] {
                            FlatPatternNode::Var(name) => {
                                match bind_class(egraph, &mut subst, name, class) {
                                    Ok(true) => {
                                        if let Err(reason) = push_work(
                                            &mut frontier,
                                            Work::Run { goals, subst },
                                            limits.frontier,
                                        ) {
                                            return failure(reason, work_count, stats);
                                        }
                                    },
                                    Ok(false) => {},
                                    Err(reason) => return failure(reason, work_count, stats),
                                }
                            },
                            FlatPatternNode::App { .. }
                            | FlatPatternNode::OrderedCollection { .. }
                            | FlatPatternNode::UnorderedCollection { .. } => {
                                if let Err(reason) = push_work(
                                    &mut frontier,
                                    Work::NodeCandidates {
                                        pattern: pattern_index,
                                        class,
                                        next_node: 0,
                                        goals,
                                        subst,
                                    },
                                    limits.frontier,
                                ) {
                                    return failure(reason, work_count, stats);
                                }
                            },
                        }
                    },
                    Goal::BindOrderedRemainder { pattern: pattern_index, complement } => {
                        let FlatPatternNode::OrderedCollection { op, rest, .. } =
                            &pattern.nodes[pattern_index]
                        else {
                            return failure(
                                FlatMatchStop::InvalidPattern(
                                    FlatPatternError::NonPositionalNode { node: pattern_index },
                                ),
                                work_count,
                                stats,
                            );
                        };
                        match bind_remainder(
                            egraph,
                            &mut subst,
                            op,
                            rest.as_deref(),
                            complement,
                            false,
                        ) {
                            Ok(true) => {
                                if let Err(reason) = push_work(
                                    &mut frontier,
                                    Work::Run { goals, subst },
                                    limits.frontier,
                                ) {
                                    return failure(reason, work_count, stats);
                                }
                            },
                            Ok(false) => {},
                            Err(reason) => return failure(reason, work_count, stats),
                        }
                    },
                    Goal::ContinueUnorderedPairing {
                        pattern: pattern_index,
                        selection,
                        complement,
                        used,
                        depth,
                    } => {
                        let FlatPatternNode::UnorderedCollection { op, fixed, rest } =
                            &pattern.nodes[pattern_index]
                        else {
                            return failure(
                                FlatMatchStop::InvalidPattern(
                                    FlatPatternError::NonPositionalNode { node: pattern_index },
                                ),
                                work_count,
                                stats,
                            );
                        };
                        if depth == fixed.len() {
                            match bind_remainder(
                                egraph,
                                &mut subst,
                                op,
                                rest.as_deref(),
                                complement,
                                true,
                            ) {
                                Ok(true) => {
                                    if let Err(reason) = push_work(
                                        &mut frontier,
                                        Work::Run { goals, subst },
                                        limits.frontier,
                                    ) {
                                        return failure(reason, work_count, stats);
                                    }
                                },
                                Ok(false) => {},
                                Err(reason) => return failure(reason, work_count, stats),
                            }
                        } else if let Err(reason) = push_work(
                            &mut frontier,
                            Work::PairChoices {
                                pattern: pattern_index,
                                selection,
                                complement,
                                used,
                                depth,
                                next_index: 0,
                                goals,
                                subst,
                            },
                            limits.frontier,
                        ) {
                            return failure(reason, work_count, stats);
                        }
                    },
                }
            },
            Work::NodeCandidates {
                pattern: pattern_index,
                class,
                next_node,
                goals,
                subst,
            } => {
                let Some(node) = egraph.nodes(class).get(next_node) else {
                    continue;
                };
                stats.root_nodes = stats.root_nodes.saturating_add(1);
                stats.candidate_evaluations = stats.candidate_evaluations.saturating_add(1);

                let next_goals = match try_clone_goals(&goals) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let next_subst = match try_clone_subst(&subst) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                if let Err(reason) = push_work(
                    &mut frontier,
                    Work::NodeCandidates {
                        pattern: pattern_index,
                        class,
                        next_node: next_node + 1,
                        goals: next_goals,
                        subst: next_subst,
                    },
                    limits.frontier,
                ) {
                    return failure(reason, work_count, stats);
                }

                match &pattern.nodes[pattern_index] {
                    FlatPatternNode::Var(_) => {
                        return failure(
                            FlatMatchStop::InvalidPattern(FlatPatternError::NonPositionalNode {
                                node: pattern_index,
                            }),
                            work_count,
                            stats,
                        );
                    },
                    FlatPatternNode::App { op, args }
                        if node.op == *op && node.children.len() == args.len() =>
                    {
                        let mut branch_goals = goals;
                        if let Err(reason) = reserve_goals(&mut branch_goals, args.len()) {
                            return failure(reason, work_count, stats);
                        }
                        for (&child_pattern, &child) in args.iter().zip(&node.children).rev() {
                            branch_goals.push(Goal::Match {
                                pattern: child_pattern,
                                class: egraph.find(child),
                            });
                        }
                        if let Err(reason) = push_work(
                            &mut frontier,
                            Work::Run { goals: branch_goals, subst },
                            limits.frontier,
                        ) {
                            return failure(reason, work_count, stats);
                        }
                    },
                    FlatPatternNode::OrderedCollection { op, fixed, rest }
                        if node.op == *op
                            && collection_arity_matches(
                                node.children.len(),
                                fixed.len(),
                                rest.is_some(),
                            ) =>
                    {
                        let mut complement = Vec::new();
                        let suffix = &node.children[fixed.len()..];
                        if complement.try_reserve_exact(suffix.len()).is_err() {
                            return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                        }
                        complement.extend(suffix.iter().map(|&child| egraph.find(child)));

                        let mut branch_goals = goals;
                        if let Err(reason) =
                            reserve_goals(&mut branch_goals, fixed.len().saturating_add(1))
                        {
                            return failure(reason, work_count, stats);
                        }
                        branch_goals.push(Goal::BindOrderedRemainder {
                            pattern: pattern_index,
                            complement,
                        });
                        for (&child_pattern, &child) in
                            fixed.iter().zip(&node.children[..fixed.len()]).rev()
                        {
                            branch_goals.push(Goal::Match {
                                pattern: child_pattern,
                                class: egraph.find(child),
                            });
                        }
                        if let Err(reason) = push_work(
                            &mut frontier,
                            Work::Run { goals: branch_goals, subst },
                            limits.frontier,
                        ) {
                            return failure(reason, work_count, stats);
                        }
                    },
                    FlatPatternNode::UnorderedCollection { op, fixed, rest }
                        if node.op == *op
                            && collection_arity_matches(
                                node.children.len(),
                                fixed.len(),
                                rest.is_some(),
                            ) =>
                    {
                        let mut bag = Vec::new();
                        if bag.try_reserve_exact(node.children.len()).is_err() {
                            return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                        }
                        bag.extend(node.children.iter().map(|&child| egraph.find(child)));
                        let selections = match LazyAcSelect::try_new(&bag, fixed.len()) {
                            Ok(value) => value,
                            Err(_) => {
                                return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                            },
                        };
                        if let Err(reason) = push_work(
                            &mut frontier,
                            Work::Selections {
                                pattern: pattern_index,
                                selections,
                                goals,
                                subst,
                            },
                            limits.frontier,
                        ) {
                            return failure(reason, work_count, stats);
                        }
                    },
                    _ => {},
                }
            },
            Work::Selections {
                pattern: pattern_index,
                mut selections,
                goals,
                subst,
            } => {
                let selected = match selections.try_next() {
                    Ok(value) => value,
                    Err(_) => {
                        return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                    },
                };
                let Some((selection, complement)) = selected else {
                    continue;
                };
                let next_goals = match try_clone_goals(&goals) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let next_subst = match try_clone_subst(&subst) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                if let Err(reason) = push_work(
                    &mut frontier,
                    Work::Selections {
                        pattern: pattern_index,
                        selections,
                        goals: next_goals,
                        subst: next_subst,
                    },
                    limits.frontier,
                ) {
                    return failure(reason, work_count, stats);
                }
                let mut used = Vec::new();
                if used.try_reserve_exact(selection.len()).is_err() {
                    return failure(FlatMatchStop::AllocationFailed, work_count, stats);
                }
                used.resize(selection.len(), false);
                let mut branch_goals = goals;
                if let Err(reason) = reserve_goals(&mut branch_goals, 1) {
                    return failure(reason, work_count, stats);
                }
                branch_goals.push(Goal::ContinueUnorderedPairing {
                    pattern: pattern_index,
                    selection,
                    complement,
                    used,
                    depth: 0,
                });
                if let Err(reason) = push_work(
                    &mut frontier,
                    Work::Run { goals: branch_goals, subst },
                    limits.frontier,
                ) {
                    return failure(reason, work_count, stats);
                }
            },
            Work::PairChoices {
                pattern: pattern_index,
                selection,
                complement,
                used,
                depth,
                mut next_index,
                goals,
                subst,
            } => {
                while next_index < selection.len() && used[next_index] {
                    next_index += 1;
                }
                if next_index == selection.len() {
                    continue;
                }
                let selected_index = next_index;
                let continuation_selection = match try_clone_copy_slice(&selection) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let continuation_complement = match try_clone_copy_slice(&complement) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let continuation_used = match try_clone_copy_slice(&used) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let continuation_goals = match try_clone_goals(&goals) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                let continuation_subst = match try_clone_subst(&subst) {
                    Ok(value) => value,
                    Err(reason) => return failure(reason, work_count, stats),
                };
                if let Err(reason) = push_work(
                    &mut frontier,
                    Work::PairChoices {
                        pattern: pattern_index,
                        selection: continuation_selection,
                        complement: continuation_complement,
                        used: continuation_used,
                        depth,
                        next_index: selected_index + 1,
                        goals: continuation_goals,
                        subst: continuation_subst,
                    },
                    limits.frontier,
                ) {
                    return failure(reason, work_count, stats);
                }

                let FlatPatternNode::UnorderedCollection { fixed, .. } =
                    &pattern.nodes[pattern_index]
                else {
                    return failure(
                        FlatMatchStop::InvalidPattern(FlatPatternError::NonPositionalNode {
                            node: pattern_index,
                        }),
                        work_count,
                        stats,
                    );
                };
                let mut branch_used = used;
                branch_used[selected_index] = true;
                let selected_class = egraph.find(selection[selected_index]);
                let mut branch_goals = goals;
                if let Err(reason) = reserve_goals(&mut branch_goals, 2) {
                    return failure(reason, work_count, stats);
                }
                branch_goals.push(Goal::ContinueUnorderedPairing {
                    pattern: pattern_index,
                    selection,
                    complement,
                    used: branch_used,
                    depth: depth + 1,
                });
                branch_goals.push(Goal::Match {
                    pattern: fixed[depth],
                    class: selected_class,
                });
                if let Err(reason) = push_work(
                    &mut frontier,
                    Work::Run { goals: branch_goals, subst },
                    limits.frontier,
                ) {
                    return failure(reason, work_count, stats);
                }
            },
        }
    }

    Ok(FlatMatchRun { matches, work: work_count, stats })
}

fn collection_arity_matches(actual: usize, fixed: usize, has_remainder: bool) -> bool {
    if has_remainder {
        actual >= fixed
    } else {
        actual == fixed
    }
}

fn bind_class<L>(
    egraph: &EGraph<L>,
    subst: &mut Subst,
    name: &str,
    class: EClassId,
) -> Result<bool, FlatMatchStop>
where
    L: Clone + Eq + Hash,
{
    if let Some(&existing) = subst.get(name) {
        return Ok(egraph.equiv(existing, class));
    }
    subst
        .try_reserve(1)
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    subst.insert(try_clone_string(name)?, class);
    Ok(true)
}

fn bind_remainder<L>(
    egraph: &mut EGraph<L>,
    subst: &mut Subst,
    op: &L,
    rest: Option<&str>,
    complement: Vec<EClassId>,
    unordered: bool,
) -> Result<bool, FlatMatchStop>
where
    L: Clone + Eq + Hash + SemanticHash,
{
    let Some(name) = rest else {
        return Ok(complement.is_empty());
    };
    let mut children = complement;
    for child in &mut children {
        *child = egraph.find(*child);
    }
    if unordered {
        let mut keyed = Vec::new();
        keyed
            .try_reserve_exact(children.len())
            .map_err(|_| FlatMatchStop::AllocationFailed)?;
        for child in children {
            keyed.push((egraph.canonical_class_key(child), child));
        }
        keyed.sort_unstable_by(|left, right| left.0.cmp(&right.0));
        children = Vec::new();
        children
            .try_reserve_exact(keyed.len())
            .map_err(|_| FlatMatchStop::AllocationFailed)?;
        children.extend(keyed.into_iter().map(|(_, child)| child));
    }
    let Some(class) = egraph.try_add_with_budget(ENode::new(op.clone(), children)) else {
        return Err(FlatMatchStop::EGraphNodeBudgetExhausted);
    };
    bind_class(egraph, subst, name, class)
}

fn charge<C>(work: &mut u64, limit: u64, is_cancelled: &mut C) -> Result<(), FlatMatchStop>
where
    C: FnMut() -> bool,
{
    if is_cancelled() {
        return Err(FlatMatchStop::Cancelled);
    }
    if *work == limit {
        return Err(FlatMatchStop::WorkBudgetExhausted);
    }
    *work = work
        .checked_add(1)
        .ok_or(FlatMatchStop::WorkBudgetExhausted)?;
    Ok(())
}

fn push_work(frontier: &mut Vec<Work>, task: Work, limit: usize) -> Result<(), FlatMatchStop> {
    if frontier.len() == limit {
        return Err(FlatMatchStop::FrontierLimitExceeded);
    }
    frontier
        .try_reserve(1)
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    frontier.push(task);
    Ok(())
}

fn reserve_goals(goals: &mut Vec<Goal>, additional: usize) -> Result<(), FlatMatchStop> {
    goals
        .try_reserve(additional)
        .map_err(|_| FlatMatchStop::AllocationFailed)
}

fn try_clone_string(source: &str) -> Result<String, FlatMatchStop> {
    let mut value = String::new();
    value
        .try_reserve_exact(source.len())
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    value.push_str(source);
    Ok(value)
}

fn try_clone_subst(source: &Subst) -> Result<Subst, FlatMatchStop> {
    let mut copy: HashMap<String, EClassId> = HashMap::default();
    copy.try_reserve(source.len())
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    for (name, &class) in source {
        copy.insert(try_clone_string(name)?, class);
    }
    Ok(copy)
}

fn try_clone_copy_slice<T: Copy>(source: &[T]) -> Result<Vec<T>, FlatMatchStop> {
    let mut copy = Vec::new();
    copy.try_reserve_exact(source.len())
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    copy.extend_from_slice(source);
    Ok(copy)
}

fn try_clone_goals(source: &[Goal]) -> Result<Vec<Goal>, FlatMatchStop> {
    let mut copy = Vec::new();
    copy.try_reserve_exact(source.len())
        .map_err(|_| FlatMatchStop::AllocationFailed)?;
    for goal in source {
        copy.push(match goal {
            Goal::Match { pattern, class } => Goal::Match { pattern: *pattern, class: *class },
            Goal::BindOrderedRemainder { pattern, complement } => Goal::BindOrderedRemainder {
                pattern: *pattern,
                complement: try_clone_copy_slice(complement)?,
            },
            Goal::ContinueUnorderedPairing {
                pattern,
                selection,
                complement,
                used,
                depth,
            } => Goal::ContinueUnorderedPairing {
                pattern: *pattern,
                selection: try_clone_copy_slice(selection)?,
                complement: try_clone_copy_slice(complement)?,
                used: try_clone_copy_slice(used)?,
                depth: *depth,
            },
        });
    }
    Ok(copy)
}

fn failure<T>(
    reason: FlatMatchStop,
    work: u64,
    stats: SetAutomatonStats,
) -> Result<T, FlatMatchFailure> {
    Err(FlatMatchFailure { reason, work, stats })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn limits() -> FlatMatchLimits {
        FlatMatchLimits {
            work: 100_000,
            outputs: 100,
            frontier: 100_000,
        }
    }

    #[test]
    fn ordered_collection_binds_the_exact_suffix() {
        let mut graph = EGraph::new();
        let a = graph.add(ENode::leaf("a".to_string()));
        let b = graph.add(ENode::leaf("b".to_string()));
        let c = graph.add(ENode::leaf("c".to_string()));
        let list = graph.add(ENode::new("list".to_string(), vec![a, b, c]));
        let pattern = FlatPattern {
            nodes: vec![
                FlatPatternNode::App { op: "a".to_string(), args: vec![] },
                FlatPatternNode::Var("x".to_string()),
                FlatPatternNode::OrderedCollection {
                    op: "list".to_string(),
                    fixed: vec![0, 1],
                    rest: Some("rest".to_string()),
                },
            ],
            root: 2,
        };

        let run = match_flat_eclass_bounded(&mut graph, &pattern, list, limits(), || false)
            .expect("bounded ordered match");
        assert_eq!(run.matches.len(), 1);
        assert!(graph.equiv(run.matches[0].subst["x"], b));
        let rest = run.matches[0].subst["rest"];
        assert!(graph.nodes(rest).iter().any(|node| {
            node.op == "list" && node.children.len() == 1 && graph.equiv(node.children[0], c)
        }));
    }

    #[test]
    fn collection_without_remainder_is_exact() {
        let mut graph = EGraph::new();
        let a = graph.add(ENode::leaf("a".to_string()));
        let b = graph.add(ENode::leaf("b".to_string()));
        let list = graph.add(ENode::new("list".to_string(), vec![a, b]));
        let pattern = FlatPattern {
            nodes: vec![
                FlatPatternNode::Var("x".to_string()),
                FlatPatternNode::OrderedCollection {
                    op: "list".to_string(),
                    fixed: vec![0],
                    rest: None,
                },
            ],
            root: 1,
        };
        let run = match_flat_eclass_bounded(&mut graph, &pattern, list, limits(), || false)
            .expect("bounded exact match");
        assert!(run.matches.is_empty());
    }

    #[test]
    fn unordered_collection_pairs_permutations_and_binds_exact_complements() {
        let mut graph = EGraph::new();
        let a = graph.add(ENode::leaf("a".to_string()));
        let b = graph.add(ENode::leaf("b".to_string()));
        let c = graph.add(ENode::leaf("c".to_string()));
        let bag = graph.add(ENode::new("bag".to_string(), vec![c, a, b]));
        let pattern = FlatPattern {
            nodes: vec![
                FlatPatternNode::App { op: "a".to_string(), args: vec![] },
                FlatPatternNode::Var("x".to_string()),
                FlatPatternNode::UnorderedCollection {
                    op: "bag".to_string(),
                    fixed: vec![0, 1],
                    rest: Some("rest".to_string()),
                },
            ],
            root: 2,
        };

        let run = match_flat_eclass_bounded(&mut graph, &pattern, bag, limits(), || false)
            .expect("bounded unordered match");
        let mut bindings: Vec<_> = run
            .matches
            .iter()
            .map(|matched| graph.find(matched.subst["x"]))
            .collect();
        bindings.sort_unstable();
        bindings.dedup();
        assert_eq!(bindings, vec![b, c]);
        for matched in run.matches {
            let x = graph.find(matched.subst["x"]);
            let rest = matched.subst["rest"];
            let expected = if x == b { c } else { b };
            assert!(graph.nodes(rest).iter().any(|node| {
                node.op == "bag"
                    && node.children.len() == 1
                    && graph.equiv(node.children[0], expected)
            }));
        }
    }

    #[test]
    fn nonlinear_variables_are_checked_by_eclass_evidence() {
        let mut graph = EGraph::new();
        let a = graph.add(ENode::leaf("a".to_string()));
        let b = graph.add(ENode::leaf("b".to_string()));
        let pair = graph.add(ENode::new("pair".to_string(), vec![a, b]));
        let pattern = FlatPattern {
            nodes: vec![
                FlatPatternNode::Var("x".to_string()),
                FlatPatternNode::App { op: "pair".to_string(), args: vec![0, 0] },
            ],
            root: 1,
        };
        let run = match_flat_eclass_bounded(&mut graph, &pattern, pair, limits(), || false)
            .expect("bounded nonlinear match");
        assert!(run.matches.is_empty());
    }

    #[test]
    fn cancellation_and_limits_never_publish_a_prefix() {
        let mut graph = EGraph::new();
        let a = graph.add(ENode::leaf("a".to_string()));
        let pattern = FlatPattern {
            nodes: vec![FlatPatternNode::Var("x".to_string())],
            root: 0,
        };
        let cancelled = match_flat_eclass_bounded(&mut graph, &pattern, a, limits(), || true)
            .expect_err("cancelled match must not publish");
        assert_eq!(cancelled.reason, FlatMatchStop::Cancelled);
        let exhausted = match_flat_eclass_bounded(
            &mut graph,
            &pattern,
            a,
            FlatMatchLimits { work: 0, ..limits() },
            || false,
        )
        .expect_err("zero work cannot publish");
        assert_eq!(exhausted.reason, FlatMatchStop::WorkBudgetExhausted);
    }

    #[test]
    fn deep_flat_pattern_matches_on_a_small_native_stack() {
        std::thread::Builder::new()
            .name("flat-matcher-small-stack".to_string())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 20_000;
                let mut graph = EGraph::new();
                let mut root = graph.add(ENode::leaf("z".to_string()));
                let mut nodes = vec![FlatPatternNode::App { op: "z".to_string(), args: vec![] }];
                for _ in 0..DEPTH {
                    root = graph.add(ENode::new("s".to_string(), vec![root]));
                    let child = nodes.len() - 1;
                    nodes.push(FlatPatternNode::App { op: "s".to_string(), args: vec![child] });
                }
                let pattern = FlatPattern { root: nodes.len() - 1, nodes };
                let run = match_flat_eclass_bounded(
                    &mut graph,
                    &pattern,
                    root,
                    FlatMatchLimits {
                        work: 200_000,
                        outputs: 1,
                        frontier: 100_000,
                    },
                    || false,
                )
                .expect("deep flat pattern matches iteratively");
                assert_eq!(run.matches.len(), 1);
            })
            .expect("small-stack thread starts")
            .join()
            .expect("flat matcher does not overflow a 256 KiB stack");
    }
}
