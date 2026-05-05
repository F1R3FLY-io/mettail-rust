//! Set automaton for a finite pattern set.
//!
//! Direct implementation of the construction in
//! Bouwman & Erkens, *Term Rewriting Based on Set Automaton Matching*
//! (arXiv:2202.08687, Section 4).
//!
//! States are encoded as canonical sets of *match goals*, partitioned by
//! a dependency relation and lifted by greatest common prefixes during
//! the derivative step. We support both the original `R_dep` relation and
//! the outermost-preserving `R_op` relation; the latter is recommended
//! for compiling rewrite rules that should fire outermost-first, which is
//! the common case for evaluation contexts.

use std::collections::{BTreeMap, BTreeSet};

use crate::gslt::Pattern;

/// A position in a term, represented as a sequence of 1-based child indices.
/// The empty position is the root.
pub type Position = Vec<usize>;

pub fn position_root() -> Position {
    Vec::new()
}

pub fn position_extend(p: &Position, i: usize) -> Position {
    let mut q = p.clone();
    q.push(i);
    q
}

pub fn position_concat(p: &Position, q: &Position) -> Position {
    let mut r = p.clone();
    r.extend_from_slice(q);
    r
}

/// Greatest common prefix of a non-empty set of positions.
pub fn gcp(positions: &BTreeSet<Position>) -> Position {
    let mut iter = positions.iter();
    let first = match iter.next() {
        Some(p) => p.clone(),
        None => return Vec::new(),
    };
    let mut prefix = first;
    for p in iter {
        let mut k = 0usize;
        while k < prefix.len() && k < p.len() && prefix[k] == p[k] {
            k += 1;
        }
        prefix.truncate(k);
        if prefix.is_empty() {
            break;
        }
    }
    prefix
}

/// Strip prefix from a position, panicking if the prefix is not a prefix.
fn strip_prefix(p: &Position, prefix: &Position) -> Position {
    debug_assert!(p.len() >= prefix.len());
    debug_assert!(p[..prefix.len()] == prefix[..]);
    p[prefix.len()..].to_vec()
}

// ---------------------------------------------------------------------------
// Match goals
// ---------------------------------------------------------------------------

/// A single (sub)pattern paired with the position at which it must be observed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Obligation {
    pub pattern: Pattern,
    pub position: Position,
}

/// A match announcement: which rule's LHS is being matched, and at which
/// (relative) position the match will be reported.
///
/// We tag rules by their index in the input GSLT for stability of
/// state-canonicalisation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Announcement {
    pub rule_index: usize,
    pub position: Position,
}

/// A match goal: `mo ↪ ma`, "in order to announce `ma`, observe each
/// pattern in `mo` at its associated position".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Goal {
    pub obligations: BTreeSet<Obligation>,
    pub announcement: Announcement,
}

impl Goal {
    /// The set of obligation positions (used for the dependency relation).
    pub fn obligation_positions(&self) -> BTreeSet<Position> {
        self.obligations.iter().map(|o| o.position.clone()).collect()
    }

    /// Whether this is a "root goal" (announcement at root position).
    /// Bouwman-Erkens guarantees every reachable state has at least one
    /// such goal; the state's position label `L(s)` is chosen from the
    /// obligation positions of a root goal.
    pub fn is_root(&self) -> bool {
        self.announcement.position.is_empty()
    }
}

// ---------------------------------------------------------------------------
// States
// ---------------------------------------------------------------------------

/// A state is canonically represented by its (sorted) set of match goals.
///
/// We store states as `BTreeSet<Goal>` so that two semantically-equal states
/// have identical Rust-level representations and can be hashed/keyed.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StateData {
    pub goals: BTreeSet<Goal>,
}

/// Stable index of a state in the automaton's state vector.
pub type StateId = usize;

// ---------------------------------------------------------------------------
// Set automaton
// ---------------------------------------------------------------------------

/// Choice of dependency relation when partitioning derivatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DependencyKind {
    /// Direct dependency `R_dep`: positions overlap.
    Direct,
    /// Outermost-preserving `R_op`: announcement positions are
    /// prefix-comparable.
    OutermostPreserving,
}

/// The set automaton.
#[derive(Clone, Debug)]
pub struct SetAutomaton {
    /// Indexed states. Index 0 is the initial state by construction.
    pub states: Vec<StateData>,
    /// `transitions[s][f]` = the set of `(s', p')` such that
    /// `(s', p') ∈ δ(s, f)`. Symbols are keyed by name.
    pub transitions: Vec<BTreeMap<String, Vec<(StateId, Position)>>>,
    /// `outputs[s][f]` = the set of `(rule_index, position)` such that
    /// `(rule_index, position) ∈ η(s, f)`.
    pub outputs: Vec<BTreeMap<String, Vec<Announcement>>>,
    /// Position label of each state (which position to inspect from this
    /// state). Indexed by `StateId`.
    pub labels: Vec<Position>,
    /// Choice of dependency relation used for construction.
    pub dependency_kind: DependencyKind,
    /// The signature: maps each constructor name to its arity.
    pub signature: BTreeMap<String, usize>,
    /// The original LHS patterns, indexed by rule_index.
    pub lhss: Vec<Pattern>,
}

impl SetAutomaton {
    /// Construct the set automaton for the given LHS patterns over the
    /// given signature, using the requested dependency relation.
    pub fn build(
        signature: &[(&str, usize)],
        lhss: Vec<Pattern>,
        dependency_kind: DependencyKind,
    ) -> Self {
        let signature: BTreeMap<String, usize> = signature
            .iter()
            .map(|(s, n)| (s.to_string(), *n))
            .collect();

        // Initial state: one fresh root goal per LHS.
        let initial_goals: BTreeSet<Goal> = lhss
            .iter()
            .enumerate()
            .map(|(i, lhs)| Goal {
                obligations: {
                    let mut s = BTreeSet::new();
                    s.insert(Obligation {
                        pattern: lhs.clone(),
                        position: position_root(),
                    });
                    s
                },
                announcement: Announcement {
                    rule_index: i,
                    position: position_root(),
                },
            })
            .collect();
        let initial_state = StateData {
            goals: initial_goals,
        };

        let mut aut = SetAutomaton {
            states: Vec::new(),
            transitions: Vec::new(),
            outputs: Vec::new(),
            labels: Vec::new(),
            dependency_kind,
            signature,
            lhss,
        };
        // Map from state-data to its allocated id, for hash-consing.
        let mut intern: BTreeMap<StateData, StateId> = BTreeMap::new();
        // Worklist of states needing transition computation.
        let mut worklist: Vec<StateId> = Vec::new();

        let s0 = aut.intern_state(initial_state, &mut intern, &mut worklist);
        debug_assert_eq!(s0, 0);

        while let Some(s) = worklist.pop() {
            aut.compute_transitions(s, &mut intern, &mut worklist);
        }

        aut
    }

    fn intern_state(
        &mut self,
        sd: StateData,
        intern: &mut BTreeMap<StateData, StateId>,
        worklist: &mut Vec<StateId>,
    ) -> StateId {
        if let Some(&id) = intern.get(&sd) {
            return id;
        }
        let id = self.states.len();
        intern.insert(sd.clone(), id);
        let label = self.choose_label(&sd);
        self.states.push(sd);
        self.transitions.push(BTreeMap::new());
        self.outputs.push(BTreeMap::new());
        self.labels.push(label);
        worklist.push(id);
        id
    }

    /// Choose `L(s)` from the obligation positions of root goals.
    /// Canonical choice: lexicographically smallest such position.
    fn choose_label(&self, sd: &StateData) -> Position {
        let mut candidates: Vec<&Position> = Vec::new();
        for g in &sd.goals {
            if g.is_root() {
                for o in &g.obligations {
                    candidates.push(&o.position);
                }
            }
        }
        if let Some(min) = candidates.into_iter().min_by(|a, b| a.cmp(b)) {
            min.clone()
        } else {
            // Fallback: any obligation position. (Should not happen for
            // well-formed states.)
            sd.goals
                .iter()
                .flat_map(|g| g.obligations.iter().map(|o| o.position.clone()))
                .min_by(|a, b| a.cmp(b))
                .unwrap_or_default()
        }
    }

    fn compute_transitions(
        &mut self,
        s: StateId,
        intern: &mut BTreeMap<StateData, StateId>,
        worklist: &mut Vec<StateId>,
    ) {
        let label = self.labels[s].clone();
        let signature = self.signature.clone();
        let sd = self.states[s].clone();

        for (f, &arity) in &signature {
            let (deriv_state, announcements) =
                self.derivative(&sd, &label, f, arity);

            if !announcements.is_empty() {
                self.outputs[s]
                    .entry(f.clone())
                    .or_default()
                    .extend(announcements);
            }
            if deriv_state.goals.is_empty() {
                continue;
            }

            // Partition by dependency relation.
            let classes = partition_goals(&deriv_state.goals, self.dependency_kind);

            for class in classes {
                let class_set: BTreeSet<Goal> = class.into_iter().collect();
                if class_set.is_empty() {
                    continue;
                }

                // Lift positions by gcp of announcement positions.
                let ann_positions: BTreeSet<Position> = class_set
                    .iter()
                    .map(|g| g.announcement.position.clone())
                    .collect();
                let prefix = gcp(&ann_positions);

                let lifted = StateData {
                    goals: class_set
                        .iter()
                        .map(|g| lift_goal(g, &prefix))
                        .collect(),
                };

                let target = self.intern_state(lifted, intern, worklist);
                self.transitions[s]
                    .entry(f.clone())
                    .or_default()
                    .push((target, prefix));
            }
        }
    }

    /// Compute the f-derivative of state `sd` at position `label`.
    ///
    /// Returns the derivative as a `StateData` (before partitioning) plus
    /// the announcements that fire at this transition.
    fn derivative(
        &self,
        sd: &StateData,
        label: &Position,
        f: &str,
        arity: usize,
    ) -> (StateData, Vec<Announcement>) {
        let mut new_goals: BTreeSet<Goal> = BTreeSet::new();
        let mut announcements: Vec<Announcement> = Vec::new();

        // 1. Process existing goals.
        for g in &sd.goals {
            // If `label` is not in the goal's obligation positions, the
            // goal is unchanged.
            if !g.obligation_positions().contains(label) {
                new_goals.insert(g.clone());
                continue;
            }
            // Otherwise reduce: try to match symbol f at position label.
            let mut new_obligations: BTreeSet<Obligation> = BTreeSet::new();
            let mut goal_alive = true;

            for o in &g.obligations {
                if o.position != *label {
                    new_obligations.insert(o.clone());
                    continue;
                }
                // Try to reduce this obligation against (f, arity).
                match &o.pattern {
                    Pattern::Cons { name, args } if name == f && args.len() == arity => {
                        // Match. Push children that aren't variables.
                        for (i, child) in args.iter().enumerate() {
                            let child_pos = position_extend(&o.position, i + 1);
                            if !is_open(child) {
                                new_obligations.insert(Obligation {
                                    pattern: child.clone(),
                                    position: child_pos,
                                });
                            }
                        }
                    }
                    Pattern::Cons { .. } => {
                        // Mismatch. Goal dies.
                        goal_alive = false;
                        break;
                    }
                    Pattern::Var(_) | Pattern::Wild | Pattern::Rest(_) => {
                        // Open obligation: anything matches at the surface
                        // level; no children to add. Goal stays alive
                        // with this obligation removed.
                    }
                }
            }

            if !goal_alive {
                continue;
            }
            // Empty obligation set => announce.
            if new_obligations.is_empty() {
                announcements.push(g.announcement.clone());
                continue;
            }
            new_goals.insert(Goal {
                obligations: new_obligations,
                announcement: g.announcement.clone(),
            });
        }

        // 2. Add fresh root goals at every child position of `label`.
        // (This is the "fresh" component of the derivative. It ensures the
        // automaton can find matches at any depth.)
        for i in 1..=arity {
            let child_pos = position_extend(label, i);
            for (rule_idx, lhs) in self.lhss.iter().enumerate() {
                new_goals.insert(Goal {
                    obligations: {
                        let mut s = BTreeSet::new();
                        s.insert(Obligation {
                            pattern: lhs.clone(),
                            position: child_pos.clone(),
                        });
                        s
                    },
                    announcement: Announcement {
                        rule_index: rule_idx,
                        position: child_pos.clone(),
                    },
                });
            }
        }

        (StateData { goals: new_goals }, announcements)
    }

    pub fn initial_state(&self) -> StateId {
        0
    }

    pub fn label(&self, s: StateId) -> &Position {
        &self.labels[s]
    }

    pub fn step(&self, s: StateId, f: &str) -> &[(StateId, Position)] {
        self.transitions[s]
            .get(f)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    pub fn announcements_at(&self, s: StateId, f: &str) -> &[Announcement] {
        self.outputs[s]
            .get(f)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }
}

/// Whether a pattern is "open" (a variable, wildcard, or rest pattern).
/// Open patterns at sub-positions of a reduction are dropped from the
/// obligations, since any subterm matches them.
fn is_open(p: &Pattern) -> bool {
    matches!(p, Pattern::Var(_) | Pattern::Wild | Pattern::Rest(_))
}

/// Lift a goal by stripping `prefix` from every position in the goal.
fn lift_goal(g: &Goal, prefix: &Position) -> Goal {
    let mut new_obligations: BTreeSet<Obligation> = BTreeSet::new();
    for o in &g.obligations {
        let new_pos = if o.position.starts_with(prefix) {
            strip_prefix(&o.position, prefix)
        } else {
            // Obligation position not under the prefix: keep as-is.
            // (For well-formed equivalence classes this should not happen,
            // but we are defensive.)
            o.position.clone()
        };
        new_obligations.insert(Obligation {
            pattern: o.pattern.clone(),
            position: new_pos,
        });
    }
    let new_ann_pos = if g.announcement.position.starts_with(prefix) {
        strip_prefix(&g.announcement.position, prefix)
    } else {
        g.announcement.position.clone()
    };
    Goal {
        obligations: new_obligations,
        announcement: Announcement {
            rule_index: g.announcement.rule_index,
            position: new_ann_pos,
        },
    }
}

// ---------------------------------------------------------------------------
// Partitioning by dependency relation
// ---------------------------------------------------------------------------

fn related(g1: &Goal, g2: &Goal, kind: DependencyKind) -> bool {
    match kind {
        DependencyKind::Direct => {
            // Obligation positions overlap.
            let p1 = g1.obligation_positions();
            let p2 = g2.obligation_positions();
            p1.intersection(&p2).next().is_some()
        }
        DependencyKind::OutermostPreserving => {
            // Either (a) obligation positions overlap, or (b)
            // announcement positions are prefix-comparable. The Direct
            // overlap is always part of OP since OP is coarser.
            if related(g1, g2, DependencyKind::Direct) {
                return true;
            }
            let a = &g1.announcement.position;
            let b = &g2.announcement.position;
            a.starts_with(b) || b.starts_with(a)
        }
    }
}

/// Partition a set of goals into equivalence classes under the (transitive
/// closure of the) dependency relation.
fn partition_goals(goals: &BTreeSet<Goal>, kind: DependencyKind) -> Vec<Vec<Goal>> {
    // Union-find over goal indices.
    let goals: Vec<&Goal> = goals.iter().collect();
    let n = goals.len();
    let mut parent: Vec<usize> = (0..n).collect();

    fn find(parent: &mut [usize], i: usize) -> usize {
        if parent[i] == i {
            i
        } else {
            let r = find(parent, parent[i]);
            parent[i] = r;
            r
        }
    }
    fn union(parent: &mut [usize], i: usize, j: usize) {
        let ri = find(parent, i);
        let rj = find(parent, j);
        if ri != rj {
            parent[ri] = rj;
        }
    }

    for i in 0..n {
        for j in (i + 1)..n {
            if related(goals[i], goals[j], kind) {
                union(&mut parent, i, j);
            }
        }
    }

    let mut classes: BTreeMap<usize, Vec<Goal>> = BTreeMap::new();
    for i in 0..n {
        let r = find(&mut parent, i);
        classes.entry(r).or_default().push(goals[i].clone());
    }
    classes.into_values().collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn lambda_signature() -> Vec<(&'static str, usize)> {
        vec![("app", 2), ("lam", 1)]
    }

    fn beta_lhs() -> Pattern {
        // app(lam(M), N)
        Pattern::cons(
            "app",
            vec![
                Pattern::cons("lam", vec![Pattern::var("M")]),
                Pattern::var("N"),
            ],
        )
    }

    #[test]
    fn lambda_automaton_builds() {
        let aut = SetAutomaton::build(
            &lambda_signature(),
            vec![beta_lhs()],
            DependencyKind::OutermostPreserving,
        );
        // Should have a finite, non-trivial state space.
        assert!(aut.states.len() >= 2);
        // Initial state has empty label.
        assert_eq!(aut.label(aut.initial_state()), &position_root());
        // From s0 reading 'app' there should be transitions.
        let s0 = aut.initial_state();
        let trans = aut.step(s0, "app");
        assert!(!trans.is_empty(), "expected app-transitions from s0");
    }

    #[test]
    fn rho_automaton_builds() {
        let signature = vec![
            ("par", 2),
            ("in", 3),
            ("out", 2),
            ("nil", 0),
            ("drop", 1),
        ];
        let comm_lhs = Pattern::cons(
            "par",
            vec![
                Pattern::cons("in", vec![
                    Pattern::var("x"),
                    Pattern::var("y"),
                    Pattern::var("P"),
                ]),
                Pattern::cons("out", vec![
                    Pattern::var("x"),
                    Pattern::var("Q"),
                ]),
            ],
        );
        let aut = SetAutomaton::build(
            &signature,
            vec![comm_lhs],
            DependencyKind::Direct,
        );
        assert!(aut.states.len() >= 2);
        let s0 = aut.initial_state();
        let trans = aut.step(s0, "par");
        assert!(!trans.is_empty(), "expected par-transitions from s0");
    }

    #[test]
    fn gcp_basic() {
        let mut s = BTreeSet::new();
        s.insert(vec![1, 2, 3]);
        s.insert(vec![1, 2, 4]);
        s.insert(vec![1, 2, 5, 6]);
        assert_eq!(gcp(&s), vec![1, 2]);
    }

    #[test]
    fn gcp_empty_intersection() {
        let mut s = BTreeSet::new();
        s.insert(vec![1, 2]);
        s.insert(vec![3, 4]);
        assert_eq!(gcp(&s), Vec::<usize>::new());
    }
}
