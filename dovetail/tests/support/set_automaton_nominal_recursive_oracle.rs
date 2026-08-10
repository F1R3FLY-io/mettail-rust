//! Independent bounded model of the pre-D-E5 name-bearing automaton equations.
//!
//! Production state identity is slot-shaped. This test-only oracle deliberately
//! retains variable names in its interner and substitutions so equivalence does
//! not follow by restating the implementation under test.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NominalStateKey<L> {
    Var(String),
    App { op: L, args: Vec<usize> },
}

fn compile_nominal<L: Clone + Eq + Hash>(
    pattern: &Pattern<L>,
    table: &mut HashMap<NominalStateKey<L>, usize>,
) -> usize {
    let key = match pattern {
        Pattern::Var(name) => NominalStateKey::Var(name.clone()),
        Pattern::App { op, args } => NominalStateKey::App {
            op: op.clone(),
            args: args.iter().map(|arg| compile_nominal(arg, table)).collect(),
        },
        Pattern::AcApp { .. } => unreachable!("the nominal oracle is positional only"),
    };
    if let Some(&state) = table.get(&key) {
        return state;
    }
    let state = table.len();
    table.insert(key, state);
    state
}

pub(super) fn state_count<L: Clone + Eq + Hash>(patterns: &[(PatternId, Pattern<L>)]) -> usize {
    let mut table = HashMap::default();
    for (_, pattern) in patterns {
        compile_nominal(pattern, &mut table);
    }
    table.len()
}

fn merge_substs<L: Clone + Eq + Hash>(
    eg: &EGraph<L>,
    left: &Subst,
    right: &Subst,
) -> Option<Subst> {
    let mut merged = left.clone();
    for (name, &class) in right {
        let class = eg.find(class);
        match merged.get(name) {
            Some(&existing) if eg.find(existing) == class => {},
            Some(_) => return None,
            None => {
                merged.insert(name.clone(), class);
            },
        }
    }
    Some(merged)
}

fn match_pattern<L: Clone + Eq + Hash>(
    pattern: &Pattern<L>,
    class: EClassId,
    eg: &EGraph<L>,
) -> Vec<Subst> {
    let class = eg.find(class);
    match pattern {
        Pattern::Var(name) => {
            let mut subst = Subst::default();
            subst.insert(name.clone(), class);
            vec![subst]
        },
        Pattern::App { op, args } => {
            let mut out = Vec::new();
            for node in eg
                .nodes(class)
                .iter()
                .filter(|node| node.op == *op && node.children.len() == args.len())
            {
                let mut partial = vec![Subst::default()];
                for (arg, &child) in args.iter().zip(&node.children) {
                    let child_matches = match_pattern(arg, child, eg);
                    let mut next = Vec::new();
                    for left in &partial {
                        for right in &child_matches {
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
            out
        },
        Pattern::AcApp { .. } => unreachable!("the nominal oracle is positional only"),
    }
}

pub(super) fn search_egraph<L: Clone + Eq + Hash>(
    patterns: &[(PatternId, Pattern<L>)],
    eg: &EGraph<L>,
) -> Vec<SetAutomatonMatch> {
    let mut out = Vec::new();
    let mut visited_roots = HashSet::default();
    for class in eg.classes() {
        let root = eg.find(class);
        if !visited_roots.insert(root) {
            continue;
        }

        for (id, pattern) in patterns {
            if matches!(pattern, Pattern::Var(_)) {
                out.extend(
                    match_pattern(pattern, root, eg)
                        .into_iter()
                        .map(|subst| SetAutomatonMatch { pattern: *id, root, subst }),
                );
            }
        }

        let mut dispatched_keys = HashSet::default();
        for node in eg.nodes(root) {
            let key = RootKey {
                op: node.op.clone(),
                arity: node.children.len(),
            };
            if !dispatched_keys.insert(key.clone()) {
                continue;
            }
            for (id, pattern) in patterns {
                let Pattern::App { op, args } = pattern else {
                    continue;
                };
                if *op != key.op || args.len() != key.arity {
                    continue;
                }
                out.extend(
                    match_pattern(pattern, root, eg)
                        .into_iter()
                        .map(|subst| SetAutomatonMatch { pattern: *id, root, subst }),
                );
            }
        }
    }
    out
}
