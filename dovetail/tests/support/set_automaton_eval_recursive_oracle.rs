//! Bounded recursive reference equations for the set-automaton evaluator.
//!
//! This module is compiled only by `set_automaton`'s unit tests. Production uses
//! the explicit pushdown automaton in `SetAutomaton::eval_state`.

use super::*;

pub(super) fn search_egraph<L: Clone + Eq + Hash>(
    automaton: &SetAutomaton<L>,
    eg: &EGraph<L>,
) -> SetAutomatonRun {
    let mut run = SetAutomatonRun::default();
    let mut cache = HashMap::<(StateId, EClassId), CachedSubsts>::default();
    let mut visited_roots = HashSet::default();
    for class in eg.classes() {
        let root = eg.find(class);
        if !visited_roots.insert(root) {
            continue;
        }
        run.stats.root_classes += 1;

        for &entry_idx in &automaton.variable_roots {
            extend_entry_matches(automaton, eg, entry_idx, root, &mut cache, &mut run);
        }

        let mut dispatched_keys = HashSet::default();
        for node in eg.nodes(root) {
            run.stats.root_nodes += 1;
            let key = RootKey {
                op: node.op.clone(),
                arity: node.children.len(),
            };
            let Some(candidate_entries) = automaton.app_roots.get(&key) else {
                continue;
            };
            if !dispatched_keys.insert(key) {
                continue;
            }
            for &entry_idx in candidate_entries {
                run.stats.candidate_evaluations += 1;
                extend_entry_matches(automaton, eg, entry_idx, root, &mut cache, &mut run);
            }
        }
    }
    run
}

fn extend_entry_matches<L: Clone + Eq + Hash>(
    automaton: &SetAutomaton<L>,
    eg: &EGraph<L>,
    entry_idx: usize,
    root: EClassId,
    cache: &mut HashMap<(StateId, EClassId), CachedSubsts>,
    run: &mut SetAutomatonRun,
) {
    let entry = &automaton.entries[entry_idx];
    let matches = eval_state(automaton, eg, entry.root_state, root, cache, &mut run.stats);
    run.matches.extend(matches.iter().map(|slots| {
        let mut subst = Subst::default();
        for (name, &class) in entry.slot_names.iter().zip(slots.iter()) {
            subst.insert(name.clone(), class);
        }
        SetAutomatonMatch { pattern: entry.id, root, subst }
    }));
}

fn eval_state<L: Clone + Eq + Hash>(
    automaton: &SetAutomaton<L>,
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
    let matches = match &automaton.compiler.states[state_id.0] {
        PatternState::Var => cached_substs(vec![vec![class].into_boxed_slice()]),
        PatternState::App { op, args, slot_count } => {
            eval_app_state(automaton, eg, op, args, *slot_count, class, cache, stats)
        },
    };
    cache.insert(key, Rc::clone(&matches));
    matches
}

fn eval_app_state<L: Clone + Eq + Hash>(
    automaton: &SetAutomaton<L>,
    eg: &EGraph<L>,
    op: &L,
    args: &[StateInvocation],
    slot_count: usize,
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
        let mut partial = vec![vec![None; slot_count].into_boxed_slice()];
        for (invocation, &child) in args.iter().zip(&node.children) {
            let child_matches = eval_state(automaton, eg, invocation.state(), child, cache, stats);
            if child_matches.is_empty() {
                partial.clear();
                break;
            }

            let mut next = Vec::new();
            for left in &partial {
                for right in child_matches.iter() {
                    if let Some(merged) = merge_slot_substs(eg, left, invocation, right) {
                        next.push(merged);
                    }
                }
            }
            partial = next;
            if partial.is_empty() {
                break;
            }
        }
        finish_slot_substs(&mut partial, &mut out);
    }
    cached_substs(out)
}
