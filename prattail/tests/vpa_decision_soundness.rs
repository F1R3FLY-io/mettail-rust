use std::collections::{HashSet, VecDeque};

use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::vpa::{
    check_equivalence, complement, intersect, is_language_empty, try_is_language_empty, Vpa,
    VpaAlphabet, VpaValidationError,
};
use proptest::prelude::*;

fn alphabet(calls: &[&str], returns: &[&str], internals: &[&str]) -> VpaAlphabet {
    VpaAlphabet::new(
        calls.iter().map(|symbol| (*symbol).to_string()).collect(),
        returns.iter().map(|symbol| (*symbol).to_string()).collect(),
        internals
            .iter()
            .map(|symbol| (*symbol).to_string())
            .collect(),
    )
}

#[test]
fn bottom_returns_read_but_never_pop_the_bottom_marker() {
    let mut vpa = Vpa::new(alphabet(&[], &["r"], &[]));
    let start = vpa.add_state(Some("start".into()));
    let accepting = vpa.add_state(Some("accepting".into()));
    vpa.initial_states.insert(start);
    vpa.accepting_states.insert(accepting);
    vpa.return_transitions.insert(
        (start, "r".into(), vpa.initial_stack_symbol.clone()),
        vec![(accepting, BooleanWeight::one())],
    );
    vpa.return_transitions.insert(
        (accepting, "r".into(), vpa.initial_stack_symbol.clone()),
        vec![(accepting, BooleanWeight::one())],
    );

    assert!(vpa.weighted_run(&["r"]).0);
    assert!(vpa.weighted_run(&["r", "r", "r"]).0);
    assert!(!is_language_empty(&vpa));

    let det = vpa.determinize();
    assert!(det.weighted_run(&["r", "r"]).0);
    assert!(!complement(&vpa).weighted_run(&["r", "r"]).0);
}

#[test]
fn final_state_acceptance_allows_residual_unmatched_calls() {
    let mut vpa = Vpa::new(alphabet(&["c"], &[], &[]));
    let start = vpa.add_state(None);
    let accepting = vpa.add_state(None);
    vpa.initial_states.insert(start);
    vpa.accepting_states.insert(accepting);
    vpa.call_transitions
        .insert((start, "c".into()), vec![(accepting, "frame".into(), BooleanWeight::one())]);

    assert!(vpa.weighted_run(&["c"]).0);
    assert!(!is_language_empty(&vpa));
}

#[test]
fn matched_summary_finds_the_old_depth_cap_counterexample() {
    const P: usize = 9;
    const R: usize = 10;
    const STEPS: usize = P * R;
    let calls: Vec<String> = (0..STEPS).map(|i| format!("c{i}")).collect();
    let returns: Vec<String> = (0..STEPS).map(|i| format!("r{i}")).collect();
    let mut vpa = Vpa::new(VpaAlphabet::new(
        calls.iter().cloned().collect(),
        returns.iter().cloned().collect(),
        HashSet::new(),
    ));
    for _ in 0..(P + R + 1) {
        vpa.add_state(None);
    }
    let terminal = P + R;
    let pair = |index: usize| -> (usize, usize) {
        if index == STEPS {
            (terminal, terminal)
        } else {
            (index / R, P + index % R)
        }
    };
    let (initial, accepting) = pair(0);
    vpa.initial_states.insert(initial);
    vpa.accepting_states.insert(accepting);
    for i in 0..STEPS {
        let (call_source, return_target) = pair(i);
        let (call_target, return_source) = pair(i + 1);
        let gamma = format!("gamma-{i}");
        vpa.call_transitions.insert(
            (call_source, calls[i].clone()),
            vec![(call_target, gamma.clone(), BooleanWeight::one())],
        );
        vpa.return_transitions.insert(
            (return_source, returns[i].clone(), gamma),
            vec![(return_target, BooleanWeight::one())],
        );
    }

    assert_eq!(vpa.states.len(), 20);
    assert!(STEPS + 1 > vpa.states.len() * 4 + 2);
    assert!(!is_language_empty(&vpa));

    let mut word: Vec<&str> = calls.iter().map(String::as_str).collect();
    word.extend(returns.iter().rev().map(String::as_str));
    assert!(vpa.weighted_run(&word).0);
}

#[test]
fn determinization_preserves_call_gamma_return_correlation() {
    let mut vpa = Vpa::new(alphabet(&["c"], &["r"], &[]));
    let q0 = vpa.add_state(None);
    let left = vpa.add_state(None);
    let right = vpa.add_state(None);
    let accepting = vpa.add_state(None);
    vpa.initial_states.insert(q0);
    vpa.accepting_states.insert(accepting);
    vpa.call_transitions.insert(
        (q0, "c".into()),
        vec![
            (left, "A".into(), BooleanWeight::one()),
            (right, "B".into(), BooleanWeight::one()),
        ],
    );
    // Both return edges deliberately require the other branch's stack symbol.
    vpa.return_transitions
        .insert((left, "r".into(), "B".into()), vec![(accepting, BooleanWeight::one())]);
    vpa.return_transitions
        .insert((right, "r".into(), "A".into()), vec![(accepting, BooleanWeight::one())]);

    assert!(!vpa.weighted_run(&["c", "r"]).0);
    assert!(is_language_empty(&vpa));
    let det = vpa.determinize();
    assert!(det.is_deterministic());
    assert!(!det.weighted_run(&["c", "r"]).0);
    assert!(check_equivalence(&vpa, &det));
}

#[test]
fn complement_totalizes_missing_transitions() {
    let mut vpa = Vpa::new(alphabet(&[], &[], &["a"]));
    let start = vpa.add_state(None);
    vpa.initial_states.insert(start);
    vpa.accepting_states.insert(start);

    let complement = complement(&vpa);
    assert!(!complement.weighted_run(&[]).0);
    assert!(complement.weighted_run(&["a"]).0);
}

#[test]
fn false_boolean_edges_do_not_create_reachability() {
    let mut vpa = Vpa::new(alphabet(&[], &[], &["a"]));
    let start = vpa.add_state(None);
    let accepting = vpa.add_state(None);
    vpa.initial_states.insert(start);
    vpa.accepting_states.insert(accepting);
    vpa.internal_transitions
        .insert((start, "a".into()), vec![(accepting, BooleanWeight(false))]);

    assert!(is_language_empty(&vpa));
    assert!(!vpa.weighted_run(&["a"]).0);
}

#[test]
fn false_initial_and_final_weights_do_not_enter_product_support() {
    let mut zero_initial = Vpa::new(alphabet(&[], &[], &[]));
    let left_state = zero_initial.add_state(None);
    zero_initial.initial_states.insert(left_state);
    zero_initial.accepting_states.insert(left_state);
    zero_initial
        .initial_weights
        .insert(left_state, BooleanWeight(false));

    let mut universal_empty_word = Vpa::new(alphabet(&[], &[], &[]));
    let right_state = universal_empty_word.add_state(None);
    universal_empty_word.initial_states.insert(right_state);
    universal_empty_word.accepting_states.insert(right_state);

    assert!(!zero_initial.weighted_run(&[]).0);
    assert!(is_language_empty(&zero_initial));
    assert!(is_language_empty(&intersect(&zero_initial, &universal_empty_word)));

    let mut zero_final = universal_empty_word.clone();
    zero_final
        .accepting_weights
        .insert(right_state, BooleanWeight(false));
    assert!(!zero_final.weighted_run(&[]).0);
    assert!(is_language_empty(&zero_final));
    assert!(is_language_empty(&intersect(&universal_empty_word, &zero_final)));
}

#[test]
fn weighted_inclusion_matches_boolean_language_inclusion() {
    let mut subset = Vpa::new(alphabet(&[], &[], &["a"]));
    let subset_start = subset.add_state(None);
    subset.initial_states.insert(subset_start);
    subset.accepting_states.insert(subset_start);

    let mut superset = subset.clone();
    superset
        .internal_transitions
        .insert((subset_start, "a".into()), vec![(subset_start, BooleanWeight::one())]);

    assert_eq!(
        subset.weighted_inclusion(&superset),
        mettail_prattail::vpa::check_inclusion(&subset, &superset)
    );
    assert!(subset.weighted_inclusion(&superset));
    assert!(!superset.weighted_inclusion(&subset));
}

#[test]
fn validation_rejects_partition_overlap_and_pushed_bottom() {
    let mut overlap = Vpa::new(alphabet(&["x"], &["x"], &[]));
    overlap.add_state(None);
    assert!(matches!(
        try_is_language_empty(&overlap),
        Err(VpaValidationError::AlphabetOverlap { .. })
    ));

    let mut pushed_bottom = Vpa::new(alphabet(&["c"], &[], &[]));
    let q0 = pushed_bottom.add_state(None);
    let q1 = pushed_bottom.add_state(None);
    pushed_bottom.initial_states.insert(q0);
    pushed_bottom.call_transitions.insert(
        (q0, "c".into()),
        vec![(q1, pushed_bottom.initial_stack_symbol.clone(), BooleanWeight::one())],
    );
    assert!(matches!(pushed_bottom.validate(), Err(VpaValidationError::PushesBottom { .. })));
}

#[test]
fn product_stack_encoding_is_injective_for_comma_ambiguous_names() {
    let mut left = Vpa::new(alphabet(&["c"], &[], &[]));
    let l0 = left.add_state(None);
    let l1 = left.add_state(None);
    left.initial_states.insert(l0);
    left.call_transitions.insert(
        (l0, "c".into()),
        vec![(l1, "a,b".into(), BooleanWeight::one()), (l1, "a".into(), BooleanWeight::one())],
    );

    let mut right = Vpa::new(alphabet(&["c"], &[], &[]));
    let r0 = right.add_state(None);
    let r1 = right.add_state(None);
    right.initial_states.insert(r0);
    right.call_transitions.insert(
        (r0, "c".into()),
        vec![(r1, "c".into(), BooleanWeight::one()), (r1, "b,c".into(), BooleanWeight::one())],
    );

    let product = intersect(&left, &right);
    let pushed: HashSet<_> = product
        .call_transitions
        .values()
        .flatten()
        .map(|(_, g, _)| g)
        .collect();
    assert_eq!(pushed.len(), 4);
}

fn internal_graph_oracle(vpa: &Vpa) -> bool {
    let mut seen = vec![false; vpa.states.len()];
    let mut queue = VecDeque::new();
    for &initial in &vpa.initial_states {
        seen[initial] = true;
        queue.push_back(initial);
    }
    while let Some(source) = queue.pop_front() {
        for ((edge_source, _), targets) in &vpa.internal_transitions {
            if *edge_source == source {
                for &(target, weight) in targets {
                    if !weight.is_zero() && !seen[target] {
                        seen[target] = true;
                        queue.push_back(target);
                    }
                }
            }
        }
    }
    !(0..vpa.states.len()).any(|state| seen[state] && vpa.accepting_states.contains(&state))
}

fn active_initial(vpa: &Vpa, state: usize) -> bool {
    vpa.initial_states.contains(&state)
        && vpa
            .initial_weights
            .get(&state)
            .is_none_or(|weight| !weight.is_zero())
}

fn active_final(vpa: &Vpa, state: usize) -> bool {
    vpa.accepting_states.contains(&state)
        && vpa
            .accepting_weights
            .get(&state)
            .is_none_or(|weight| !weight.is_zero())
}

/// Independent executable specification: repeated full scans rather than the
/// production queue/incremental-predecessor saturation.
fn naive_summary_emptiness_oracle(vpa: &Vpa) -> bool {
    let n = vpa.states.len();
    let mut summary = vec![vec![false; n]; n];
    for (state, row) in summary.iter_mut().enumerate() {
        row[state] = true;
    }
    for ((source, _), targets) in &vpa.internal_transitions {
        for &(target, weight) in targets {
            if !weight.is_zero() {
                summary[*source][target] = true;
            }
        }
    }

    loop {
        let mut changed = false;
        for middle in 0..n {
            let middle_row = summary[middle].clone();
            for source_row in &mut summary {
                if !source_row[middle] {
                    continue;
                }
                for (target_cell, &middle_reaches_target) in source_row.iter_mut().zip(&middle_row)
                {
                    if middle_reaches_target && !*target_cell {
                        *target_cell = true;
                        changed = true;
                    }
                }
            }
        }
        for ((call_source, _), call_targets) in &vpa.call_transitions {
            for &(call_target, ref gamma, call_weight) in call_targets {
                if call_weight.is_zero() {
                    continue;
                }
                for ((return_source, _, return_gamma), return_targets) in &vpa.return_transitions {
                    if return_gamma != gamma || !summary[call_target][*return_source] {
                        continue;
                    }
                    for &(return_target, return_weight) in return_targets {
                        if !return_weight.is_zero() && !summary[*call_source][return_target] {
                            summary[*call_source][return_target] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut ground: Vec<bool> = (0..n).map(|state| active_initial(vpa, state)).collect();
    loop {
        let mut changed = false;
        for source in 0..n {
            if !ground[source] {
                continue;
            }
            for target in 0..n {
                if summary[source][target] && !ground[target] {
                    ground[target] = true;
                    changed = true;
                }
            }
            for ((return_source, _, gamma), targets) in &vpa.return_transitions {
                if *return_source != source || gamma != &vpa.initial_stack_symbol {
                    continue;
                }
                for &(target, weight) in targets {
                    if !weight.is_zero() && !ground[target] {
                        ground[target] = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut prefix = ground;
    loop {
        let mut changed = false;
        for source in 0..n {
            if !prefix[source] {
                continue;
            }
            for target in 0..n {
                if summary[source][target] && !prefix[target] {
                    prefix[target] = true;
                    changed = true;
                }
            }
            for ((call_source, _), targets) in &vpa.call_transitions {
                if *call_source != source {
                    continue;
                }
                for &(target, _, weight) in targets {
                    if !weight.is_zero() && !prefix[target] {
                        prefix[target] = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    !(0..n).any(|state| prefix[state] && active_final(vpa, state))
}

fn output_is_total(vpa: &Vpa) -> bool {
    let pushed: HashSet<_> = vpa
        .call_transitions
        .values()
        .flatten()
        .map(|(_, gamma, _)| gamma.clone())
        .collect();
    (0..vpa.states.len()).all(|state| {
        vpa.alphabet.internal_symbols.iter().all(|symbol| {
            vpa.internal_transitions
                .get(&(state, symbol.clone()))
                .is_some_and(|targets| targets.len() == 1)
        }) && vpa.alphabet.call_symbols.iter().all(|symbol| {
            vpa.call_transitions
                .get(&(state, symbol.clone()))
                .is_some_and(|targets| targets.len() == 1)
        }) && vpa.alphabet.return_symbols.iter().all(|symbol| {
            vpa.return_transitions
                .get(&(state, symbol.clone(), vpa.initial_stack_symbol.clone()))
                .is_some_and(|targets| targets.len() == 1)
                && pushed.iter().all(|gamma| {
                    vpa.return_transitions
                        .get(&(state, symbol.clone(), gamma.clone()))
                        .is_some_and(|targets| targets.len() == 1)
                })
        })
    })
}

fn all_words(alphabet: &[&'static str], max_len: usize) -> Vec<Vec<&'static str>> {
    let mut words = vec![Vec::new()];
    let mut frontier = vec![Vec::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for word in frontier {
            for symbol in alphabet {
                let mut extended = word.clone();
                extended.push(*symbol);
                words.push(extended.clone());
                next.push(extended);
            }
        }
        frontier = next;
    }
    words
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn exact_emptiness_matches_independent_finite_graph_oracle(
        edges in prop::collection::vec(any::<bool>(), 16),
        initials in prop::collection::vec(any::<bool>(), 4),
        accepting in prop::collection::vec(any::<bool>(), 4),
    ) {
        let mut vpa = Vpa::new(alphabet(&[], &[], &["i"]));
        for _ in 0..4 { vpa.add_state(None); }
        for state in 0..4 {
            if initials[state] { vpa.initial_states.insert(state); }
            if accepting[state] { vpa.accepting_states.insert(state); }
        }
        for source in 0..4 {
            let targets: Vec<_> = (0..4)
                .filter(|target| edges[source * 4 + target])
                .map(|target| (target, BooleanWeight::one()))
                .collect();
            if !targets.is_empty() {
                vpa.internal_transitions.insert((source, "i".into()), targets);
            }
        }
        prop_assert_eq!(is_language_empty(&vpa), internal_graph_oracle(&vpa));
    }

    #[test]
    fn summary_determinization_preserves_random_small_vpa_membership(
        bits in prop::collection::vec(any::<bool>(), 28),
    ) {
        let mut vpa = Vpa::new(alphabet(&["c"], &["r"], &["i"]));
        for _ in 0..2 { vpa.add_state(None); }
        for state in 0..2 {
            if bits[state] { vpa.initial_states.insert(state); }
            if bits[2 + state] { vpa.accepting_states.insert(state); }
        }
        let mut bit = 4;
        for source in 0..2 {
            for target in 0..2 {
                if bits[bit] {
                    vpa.internal_transitions.entry((source, "i".into())).or_default()
                        .push((target, BooleanWeight::one()));
                }
                bit += 1;
            }
        }
        for source in 0..2 {
            for target in 0..2 {
                for gamma in ["A", "B"] {
                    if bits[bit] {
                        vpa.call_transitions.entry((source, "c".into())).or_default()
                            .push((target, gamma.into(), BooleanWeight::one()));
                    }
                    bit += 1;
                }
            }
        }
        for source in 0..2 {
            for target in 0..2 {
                for gamma in ["A", "B", "Z0"] {
                    if bits[bit] {
                        vpa.return_transitions.entry((source, "r".into(), gamma.into())).or_default()
                            .push((target, BooleanWeight::one()));
                    }
                    bit += 1;
                }
            }
        }
        prop_assert_eq!(bit, 28);
        prop_assert_eq!(
            is_language_empty(&vpa),
            naive_summary_emptiness_oracle(&vpa)
        );
        let det = vpa.determinize();
        prop_assert!(det.is_deterministic());
        prop_assert!(output_is_total(&det));
        for word in all_words(&["c", "r", "i"], 4) {
            prop_assert_eq!(
                vpa.weighted_run(&word).0,
                det.weighted_run(&word).0,
                "word={:?}",
                word
            );
        }
    }
}
