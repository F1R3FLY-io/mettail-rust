//! Differential and resource-safety gates for the retained FLT set automaton.
//!
//! The production matcher is always compared with f1r3node's spatial matcher;
//! no expectation below is derived from the implementation under test.  The
//! corpus separates eligible positional reflections from deliberately declined
//! shapes so both the fast-path and fail-closed boundary remain executable.

use mettail_rholang_codegen::{
    reflect_flt_pattern, reflect_ground_term_par, FltHole, GroundTerm, FREE_VAR_REFLECT_LABEL,
};
use mettail_rholang_runtime::guard_par_substrate::SubstrateGuardMatcher;
use models::rhoapi::{BindPattern, ListParWithRandom, Par, Receive, ReceiveBind};
use models::rust::utils::{new_freevar_par, new_gstring_par};
use proptest::prelude::*;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rspace_plus_plus::rspace::r#match::Match;

const FP: &str = "flt-automaton-differential-v1";

fn node(label: impl Into<String>, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}

fn free(name: &str) -> GroundTerm {
    node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(name)])
}

fn bind_pattern(template: &GroundTerm, holes: &[FltHole], fingerprint: &str) -> BindPattern {
    let reflected = reflect_flt_pattern(template, holes, fingerprint).expect("valid FLT pattern");
    BindPattern {
        patterns: vec![reflected.pattern],
        remainder: None,
        free_count: reflected.free_count,
    }
}

fn datum(pars: Vec<Par>) -> ListParWithRandom {
    ListParWithRandom {
        pars,
        random_state: vec![3, 1, 4, 1, 5, 9],
    }
}

fn assert_matches_oracle(pattern: &BindPattern, data: &ListParWithRandom) {
    let oracle = Matcher.get(pattern, data);
    let retained = SubstrateGuardMatcher::new().get(pattern, data);
    assert_eq!(retained, oracle);
}

fn receive_program(patterns: Vec<BindPattern>) -> Par {
    let receives = patterns
        .into_iter()
        .enumerate()
        .map(|(index, pattern)| Receive {
            binds: vec![ReceiveBind {
                patterns: pattern.patterns,
                source: Some(new_gstring_par(format!("flt-prepare-{index}"), Vec::new(), false)),
                remainder: pattern.remainder,
                free_count: pattern.free_count,
            }],
            body: Some(Par::default()),
            persistent: false,
            peek: false,
            bind_count: pattern.free_count,
            locally_free: Vec::new(),
            connective_used: false,
            condition: None,
        })
        .collect();
    Par::default().with_receives(receives)
}

#[test]
fn positional_match_miss_wildcard_and_repeated_holes_equal_the_spatial_oracle() {
    let a = GroundTerm::nullary("A");
    let b = GroundTerm::nullary("B");

    let one_hole = bind_pattern(
        &node("Pair", vec![free("x"), GroundTerm::nullary("Tail")]),
        &[FltHole::new("x")],
        FP,
    );
    let matching = datum(vec![reflect_ground_term_par(
        &node("Pair", vec![a.clone(), GroundTerm::nullary("Tail")]),
        FP,
    )]);
    let miss = datum(vec![reflect_ground_term_par(
        &node("Pair", vec![a.clone(), GroundTerm::nullary("Other")]),
        FP,
    )]);

    let matcher = SubstrateGuardMatcher::new();
    let oracle_match = Matcher.get(&one_hole, &matching);
    assert_eq!(matcher.get(&one_hole, &matching), oracle_match);
    assert_eq!(
        oracle_match.expect("one-hole match").pars,
        vec![reflect_ground_term_par(&a, FP)]
    );
    assert_eq!(matcher.get(&one_hole, &miss), Matcher.get(&one_hole, &miss));

    let wildcard = bind_pattern(
        &node("Pair", vec![free("wild"), GroundTerm::nullary("Tail")]),
        &[FltHole::new("wild")],
        FP,
    );
    let mut wildcard_pattern = wildcard.clone();
    let root = &mut wildcard_pattern.patterns[0];
    let list = match root.exprs[0]
        .expr_instance
        .as_mut()
        .expect("reflected list")
    {
        models::rhoapi::expr::ExprInstance::EListBody(list) => list,
        other => panic!("expected EList, got {other:?}"),
    };
    list.ps[2] = models::rust::utils::new_wildcard_par(Vec::new(), true);
    assert_matches_oracle(&wildcard_pattern, &matching);

    let repeated =
        bind_pattern(&node("Pair", vec![free("x"), free("x")]), &[FltHole::new("x")], FP);
    let repeated_data =
        datum(vec![reflect_ground_term_par(&node("Pair", vec![a.clone(), b.clone()]), FP)]);
    let oracle = Matcher
        .get(&repeated, &repeated_data)
        .expect("spatial repeated-hole capture");
    let fast = matcher
        .get(&repeated, &repeated_data)
        .expect("automaton repeated-hole capture");
    assert_eq!(fast, oracle);
    assert_eq!(
        fast.pars,
        vec![reflect_ground_term_par(&a, FP), reflect_ground_term_par(&b, FP)]
    );

    let stats = matcher.flt_automaton_stats();
    assert_eq!(stats.fast_matches, 2);
    assert_eq!(stats.fast_misses, 1);
    assert_eq!(stats.spatial_fallbacks, 0);
}

#[test]
fn canonical_preparation_is_order_independent_and_serializes_only_the_new_suffix() {
    let p1 = bind_pattern(
        &node("Pair", vec![free("x"), GroundTerm::nullary("A")]),
        &[FltHole::new("x")],
        FP,
    );
    let p2 = bind_pattern(
        &node("Pair", vec![free("y"), GroundTerm::nullary("B")]),
        &[FltHole::new("y")],
        FP,
    );

    let forward = SubstrateGuardMatcher::new();
    assert_eq!(
        forward.prepare_flt_patterns(&receive_program(vec![p1.clone(), p2.clone()])),
        Ok(2)
    );
    let forward_stats = forward.flt_automaton_stats();
    let forward_layout = forward.flt_automaton_layout_fingerprint();
    assert_eq!(forward_stats.registered_patterns, 2);
    assert_eq!(forward_stats.automaton_states, forward_stats.serialized_states);
    assert_eq!(forward_stats.extensions, 0);

    let reverse = SubstrateGuardMatcher::new();
    assert_eq!(
        reverse.prepare_flt_patterns(&receive_program(vec![p2.clone(), p1.clone()])),
        Ok(2)
    );
    assert_eq!(reverse.flt_automaton_stats(), forward_stats);
    assert_eq!(reverse.flt_automaton_layout_fingerprint(), forward_layout);

    assert_eq!(
        forward.prepare_flt_patterns(&receive_program(vec![p1.clone(), p2.clone()])),
        Ok(0)
    );
    assert_eq!(forward.flt_automaton_stats(), forward_stats);
    assert_eq!(forward.flt_automaton_layout_fingerprint(), forward_layout);

    let p3 = bind_pattern(
        &node("Pair", vec![free("z"), GroundTerm::nullary("C")]),
        &[FltHole::new("z")],
        FP,
    );
    assert_eq!(forward.prepare_flt_patterns(&receive_program(vec![p3])), Ok(1));
    let extended_stats = forward.flt_automaton_stats();
    assert_eq!(extended_stats.registered_patterns, 3);
    assert_eq!(extended_stats.extensions, 1);
    assert_eq!(extended_stats.automaton_states, extended_stats.serialized_states);
    assert!(extended_stats.automaton_states >= forward_stats.automaton_states);

    let only_p1 = SubstrateGuardMatcher::new();
    only_p1
        .prepare_flt_patterns(&receive_program(vec![p1]))
        .unwrap();
    let only_p2 = SubstrateGuardMatcher::new();
    only_p2
        .prepare_flt_patterns(&receive_program(vec![p2]))
        .unwrap();
    assert!(
        forward_stats.automaton_states
            < only_p1.flt_automaton_stats().automaton_states
                + only_p2.flt_automaton_stats().automaton_states,
        "shared reflected states must be interned rather than serialized twice"
    );
}

#[test]
fn unsafe_shapes_delegate_verbatim_to_the_spatial_matcher() {
    let subject = reflect_ground_term_par(&GroundTerm::nullary("A"), FP);
    let other = reflect_ground_term_par(&GroundTerm::nullary("B"), FP);
    let matcher = SubstrateGuardMatcher::new();

    let bare = BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new())],
        remainder: None,
        free_count: 1,
    };
    let one = datum(vec![subject.clone()]);
    assert_eq!(matcher.get(&bare, &one), Matcher.get(&bare, &one));

    let multi = BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new()), new_freevar_par(1, Vec::new())],
        remainder: None,
        free_count: 2,
    };
    let two = datum(vec![subject.clone(), other.clone()]);
    assert_eq!(matcher.get(&multi, &two), Matcher.get(&multi, &two));

    let remainder = BindPattern {
        patterns: vec![new_freevar_par(0, Vec::new())],
        remainder: Some(models::rhoapi::Var {
            var_instance: Some(models::rhoapi::var::VarInstance::FreeVar(1)),
        }),
        free_count: 2,
    };
    assert_eq!(matcher.get(&remainder, &two), Matcher.get(&remainder, &two));

    let mixed_pattern = reflect_ground_term_par(
        &node("Pair", vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")]),
        FP,
    );
    let mut mixed_pattern = mixed_pattern;
    let list = match mixed_pattern.exprs[0]
        .expr_instance
        .as_mut()
        .expect("reflected list")
    {
        models::rhoapi::expr::ExprInstance::EListBody(list) => list,
        other => panic!("expected EList, got {other:?}"),
    };
    list.ps[2] = reflect_ground_term_par(&GroundTerm::nullary("A"), "foreign-fingerprint");
    let mixed = BindPattern {
        patterns: vec![mixed_pattern.clone()],
        remainder: None,
        free_count: 0,
    };
    let mixed_data = datum(vec![mixed_pattern]);
    assert_eq!(matcher.get(&mixed, &mixed_data), Matcher.get(&mixed, &mixed_data));

    let collection = GroundTerm::collection(
        mettail_rholang_codegen::CollectionType::HashSet,
        "Bag",
        vec![GroundTerm::nullary("A"), GroundTerm::nullary("B")],
    );
    let collection_par = reflect_ground_term_par(&collection, FP);
    let collection_pattern = BindPattern {
        patterns: vec![collection_par.clone()],
        remainder: None,
        free_count: 0,
    };
    let collection_data = datum(vec![collection_par]);
    assert_eq!(
        matcher.get(&collection_pattern, &collection_data),
        Matcher.get(&collection_pattern, &collection_data)
    );

    assert_eq!(matcher.flt_automaton_stats().spatial_fallbacks, 5);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn randomized_unary_reflections_equal_the_spatial_oracle(
        pattern_labels in prop::collection::vec(0u8..5, 0..24),
        target_labels in prop::collection::vec(0u8..5, 0..24),
        hole_leaf in any::<bool>(),
        target_leaf in 0u8..4,
    ) {
        let mut template = if hole_leaf {
            free("x")
        } else {
            GroundTerm::nullary("Leaf0")
        };
        for label in pattern_labels {
            template = node(format!("N{label}"), vec![template]);
        }

        let mut target = GroundTerm::nullary(format!("Leaf{target_leaf}"));
        for label in target_labels {
            target = node(format!("N{label}"), vec![target]);
        }

        let holes = hole_leaf.then(|| vec![FltHole::new("x")]).unwrap_or_default();
        let pattern = bind_pattern(&template, &holes, FP);
        let data = datum(vec![reflect_ground_term_par(&target, FP)]);
        prop_assert_eq!(SubstrateGuardMatcher::new().get(&pattern, &data), Matcher.get(&pattern, &data));
    }
}

#[test]
fn twenty_thousand_level_match_and_teardown_fit_a_256_kib_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("flt-automaton-deep-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut template = free("x");
            let mut target = GroundTerm::nullary("Leaf");
            for _ in 0..DEPTH {
                template = node("Spine", vec![template]);
                target = node("Spine", vec![target]);
            }

            let pattern = bind_pattern(&template, &[FltHole::new("x")], FP);
            let leaf = reflect_ground_term_par(&GroundTerm::nullary("Leaf"), FP);
            let data = datum(vec![reflect_ground_term_par(&target, FP)]);
            let matcher = SubstrateGuardMatcher::new();
            matcher
                .prepare_flt_patterns(&receive_program(vec![pattern.clone()]))
                .expect("deep canonical preparation");
            let matched = matcher.get(&pattern, &data).expect("deep automaton match");
            assert_eq!(matched.pars, vec![leaf]);
            assert_eq!(matched, Matcher.get(&pattern, &data).expect("deep spatial oracle"));
            let stats = matcher.flt_automaton_stats();
            assert_eq!(stats.automaton_states, stats.serialized_states);
            assert!(stats.automaton_states >= DEPTH);
        })
        .expect("spawn 256-KiB stack thread")
        .join()
        .expect("deep FLT matcher must not overflow or panic");
}
