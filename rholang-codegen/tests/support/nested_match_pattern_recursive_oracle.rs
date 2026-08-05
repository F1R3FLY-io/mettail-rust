use super::*;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn variable(name: &str) -> Pattern {
    Pattern::Term(PatternTerm::Var(ident(name)))
}

fn apply(constructor: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
}

#[allow(clippy::too_many_arguments)]
fn recursive_report_pattern(
    pattern: &Pattern,
    nonlinear_var: &Ident,
    spliced_rest: &Ident,
    spliced_rest_slot: usize,
    next_guard_slot: &mut usize,
    occurrence_levels: &mut Vec<usize>,
    language_fingerprint: &str,
) -> Par {
    match pattern {
        Pattern::Term(PatternTerm::Var(variable)) if variable == nonlinear_var => {
            let slot = *next_guard_slot;
            *next_guard_slot += 1;
            occurrence_levels.push(slot);
            new_freevar_par(slot as i32, Vec::new())
        },
        Pattern::Term(PatternTerm::Var(_)) => new_wildcard_par(Vec::new(), true),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let channel = ac_soup_channel(language_fingerprint, &constructor.to_string());
                let mut soup = if rest.as_ref() == Some(spliced_rest) {
                    new_freevar_par(spliced_rest_slot as i32, Vec::new())
                } else {
                    new_wildcard_par(Vec::new(), true)
                };
                for element in elements {
                    let element = recursive_report_pattern(
                        element,
                        nonlinear_var,
                        spliced_rest,
                        spliced_rest_slot,
                        next_guard_slot,
                        occurrence_levels,
                        language_fingerprint,
                    );
                    soup = soup.append(new_send_par(
                        new_gstring_par(channel.clone(), Vec::new(), false),
                        vec![element],
                        false,
                        Vec::new(),
                        true,
                        Vec::new(),
                        true,
                    ));
                }
                soup
            } else {
                let label = constructor.to_string();
                let mut items = Vec::with_capacity(args.len() + 2);
                items.push(GPrivateBuilder::new_par_from_string(reflect_tag(
                    language_fingerprint,
                    &label,
                )));
                if is_marked_object_label(&label) {
                    items.push(new_wildcard_par(Vec::new(), true));
                }
                for arg in args {
                    items.push(recursive_report_pattern(
                        arg,
                        nonlinear_var,
                        spliced_rest,
                        spliced_rest_slot,
                        next_guard_slot,
                        occurrence_levels,
                        language_fingerprint,
                    ));
                }
                new_elist_par(items, Vec::new(), true, None, Vec::new(), true)
            }
        },
        _ => new_wildcard_par(Vec::new(), true),
    }
}

fn recursive_binding_pattern(
    pattern: &Pattern,
    nonlinear_var: &Ident,
    referenced: &HashSet<String>,
    state: &mut NestedBindState,
    language_fingerprint: &str,
) -> Par {
    match pattern {
        Pattern::Term(PatternTerm::Var(variable)) if variable == nonlinear_var => {
            let slot = state.next_level;
            state.next_level += 1;
            state.occurrence_levels.push(slot);
            state.slot_of.entry(variable.to_string()).or_insert(slot);
            new_freevar_par(slot as i32, Vec::new())
        },
        Pattern::Term(PatternTerm::Var(variable)) if referenced.contains(&variable.to_string()) => {
            let slot = state.next_level;
            state.next_level += 1;
            state.slot_of.entry(variable.to_string()).or_insert(slot);
            new_freevar_par(slot as i32, Vec::new())
        },
        Pattern::Term(PatternTerm::Var(_)) => new_wildcard_par(Vec::new(), true),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let channel = ac_soup_channel(language_fingerprint, &constructor.to_string());
                let mut soup = match rest {
                    Some(rest) if referenced.contains(&rest.to_string()) => {
                        let slot = state.next_level;
                        state.next_level += 1;
                        state.slot_of.entry(rest.to_string()).or_insert(slot);
                        new_freevar_par(slot as i32, Vec::new())
                    },
                    Some(_) => new_wildcard_par(Vec::new(), true),
                    None => Par::default(),
                };
                for element in elements {
                    let element = recursive_binding_pattern(
                        element,
                        nonlinear_var,
                        referenced,
                        state,
                        language_fingerprint,
                    );
                    soup = soup.append(new_send_par(
                        new_gstring_par(channel.clone(), Vec::new(), false),
                        vec![element],
                        false,
                        Vec::new(),
                        true,
                        Vec::new(),
                        true,
                    ));
                }
                soup
            } else {
                let label = constructor.to_string();
                let mut items = Vec::with_capacity(args.len() + 2);
                items.push(GPrivateBuilder::new_par_from_string(reflect_tag(
                    language_fingerprint,
                    &label,
                )));
                if is_marked_object_label(&label) {
                    items.push(new_wildcard_par(Vec::new(), true));
                }
                for arg in args {
                    items.push(recursive_binding_pattern(
                        arg,
                        nonlinear_var,
                        referenced,
                        state,
                        language_fingerprint,
                    ));
                }
                new_elist_par(items, Vec::new(), true, None, Vec::new(), true)
            }
        },
        _ => new_wildcard_par(Vec::new(), true),
    }
}

fn fixture() -> Pattern {
    apply(
        "PPar",
        vec![Pattern::Collection {
            coll_type: Some(CollectionType::HashBag),
            elements: vec![
                apply("Cap", vec![variable("M"), variable("x")]),
                apply(
                    "Nest",
                    vec![
                        variable("M"),
                        apply(
                            "PPar",
                            vec![Pattern::Collection {
                                coll_type: Some(CollectionType::HashBag),
                                elements: vec![variable("y"), variable("dropped")],
                                rest: Some(ident("inner_rest")),
                            }],
                        ),
                    ],
                ),
            ],
            rest: Some(ident("outer_rest")),
        }],
    )
}

#[test]
fn shared_nested_match_pda_matches_both_recursive_policies() {
    let pattern = fixture();
    let nonlinear = ident("M");
    let outer_rest = ident("outer_rest");
    let mut actual_next = 0;
    let mut expected_next = 0;
    let mut actual_occurrences = Vec::new();
    let mut expected_occurrences = Vec::new();
    let actual = nested_match_pattern_for(
        &pattern,
        &nonlinear,
        &outer_rest,
        2,
        &mut actual_next,
        &mut actual_occurrences,
        "test-fingerprint",
    );
    let expected = recursive_report_pattern(
        &pattern,
        &nonlinear,
        &outer_rest,
        2,
        &mut expected_next,
        &mut expected_occurrences,
        "test-fingerprint",
    );
    assert_eq!(actual, expected);
    assert_eq!(actual_next, expected_next);
    assert_eq!(actual_occurrences, expected_occurrences);

    let referenced = HashSet::from([
        "M".to_owned(),
        "x".to_owned(),
        "y".to_owned(),
        "inner_rest".to_owned(),
        "outer_rest".to_owned(),
    ]);
    let mut actual_state = NestedBindState {
        next_level: 0,
        slot_of: HashMap::new(),
        occurrence_levels: Vec::new(),
    };
    let mut expected_state = NestedBindState {
        next_level: 0,
        slot_of: HashMap::new(),
        occurrence_levels: Vec::new(),
    };
    let actual = nested_match_bind_pattern_for(
        &pattern,
        &nonlinear,
        &referenced,
        &mut actual_state,
        "test-fingerprint",
    );
    let expected = recursive_binding_pattern(
        &pattern,
        &nonlinear,
        &referenced,
        &mut expected_state,
        "test-fingerprint",
    );
    assert_eq!(actual, expected);
    assert_eq!(actual_state.next_level, expected_state.next_level);
    assert_eq!(actual_state.slot_of, expected_state.slot_of);
    assert_eq!(actual_state.occurrence_levels, expected_state.occurrence_levels);
}

#[test]
fn deep_nested_match_policies_fit_on_a_small_native_stack() {
    // A reflected Par node is substantially larger than its source Pattern
    // node. This depth already exceeds the former 256 KiB recursion budget
    // while keeping the exact output tree's resident size modest.
    const DEPTH: usize = 2_000;
    let handle = std::thread::Builder::new()
        .name("nested-match-policy-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = variable("M");
            for _ in 0..DEPTH {
                pattern = apply("Node", vec![pattern]);
            }
            let nonlinear = ident("M");
            let rest = ident("rest");
            let mut next = 0;
            let mut occurrences = Vec::new();
            let report = nested_match_pattern_for(
                &pattern,
                &nonlinear,
                &rest,
                1,
                &mut next,
                &mut occurrences,
                "test-fingerprint",
            );
            assert_eq!(next, 1);
            assert_eq!(occurrences, [0]);
            drop(report);

            let mut state = NestedBindState {
                next_level: 0,
                slot_of: HashMap::new(),
                occurrence_levels: Vec::new(),
            };
            let bound = nested_match_bind_pattern_for(
                &pattern,
                &nonlinear,
                &HashSet::from(["M".to_owned()]),
                &mut state,
                "test-fingerprint",
            );
            assert_eq!(state.next_level, 1);
            assert_eq!(state.occurrence_levels, [0]);
            drop(bound);
            drop(pattern);
        })
        .expect("small-stack nested match policy thread must spawn");
    handle
        .join()
        .expect("nested match policy PDA must not overflow the native stack");
}
