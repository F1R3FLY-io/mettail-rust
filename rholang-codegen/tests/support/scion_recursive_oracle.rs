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

fn recursive_could_unify(lhs: &Pattern, sub: &Pattern) -> bool {
    match (lhs, sub) {
        (Pattern::Term(PatternTerm::Var(_)), _) | (_, Pattern::Term(PatternTerm::Var(_))) => true,
        (
            Pattern::Term(PatternTerm::Apply { constructor: c1, args: a1 }),
            Pattern::Term(PatternTerm::Apply { constructor: c2, args: a2 }),
        ) => {
            c1 == c2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2)
                    .all(|(left, right)| recursive_could_unify(left, right))
        },
        _ => true,
    }
}

fn recursive_contains_recheck(pattern: &Pattern, fireable_lhs: &[&Pattern]) -> bool {
    match pattern {
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            fireable_lhs
                .iter()
                .any(|lhs| recursive_could_unify(lhs, pattern))
                || args
                    .iter()
                    .any(|arg| recursive_contains_recheck(arg, fireable_lhs))
        },
        _ => false,
    }
}

fn recursive_collect_slots(
    rhs: &Pattern,
    path: &mut Vec<usize>,
    sigma_set: &HashSet<String>,
    out: &mut Vec<(Vec<usize>, String)>,
) -> Result<(), String> {
    match rhs {
        Pattern::Term(PatternTerm::Var(name)) => {
            let name = name.to_string();
            if sigma_set.contains(&name) {
                out.push((path.clone(), name));
                Ok(())
            } else {
                Err(format!("scion: RHS variable {name:?} is not a σ capture (dangling)"))
            }
        },
        Pattern::Term(PatternTerm::Apply { args, .. }) => {
            for (index, arg) in args.iter().enumerate() {
                path.push(index);
                recursive_collect_slots(arg, path, sigma_set, out)?;
                path.pop();
            }
            Ok(())
        },
        _ => Err("scion: non-positional RHS shape (binder / substitution / collection) is not \
             driver-scion-supported this stage"
            .to_string()),
    }
}

fn recursive_build_pure(
    pattern: &Pattern,
    path: &[usize],
    slot_index: &HashMap<Vec<usize>, usize>,
    env: &Env,
    fingerprint: &str,
) -> Node {
    match pattern {
        Pattern::Term(PatternTerm::Var(_)) => {
            let index = slot_index.get(path).copied().unwrap_or(0);
            env.var(&format!("s{index}"))
        },
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let children = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let mut child_path = path.to_vec();
                    child_path.push(index);
                    recursive_build_pure(arg, &child_path, slot_index, env, fingerprint)
                })
                .collect();
            tagged(fingerprint, &constructor.to_string(), children)
        },
        _ => tagged(fingerprint, "^scion-bug", Vec::new()),
    }
}

fn recursive_build_raw(pattern: &Pattern, env: &Env, fingerprint: &str) -> Node {
    match pattern {
        Pattern::Term(PatternTerm::Var(name)) => env.var(&name.to_string()),
        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
            let children = args
                .iter()
                .map(|arg| recursive_build_raw(arg, env, fingerprint))
                .collect();
            tagged(fingerprint, &constructor.to_string(), children)
        },
        _ => tagged(fingerprint, "^scion-bug", Vec::new()),
    }
}

fn recursive_emit_recheck_point(
    subtree: &Pattern,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    next_index: &std::cell::Cell<usize>,
    tail: &dyn Fn(Node, &Env) -> Result<Node, String>,
) -> Result<Node, String> {
    let index = next_index.get();
    next_index.set(index + 1);
    let return_name = format!("r{index}");
    let child_name = format!("c{index}");
    let return_env = env.push(&[return_name.as_str()]);
    let drive_call = send(
        ground(tag_par(fingerprint, DRIVE_RESERVED_LABEL)),
        vec![
            recursive_build_raw(subtree, &return_env, fingerprint),
            eminus(return_env.var(fuel_var), gint(1)),
            return_env.var(&return_name),
        ],
    );
    let child_env = return_env.push(&[child_name.as_str()]);
    let body = tail(child_env.var(&child_name), &child_env)?;
    Ok(new_scope(1, par2(drive_call, for1(return_env.var(&return_name), body))))
}

#[allow(clippy::too_many_arguments)]
fn recursive_emit_point(
    pattern: &Pattern,
    path: &[usize],
    slot_index: &HashMap<Vec<usize>, usize>,
    fireable_lhs: &[&Pattern],
    redex_roots: &HashSet<String>,
    fingerprint: &str,
    env: &Env,
    fuel_var: &str,
    next_index: &std::cell::Cell<usize>,
    tail: &dyn Fn(Node, &Env) -> Result<Node, String>,
) -> Result<Node, String> {
    if !recursive_contains_recheck(pattern, fireable_lhs) {
        return tail(recursive_build_pure(pattern, path, slot_index, env, fingerprint), env);
    }
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return Err("scion: re-check at a non-constructor RHS position".to_string());
    };
    let label = constructor.to_string();
    if fireable_lhs
        .iter()
        .any(|lhs| recursive_could_unify(lhs, pattern))
    {
        if args
            .iter()
            .any(|arg| recursive_contains_recheck(arg, fireable_lhs))
        {
            return Err(
                "scion: nested re-check (re-check above a re-check) unsupported this stage"
                    .to_string(),
            );
        }
        return recursive_emit_recheck_point(pattern, fingerprint, env, fuel_var, next_index, tail);
    }
    if redex_roots.contains(&label) {
        return Err(format!(
            "scion: inert-graft rootedness (Fold 1) — Skip ctor {label:?} is a rule redex root \
             above a reducible subtree; grafting it inert could under-reduce vs control"
        ));
    }
    let non_pure: Vec<usize> = (0..args.len())
        .filter(|&index| recursive_contains_recheck(&args[index], fireable_lhs))
        .collect();
    if non_pure.len() > 1 {
        return Err(
            "scion: branching re-check (>1 re-check child) unsupported this stage".to_string()
        );
    }
    let selected = non_pure[0];
    let mut child_path = path.to_vec();
    child_path.push(selected);
    let child_tail = |child_value: Node, tail_env: &Env| -> Result<Node, String> {
        let children = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                if index == selected {
                    child_value.clone()
                } else {
                    let mut sibling_path = path.to_vec();
                    sibling_path.push(index);
                    recursive_build_pure(arg, &sibling_path, slot_index, tail_env, fingerprint)
                }
            })
            .collect();
        tail(tagged(fingerprint, &label, children), tail_env)
    };
    recursive_emit_point(
        &args[selected],
        &child_path,
        slot_index,
        fireable_lhs,
        redex_roots,
        fingerprint,
        env,
        fuel_var,
        next_index,
        &child_tail,
    )
}

#[test]
fn iterative_scion_algorithms_match_recursive_oracles() {
    let lhs = apply("Hit", vec![variable("needle")]);
    let rhs = apply("Outer", vec![variable("left"), apply("Hit", vec![variable("right")])]);
    let fireable = [&lhs];
    assert_eq!(scion_could_unify(&lhs, &rhs), recursive_could_unify(&lhs, &rhs));
    let index = scion_recheck_index(&rhs, &fireable);
    assert_eq!(
        index.get(&(&rhs as *const Pattern)).copied(),
        Some(recursive_contains_recheck(&rhs, &fireable))
    );

    let sigma = HashSet::from(["left".to_string(), "right".to_string()]);
    let mut actual_slots = Vec::new();
    let mut expected_slots = Vec::new();
    scion_collect_slots(&rhs, &mut Vec::new(), &sigma, &mut actual_slots)
        .expect("iterative slot collection succeeds");
    recursive_collect_slots(&rhs, &mut Vec::new(), &sigma, &mut expected_slots)
        .expect("recursive slot collection succeeds");
    assert_eq!(actual_slots, expected_slots);

    let slot_index = HashMap::from([(vec![0], 0), (vec![1, 0], 1)]);
    let env = Env::root(&["fuel", "ret", "left", "right", "s0", "s1"]);
    let actual = scion_build_pure(&rhs, &[], &slot_index, &env, "oracle-fp");
    let expected = recursive_build_pure(&rhs, &[], &slot_index, &env, "oracle-fp");
    assert_eq!(actual.par, expected.par);
    assert_eq!(actual.free, expected.free);
    let actual = scion_build_raw(&rhs, &env, "oracle-fp");
    let expected = recursive_build_raw(&rhs, &env, "oracle-fp");
    assert_eq!(actual.par, expected.par);
    assert_eq!(actual.free, expected.free);

    let redex_roots = HashSet::from(["Hit".to_string()]);
    let tail = |value: Node, tail_env: &Env| Ok(send(tail_env.var("ret"), vec![value]));
    let actual_next = std::cell::Cell::new(2);
    let expected_next = std::cell::Cell::new(2);
    let actual = scion_emit_point(
        &rhs,
        &[],
        &slot_index,
        &fireable,
        &redex_roots,
        "oracle-fp",
        &env,
        "fuel",
        &actual_next,
        &tail,
    )
    .expect("iterative emitter succeeds");
    let expected = recursive_emit_point(
        &rhs,
        &[],
        &slot_index,
        &fireable,
        &redex_roots,
        "oracle-fp",
        &env,
        "fuel",
        &expected_next,
        &tail,
    )
    .expect("recursive emitter succeeds");
    assert_eq!(actual.par, expected.par);
    assert_eq!(actual.free, expected.free);
    assert_eq!(actual_next.get(), expected_next.get());
}

#[test]
fn scion_pdas_handle_deep_inputs_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("rho-scion-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const ANALYSIS_DEPTH: usize = 20_000;
            let mut lhs = variable("x");
            let mut rhs = variable("x");
            for _ in 0..ANALYSIS_DEPTH {
                lhs = apply("N", vec![lhs]);
                rhs = apply("N", vec![rhs]);
            }
            assert!(scion_could_unify(&lhs, &rhs));
            let mut slots = Vec::new();
            scion_collect_slots(
                &rhs,
                &mut Vec::new(),
                &HashSet::from(["x".to_string()]),
                &mut slots,
            )
            .expect("deep slot collection succeeds");
            assert_eq!(slots[0].0.len(), ANALYSIS_DEPTH);
            drop(lhs);
            drop(rhs);

            const EMIT_DEPTH: usize = 2_000;
            let lhs = apply("Hit", vec![variable("slot")]);
            let mut rhs = apply("Hit", vec![variable("slot")]);
            for _ in 0..EMIT_DEPTH {
                rhs = apply("N", vec![rhs]);
            }
            let env = Env::root(&["fuel", "ret", "slot"]);
            let tail = |value: Node, tail_env: &Env| Ok(send(tail_env.var("ret"), vec![value]));
            let emitted = scion_emit_point(
                &rhs,
                &[],
                &HashMap::new(),
                &[&lhs],
                &HashSet::from(["Hit".to_string()]),
                "deep-fp",
                &env,
                "fuel",
                &std::cell::Cell::new(0),
                &tail,
            )
            .expect("deep scion spine emits iteratively");
            assert!(!emitted.par.news.is_empty());
        })
        .expect("small-stack thread starts")
        .join()
        .expect("scion PDAs do not overflow a 256 KiB stack");
}
