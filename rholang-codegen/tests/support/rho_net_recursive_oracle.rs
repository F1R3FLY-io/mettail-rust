use super::*;
use syn::Ident;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn recursive_add_term_guard_predicates_for_params(
    program: &mut RhoNetProgram,
    label: &str,
    params: &[TermParam],
) {
    for param in params {
        match param {
            TermParam::GuardBody { name } => {
                program.push_semantic_predicate(RhoNetSemanticPredicate::new(
                    format!("term:{label}:guard:{name}"),
                    RhoNetSemanticPredicateQuality::RuntimeObservation,
                ));
            },
            TermParam::Optional { params } => {
                recursive_add_term_guard_predicates_for_params(program, label, params);
            },
            TermParam::Simple { .. }
            | TermParam::Abstraction { .. }
            | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

fn recursive_add_premise_input(
    program: &mut RhoNetProgram,
    owner_kind: &str,
    owner_name: &str,
    index: usize,
    premise: &Premise,
    inputs: &mut Vec<String>,
    semantic_guards: &mut Vec<String>,
) {
    match premise {
        Premise::Freshness(_) => program.push_consistency_input(
            format!("{owner_kind}/{owner_name}/freshness/{index}"),
            premise,
            inputs,
        ),
        Premise::RelationQuery { .. } => program.push_consistency_input(
            format!("{owner_kind}/{owner_name}/relation/{index}"),
            premise,
            inputs,
        ),
        Premise::SyntheticInjGuard { .. } => program.push_consistency_input(
            format!("{owner_kind}/{owner_name}/synthetic-injection/{index}"),
            premise,
            inputs,
        ),
        Premise::Congruence { source, target } => {
            let channel = RhoNetChannel::location(
                &program.language_fingerprint,
                format!(
                    "{owner_kind}/{owner_name}/contextual-premise/{index}/{source}-to-{target}"
                ),
            );
            inputs.push(channel.name.clone());
            program.push_channel(channel);
        },
        Premise::CongruenceWithheld { .. } => {},
        Premise::ForAll { body, .. } => {
            program.push_consistency_input(
                format!("{owner_kind}/{owner_name}/forall/{index}"),
                premise,
                inputs,
            );
            recursive_add_premise_input(
                program,
                owner_kind,
                owner_name,
                index,
                body,
                inputs,
                semantic_guards,
            );
        },
        Premise::BehavioralGuard(pred) => {
            let id = format!("{owner_kind}:{owner_name}:guard:{index}");
            if recursive_behavioral_predicate_has_structural_component(pred) {
                let channel = RhoNetChannel::consistency(
                    &program.language_fingerprint,
                    format!(
                        "{owner_kind}/{owner_name}/structural-guard/{index}/{}",
                        fingerprint_fragment("behavioral", &behavioral_predicate_identity(pred))
                    ),
                );
                inputs.push(channel.name.clone());
                program.push_channel(channel);
            } else {
                program.push_semantic_predicate(RhoNetSemanticPredicate::new(
                    id.clone(),
                    semantic_predicate_quality(pred),
                ));
                semantic_guards.push(id);
            }
        },
    }
}

fn recursive_behavioral_predicate_has_structural_component(pred: &BehavioralPred) -> bool {
    match pred {
        BehavioralPred::AcMatch { .. } => true,
        BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
            recursive_behavioral_predicate_has_structural_component(body)
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            recursive_behavioral_predicate_has_structural_component(left)
                || recursive_behavioral_predicate_has_structural_component(right)
        },
        BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => false,
    }
}

fn nested_optional(depth: usize, leaf: TermParam) -> Vec<TermParam> {
    let mut leaf = leaf;
    for _ in 0..depth {
        leaf = TermParam::Optional { params: vec![leaf] };
    }
    vec![leaf]
}

fn nested_forall(depth: usize, leaf: Premise) -> Premise {
    let mut leaf = leaf;
    for _ in 0..depth {
        leaf = Premise::ForAll {
            collection: ident("values"),
            param: ident("value"),
            body: Box::new(leaf),
        };
    }
    leaf
}

fn structural_predicate() -> BehavioralPred {
    BehavioralPred::Or(
        Box::new(BehavioralPred::Top),
        Box::new(BehavioralPred::Not(Box::new(BehavioralPred::AcMatch {
            bag: ident("bag"),
            elements: vec![ident("x"), ident("y")],
            rest: None,
        }))),
    )
}

#[test]
fn iterative_rho_net_guard_walkers_match_recursive_oracles() {
    let structural = structural_predicate();
    let non_structural = BehavioralPred::Not(Box::new(BehavioralPred::Top));
    for pred in [&structural, &non_structural] {
        assert_eq!(
            behavioral_predicate_has_structural_component(pred),
            recursive_behavioral_predicate_has_structural_component(pred)
        );
    }

    for depth in 0..64 {
        let params = nested_optional(depth, TermParam::GuardBody { name: ident("guard") });
        let mut actual = RhoNetProgram::new("test-fingerprint");
        let mut expected = actual.clone();
        actual.add_term_guard_predicates_for_params("Send", &params);
        recursive_add_term_guard_predicates_for_params(&mut expected, "Send", &params);
        assert_eq!(actual, expected);

        let premise = nested_forall(
            depth,
            Premise::BehavioralGuard(if depth % 2 == 0 {
                BehavioralPred::Top
            } else {
                structural_predicate()
            }),
        );
        let mut actual = RhoNetProgram::new("test-fingerprint");
        let mut expected = actual.clone();
        let mut actual_inputs = Vec::new();
        let mut expected_inputs = Vec::new();
        let mut actual_guards = Vec::new();
        let mut expected_guards = Vec::new();
        actual.add_premise_input(
            "rewrite",
            "Send",
            3,
            &premise,
            &mut actual_inputs,
            &mut actual_guards,
        );
        recursive_add_premise_input(
            &mut expected,
            "rewrite",
            "Send",
            3,
            &premise,
            &mut expected_inputs,
            &mut expected_guards,
        );
        assert_eq!(actual, expected);
        assert_eq!(actual_inputs, expected_inputs);
        assert_eq!(actual_guards, expected_guards);
    }
}

#[test]
fn deep_rho_net_guard_walks_fit_on_a_small_native_stack() {
    const PARAM_DEPTH: usize = 20_000;
    const PREMISE_DEPTH: usize = 2_000;
    let handle = std::thread::Builder::new()
        .name("rho-net-guard-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let params =
                nested_optional(PARAM_DEPTH, TermParam::GuardBody { name: ident("guard") });
            let mut program = RhoNetProgram::new("test-fingerprint");
            program.add_term_guard_predicates_for_params("Deep", &params);
            assert_eq!(program.semantic_predicates.len(), 1);
            drop(params);

            // Each nested quantifier intentionally contributes its own stable
            // consistency-channel identity. Two thousand levels are enough to
            // exceed the old native recursion budget while keeping the test's
            // exact canonical-identity workload proportionate.
            let premise =
                nested_forall(PREMISE_DEPTH, Premise::BehavioralGuard(BehavioralPred::Top));
            let mut inputs = Vec::new();
            let mut guards = Vec::new();
            program.add_premise_input("rewrite", "Deep", 0, &premise, &mut inputs, &mut guards);
            assert_eq!(inputs.len(), PREMISE_DEPTH);
            assert_eq!(guards, ["rewrite:Deep:guard:0"]);
            drop(premise);
        })
        .expect("small-stack RhoNet guard thread must spawn");
    handle
        .join()
        .expect("RhoNet guard PDAs must not overflow the native stack");
}
