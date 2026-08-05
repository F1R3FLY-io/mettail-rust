use super::*;
use syn::Ident;

fn ident(name: &str) -> Ident {
    syn::parse_str(name).expect("test identifier must parse")
}

fn recursive_pred_has_structural_component(pred: &BehavioralPred) -> bool {
    match pred {
        BehavioralPred::AcMatch { .. } => true,
        BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
            recursive_pred_has_structural_component(body)
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            recursive_pred_has_structural_component(left)
                || recursive_pred_has_structural_component(right)
        },
        BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => false,
    }
}

fn recursive_collect_term_param_guard_obligations(
    label: &str,
    params: &[TermParam],
    declared: &BTreeSet<String>,
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    for param in params {
        match param {
            TermParam::GuardBody { name } => {
                out.insert(RhoGuardObligation::new(
                    format!("term:{label}:guard:{name}"),
                    RhoGuardObligationKind::BehavioralPredicate,
                ));
            },
            TermParam::Simple { name, .. } if declared.contains(&name.to_string()) => {
                out.insert(RhoGuardObligation::new(
                    format!("term:{label}:guard:{name}"),
                    RhoGuardObligationKind::BehavioralPredicate,
                ));
            },
            TermParam::Optional { params } => {
                recursive_collect_term_param_guard_obligations(label, params, declared, out);
            },
            TermParam::Simple { .. }
            | TermParam::Abstraction { .. }
            | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

fn recursive_params_have_guard_body(params: &[TermParam]) -> bool {
    params.iter().any(|param| match param {
        TermParam::GuardBody { .. } => true,
        TermParam::Optional { params } => recursive_params_have_guard_body(params),
        TermParam::Simple { .. }
        | TermParam::Abstraction { .. }
        | TermParam::MultiAbstraction { .. } => false,
    })
}

fn recursive_collect_premise_guard_obligations(
    owner_kind: &str,
    owner_name: &str,
    premises: &[Premise],
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    fn walk(
        owner_kind: &str,
        owner_name: &str,
        premise: &Premise,
        index: usize,
        out: &mut BTreeSet<RhoGuardObligation>,
    ) {
        match premise {
            Premise::BehavioralGuard(pred) => {
                out.insert(RhoGuardObligation::new(
                    format!("{owner_kind}:{owner_name}:guard:{index}"),
                    guard_pred_obligation_kind(pred),
                ));
            },
            Premise::ForAll { body, .. } => walk(owner_kind, owner_name, body, index, out),
            Premise::Freshness(_)
            | Premise::Congruence { .. }
            | Premise::CongruenceWithheld { .. }
            | Premise::RelationQuery { .. }
            | Premise::SyntheticInjGuard { .. } => {},
        }
    }

    for (index, premise) in premises.iter().enumerate() {
        walk(owner_kind, owner_name, premise, index, out);
    }
}

fn structural_predicate() -> BehavioralPred {
    BehavioralPred::And(
        Box::new(BehavioralPred::Top),
        Box::new(BehavioralPred::Not(Box::new(BehavioralPred::AcMatch {
            bag: ident("bag"),
            elements: vec![ident("x")],
            rest: Some(ident("rest")),
        }))),
    )
}

fn nested_optional(depth: usize, leaf: TermParam) -> Vec<TermParam> {
    let mut leaf = leaf;
    for _ in 0..depth {
        leaf = TermParam::Optional { params: vec![leaf] };
    }
    vec![leaf]
}

fn nested_premise(depth: usize, leaf: Premise) -> Premise {
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

#[test]
fn iterative_backend_guard_walkers_match_recursive_oracles() {
    let non_structural = BehavioralPred::Not(Box::new(BehavioralPred::And(
        Box::new(BehavioralPred::Top),
        Box::new(BehavioralPred::Top),
    )));
    for pred in [&non_structural, &structural_predicate()] {
        assert_eq!(
            pred_has_structural_component(pred),
            recursive_pred_has_structural_component(pred)
        );
    }

    let declared = BTreeSet::from(["declared".to_owned()]);
    for depth in 0..64 {
        let mut params = nested_optional(depth, TermParam::GuardBody { name: ident("body") });
        params.push(TermParam::Simple {
            name: ident("declared"),
            ty: TypeExpr::Base(ident("Proc")),
        });
        params.push(TermParam::Simple {
            name: ident("ordinary"),
            ty: TypeExpr::Base(ident("Proc")),
        });

        let mut actual = BTreeSet::new();
        let mut expected = BTreeSet::new();
        collect_term_param_guard_obligations("Send", &params, &declared, &mut actual);
        recursive_collect_term_param_guard_obligations("Send", &params, &declared, &mut expected);
        assert_eq!(actual, expected);
        assert_eq!(params_have_guard_body(&params), recursive_params_have_guard_body(&params));

        let premises = vec![
            nested_premise(depth, Premise::BehavioralGuard(structural_predicate())),
            Premise::BehavioralGuard(BehavioralPred::Top),
        ];
        let mut actual = BTreeSet::new();
        let mut expected = BTreeSet::new();
        collect_premise_guard_obligations("rewrite", "Send", &premises, &mut actual);
        recursive_collect_premise_guard_obligations("rewrite", "Send", &premises, &mut expected);
        assert_eq!(actual, expected);
    }
}

#[test]
fn deep_backend_guard_metadata_walks_fit_on_a_small_native_stack() {
    const DEPTH: usize = 20_000;
    let handle = std::thread::Builder::new()
        .name("backend-guard-metadata-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let params = nested_optional(DEPTH, TermParam::GuardBody { name: ident("guard") });
            let mut obligations = BTreeSet::new();
            collect_term_param_guard_obligations(
                "Deep",
                &params,
                &BTreeSet::new(),
                &mut obligations,
            );
            assert!(params_have_guard_body(&params));
            assert_eq!(obligations.len(), 1);
            drop(params);

            let premises =
                vec![nested_premise(DEPTH, Premise::BehavioralGuard(BehavioralPred::Top))];
            obligations.clear();
            collect_premise_guard_obligations("rewrite", "Deep", &premises, &mut obligations);
            assert_eq!(obligations.len(), 1);
            drop(premises);
        })
        .expect("small-stack backend metadata thread must spawn");
    handle
        .join()
        .expect("backend guard metadata PDAs must not overflow the native stack");
}
