use mettail_ast::language::{
    ConstraintDomain, LinearRelation, PredArg, Quantifier, RefinementPredicate,
};
use proc_macro2::{Ident, Span};

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

#[allow(dead_code)]
#[derive(Debug)]
enum RefinementOracle<'tree> {
    Linear {
        terms: &'tree [(Ident, i64)],
        relation: &'tree LinearRelation,
        rhs: i64,
    },
    Relation {
        name: &'tree Ident,
        args: &'tree [PredArg],
        negated: bool,
    },
    Quantified {
        quantifier: &'tree Quantifier,
        var: &'tree Ident,
        domain: &'tree Option<Ident>,
        bound: Option<usize>,
        body: Box<RefinementOracle<'tree>>,
    },
    And(Box<RefinementOracle<'tree>>, Box<RefinementOracle<'tree>>),
    Or(Box<RefinementOracle<'tree>>, Box<RefinementOracle<'tree>>),
    Not(Box<RefinementOracle<'tree>>),
    Implies(Box<RefinementOracle<'tree>>, Box<RefinementOracle<'tree>>),
    TermEq(&'tree PredArg, &'tree PredArg),
    TermNeq(&'tree PredArg, &'tree PredArg),
}

fn debug_oracle(predicate: &RefinementPredicate) -> RefinementOracle<'_> {
    match predicate {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            RefinementOracle::Linear { terms, relation, rhs: *rhs }
        },
        RefinementPredicate::Relation { name, args, negated } => {
            RefinementOracle::Relation { name, args, negated: *negated }
        },
        RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
            RefinementOracle::Quantified {
                quantifier,
                var,
                domain,
                bound: *bound,
                body: Box::new(debug_oracle(body)),
            }
        },
        RefinementPredicate::And(left, right) => {
            RefinementOracle::And(Box::new(debug_oracle(left)), Box::new(debug_oracle(right)))
        },
        RefinementPredicate::Or(left, right) => {
            RefinementOracle::Or(Box::new(debug_oracle(left)), Box::new(debug_oracle(right)))
        },
        RefinementPredicate::Not(inner) => RefinementOracle::Not(Box::new(debug_oracle(inner))),
        RefinementPredicate::Implies(left, right) => {
            RefinementOracle::Implies(Box::new(debug_oracle(left)), Box::new(debug_oracle(right)))
        },
        RefinementPredicate::TermEq(left, right) => RefinementOracle::TermEq(left, right),
        RefinementPredicate::TermNeq(left, right) => RefinementOracle::TermNeq(left, right),
    }
}

fn recursive_display(predicate: &RefinementPredicate, output: &mut String) {
    use std::fmt::Write;
    match predicate {
        RefinementPredicate::Linear { terms, relation, rhs } => {
            for (index, (variable, coefficient)) in terms.iter().enumerate() {
                if index != 0 {
                    output.push_str(" + ");
                }
                if *coefficient == 1 {
                    write!(output, "{variable}").expect("String writes cannot fail");
                } else {
                    write!(output, "{coefficient}*{variable}").expect("String writes cannot fail");
                }
            }
            write!(output, " {relation} {rhs}").expect("String writes cannot fail");
        },
        RefinementPredicate::Relation { name, args, negated } => {
            if *negated {
                output.push('~');
            }
            write!(output, "{name}(").expect("String writes cannot fail");
            for (index, argument) in args.iter().enumerate() {
                if index != 0 {
                    output.push_str(", ");
                }
                match argument {
                    PredArg::Var(value) | PredArg::Constant(value) => {
                        write!(output, "{value}").expect("String writes cannot fail");
                    },
                }
            }
            output.push(')');
        },
        RefinementPredicate::Quantified { quantifier, var, domain, bound, body } => {
            output.push_str(match quantifier {
                Quantifier::ForAll => "forall",
                Quantifier::Exists => "exists",
            });
            if let Some(bound) = bound {
                write!(output, "_{{k={bound}}}").expect("String writes cannot fail");
            }
            write!(output, " {var}").expect("String writes cannot fail");
            if let Some(domain) = domain {
                write!(output, " in {domain}").expect("String writes cannot fail");
            }
            output.push_str(". (");
            recursive_display(body, output);
            output.push(')');
        },
        RefinementPredicate::And(left, right)
        | RefinementPredicate::Or(left, right)
        | RefinementPredicate::Implies(left, right) => {
            output.push('(');
            recursive_display(left, output);
            output.push_str(match predicate {
                RefinementPredicate::And(..) => " && ",
                RefinementPredicate::Or(..) => " || ",
                RefinementPredicate::Implies(..) => " => ",
                _ => unreachable!(),
            });
            recursive_display(right, output);
            output.push(')');
        },
        RefinementPredicate::Not(inner) => {
            output.push('~');
            recursive_display(inner, output);
        },
        RefinementPredicate::TermEq(left, right) | RefinementPredicate::TermNeq(left, right) => {
            let write_arg = |argument: &PredArg, output: &mut String| match argument {
                PredArg::Var(value) | PredArg::Constant(value) => {
                    write!(output, "{value}").expect("String writes cannot fail");
                },
            };
            write_arg(left, output);
            output.push_str(if matches!(predicate, RefinementPredicate::TermEq(..)) {
                " == "
            } else {
                " != "
            });
            write_arg(right, output);
        },
    }
}

fn recursive_classify(predicate: &RefinementPredicate) -> ConstraintDomain {
    fn flatten(domain: &ConstraintDomain, output: &mut Vec<ConstraintDomain>) {
        match domain {
            ConstraintDomain::Product(children) => {
                for child in children {
                    flatten(child, output);
                }
            },
            leaf => output.push(leaf.clone()),
        }
    }

    fn merge(left: ConstraintDomain, right: ConstraintDomain) -> ConstraintDomain {
        if left == right {
            return left;
        }
        let mut children = Vec::new();
        flatten(&left, &mut children);
        flatten(&right, &mut children);
        let mut seen = Vec::new();
        children.retain(|domain| {
            if seen.contains(domain) {
                false
            } else {
                seen.push(domain.clone());
                true
            }
        });
        if children.len() == 1 {
            children.pop().expect("deduplicated domain is non-empty")
        } else {
            ConstraintDomain::Product(children)
        }
    }

    match predicate {
        RefinementPredicate::Linear { .. } => ConstraintDomain::Presburger,
        RefinementPredicate::Relation { .. } | RefinementPredicate::Quantified { .. } => {
            ConstraintDomain::Behavioral
        },
        RefinementPredicate::TermEq(..) | RefinementPredicate::TermNeq(..) => {
            ConstraintDomain::Unification
        },
        RefinementPredicate::Not(inner) => recursive_classify(inner),
        RefinementPredicate::And(left, right)
        | RefinementPredicate::Or(left, right)
        | RefinementPredicate::Implies(left, right) => {
            merge(recursive_classify(left), recursive_classify(right))
        },
    }
}

fn linear(name: &str) -> RefinementPredicate {
    RefinementPredicate::Linear {
        terms: vec![(ident(name), 3), (ident("offset"), -2)],
        relation: LinearRelation::Le,
        rhs: 17,
    }
}

fn relation(name: &str) -> RefinementPredicate {
    RefinementPredicate::Relation {
        name: ident(name),
        args: vec![PredArg::Var(ident("x")), PredArg::Constant(ident("Root"))],
        negated: name == "blocked",
    }
}

fn rich_predicate() -> RefinementPredicate {
    RefinementPredicate::Implies(
        Box::new(RefinementPredicate::And(
            Box::new(linear("x")),
            Box::new(RefinementPredicate::Quantified {
                quantifier: Quantifier::Exists,
                var: ident("candidate"),
                domain: Some(ident("nodes")),
                bound: Some(9),
                body: Box::new(relation("reachable")),
            }),
        )),
        Box::new(RefinementPredicate::Or(
            Box::new(RefinementPredicate::Not(Box::new(relation("blocked")))),
            Box::new(RefinementPredicate::And(
                Box::new(RefinementPredicate::TermEq(
                    PredArg::Var(ident("x")),
                    PredArg::Constant(ident("Nil")),
                )),
                Box::new(RefinementPredicate::TermNeq(
                    PredArg::Var(ident("x")),
                    PredArg::Var(ident("y")),
                )),
            )),
        )),
    )
}

#[allow(dead_code)]
#[derive(Debug)]
enum DomainOracle {
    Presburger,
    Lattice,
    Behavioral,
    Unification,
    Product(Vec<DomainOracle>),
}

fn domain_debug_oracle(domain: &ConstraintDomain) -> DomainOracle {
    match domain {
        ConstraintDomain::Presburger => DomainOracle::Presburger,
        ConstraintDomain::Lattice => DomainOracle::Lattice,
        ConstraintDomain::Behavioral => DomainOracle::Behavioral,
        ConstraintDomain::Unification => DomainOracle::Unification,
        ConstraintDomain::Product(children) => {
            DomainOracle::Product(children.iter().map(domain_debug_oracle).collect())
        },
    }
}

fn recursive_domain_display(domain: &ConstraintDomain, output: &mut String) {
    match domain {
        ConstraintDomain::Presburger => output.push_str("Presburger"),
        ConstraintDomain::Lattice => output.push_str("Lattice"),
        ConstraintDomain::Behavioral => output.push_str("Behavioral"),
        ConstraintDomain::Unification => output.push_str("Unification"),
        ConstraintDomain::Product(children) => {
            output.push_str("Product(");
            for (index, child) in children.iter().enumerate() {
                if index != 0 {
                    output.push_str(", ");
                }
                recursive_domain_display(child, output);
            }
            output.push(')');
        },
    }
}

#[test]
fn refinement_pdas_match_recursive_and_derived_oracles() {
    let predicate = rich_predicate();
    assert_eq!(format!("{predicate:?}"), format!("{:?}", debug_oracle(&predicate)));
    assert_eq!(format!("{predicate:#?}"), format!("{:#?}", debug_oracle(&predicate)));

    let mut expected_display = String::new();
    recursive_display(&predicate, &mut expected_display);
    assert_eq!(predicate.to_string(), expected_display);
    assert_eq!(predicate.classify(), recursive_classify(&predicate));
    assert_eq!(predicate.to_pred_kind_str(), "Mixed");

    let behavioral_quantifier = RefinementPredicate::Quantified {
        quantifier: Quantifier::ForAll,
        var: ident("x"),
        domain: None,
        bound: None,
        body: Box::new(linear("x")),
    };
    assert_eq!(behavioral_quantifier.classify(), ConstraintDomain::Behavioral);
}

#[test]
fn constraint_domain_pdas_match_recursive_and_derived_oracles() {
    let domain = ConstraintDomain::Product(vec![
        ConstraintDomain::Presburger,
        ConstraintDomain::Product(vec![
            ConstraintDomain::Lattice,
            ConstraintDomain::Behavioral,
            ConstraintDomain::Product(vec![ConstraintDomain::Unification]),
        ]),
    ]);
    assert_eq!(format!("{domain:?}"), format!("{:?}", domain_debug_oracle(&domain)));
    assert_eq!(format!("{domain:#?}"), format!("{:#?}", domain_debug_oracle(&domain)));
    let mut expected_display = String::new();
    recursive_domain_display(&domain, &mut expected_display);
    assert_eq!(domain.to_string(), expected_display);
    assert_eq!(domain, domain.clone());
}

#[test]
fn refinement_and_domain_lifecycle_handle_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("refinement-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut predicate = linear("x");
            for _ in 0..DEPTH {
                predicate = RefinementPredicate::Not(Box::new(predicate));
            }
            let clone = predicate.clone();
            assert_eq!(predicate.classify(), ConstraintDomain::Presburger);
            assert!(format!("{predicate:?}").starts_with("Not(Not(Not("));
            assert!(predicate.to_string().starts_with("~~~"));
            drop(clone);
            drop(predicate);

            let mut domain = ConstraintDomain::Presburger;
            for _ in 0..DEPTH {
                domain = ConstraintDomain::Product(vec![domain]);
            }
            let clone = domain.clone();
            assert_eq!(domain, clone);
            assert!(format!("{domain:?}").starts_with("Product([Product([Product(["));
            assert!(domain.to_string().starts_with("Product(Product(Product("));
            drop(clone);
            drop(domain);
        })
        .expect("small-stack refinement lifecycle thread must spawn")
        .join()
        .expect("refinement lifecycle PDAs must not overflow the native stack");
}
