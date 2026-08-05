use mettail_ast::language::{
    BehavioralPred, Condition, FreshnessCondition, FreshnessTarget, PredArg, Premise, Quantifier,
};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

#[allow(dead_code)]
#[derive(Debug)]
enum BehavioralPredOracle<'tree> {
    RelationQuery {
        relation_name: &'tree Ident,
        args: &'tree [PredArg],
        negated: bool,
    },
    Quantified {
        quantifier: &'tree Quantifier,
        var: &'tree Ident,
        domain: &'tree Option<Ident>,
        bound: Option<usize>,
        body: Box<BehavioralPredOracle<'tree>>,
    },
    And(Box<BehavioralPredOracle<'tree>>, Box<BehavioralPredOracle<'tree>>),
    Or(Box<BehavioralPredOracle<'tree>>, Box<BehavioralPredOracle<'tree>>),
    Not(Box<BehavioralPredOracle<'tree>>),
    Implies(Box<BehavioralPredOracle<'tree>>, Box<BehavioralPredOracle<'tree>>),
    AcMatch {
        bag: &'tree Ident,
        elements: &'tree [Ident],
        rest: &'tree Option<Ident>,
    },
    Top,
}

fn behavioral_oracle(predicate: &BehavioralPred) -> BehavioralPredOracle<'_> {
    match predicate {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            BehavioralPredOracle::RelationQuery { relation_name, args, negated: *negated }
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            BehavioralPredOracle::Quantified {
                quantifier,
                var,
                domain,
                bound: *bound,
                body: Box::new(behavioral_oracle(body)),
            }
        },
        BehavioralPred::And(left, right) => BehavioralPredOracle::And(
            Box::new(behavioral_oracle(left)),
            Box::new(behavioral_oracle(right)),
        ),
        BehavioralPred::Or(left, right) => BehavioralPredOracle::Or(
            Box::new(behavioral_oracle(left)),
            Box::new(behavioral_oracle(right)),
        ),
        BehavioralPred::Not(inner) => BehavioralPredOracle::Not(Box::new(behavioral_oracle(inner))),
        BehavioralPred::Implies(left, right) => BehavioralPredOracle::Implies(
            Box::new(behavioral_oracle(left)),
            Box::new(behavioral_oracle(right)),
        ),
        BehavioralPred::AcMatch { bag, elements, rest } => {
            BehavioralPredOracle::AcMatch { bag, elements, rest }
        },
        BehavioralPred::Top => BehavioralPredOracle::Top,
    }
}

#[allow(dead_code)]
#[derive(Debug)]
enum PremiseOracle<'tree> {
    Freshness(&'tree FreshnessCondition),
    Congruence {
        source: &'tree Ident,
        target: &'tree Ident,
    },
    CongruenceWithheld {
        source: &'tree Ident,
        target: &'tree Ident,
    },
    RelationQuery {
        relation: &'tree Ident,
        args: &'tree [Ident],
    },
    ForAll {
        collection: &'tree Ident,
        param: &'tree Ident,
        body: Box<PremiseOracle<'tree>>,
    },
    BehavioralGuard(BehavioralPredOracle<'tree>),
    SyntheticInjGuard {
        inner_var: &'tree Ident,
        source_category: &'tree Ident,
        excluded_variants: &'tree [Ident],
    },
}

fn premise_oracle(premise: &Premise) -> PremiseOracle<'_> {
    match premise {
        Premise::Freshness(condition) => PremiseOracle::Freshness(condition),
        Premise::Congruence { source, target } => PremiseOracle::Congruence { source, target },
        Premise::CongruenceWithheld { source, target } => {
            PremiseOracle::CongruenceWithheld { source, target }
        },
        Premise::RelationQuery { relation, args } => {
            PremiseOracle::RelationQuery { relation, args }
        },
        Premise::ForAll { collection, param, body } => PremiseOracle::ForAll {
            collection,
            param,
            body: Box::new(premise_oracle(body)),
        },
        Premise::BehavioralGuard(predicate) => {
            PremiseOracle::BehavioralGuard(behavioral_oracle(predicate))
        },
        Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => PremiseOracle::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        },
    }
}

#[allow(dead_code)]
#[derive(Debug)]
enum ConditionOracle<'tree> {
    Freshness(&'tree FreshnessCondition),
    EnvQuery {
        relation: &'tree Ident,
        args: &'tree [Ident],
    },
    ForAll {
        collection: &'tree Ident,
        param: &'tree Ident,
        body: Box<ConditionOracle<'tree>>,
    },
    BehavioralGuard(BehavioralPredOracle<'tree>),
    SyntheticInjGuard {
        inner_var: &'tree Ident,
        source_category: &'tree Ident,
        excluded_variants: &'tree [Ident],
    },
}

fn condition_oracle(condition: &Condition) -> ConditionOracle<'_> {
    match condition {
        Condition::Freshness(condition) => ConditionOracle::Freshness(condition),
        Condition::EnvQuery { relation, args } => ConditionOracle::EnvQuery { relation, args },
        Condition::ForAll { collection, param, body } => ConditionOracle::ForAll {
            collection,
            param,
            body: Box::new(condition_oracle(body)),
        },
        Condition::BehavioralGuard(predicate) => {
            ConditionOracle::BehavioralGuard(behavioral_oracle(predicate))
        },
        Condition::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => ConditionOracle::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        },
    }
}

fn recursive_formula(predicate: &BehavioralPred) -> Result<TokenStream, String> {
    match predicate {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            let relation = relation_name.to_string();
            let args: Vec<_> = args
                .iter()
                .map(|arg| match arg {
                    PredArg::Var(var) => {
                        let var = var.to_string();
                        quote! { prattail::logict::QuantifiedArg::Var(#var.to_string()) }
                    },
                    PredArg::Constant(constant) => {
                        let constant = constant.to_string();
                        quote! { prattail::logict::QuantifiedArg::Constant(#constant.to_string()) }
                    },
                })
                .collect();
            let atom = quote! {
                prattail::logict::QuantifiedFormula::atom(
                    #relation,
                    vec![#(#args),*],
                )
            };
            Ok(if *negated {
                quote! { prattail::logict::QuantifiedFormula::not(#atom) }
            } else {
                atom
            })
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            let var = var.to_string();
            let body = recursive_formula(body)?;
            let domain = if let Some(domain) = domain {
                let relation = domain.to_string();
                if let Some(limit) = bound {
                    quote! {
                        prattail::logict::QuantifiedDomain::Bounded {
                            relation: #relation.to_string(),
                            limit: #limit,
                        }
                    }
                } else {
                    quote! {
                        prattail::logict::QuantifiedDomain::Relation(#relation.to_string())
                    }
                }
            } else {
                quote! { prattail::logict::QuantifiedDomain::Relation(#var.to_string()) }
            };
            Ok(match quantifier {
                Quantifier::ForAll => quote! {
                    prattail::logict::QuantifiedFormula::forall(#var, #domain, #body)
                },
                Quantifier::Exists => quote! {
                    prattail::logict::QuantifiedFormula::exists(#var, #domain, #body)
                },
            })
        },
        BehavioralPred::And(left, right) => {
            let left = recursive_formula(left)?;
            let right = recursive_formula(right)?;
            Ok(quote! { prattail::logict::QuantifiedFormula::and(#left, #right) })
        },
        BehavioralPred::Or(left, right) => {
            let left = recursive_formula(left)?;
            let right = recursive_formula(right)?;
            Ok(quote! { prattail::logict::QuantifiedFormula::or(#left, #right) })
        },
        BehavioralPred::Not(inner) => {
            let inner = recursive_formula(inner)?;
            Ok(quote! { prattail::logict::QuantifiedFormula::not(#inner) })
        },
        BehavioralPred::Implies(left, right) => {
            let left = recursive_formula(left)?;
            let right = recursive_formula(right)?;
            Ok(quote! { prattail::logict::QuantifiedFormula::implies(#left, #right) })
        },
        BehavioralPred::AcMatch { .. } => Err("ac_match behavioral predicates require specialized Ascent partition lowering and cannot be embedded in QuantifiedFormula".to_string()),
        BehavioralPred::Top => Ok(quote! {
            prattail::logict::QuantifiedFormula::atom(
                "__top__",
                vec![],
            )
        }),
    }
}

fn relation(name: &str) -> BehavioralPred {
    BehavioralPred::RelationQuery {
        relation_name: ident(name),
        args: vec![PredArg::Var(ident("x")), PredArg::Constant(ident("Root"))],
        negated: name == "blocked",
    }
}

fn rich_predicate() -> BehavioralPred {
    BehavioralPred::Quantified {
        quantifier: Quantifier::ForAll,
        var: ident("x"),
        domain: Some(ident("nodes")),
        bound: Some(32),
        body: Box::new(BehavioralPred::Implies(
            Box::new(BehavioralPred::And(
                Box::new(relation("reachable")),
                Box::new(BehavioralPred::Not(Box::new(relation("blocked")))),
            )),
            Box::new(BehavioralPred::Or(
                Box::new(BehavioralPred::AcMatch {
                    bag: ident("messages"),
                    elements: vec![ident("head"), ident("tail")],
                    rest: Some(ident("rest")),
                }),
                Box::new(BehavioralPred::Top),
            )),
        )),
    }
}

#[test]
fn lifecycle_debug_is_byte_equivalent_to_derived_debug() {
    let predicate = rich_predicate();
    assert_eq!(format!("{predicate:?}"), format!("{:?}", behavioral_oracle(&predicate)));
    assert_eq!(format!("{predicate:#?}"), format!("{:#?}", behavioral_oracle(&predicate)));

    let premises = vec![
        Premise::Freshness(FreshnessCondition {
            var: ident("fresh"),
            term: FreshnessTarget::CollectionRest(ident("rest")),
        }),
        Premise::Congruence {
            source: ident("source"),
            target: ident("target"),
        },
        Premise::CongruenceWithheld {
            source: ident("source"),
            target: ident("target"),
        },
        Premise::RelationQuery {
            relation: ident("reachable"),
            args: vec![ident("source"), ident("target")],
        },
        Premise::ForAll {
            collection: ident("items"),
            param: ident("item"),
            body: Box::new(Premise::BehavioralGuard(predicate.clone())),
        },
        Premise::SyntheticInjGuard {
            inner_var: ident("inner"),
            source_category: ident("Process"),
            excluded_variants: vec![ident("NameToProcess"), ident("IntToProcess")],
        },
    ];
    for premise in &premises {
        assert_eq!(format!("{premise:?}"), format!("{:?}", premise_oracle(premise)));
        assert_eq!(format!("{premise:#?}"), format!("{:#?}", premise_oracle(premise)));
    }

    let conditions = vec![
        Condition::Freshness(FreshnessCondition {
            var: ident("fresh"),
            term: FreshnessTarget::Var(ident("term")),
        }),
        Condition::EnvQuery {
            relation: ident("environment"),
            args: vec![ident("key"), ident("value")],
        },
        Condition::ForAll {
            collection: ident("items"),
            param: ident("item"),
            body: Box::new(Condition::BehavioralGuard(predicate)),
        },
        Condition::SyntheticInjGuard {
            inner_var: ident("inner"),
            source_category: ident("Process"),
            excluded_variants: vec![ident("NameToProcess"), ident("IntToProcess")],
        },
    ];
    for condition in &conditions {
        assert_eq!(format!("{condition:?}"), format!("{:?}", condition_oracle(condition)));
        assert_eq!(format!("{condition:#?}"), format!("{:#?}", condition_oracle(condition)));
    }
}

#[test]
fn formula_pda_is_equivalent_to_the_previous_recursive_lowering() {
    let predicate = BehavioralPred::And(
        Box::new(BehavioralPred::Quantified {
            quantifier: Quantifier::Exists,
            var: ident("candidate"),
            domain: Some(ident("nodes")),
            bound: Some(7),
            body: Box::new(relation("reachable")),
        }),
        Box::new(BehavioralPred::Or(
            Box::new(BehavioralPred::Not(Box::new(relation("blocked")))),
            Box::new(BehavioralPred::Top),
        )),
    );
    assert_eq!(
        predicate
            .try_to_quantified_formula()
            .expect("PDA formula lowering")
            .to_string(),
        recursive_formula(&predicate)
            .expect("recursive formula oracle")
            .to_string(),
    );

    let unsupported = BehavioralPred::AcMatch {
        bag: ident("messages"),
        elements: vec![ident("head")],
        rest: None,
    };
    assert_eq!(
        unsupported
            .try_to_quantified_formula()
            .expect_err("AC matching is not a QuantifiedFormula"),
        recursive_formula(&unsupported).expect_err("recursive oracle must reject AC matching"),
    );
}

fn nested_predicate(depth: usize) -> BehavioralPred {
    let mut predicate = BehavioralPred::Top;
    for _ in 0..depth {
        predicate = BehavioralPred::Not(Box::new(predicate));
    }
    predicate
}

fn nested_premise(depth: usize) -> Premise {
    let mut premise = Premise::BehavioralGuard(BehavioralPred::Top);
    for _ in 0..depth {
        premise = Premise::ForAll {
            collection: ident("items"),
            param: ident("item"),
            body: Box::new(premise),
        };
    }
    premise
}

fn nested_condition(depth: usize) -> Condition {
    let mut condition = Condition::BehavioralGuard(BehavioralPred::Top);
    for _ in 0..depth {
        condition = Condition::ForAll {
            collection: ident("items"),
            param: ident("item"),
            body: Box::new(condition),
        };
    }
    condition
}

#[test]
fn language_ast_lifecycle_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("language-ast-lifecycle-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let predicate = nested_predicate(DEPTH);
            let cloned = predicate.clone();
            let rendered = format!("{predicate:?}");
            assert!(rendered.starts_with("Not(Not(Not("));
            assert!(rendered.ends_with(")".repeat(DEPTH).as_str()));
            drop(cloned);
            drop(predicate);

            let premise = nested_premise(DEPTH);
            let cloned = premise.clone();
            let rendered = format!("{premise:?}");
            assert!(rendered.starts_with("ForAll { collection:"));
            assert!(rendered.contains("BehavioralGuard(Top)"));
            drop(cloned);
            drop(premise);

            let condition = nested_condition(DEPTH);
            let cloned = condition.clone();
            let rendered = format!("{condition:?}");
            assert!(rendered.starts_with("ForAll { collection:"));
            assert!(rendered.contains("BehavioralGuard(Top)"));
            drop(cloned);
            drop(condition);
        })
        .expect("small-stack language AST lifecycle thread must spawn")
        .join()
        .expect("language AST lifecycle PDAs must not overflow the native stack");
}
