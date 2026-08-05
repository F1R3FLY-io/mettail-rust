//! Small-depth recursive oracle retained only for differential testing.

use mettail_prattail::behavioral_algebra::{Arg, BehavioralFormula, QDomain};
use mettail_prattail::behavioral_pred::{BehavioralPred, PredArg, QuantifiedDomain, Quantifier};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OracleBehavioralPred {
    RelationQuery {
        relation_name: String,
        args: Vec<PredArg>,
        negated: bool,
    },
    Quantified {
        quantifier: Quantifier,
        var: String,
        domain: Option<QuantifiedDomain>,
        body: Box<OracleBehavioralPred>,
    },
    AcMatch {
        bag: PredArg,
        elements: Vec<PredArg>,
        rest: Option<String>,
    },
    And(Box<OracleBehavioralPred>, Box<OracleBehavioralPred>),
    Or(Box<OracleBehavioralPred>, Box<OracleBehavioralPred>),
    Not(Box<OracleBehavioralPred>),
    Implies(Box<OracleBehavioralPred>, Box<OracleBehavioralPred>),
    Top,
}

impl OracleBehavioralPred {
    pub fn to_production(&self) -> BehavioralPred {
        match self {
            Self::RelationQuery { relation_name, args, negated } => BehavioralPred::RelationQuery {
                relation_name: relation_name.clone(),
                args: args.clone(),
                negated: *negated,
            },
            Self::Quantified { quantifier, var, domain, body } => BehavioralPred::Quantified {
                quantifier: *quantifier,
                var: var.clone(),
                domain: domain.clone(),
                body: Box::new(body.to_production()),
            },
            Self::AcMatch { bag, elements, rest } => BehavioralPred::AcMatch {
                bag: bag.clone(),
                elements: elements.clone(),
                rest: rest.clone(),
            },
            Self::And(left, right) => {
                BehavioralPred::And(Box::new(left.to_production()), Box::new(right.to_production()))
            },
            Self::Or(left, right) => {
                BehavioralPred::Or(Box::new(left.to_production()), Box::new(right.to_production()))
            },
            Self::Not(inner) => BehavioralPred::Not(Box::new(inner.to_production())),
            Self::Implies(left, right) => BehavioralPred::Implies(
                Box::new(left.to_production()),
                Box::new(right.to_production()),
            ),
            Self::Top => BehavioralPred::Top,
        }
    }

    pub fn substitute_var(&self, old: &str, new: &str) -> Self {
        let substitute = |arg: &PredArg| match arg {
            PredArg::Var(var) if var == old => PredArg::Var(new.to_owned()),
            other => other.clone(),
        };
        match self {
            Self::RelationQuery { relation_name, args, negated } => Self::RelationQuery {
                relation_name: relation_name.clone(),
                args: args.iter().map(substitute).collect(),
                negated: *negated,
            },
            Self::Quantified { quantifier, var, domain, body } if var != old => {
                let domain = domain.as_ref().map(|domain| match domain {
                    QuantifiedDomain::Named(name) => QuantifiedDomain::Named(name.clone()),
                    QuantifiedDomain::Bounded(bound) => QuantifiedDomain::Bounded(*bound),
                    QuantifiedDomain::Enumerated(args) => {
                        QuantifiedDomain::Enumerated(args.iter().map(substitute).collect())
                    },
                });
                Self::Quantified {
                    quantifier: *quantifier,
                    var: var.clone(),
                    domain,
                    body: Box::new(body.substitute_var(old, new)),
                }
            },
            Self::Quantified { .. } => self.clone(),
            Self::AcMatch { bag, elements, rest } => Self::AcMatch {
                bag: substitute(bag),
                elements: elements.iter().map(substitute).collect(),
                rest: rest.clone(),
            },
            Self::And(left, right) => Self::And(
                Box::new(left.substitute_var(old, new)),
                Box::new(right.substitute_var(old, new)),
            ),
            Self::Or(left, right) => Self::Or(
                Box::new(left.substitute_var(old, new)),
                Box::new(right.substitute_var(old, new)),
            ),
            Self::Not(inner) => Self::Not(Box::new(inner.substitute_var(old, new))),
            Self::Implies(left, right) => Self::Implies(
                Box::new(left.substitute_var(old, new)),
                Box::new(right.substitute_var(old, new)),
            ),
            Self::Top => Self::Top,
        }
    }

    pub fn free_vars(&self) -> HashSet<String> {
        fn visit(
            pred: &OracleBehavioralPred,
            bound: &mut HashSet<String>,
            free: &mut HashSet<String>,
        ) {
            let collect = |arg: &PredArg, bound: &HashSet<String>, free: &mut HashSet<String>| {
                if let PredArg::Var(var) = arg {
                    if !bound.contains(var) {
                        free.insert(var.clone());
                    }
                }
            };
            match pred {
                OracleBehavioralPred::Top => {},
                OracleBehavioralPred::RelationQuery { args, .. } => {
                    for arg in args {
                        collect(arg, bound, free);
                    }
                },
                OracleBehavioralPred::Quantified { var, domain, body, .. } => {
                    if let Some(QuantifiedDomain::Enumerated(args)) = domain {
                        for arg in args {
                            collect(arg, bound, free);
                        }
                    }
                    let inserted = bound.insert(var.clone());
                    visit(body, bound, free);
                    if inserted {
                        bound.remove(var);
                    }
                },
                OracleBehavioralPred::AcMatch { bag, elements, .. } => {
                    collect(bag, bound, free);
                    for element in elements {
                        collect(element, bound, free);
                    }
                },
                OracleBehavioralPred::And(left, right)
                | OracleBehavioralPred::Or(left, right)
                | OracleBehavioralPred::Implies(left, right) => {
                    visit(left, bound, free);
                    visit(right, bound, free);
                },
                OracleBehavioralPred::Not(inner) => visit(inner, bound, free),
            }
        }

        let mut free = HashSet::new();
        visit(self, &mut HashSet::new(), &mut free);
        free
    }

    pub fn to_behavioral_formula(&self) -> Option<BehavioralFormula> {
        let lower_arg = |arg: &PredArg| match arg {
            PredArg::Var(var) => Arg::Var(var.clone()),
            PredArg::IntLit(value) => Arg::Lit(value.to_string()),
            PredArg::StringLit(value) => Arg::Lit(value.clone()),
        };
        let lower_domain = |domain: Option<&QuantifiedDomain>| match domain {
            Some(QuantifiedDomain::Named(name)) => QDomain::RelationColumn(name.clone(), 0),
            Some(QuantifiedDomain::Bounded(bound)) => {
                QDomain::Bounded(Box::new(QDomain::Active), *bound)
            },
            Some(QuantifiedDomain::Enumerated(args)) => QDomain::Values(
                args.iter()
                    .map(|arg| match arg {
                        PredArg::Var(var) => var.clone(),
                        PredArg::IntLit(value) => value.to_string(),
                        PredArg::StringLit(value) => value.clone(),
                    })
                    .collect(),
            ),
            None => QDomain::Active,
        };
        match self {
            Self::Top => Some(BehavioralFormula::Top),
            Self::RelationQuery { relation_name, args, negated } => {
                let relation = BehavioralFormula::Relation {
                    name: relation_name.clone(),
                    args: args.iter().map(lower_arg).collect(),
                };
                Some(if *negated {
                    BehavioralFormula::Not(Box::new(relation))
                } else {
                    relation
                })
            },
            Self::Quantified { quantifier, var, domain, body } => {
                let body = Box::new(body.to_behavioral_formula()?);
                Some(match quantifier {
                    Quantifier::ForAll => BehavioralFormula::Forall {
                        var: var.clone(),
                        domain: lower_domain(domain.as_ref()),
                        body,
                    },
                    Quantifier::Exists => BehavioralFormula::Exists {
                        var: var.clone(),
                        domain: lower_domain(domain.as_ref()),
                        body,
                    },
                })
            },
            Self::AcMatch { .. } => None,
            Self::And(left, right) => Some(BehavioralFormula::And(
                Box::new(left.to_behavioral_formula()?),
                Box::new(right.to_behavioral_formula()?),
            )),
            Self::Or(left, right) => Some(BehavioralFormula::Or(
                Box::new(left.to_behavioral_formula()?),
                Box::new(right.to_behavioral_formula()?),
            )),
            Self::Not(inner) => {
                Some(BehavioralFormula::Not(Box::new(inner.to_behavioral_formula()?)))
            },
            Self::Implies(left, right) => Some(BehavioralFormula::Or(
                Box::new(BehavioralFormula::Not(Box::new(left.to_behavioral_formula()?))),
                Box::new(right.to_behavioral_formula()?),
            )),
        }
    }
}

impl fmt::Display for OracleBehavioralPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Top => formatter.write_str("true()"),
            Self::RelationQuery { relation_name, args, negated } => {
                if *negated {
                    formatter.write_str("not ")?;
                }
                write!(formatter, "{relation_name}(")?;
                for (index, arg) in args.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{arg}")?;
                }
                formatter.write_str(")")
            },
            Self::Quantified { quantifier, var, domain, body } => {
                let name = match quantifier {
                    Quantifier::ForAll => "forall",
                    Quantifier::Exists => "exists",
                };
                write!(formatter, "{name}({var}")?;
                if let Some(domain) = domain {
                    write!(formatter, ", {domain}")?;
                }
                write!(formatter, ", {body})")
            },
            Self::AcMatch { bag, elements, rest } => {
                write!(formatter, "ac_match({bag}, [")?;
                for (index, element) in elements.iter().enumerate() {
                    if index != 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{element}")?;
                }
                if let Some(rest) = rest {
                    write!(formatter, ", ...{rest}")?;
                }
                formatter.write_str("])")
            },
            Self::And(left, right) => write!(formatter, "({left} and {right})"),
            Self::Or(left, right) => write!(formatter, "({left} or {right})"),
            Self::Not(inner) => write!(formatter, "(not {inner})"),
            Self::Implies(left, right) => write!(formatter, "({left} entails {right})"),
        }
    }
}

pub fn representative_cases() -> Vec<OracleBehavioralPred> {
    use OracleBehavioralPred as P;
    let atom = |name: &str, args: Vec<PredArg>| P::RelationQuery {
        relation_name: name.to_owned(),
        args,
        negated: false,
    };
    vec![
        P::Top,
        P::RelationQuery {
            relation_name: "blocked".into(),
            args: vec![PredArg::Var("x".into()), PredArg::IntLit(7)],
            negated: true,
        },
        P::AcMatch {
            bag: PredArg::Var("bag".into()),
            elements: vec![PredArg::StringLit("a".into()), PredArg::Var("x".into())],
            rest: Some("tail".into()),
        },
        P::Quantified {
            quantifier: Quantifier::ForAll,
            var: "x".into(),
            domain: Some(QuantifiedDomain::Enumerated(vec![
                PredArg::Var("outer".into()),
                PredArg::IntLit(3),
            ])),
            body: Box::new(P::Quantified {
                quantifier: Quantifier::Exists,
                var: "x".into(),
                domain: Some(QuantifiedDomain::Named("nodes".into())),
                body: Box::new(atom(
                    "edge",
                    vec![PredArg::Var("x".into()), PredArg::Var("free".into())],
                )),
            }),
        },
        P::And(
            Box::new(P::Not(Box::new(atom("left", vec![PredArg::Var("x".into())])))),
            Box::new(P::Or(
                Box::new(atom("middle", vec![])),
                Box::new(P::Implies(
                    Box::new(atom("before", vec![])),
                    Box::new(atom("after", vec![])),
                )),
            )),
        ),
    ]
}
