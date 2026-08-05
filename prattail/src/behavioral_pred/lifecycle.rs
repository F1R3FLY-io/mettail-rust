//! Explicit heap-backed lifecycle and transformation machines for
//! [`BehavioralPred`].
//!
//! Keeping these implementations together prevents a recursive carrier from
//! silently regaining a call-stack traversal through a derived trait or a
//! seemingly harmless utility method.

use super::{BehavioralPred, PredArg, QuantifiedDomain, Quantifier};
use crate::behavioral_algebra::BehavioralFormula;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

enum RebuildTask<'pred> {
    Visit(&'pred BehavioralPred, bool),
    Quantified {
        quantifier: Quantifier,
        var: &'pred str,
        domain: &'pred Option<QuantifiedDomain>,
        substitute_here: bool,
        value_base: usize,
    },
    And(usize),
    Or(usize),
    Not(usize),
    Implies(usize),
}

fn rebuild_predicate(root: &BehavioralPred, substitution: Option<(&str, &str)>) -> BehavioralPred {
    let mut tasks = vec![RebuildTask::Visit(root, substitution.is_some())];
    let mut values = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            RebuildTask::Visit(pred, substitute_here) => match pred {
                BehavioralPred::Top => values.push(BehavioralPred::Top),
                BehavioralPred::RelationQuery { relation_name, args, negated } => {
                    let args = if substitute_here {
                        let (old, new) = substitution
                            .expect("behavioral rebuild marked substitution without a mapping");
                        args.iter()
                            .map(|arg| arg.substitute_var(old, new))
                            .collect()
                    } else {
                        args.clone()
                    };
                    values.push(BehavioralPred::RelationQuery {
                        relation_name: relation_name.clone(),
                        args,
                        negated: *negated,
                    });
                },
                BehavioralPred::Quantified { quantifier, var, domain, body } => {
                    let body_substitution =
                        substitute_here && substitution.is_some_and(|(old, _)| var.as_str() != old);
                    let value_base = values.len();
                    tasks.push(RebuildTask::Quantified {
                        quantifier: *quantifier,
                        var,
                        domain,
                        substitute_here: body_substitution,
                        value_base,
                    });
                    tasks.push(RebuildTask::Visit(body, body_substitution));
                },
                BehavioralPred::AcMatch { bag, elements, rest } => {
                    let (bag, elements) = if substitute_here {
                        let (old, new) = substitution
                            .expect("behavioral rebuild marked substitution without a mapping");
                        (
                            bag.substitute_var(old, new),
                            elements
                                .iter()
                                .map(|element| element.substitute_var(old, new))
                                .collect(),
                        )
                    } else {
                        (bag.clone(), elements.clone())
                    };
                    values.push(BehavioralPred::AcMatch { bag, elements, rest: rest.clone() });
                },
                BehavioralPred::And(left, right) => {
                    let value_base = values.len();
                    tasks.push(RebuildTask::And(value_base));
                    tasks.push(RebuildTask::Visit(right, substitute_here));
                    tasks.push(RebuildTask::Visit(left, substitute_here));
                },
                BehavioralPred::Or(left, right) => {
                    let value_base = values.len();
                    tasks.push(RebuildTask::Or(value_base));
                    tasks.push(RebuildTask::Visit(right, substitute_here));
                    tasks.push(RebuildTask::Visit(left, substitute_here));
                },
                BehavioralPred::Not(inner) => {
                    let value_base = values.len();
                    tasks.push(RebuildTask::Not(value_base));
                    tasks.push(RebuildTask::Visit(inner, substitute_here));
                },
                BehavioralPred::Implies(left, right) => {
                    let value_base = values.len();
                    tasks.push(RebuildTask::Implies(value_base));
                    tasks.push(RebuildTask::Visit(right, substitute_here));
                    tasks.push(RebuildTask::Visit(left, substitute_here));
                },
            },
            RebuildTask::Quantified {
                quantifier,
                var,
                domain,
                substitute_here,
                value_base,
            } => {
                let body = values
                    .pop()
                    .expect("behavioral rebuild lost a quantified body");
                values.truncate(value_base);
                let domain = if substitute_here {
                    let (old, new) = substitution
                        .expect("behavioral rebuild marked substitution without a mapping");
                    domain
                        .as_ref()
                        .map(|domain| domain.substitute_var(old, new))
                } else {
                    domain.clone()
                };
                values.push(BehavioralPred::Quantified {
                    quantifier,
                    var: var.to_owned(),
                    domain,
                    body: Box::new(body),
                });
            },
            RebuildTask::And(value_base) => {
                finish_binary(&mut values, value_base, |left, right| {
                    BehavioralPred::And(Box::new(left), Box::new(right))
                });
            },
            RebuildTask::Or(value_base) => {
                finish_binary(&mut values, value_base, |left, right| {
                    BehavioralPred::Or(Box::new(left), Box::new(right))
                });
            },
            RebuildTask::Not(value_base) => {
                let inner = values
                    .pop()
                    .expect("behavioral rebuild lost a negated operand");
                values.truncate(value_base);
                values.push(BehavioralPred::Not(Box::new(inner)));
            },
            RebuildTask::Implies(value_base) => {
                finish_binary(&mut values, value_base, |left, right| {
                    BehavioralPred::Implies(Box::new(left), Box::new(right))
                });
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values.pop().expect("behavioral rebuild produced no result")
}

fn finish_binary(
    values: &mut Vec<BehavioralPred>,
    value_base: usize,
    build: impl FnOnce(BehavioralPred, BehavioralPred) -> BehavioralPred,
) {
    let right = values
        .pop()
        .expect("behavioral rebuild lost a right operand");
    let left = values
        .pop()
        .expect("behavioral rebuild lost a left operand");
    values.truncate(value_base);
    values.push(build(left, right));
}

impl Clone for BehavioralPred {
    fn clone(&self) -> Self {
        rebuild_predicate(self, None)
    }
}

pub(super) fn substitute_var(root: &BehavioralPred, old: &str, new: &str) -> BehavioralPred {
    rebuild_predicate(root, Some((old, new)))
}

fn take_children(pred: &mut BehavioralPred, work: &mut Vec<BehavioralPred>) {
    let take =
        |child: &mut Box<BehavioralPred>| *std::mem::replace(child, Box::new(BehavioralPred::Top));
    match pred {
        BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
            work.push(take(body));
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        BehavioralPred::RelationQuery { .. }
        | BehavioralPred::AcMatch { .. }
        | BehavioralPred::Top => {},
    }
}

impl Drop for BehavioralPred {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut pred) = work.pop() {
            take_children(&mut pred, &mut work);
        }
    }
}

fn variant_rank(pred: &BehavioralPred) -> u8 {
    match pred {
        BehavioralPred::RelationQuery { .. } => 0,
        BehavioralPred::Quantified { .. } => 1,
        BehavioralPred::AcMatch { .. } => 2,
        BehavioralPred::And(..) => 3,
        BehavioralPred::Or(..) => 4,
        BehavioralPred::Not(..) => 5,
        BehavioralPred::Implies(..) => 6,
        BehavioralPred::Top => 7,
    }
}

impl PartialEq for BehavioralPred {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (BehavioralPred::Top, BehavioralPred::Top) => {},
                (
                    BehavioralPred::RelationQuery {
                        relation_name: left_name,
                        args: left_args,
                        negated: left_negated,
                    },
                    BehavioralPred::RelationQuery {
                        relation_name: right_name,
                        args: right_args,
                        negated: right_negated,
                    },
                ) if left_name == right_name
                    && left_args == right_args
                    && left_negated == right_negated => {},
                (
                    BehavioralPred::Quantified {
                        quantifier: left_quantifier,
                        var: left_var,
                        domain: left_domain,
                        body: left_body,
                    },
                    BehavioralPred::Quantified {
                        quantifier: right_quantifier,
                        var: right_var,
                        domain: right_domain,
                        body: right_body,
                    },
                ) if left_quantifier == right_quantifier
                    && left_var == right_var
                    && left_domain == right_domain =>
                {
                    work.push((left_body, right_body))
                },
                (
                    BehavioralPred::AcMatch {
                        bag: left_bag,
                        elements: left_elements,
                        rest: left_rest,
                    },
                    BehavioralPred::AcMatch {
                        bag: right_bag,
                        elements: right_elements,
                        rest: right_rest,
                    },
                ) if left_bag == right_bag
                    && left_elements == right_elements
                    && left_rest == right_rest => {},
                (BehavioralPred::And(left_a, left_b), BehavioralPred::And(right_a, right_b))
                | (BehavioralPred::Or(left_a, left_b), BehavioralPred::Or(right_a, right_b))
                | (
                    BehavioralPred::Implies(left_a, left_b),
                    BehavioralPred::Implies(right_a, right_b),
                ) => {
                    work.push((left_b, right_b));
                    work.push((left_a, right_a));
                },
                (BehavioralPred::Not(left), BehavioralPred::Not(right)) => {
                    work.push((left, right));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for BehavioralPred {}

impl Ord for BehavioralPred {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            let rank = variant_rank(left).cmp(&variant_rank(right));
            if rank != Ordering::Equal {
                return rank;
            }
            let leaf_order = match (left, right) {
                (
                    BehavioralPred::RelationQuery {
                        relation_name: left_name,
                        args: left_args,
                        negated: left_negated,
                    },
                    BehavioralPred::RelationQuery {
                        relation_name: right_name,
                        args: right_args,
                        negated: right_negated,
                    },
                ) => left_name
                    .cmp(right_name)
                    .then_with(|| left_args.cmp(right_args))
                    .then_with(|| left_negated.cmp(right_negated)),
                (
                    BehavioralPred::Quantified {
                        quantifier: left_quantifier,
                        var: left_var,
                        domain: left_domain,
                        body: left_body,
                    },
                    BehavioralPred::Quantified {
                        quantifier: right_quantifier,
                        var: right_var,
                        domain: right_domain,
                        body: right_body,
                    },
                ) => {
                    let order = left_quantifier
                        .cmp(right_quantifier)
                        .then_with(|| left_var.cmp(right_var))
                        .then_with(|| left_domain.cmp(right_domain));
                    if order == Ordering::Equal {
                        work.push((left_body, right_body));
                    }
                    order
                },
                (
                    BehavioralPred::AcMatch {
                        bag: left_bag,
                        elements: left_elements,
                        rest: left_rest,
                    },
                    BehavioralPred::AcMatch {
                        bag: right_bag,
                        elements: right_elements,
                        rest: right_rest,
                    },
                ) => left_bag
                    .cmp(right_bag)
                    .then_with(|| left_elements.cmp(right_elements))
                    .then_with(|| left_rest.cmp(right_rest)),
                (BehavioralPred::And(left_a, left_b), BehavioralPred::And(right_a, right_b))
                | (BehavioralPred::Or(left_a, left_b), BehavioralPred::Or(right_a, right_b))
                | (
                    BehavioralPred::Implies(left_a, left_b),
                    BehavioralPred::Implies(right_a, right_b),
                ) => {
                    work.push((left_b, right_b));
                    work.push((left_a, right_a));
                    Ordering::Equal
                },
                (BehavioralPred::Not(left), BehavioralPred::Not(right)) => {
                    work.push((left, right));
                    Ordering::Equal
                },
                (BehavioralPred::Top, BehavioralPred::Top) => Ordering::Equal,
                _ => unreachable!("equal behavioral variant ranks must have equal variants"),
            };
            if leaf_order != Ordering::Equal {
                return leaf_order;
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for BehavioralPred {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for BehavioralPred {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(pred) = work.pop() {
            std::mem::discriminant(pred).hash(state);
            match pred {
                BehavioralPred::Top => {},
                BehavioralPred::RelationQuery { relation_name, args, negated } => {
                    relation_name.hash(state);
                    args.hash(state);
                    negated.hash(state);
                },
                BehavioralPred::Quantified { quantifier, var, domain, body } => {
                    quantifier.hash(state);
                    var.hash(state);
                    domain.hash(state);
                    work.push(body);
                },
                BehavioralPred::AcMatch { bag, elements, rest } => {
                    bag.hash(state);
                    elements.hash(state);
                    rest.hash(state);
                },
                BehavioralPred::And(left, right)
                | BehavioralPred::Or(left, right)
                | BehavioralPred::Implies(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                BehavioralPred::Not(inner) => work.push(inner),
            }
        }
    }
}

enum DebugTask<'pred> {
    Visit(&'pred BehavioralPred, usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
}

fn write_indent(formatter: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
    for _ in 0..indent {
        formatter.write_str("    ")?;
    }
    Ok(())
}

impl fmt::Debug for BehavioralPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pretty = formatter.alternate();
        let mut tasks = vec![DebugTask::Visit(self, 0)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Indent(indent) => write_indent(formatter, indent)?,
                DebugTask::CloseTuple(indent) => {
                    write_indent(formatter, indent)?;
                    formatter.write_str(")")?;
                },
                DebugTask::CloseStruct(indent) => {
                    write_indent(formatter, indent)?;
                    formatter.write_str("}")?;
                },
                DebugTask::Visit(pred, indent) if !pretty => match pred {
                    BehavioralPred::Top => formatter.write_str("Top")?,
                    BehavioralPred::RelationQuery { relation_name, args, negated } => write!(
                        formatter,
                        "RelationQuery {{ relation_name: {relation_name:?}, args: {args:?}, negated: {negated:?} }}"
                    )?,
                    BehavioralPred::Quantified { quantifier, var, domain, body } => {
                        write!(
                            formatter,
                            "Quantified {{ quantifier: {quantifier:?}, var: {var:?}, domain: {domain:?}, body: "
                        )?;
                        tasks.push(DebugTask::Text(" }"));
                        tasks.push(DebugTask::Visit(body, indent));
                    },
                    BehavioralPred::AcMatch { bag, elements, rest } => write!(
                        formatter,
                        "AcMatch {{ bag: {bag:?}, elements: {elements:?}, rest: {rest:?} }}"
                    )?,
                    BehavioralPred::And(left, right) => {
                        formatter.write_str("And(")?;
                        tasks.push(DebugTask::Text(")"));
                        tasks.push(DebugTask::Visit(right, indent));
                        tasks.push(DebugTask::Text(", "));
                        tasks.push(DebugTask::Visit(left, indent));
                    },
                    BehavioralPred::Or(left, right) => {
                        formatter.write_str("Or(")?;
                        tasks.push(DebugTask::Text(")"));
                        tasks.push(DebugTask::Visit(right, indent));
                        tasks.push(DebugTask::Text(", "));
                        tasks.push(DebugTask::Visit(left, indent));
                    },
                    BehavioralPred::Not(inner) => {
                        formatter.write_str("Not(")?;
                        tasks.push(DebugTask::Text(")"));
                        tasks.push(DebugTask::Visit(inner, indent));
                    },
                    BehavioralPred::Implies(left, right) => {
                        formatter.write_str("Implies(")?;
                        tasks.push(DebugTask::Text(")"));
                        tasks.push(DebugTask::Visit(right, indent));
                        tasks.push(DebugTask::Text(", "));
                        tasks.push(DebugTask::Visit(left, indent));
                    },
                },
                DebugTask::Visit(BehavioralPred::Top, _) => formatter.write_str("Top")?,
                DebugTask::Visit(
                    BehavioralPred::RelationQuery { relation_name, args, negated },
                    indent,
                ) => {
                    formatter.write_str("RelationQuery {\n")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "relation_name: {relation_name:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "args: {args:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "negated: {negated:?},")?;
                    write_indent(formatter, indent)?;
                    formatter.write_str("}")?;
                },
                DebugTask::Visit(
                    BehavioralPred::Quantified { quantifier, var, domain, body },
                    indent,
                ) => {
                    formatter.write_str("Quantified {\n")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "quantifier: {quantifier:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "var: {var:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "domain: {domain:?},")?;
                    write_indent(formatter, indent + 1)?;
                    formatter.write_str("body: ")?;
                    tasks.push(DebugTask::CloseStruct(indent));
                    tasks.push(DebugTask::Text(",\n"));
                    tasks.push(DebugTask::Visit(body, indent + 1));
                },
                DebugTask::Visit(BehavioralPred::AcMatch { bag, elements, rest }, indent) => {
                    formatter.write_str("AcMatch {\n")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "bag: {bag:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "elements: {elements:?},")?;
                    write_indent(formatter, indent + 1)?;
                    writeln!(formatter, "rest: {rest:?},")?;
                    write_indent(formatter, indent)?;
                    formatter.write_str("}")?;
                },
                DebugTask::Visit(BehavioralPred::And(left, right), indent) => {
                    push_pretty_binary("And", left, right, indent, formatter, &mut tasks)?;
                },
                DebugTask::Visit(BehavioralPred::Or(left, right), indent) => {
                    push_pretty_binary("Or", left, right, indent, formatter, &mut tasks)?;
                },
                DebugTask::Visit(BehavioralPred::Implies(left, right), indent) => {
                    push_pretty_binary("Implies", left, right, indent, formatter, &mut tasks)?;
                },
                DebugTask::Visit(BehavioralPred::Not(inner), indent) => {
                    formatter.write_str("Not(\n")?;
                    tasks.push(DebugTask::CloseTuple(indent));
                    tasks.push(DebugTask::Text(",\n"));
                    tasks.push(DebugTask::Visit(inner, indent + 1));
                    tasks.push(DebugTask::Indent(indent + 1));
                },
            }
        }
        Ok(())
    }
}

fn push_pretty_binary<'pred>(
    name: &str,
    left: &'pred BehavioralPred,
    right: &'pred BehavioralPred,
    indent: usize,
    formatter: &mut fmt::Formatter<'_>,
    tasks: &mut Vec<DebugTask<'pred>>,
) -> fmt::Result {
    writeln!(formatter, "{name}(")?;
    tasks.push(DebugTask::CloseTuple(indent));
    tasks.push(DebugTask::Text(",\n"));
    tasks.push(DebugTask::Visit(right, indent + 1));
    tasks.push(DebugTask::Indent(indent + 1));
    tasks.push(DebugTask::Text(",\n"));
    tasks.push(DebugTask::Visit(left, indent + 1));
    tasks.push(DebugTask::Indent(indent + 1));
    Ok(())
}

enum DisplayTask<'pred> {
    Visit(&'pred BehavioralPred),
    Arg(&'pred PredArg),
    Text(&'static str),
}

impl fmt::Display for BehavioralPred {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DisplayTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DisplayTask::Text(text) => formatter.write_str(text)?,
                DisplayTask::Arg(arg) => write!(formatter, "{arg}")?,
                DisplayTask::Visit(BehavioralPred::Top) => formatter.write_str("true()")?,
                DisplayTask::Visit(BehavioralPred::RelationQuery {
                    relation_name,
                    args,
                    negated,
                }) => {
                    if *negated {
                        formatter.write_str("not ")?;
                    }
                    write!(formatter, "{relation_name}(")?;
                    tasks.push(DisplayTask::Text(")"));
                    for (index, arg) in args.iter().enumerate().rev() {
                        tasks.push(DisplayTask::Arg(arg));
                        if index != 0 {
                            tasks.push(DisplayTask::Text(", "));
                        }
                    }
                },
                DisplayTask::Visit(BehavioralPred::Quantified {
                    quantifier,
                    var,
                    domain,
                    body,
                }) => {
                    let name = match quantifier {
                        Quantifier::ForAll => "forall",
                        Quantifier::Exists => "exists",
                    };
                    write!(formatter, "{name}({var}")?;
                    if let Some(domain) = domain {
                        write!(formatter, ", {domain}")?;
                    }
                    formatter.write_str(", ")?;
                    tasks.push(DisplayTask::Text(")"));
                    tasks.push(DisplayTask::Visit(body));
                },
                DisplayTask::Visit(BehavioralPred::AcMatch { bag, elements, rest }) => {
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
                    formatter.write_str("])")?;
                },
                DisplayTask::Visit(BehavioralPred::And(left, right)) => {
                    formatter.write_str("(")?;
                    tasks.push(DisplayTask::Text(")"));
                    tasks.push(DisplayTask::Visit(right));
                    tasks.push(DisplayTask::Text(" and "));
                    tasks.push(DisplayTask::Visit(left));
                },
                DisplayTask::Visit(BehavioralPred::Or(left, right)) => {
                    formatter.write_str("(")?;
                    tasks.push(DisplayTask::Text(")"));
                    tasks.push(DisplayTask::Visit(right));
                    tasks.push(DisplayTask::Text(" or "));
                    tasks.push(DisplayTask::Visit(left));
                },
                DisplayTask::Visit(BehavioralPred::Not(inner)) => {
                    formatter.write_str("(not ")?;
                    tasks.push(DisplayTask::Text(")"));
                    tasks.push(DisplayTask::Visit(inner));
                },
                DisplayTask::Visit(BehavioralPred::Implies(left, right)) => {
                    formatter.write_str("(")?;
                    tasks.push(DisplayTask::Text(")"));
                    tasks.push(DisplayTask::Visit(right));
                    tasks.push(DisplayTask::Text(" entails "));
                    tasks.push(DisplayTask::Visit(left));
                },
            }
        }
        Ok(())
    }
}

enum FreeVarTask<'pred> {
    Visit(&'pred BehavioralPred),
    EnterBound(&'pred str, &'pred BehavioralPred),
    LeaveBound(&'pred str, bool),
}

pub(super) fn free_vars(root: &BehavioralPred) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = HashSet::new();
    let mut tasks = vec![FreeVarTask::Visit(root)];
    while let Some(task) = tasks.pop() {
        match task {
            FreeVarTask::Visit(BehavioralPred::Top) => {},
            FreeVarTask::Visit(BehavioralPred::RelationQuery { args, .. }) => {
                collect_args(args, &bound, &mut free);
            },
            FreeVarTask::Visit(BehavioralPred::Quantified { var, domain, body, .. }) => {
                if let Some(QuantifiedDomain::Enumerated(args)) = domain {
                    collect_args(args, &bound, &mut free);
                }
                tasks.push(FreeVarTask::EnterBound(var, body));
            },
            FreeVarTask::Visit(BehavioralPred::AcMatch { bag, elements, .. }) => {
                collect_arg(bag, &bound, &mut free);
                collect_args(elements, &bound, &mut free);
            },
            FreeVarTask::Visit(BehavioralPred::And(left, right))
            | FreeVarTask::Visit(BehavioralPred::Or(left, right))
            | FreeVarTask::Visit(BehavioralPred::Implies(left, right)) => {
                tasks.push(FreeVarTask::Visit(right));
                tasks.push(FreeVarTask::Visit(left));
            },
            FreeVarTask::Visit(BehavioralPred::Not(inner)) => {
                tasks.push(FreeVarTask::Visit(inner));
            },
            FreeVarTask::EnterBound(var, body) => {
                let inserted = bound.insert(var.to_owned());
                tasks.push(FreeVarTask::LeaveBound(var, inserted));
                tasks.push(FreeVarTask::Visit(body));
            },
            FreeVarTask::LeaveBound(var, true) => {
                bound.remove(var);
            },
            FreeVarTask::LeaveBound(_, false) => {},
        }
    }
    free
}

fn collect_args(args: &[PredArg], bound: &HashSet<String>, free: &mut HashSet<String>) {
    for arg in args {
        collect_arg(arg, bound, free);
    }
}

fn collect_arg(arg: &PredArg, bound: &HashSet<String>, free: &mut HashSet<String>) {
    if let PredArg::Var(var) = arg {
        if !bound.contains(var) {
            free.insert(var.clone());
        }
    }
}

enum LowerTask<'pred> {
    Visit(&'pred BehavioralPred),
    Quantified {
        quantifier: Quantifier,
        var: &'pred str,
        domain: &'pred Option<QuantifiedDomain>,
        value_base: usize,
    },
    And(usize),
    Or(usize),
    Not(usize),
    Implies(usize),
}

pub(super) fn to_behavioral_formula(root: &BehavioralPred) -> Option<BehavioralFormula> {
    let mut scan = vec![root];
    while let Some(pred) = scan.pop() {
        match pred {
            BehavioralPred::AcMatch { .. } => return None,
            BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
                scan.push(body);
            },
            BehavioralPred::And(left, right)
            | BehavioralPred::Or(left, right)
            | BehavioralPred::Implies(left, right) => {
                scan.push(right);
                scan.push(left);
            },
            BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => {},
        }
    }

    let mut tasks = vec![LowerTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            LowerTask::Visit(BehavioralPred::Top) => values.push(BehavioralFormula::Top),
            LowerTask::Visit(BehavioralPred::RelationQuery { relation_name, args, negated }) => {
                let relation = BehavioralFormula::Relation {
                    name: relation_name.clone(),
                    args: args.iter().map(PredArg::to_arg).collect(),
                };
                values.push(if *negated {
                    BehavioralFormula::Not(Box::new(relation))
                } else {
                    relation
                });
            },
            LowerTask::Visit(BehavioralPred::Quantified { quantifier, var, domain, body }) => {
                let value_base = values.len();
                tasks.push(LowerTask::Quantified {
                    quantifier: *quantifier,
                    var,
                    domain,
                    value_base,
                });
                tasks.push(LowerTask::Visit(body));
            },
            LowerTask::Visit(BehavioralPred::And(left, right)) => {
                push_lower_binary(&mut tasks, &values, LowerTask::And, left, right);
            },
            LowerTask::Visit(BehavioralPred::Or(left, right)) => {
                push_lower_binary(&mut tasks, &values, LowerTask::Or, left, right);
            },
            LowerTask::Visit(BehavioralPred::Not(inner)) => {
                let value_base = values.len();
                tasks.push(LowerTask::Not(value_base));
                tasks.push(LowerTask::Visit(inner));
            },
            LowerTask::Visit(BehavioralPred::Implies(left, right)) => {
                push_lower_binary(&mut tasks, &values, LowerTask::Implies, left, right);
            },
            LowerTask::Visit(BehavioralPred::AcMatch { .. }) => {
                unreachable!("AcMatch was rejected by the lowering pre-scan")
            },
            LowerTask::Quantified { quantifier, var, domain, value_base } => {
                let body = values
                    .pop()
                    .expect("behavioral lowering lost a quantified body");
                values.truncate(value_base);
                let fields = (var.to_owned(), QuantifiedDomain::to_qdomain(domain.as_ref()));
                values.push(match quantifier {
                    Quantifier::ForAll => BehavioralFormula::Forall {
                        var: fields.0,
                        domain: fields.1,
                        body: Box::new(body),
                    },
                    Quantifier::Exists => BehavioralFormula::Exists {
                        var: fields.0,
                        domain: fields.1,
                        body: Box::new(body),
                    },
                });
            },
            LowerTask::And(value_base) => {
                finish_lower_binary(&mut values, value_base, |left, right| {
                    BehavioralFormula::And(Box::new(left), Box::new(right))
                })
            },
            LowerTask::Or(value_base) => {
                finish_lower_binary(&mut values, value_base, |left, right| {
                    BehavioralFormula::Or(Box::new(left), Box::new(right))
                })
            },
            LowerTask::Not(value_base) => {
                let inner = values
                    .pop()
                    .expect("behavioral lowering lost a negated operand");
                values.truncate(value_base);
                values.push(BehavioralFormula::Not(Box::new(inner)));
            },
            LowerTask::Implies(value_base) => {
                finish_lower_binary(&mut values, value_base, |left, right| {
                    BehavioralFormula::Or(
                        Box::new(BehavioralFormula::Not(Box::new(left))),
                        Box::new(right),
                    )
                })
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop()
}

fn push_lower_binary<'pred>(
    tasks: &mut Vec<LowerTask<'pred>>,
    values: &[BehavioralFormula],
    finish: impl FnOnce(usize) -> LowerTask<'pred>,
    left: &'pred BehavioralPred,
    right: &'pred BehavioralPred,
) {
    tasks.push(finish(values.len()));
    tasks.push(LowerTask::Visit(right));
    tasks.push(LowerTask::Visit(left));
}

fn finish_lower_binary(
    values: &mut Vec<BehavioralFormula>,
    value_base: usize,
    build: impl FnOnce(BehavioralFormula, BehavioralFormula) -> BehavioralFormula,
) {
    let right = values
        .pop()
        .expect("behavioral lowering lost a right operand");
    let left = values
        .pop()
        .expect("behavioral lowering lost a left operand");
    values.truncate(value_base);
    values.push(build(left, right));
}
