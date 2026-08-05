//! Stack-safe lifecycle and structural analyses for behavioral formulas.

use super::{ActionPattern, Arg, BehavioralFormula, QDomain};
use std::collections::BTreeSet;
use std::fmt;
use std::hash::{Hash, Hasher};

impl Clone for QDomain {
    fn clone(&self) -> Self {
        let mut limits = Vec::new();
        let mut cursor = self;
        while let QDomain::Bounded(inner, limit) = cursor {
            limits.push(*limit);
            cursor = inner;
        }
        let mut cloned = match cursor {
            QDomain::Values(values) => QDomain::Values(values.clone()),
            QDomain::RelationColumn(relation, column) => {
                QDomain::RelationColumn(relation.clone(), *column)
            },
            QDomain::Active => QDomain::Active,
            QDomain::Bounded(..) => unreachable!("QDomain spine scan stopped on a wrapper"),
        };
        for limit in limits.into_iter().rev() {
            cloned = QDomain::Bounded(Box::new(cloned), limit);
        }
        cloned
    }
}

impl Drop for QDomain {
    fn drop(&mut self) {
        let mut next = match self {
            QDomain::Bounded(inner, _) => {
                Some(*std::mem::replace(inner, Box::new(QDomain::Active)))
            },
            _ => None,
        };
        while let Some(mut domain) = next {
            next = match &mut domain {
                QDomain::Bounded(inner, _) => {
                    Some(*std::mem::replace(inner, Box::new(QDomain::Active)))
                },
                _ => None,
            };
        }
    }
}

impl PartialEq for QDomain {
    fn eq(&self, other: &Self) -> bool {
        let mut left = self;
        let mut right = other;
        loop {
            match (left, right) {
                (QDomain::Values(a), QDomain::Values(b)) => return a == b,
                (QDomain::RelationColumn(ar, ac), QDomain::RelationColumn(br, bc)) => {
                    return ar == br && ac == bc;
                },
                (QDomain::Active, QDomain::Active) => return true,
                (QDomain::Bounded(a, al), QDomain::Bounded(b, bl)) if al == bl => {
                    left = a;
                    right = b;
                },
                _ => return false,
            }
        }
    }
}

impl Eq for QDomain {}

impl Hash for QDomain {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut cursor = self;
        loop {
            std::mem::discriminant(cursor).hash(state);
            match cursor {
                QDomain::Values(values) => {
                    values.hash(state);
                    break;
                },
                QDomain::RelationColumn(relation, column) => {
                    relation.hash(state);
                    column.hash(state);
                    break;
                },
                QDomain::Active => break,
                QDomain::Bounded(inner, limit) => {
                    limit.hash(state);
                    cursor = inner;
                },
            }
        }
    }
}

impl fmt::Debug for QDomain {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut cursor = self;
        let mut limits = Vec::new();
        loop {
            match cursor {
                QDomain::Values(values) => {
                    write!(formatter, "Values({values:?})")?;
                    break;
                },
                QDomain::RelationColumn(relation, column) => {
                    write!(formatter, "RelationColumn({relation:?}, {column:?})")?;
                    break;
                },
                QDomain::Active => {
                    formatter.write_str("Active")?;
                    break;
                },
                QDomain::Bounded(inner, limit) => {
                    write!(formatter, "Bounded(")?;
                    cursor = inner;
                    limits.push(*limit);
                },
            }
        }
        while let Some(limit) = limits.pop() {
            write!(formatter, ", {limit:?})")?;
        }
        Ok(())
    }
}

enum CloneTask<'formula> {
    Visit(&'formula BehavioralFormula),
    Forall(&'formula str, &'formula QDomain, usize),
    Exists(&'formula str, &'formula QDomain, usize),
    Diamond(&'formula ActionPattern, usize),
    BoxAll(&'formula ActionPattern, usize),
    Mu(&'formula str, usize),
    Nu(&'formula str, usize),
    And(usize),
    Or(usize),
    Not(usize),
}

impl Clone for BehavioralFormula {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(BehavioralFormula::Top) => values.push(BehavioralFormula::Top),
                CloneTask::Visit(BehavioralFormula::Bot) => values.push(BehavioralFormula::Bot),
                CloneTask::Visit(BehavioralFormula::Relation { name, args }) => {
                    values.push(BehavioralFormula::Relation {
                        name: name.clone(),
                        args: args.clone(),
                    });
                },
                CloneTask::Visit(BehavioralFormula::Forall { var, domain, body }) => {
                    push_unary(
                        &mut tasks,
                        &values,
                        |base| CloneTask::Forall(var, domain, base),
                        body,
                    );
                },
                CloneTask::Visit(BehavioralFormula::Exists { var, domain, body }) => {
                    push_unary(
                        &mut tasks,
                        &values,
                        |base| CloneTask::Exists(var, domain, base),
                        body,
                    );
                },
                CloneTask::Visit(BehavioralFormula::Atom(label)) => {
                    values.push(BehavioralFormula::Atom(label.clone()));
                },
                CloneTask::Visit(BehavioralFormula::Diamond(action, body)) => {
                    push_unary(&mut tasks, &values, |base| CloneTask::Diamond(action, base), body);
                },
                CloneTask::Visit(BehavioralFormula::BoxAll(action, body)) => {
                    push_unary(&mut tasks, &values, |base| CloneTask::BoxAll(action, base), body);
                },
                CloneTask::Visit(BehavioralFormula::Mu(var, body)) => {
                    push_unary(&mut tasks, &values, |base| CloneTask::Mu(var, base), body);
                },
                CloneTask::Visit(BehavioralFormula::Nu(var, body)) => {
                    push_unary(&mut tasks, &values, |base| CloneTask::Nu(var, base), body);
                },
                CloneTask::Visit(BehavioralFormula::FixVar(var)) => {
                    values.push(BehavioralFormula::FixVar(var.clone()));
                },
                CloneTask::Visit(BehavioralFormula::And(left, right)) => {
                    push_binary(&mut tasks, &values, CloneTask::And, left, right);
                },
                CloneTask::Visit(BehavioralFormula::Or(left, right)) => {
                    push_binary(&mut tasks, &values, CloneTask::Or, left, right);
                },
                CloneTask::Visit(BehavioralFormula::Not(inner)) => {
                    push_unary(&mut tasks, &values, CloneTask::Not, inner);
                },
                CloneTask::Forall(var, domain, base) => {
                    finish_unary(&mut values, base, |body| BehavioralFormula::Forall {
                        var: var.to_owned(),
                        domain: domain.clone(),
                        body: Box::new(body),
                    })
                },
                CloneTask::Exists(var, domain, base) => {
                    finish_unary(&mut values, base, |body| BehavioralFormula::Exists {
                        var: var.to_owned(),
                        domain: domain.clone(),
                        body: Box::new(body),
                    })
                },
                CloneTask::Diamond(action, base) => finish_unary(&mut values, base, |body| {
                    BehavioralFormula::Diamond(action.clone(), Box::new(body))
                }),
                CloneTask::BoxAll(action, base) => finish_unary(&mut values, base, |body| {
                    BehavioralFormula::BoxAll(action.clone(), Box::new(body))
                }),
                CloneTask::Mu(var, base) => finish_unary(&mut values, base, |body| {
                    BehavioralFormula::Mu(var.to_owned(), Box::new(body))
                }),
                CloneTask::Nu(var, base) => finish_unary(&mut values, base, |body| {
                    BehavioralFormula::Nu(var.to_owned(), Box::new(body))
                }),
                CloneTask::And(base) => finish_binary(&mut values, base, |left, right| {
                    BehavioralFormula::And(Box::new(left), Box::new(right))
                }),
                CloneTask::Or(base) => finish_binary(&mut values, base, |left, right| {
                    BehavioralFormula::Or(Box::new(left), Box::new(right))
                }),
                CloneTask::Not(base) => {
                    finish_unary(&mut values, base, |inner| BehavioralFormula::Not(Box::new(inner)))
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("formula clone PDA produced no result")
    }
}

fn push_unary<'formula>(
    tasks: &mut Vec<CloneTask<'formula>>,
    values: &[BehavioralFormula],
    finish: impl FnOnce(usize) -> CloneTask<'formula>,
    body: &'formula BehavioralFormula,
) {
    tasks.push(finish(values.len()));
    tasks.push(CloneTask::Visit(body));
}

fn push_binary<'formula>(
    tasks: &mut Vec<CloneTask<'formula>>,
    values: &[BehavioralFormula],
    finish: impl FnOnce(usize) -> CloneTask<'formula>,
    left: &'formula BehavioralFormula,
    right: &'formula BehavioralFormula,
) {
    tasks.push(finish(values.len()));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn finish_unary(
    values: &mut Vec<BehavioralFormula>,
    base: usize,
    build: impl FnOnce(BehavioralFormula) -> BehavioralFormula,
) {
    let body = values.pop().expect("formula clone PDA lost a unary body");
    values.truncate(base);
    values.push(build(body));
}

fn finish_binary(
    values: &mut Vec<BehavioralFormula>,
    base: usize,
    build: impl FnOnce(BehavioralFormula, BehavioralFormula) -> BehavioralFormula,
) {
    let right = values
        .pop()
        .expect("formula clone PDA lost a right operand");
    let left = values.pop().expect("formula clone PDA lost a left operand");
    values.truncate(base);
    values.push(build(left, right));
}

fn take_formula_children(formula: &mut BehavioralFormula, work: &mut Vec<BehavioralFormula>) {
    let take = |child: &mut Box<BehavioralFormula>| {
        *std::mem::replace(child, Box::new(BehavioralFormula::Top))
    };
    match formula {
        BehavioralFormula::Forall { body, .. }
        | BehavioralFormula::Exists { body, .. }
        | BehavioralFormula::Diamond(_, body)
        | BehavioralFormula::BoxAll(_, body)
        | BehavioralFormula::Mu(_, body)
        | BehavioralFormula::Nu(_, body)
        | BehavioralFormula::Not(body) => work.push(take(body)),
        BehavioralFormula::And(left, right) | BehavioralFormula::Or(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        BehavioralFormula::Top
        | BehavioralFormula::Bot
        | BehavioralFormula::Relation { .. }
        | BehavioralFormula::Atom(_)
        | BehavioralFormula::FixVar(_) => {},
    }
}

impl Drop for BehavioralFormula {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_formula_children(self, &mut work);
        while let Some(mut formula) = work.pop() {
            take_formula_children(&mut formula, &mut work);
        }
    }
}

impl PartialEq for BehavioralFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (BehavioralFormula::Top, BehavioralFormula::Top)
                | (BehavioralFormula::Bot, BehavioralFormula::Bot) => {},
                (
                    BehavioralFormula::Relation { name: an, args: aa },
                    BehavioralFormula::Relation { name: bn, args: ba },
                ) if an == bn && aa == ba => {},
                (
                    BehavioralFormula::Forall { var: av, domain: ad, body: ab },
                    BehavioralFormula::Forall { var: bv, domain: bd, body: bb },
                )
                | (
                    BehavioralFormula::Exists { var: av, domain: ad, body: ab },
                    BehavioralFormula::Exists { var: bv, domain: bd, body: bb },
                ) if av == bv && ad == bd => work.push((ab, bb)),
                (BehavioralFormula::Atom(a), BehavioralFormula::Atom(b))
                | (BehavioralFormula::FixVar(a), BehavioralFormula::FixVar(b))
                    if a == b => {},
                (BehavioralFormula::Diamond(aa, ab), BehavioralFormula::Diamond(ba, bb))
                | (BehavioralFormula::BoxAll(aa, ab), BehavioralFormula::BoxAll(ba, bb))
                    if aa == ba =>
                {
                    work.push((ab, bb))
                },
                (BehavioralFormula::Mu(av, ab), BehavioralFormula::Mu(bv, bb))
                | (BehavioralFormula::Nu(av, ab), BehavioralFormula::Nu(bv, bb))
                    if av == bv =>
                {
                    work.push((ab, bb))
                },
                (BehavioralFormula::And(al, ar), BehavioralFormula::And(bl, br))
                | (BehavioralFormula::Or(al, ar), BehavioralFormula::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (BehavioralFormula::Not(a), BehavioralFormula::Not(b)) => work.push((a, b)),
                _ => return false,
            }
        }
        true
    }
}

impl Eq for BehavioralFormula {}

impl Hash for BehavioralFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(formula) = work.pop() {
            std::mem::discriminant(formula).hash(state);
            match formula {
                BehavioralFormula::Top | BehavioralFormula::Bot => {},
                BehavioralFormula::Relation { name, args } => {
                    name.hash(state);
                    args.hash(state);
                },
                BehavioralFormula::Forall { var, domain, body }
                | BehavioralFormula::Exists { var, domain, body } => {
                    var.hash(state);
                    domain.hash(state);
                    work.push(body);
                },
                BehavioralFormula::Atom(label) | BehavioralFormula::FixVar(label) => {
                    label.hash(state);
                },
                BehavioralFormula::Diamond(action, body)
                | BehavioralFormula::BoxAll(action, body) => {
                    action.hash(state);
                    work.push(body);
                },
                BehavioralFormula::Mu(var, body) | BehavioralFormula::Nu(var, body) => {
                    var.hash(state);
                    work.push(body);
                },
                BehavioralFormula::And(left, right) | BehavioralFormula::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                BehavioralFormula::Not(inner) => work.push(inner),
            }
        }
    }
}

enum DebugTask<'formula> {
    Visit(&'formula BehavioralFormula),
    Text(&'static str),
}

impl fmt::Debug for BehavioralFormula {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(BehavioralFormula::Top) => formatter.write_str("Top")?,
                DebugTask::Visit(BehavioralFormula::Bot) => formatter.write_str("Bot")?,
                DebugTask::Visit(BehavioralFormula::Relation { name, args }) => {
                    write!(formatter, "Relation {{ name: {name:?}, args: {args:?} }}")?;
                },
                DebugTask::Visit(BehavioralFormula::Forall { var, domain, body }) => {
                    write!(formatter, "Forall {{ var: {var:?}, domain: {domain:?}, body: ")?;
                    tasks.push(DebugTask::Text(" }"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::Exists { var, domain, body }) => {
                    write!(formatter, "Exists {{ var: {var:?}, domain: {domain:?}, body: ")?;
                    tasks.push(DebugTask::Text(" }"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::Atom(label)) => {
                    write!(formatter, "Atom({label:?})")?;
                },
                DebugTask::Visit(BehavioralFormula::Diamond(action, body)) => {
                    write!(formatter, "Diamond({action:?}, ")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::BoxAll(action, body)) => {
                    write!(formatter, "BoxAll({action:?}, ")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::Mu(var, body)) => {
                    write!(formatter, "Mu({var:?}, ")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::Nu(var, body)) => {
                    write!(formatter, "Nu({var:?}, ")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(body));
                },
                DebugTask::Visit(BehavioralFormula::FixVar(var)) => {
                    write!(formatter, "FixVar({var:?})")?;
                },
                DebugTask::Visit(BehavioralFormula::And(left, right)) => {
                    formatter.write_str("And(")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(right));
                    tasks.push(DebugTask::Text(", "));
                    tasks.push(DebugTask::Visit(left));
                },
                DebugTask::Visit(BehavioralFormula::Or(left, right)) => {
                    formatter.write_str("Or(")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(right));
                    tasks.push(DebugTask::Text(", "));
                    tasks.push(DebugTask::Visit(left));
                },
                DebugTask::Visit(BehavioralFormula::Not(inner)) => {
                    formatter.write_str("Not(")?;
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(inner));
                },
            }
        }
        Ok(())
    }
}

enum FreeTask<'formula> {
    Visit(&'formula BehavioralFormula),
    Enter(&'formula str, &'formula BehavioralFormula),
    Leave(&'formula str, bool),
}

pub(super) fn free_variables(root: &BehavioralFormula) -> BTreeSet<String> {
    let mut free = BTreeSet::new();
    let mut bound = BTreeSet::new();
    let mut tasks = vec![FreeTask::Visit(root)];
    while let Some(task) = tasks.pop() {
        match task {
            FreeTask::Visit(BehavioralFormula::Relation { args, .. }) => {
                for arg in args {
                    if let Arg::Var(var) = arg {
                        if !bound.contains(var) {
                            free.insert(var.clone());
                        }
                    }
                }
            },
            FreeTask::Visit(BehavioralFormula::Forall { var, body, .. })
            | FreeTask::Visit(BehavioralFormula::Exists { var, body, .. }) => {
                tasks.push(FreeTask::Enter(var, body));
            },
            FreeTask::Visit(BehavioralFormula::And(left, right))
            | FreeTask::Visit(BehavioralFormula::Or(left, right)) => {
                tasks.push(FreeTask::Visit(right));
                tasks.push(FreeTask::Visit(left));
            },
            FreeTask::Visit(BehavioralFormula::Not(inner))
            | FreeTask::Visit(BehavioralFormula::Diamond(_, inner))
            | FreeTask::Visit(BehavioralFormula::BoxAll(_, inner))
            | FreeTask::Visit(BehavioralFormula::Mu(_, inner))
            | FreeTask::Visit(BehavioralFormula::Nu(_, inner)) => {
                tasks.push(FreeTask::Visit(inner));
            },
            FreeTask::Visit(
                BehavioralFormula::Top
                | BehavioralFormula::Bot
                | BehavioralFormula::Atom(_)
                | BehavioralFormula::FixVar(_),
            ) => {},
            FreeTask::Enter(var, body) => {
                let inserted = bound.insert(var.to_owned());
                tasks.push(FreeTask::Leave(var, inserted));
                tasks.push(FreeTask::Visit(body));
            },
            FreeTask::Leave(var, true) => {
                bound.remove(var);
            },
            FreeTask::Leave(_, false) => {},
        }
    }
    free
}

pub(super) fn has_modal(root: &BehavioralFormula) -> bool {
    let mut work = vec![root];
    while let Some(formula) = work.pop() {
        match formula {
            BehavioralFormula::Atom(_)
            | BehavioralFormula::Diamond(..)
            | BehavioralFormula::BoxAll(..)
            | BehavioralFormula::Mu(..)
            | BehavioralFormula::Nu(..)
            | BehavioralFormula::FixVar(_) => return true,
            BehavioralFormula::Forall { body, .. }
            | BehavioralFormula::Exists { body, .. }
            | BehavioralFormula::Not(body) => work.push(body),
            BehavioralFormula::And(left, right) | BehavioralFormula::Or(left, right) => {
                work.push(right);
                work.push(left);
            },
            BehavioralFormula::Top
            | BehavioralFormula::Bot
            | BehavioralFormula::Relation { .. } => {},
        }
    }
    false
}
