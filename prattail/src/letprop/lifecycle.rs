//! Heap-backed lifecycle operations for recursive `letprop` models.

use super::{LetPropArg, LetPropExpr};
use std::fmt;

enum ArgCloneTask<'arg> {
    Visit(&'arg LetPropArg),
    App { func: &'arg str, base: usize, len: usize },
}

impl Clone for LetPropArg {
    fn clone(&self) -> Self {
        let mut tasks = vec![ArgCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ArgCloneTask::Visit(LetPropArg::Var(name)) => {
                    values.push(LetPropArg::Var(name.clone()));
                },
                ArgCloneTask::Visit(LetPropArg::App { func, args }) => {
                    tasks.push(ArgCloneTask::App {
                        func,
                        base: values.len(),
                        len: args.len(),
                    });
                    tasks.extend(args.iter().rev().map(ArgCloneTask::Visit));
                },
                ArgCloneTask::App { func, base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let args = values.drain(base..).collect();
                    values.push(LetPropArg::App { func: func.to_string(), args });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("letprop argument clone produced no value")
    }
}

impl PartialEq for LetPropArg {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (LetPropArg::Var(a), LetPropArg::Var(b)) if a == b => {},
                (
                    LetPropArg::App { func: af, args: aa },
                    LetPropArg::App { func: bf, args: ba },
                ) if af == bf && aa.len() == ba.len() => {
                    work.extend(aa.iter().zip(ba).rev());
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for LetPropArg {}

fn take_arg_children(arg: &mut LetPropArg, work: &mut Vec<LetPropArg>) {
    if let LetPropArg::App { args, .. } = arg {
        work.extend(std::mem::take(args));
    }
}

impl Drop for LetPropArg {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_arg_children(self, &mut work);
        while let Some(mut arg) = work.pop() {
            take_arg_children(&mut arg, &mut work);
        }
    }
}

enum ArgDebugTask<'arg> {
    Visit(&'arg LetPropArg),
    Text(&'static str),
}

impl fmt::Debug for LetPropArg {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![ArgDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                ArgDebugTask::Text(text) => formatter.write_str(text)?,
                ArgDebugTask::Visit(LetPropArg::Var(name)) => {
                    write!(formatter, "Var({name:?})")?;
                },
                ArgDebugTask::Visit(LetPropArg::App { func, args }) => {
                    tasks.push(ArgDebugTask::Text("] }"));
                    for (index, arg) in args.iter().enumerate().rev() {
                        tasks.push(ArgDebugTask::Visit(arg));
                        if index > 0 {
                            tasks.push(ArgDebugTask::Text(", "));
                        }
                    }
                    write!(formatter, "App {{ func: {func:?}, args: [")?;
                },
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum UnaryKind {
    Forall,
    Exists,
    Not,
}

#[derive(Clone, Copy)]
enum BinaryKind {
    And,
    Or,
    Implies,
}

enum ExprCloneTask<'expr> {
    Visit(&'expr LetPropExpr),
    Unary { kind: UnaryKind, var: Option<&'expr str> },
    Binary(BinaryKind),
}

impl Clone for LetPropExpr {
    fn clone(&self) -> Self {
        let mut tasks = vec![ExprCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ExprCloneTask::Visit(LetPropExpr::True) => values.push(LetPropExpr::True),
                ExprCloneTask::Visit(LetPropExpr::False) => values.push(LetPropExpr::False),
                ExprCloneTask::Visit(LetPropExpr::Atom { relation, args }) => {
                    values.push(LetPropExpr::Atom {
                        relation: relation.clone(),
                        args: args.to_vec(),
                    });
                },
                ExprCloneTask::Visit(LetPropExpr::Recursive { args }) => {
                    values.push(LetPropExpr::Recursive { args: args.to_vec() });
                },
                ExprCloneTask::Visit(LetPropExpr::Forall { var, body }) => {
                    tasks.push(ExprCloneTask::Unary { kind: UnaryKind::Forall, var: Some(var) });
                    tasks.push(ExprCloneTask::Visit(body));
                },
                ExprCloneTask::Visit(LetPropExpr::Exists { var, body }) => {
                    tasks.push(ExprCloneTask::Unary { kind: UnaryKind::Exists, var: Some(var) });
                    tasks.push(ExprCloneTask::Visit(body));
                },
                ExprCloneTask::Visit(LetPropExpr::Not(inner)) => {
                    tasks.push(ExprCloneTask::Unary { kind: UnaryKind::Not, var: None });
                    tasks.push(ExprCloneTask::Visit(inner));
                },
                ExprCloneTask::Visit(LetPropExpr::And(left, right)) => {
                    tasks.push(ExprCloneTask::Binary(BinaryKind::And));
                    tasks.push(ExprCloneTask::Visit(right));
                    tasks.push(ExprCloneTask::Visit(left));
                },
                ExprCloneTask::Visit(LetPropExpr::Or(left, right)) => {
                    tasks.push(ExprCloneTask::Binary(BinaryKind::Or));
                    tasks.push(ExprCloneTask::Visit(right));
                    tasks.push(ExprCloneTask::Visit(left));
                },
                ExprCloneTask::Visit(LetPropExpr::Implies(left, right)) => {
                    tasks.push(ExprCloneTask::Binary(BinaryKind::Implies));
                    tasks.push(ExprCloneTask::Visit(right));
                    tasks.push(ExprCloneTask::Visit(left));
                },
                ExprCloneTask::Unary { kind, var } => {
                    let body = Box::new(values.pop().expect("letprop clone lost a unary child"));
                    let expr = match kind {
                        UnaryKind::Forall => LetPropExpr::Forall {
                            var: var.expect("forall clone lost its binder").to_string(),
                            body,
                        },
                        UnaryKind::Exists => LetPropExpr::Exists {
                            var: var.expect("exists clone lost its binder").to_string(),
                            body,
                        },
                        UnaryKind::Not => LetPropExpr::Not(body),
                    };
                    values.push(expr);
                },
                ExprCloneTask::Binary(kind) => {
                    let right = Box::new(values.pop().expect("letprop clone lost right child"));
                    let left = Box::new(values.pop().expect("letprop clone lost left child"));
                    values.push(match kind {
                        BinaryKind::And => LetPropExpr::And(left, right),
                        BinaryKind::Or => LetPropExpr::Or(left, right),
                        BinaryKind::Implies => LetPropExpr::Implies(left, right),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("letprop expression clone produced no value")
    }
}

impl PartialEq for LetPropExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (LetPropExpr::True, LetPropExpr::True)
                | (LetPropExpr::False, LetPropExpr::False) => {},
                (
                    LetPropExpr::Atom { relation: ar, args: aa },
                    LetPropExpr::Atom { relation: br, args: ba },
                ) if ar == br && aa == ba => {},
                (LetPropExpr::Recursive { args: a }, LetPropExpr::Recursive { args: b })
                    if a == b => {},
                (
                    LetPropExpr::Forall { var: av, body: ab },
                    LetPropExpr::Forall { var: bv, body: bb },
                )
                | (
                    LetPropExpr::Exists { var: av, body: ab },
                    LetPropExpr::Exists { var: bv, body: bb },
                ) if av == bv => work.push((ab, bb)),
                (LetPropExpr::Not(a), LetPropExpr::Not(b)) => work.push((a, b)),
                (LetPropExpr::And(al, ar), LetPropExpr::And(bl, br))
                | (LetPropExpr::Or(al, ar), LetPropExpr::Or(bl, br))
                | (LetPropExpr::Implies(al, ar), LetPropExpr::Implies(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for LetPropExpr {}

fn take_expr_children(expr: &mut LetPropExpr, work: &mut Vec<LetPropExpr>) {
    match expr {
        LetPropExpr::Forall { body, .. } | LetPropExpr::Exists { body, .. } => {
            work.push(*std::mem::replace(body, Box::new(LetPropExpr::True)));
        },
        LetPropExpr::Not(inner) => {
            work.push(*std::mem::replace(inner, Box::new(LetPropExpr::True)));
        },
        LetPropExpr::And(left, right)
        | LetPropExpr::Or(left, right)
        | LetPropExpr::Implies(left, right) => {
            work.push(*std::mem::replace(left, Box::new(LetPropExpr::True)));
            work.push(*std::mem::replace(right, Box::new(LetPropExpr::True)));
        },
        LetPropExpr::True
        | LetPropExpr::False
        | LetPropExpr::Atom { .. }
        | LetPropExpr::Recursive { .. } => {},
    }
}

impl Drop for LetPropExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_expr_children(self, &mut work);
        while let Some(mut expr) = work.pop() {
            take_expr_children(&mut expr, &mut work);
        }
    }
}

enum ExprDebugTask<'expr> {
    Visit(&'expr LetPropExpr),
    Text(&'static str),
}

impl fmt::Debug for LetPropExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![ExprDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                ExprDebugTask::Text(text) => formatter.write_str(text)?,
                ExprDebugTask::Visit(LetPropExpr::True) => formatter.write_str("True")?,
                ExprDebugTask::Visit(LetPropExpr::False) => formatter.write_str("False")?,
                ExprDebugTask::Visit(LetPropExpr::Atom { relation, args }) => {
                    write!(formatter, "Atom {{ relation: {relation:?}, args: {args:?} }}")?;
                },
                ExprDebugTask::Visit(LetPropExpr::Recursive { args }) => {
                    write!(formatter, "Recursive {{ args: {args:?} }}")?;
                },
                ExprDebugTask::Visit(LetPropExpr::Forall { var, body }) => {
                    tasks.push(ExprDebugTask::Text(" }"));
                    tasks.push(ExprDebugTask::Visit(body));
                    write!(formatter, "Forall {{ var: {var:?}, body: ")?;
                },
                ExprDebugTask::Visit(LetPropExpr::Exists { var, body }) => {
                    tasks.push(ExprDebugTask::Text(" }"));
                    tasks.push(ExprDebugTask::Visit(body));
                    write!(formatter, "Exists {{ var: {var:?}, body: ")?;
                },
                ExprDebugTask::Visit(LetPropExpr::Not(inner)) => {
                    tasks.push(ExprDebugTask::Text(")"));
                    tasks.push(ExprDebugTask::Visit(inner));
                    formatter.write_str("Not(")?;
                },
                ExprDebugTask::Visit(LetPropExpr::And(left, right)) => {
                    push_binary_debug(&mut tasks, left, right, "And(");
                },
                ExprDebugTask::Visit(LetPropExpr::Or(left, right)) => {
                    push_binary_debug(&mut tasks, left, right, "Or(");
                },
                ExprDebugTask::Visit(LetPropExpr::Implies(left, right)) => {
                    push_binary_debug(&mut tasks, left, right, "Implies(");
                },
            }
        }
        Ok(())
    }
}

fn push_binary_debug<'expr>(
    tasks: &mut Vec<ExprDebugTask<'expr>>,
    left: &'expr LetPropExpr,
    right: &'expr LetPropExpr,
    prefix: &'static str,
) {
    tasks.push(ExprDebugTask::Text(")"));
    tasks.push(ExprDebugTask::Visit(right));
    tasks.push(ExprDebugTask::Text(", "));
    tasks.push(ExprDebugTask::Visit(left));
    tasks.push(ExprDebugTask::Text(prefix));
}
