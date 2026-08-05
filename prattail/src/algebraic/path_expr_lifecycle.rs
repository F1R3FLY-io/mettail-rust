//! Heap-backed lifecycle PDAs for algebraic path expressions.

use super::PathExpr;
use crate::automata::semiring::Semiring;
use std::fmt;

enum CloneTask<'expr, W: Semiring> {
    Visit(&'expr PathExpr<W>),
    Seq(usize),
    Alt(usize),
    Star(usize),
}

impl<W: Semiring> Clone for PathExpr<W> {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(PathExpr::Atom(weight)) => values.push(PathExpr::Atom(*weight)),
                CloneTask::Visit(PathExpr::Zero) => values.push(PathExpr::Zero),
                CloneTask::Visit(PathExpr::One) => values.push(PathExpr::One),
                CloneTask::Visit(PathExpr::Seq(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::Seq, left, right)
                },
                CloneTask::Visit(PathExpr::Alt(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::Alt, left, right)
                },
                CloneTask::Visit(PathExpr::Star(body)) => {
                    tasks.push(CloneTask::Star(values.len()));
                    tasks.push(CloneTask::Visit(body));
                },
                CloneTask::Seq(base) => finish_binary(&mut values, base, |left, right| {
                    PathExpr::Seq(Box::new(left), Box::new(right))
                }),
                CloneTask::Alt(base) => finish_binary(&mut values, base, |left, right| {
                    PathExpr::Alt(Box::new(left), Box::new(right))
                }),
                CloneTask::Star(base) => {
                    let body = values
                        .pop()
                        .expect("path-expression clone PDA lost a star body");
                    values.truncate(base);
                    values.push(PathExpr::Star(Box::new(body)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("path-expression clone PDA produced no expression")
    }
}

fn push_binary<'expr, W: Semiring>(
    tasks: &mut Vec<CloneTask<'expr, W>>,
    base: usize,
    finish: impl FnOnce(usize) -> CloneTask<'expr, W>,
    left: &'expr PathExpr<W>,
    right: &'expr PathExpr<W>,
) {
    tasks.push(finish(base));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn finish_binary<W: Semiring>(
    values: &mut Vec<PathExpr<W>>,
    base: usize,
    build: impl FnOnce(PathExpr<W>, PathExpr<W>) -> PathExpr<W>,
) {
    let right = values
        .pop()
        .expect("path-expression clone PDA lost a right operand");
    let left = values
        .pop()
        .expect("path-expression clone PDA lost a left operand");
    values.truncate(base);
    values.push(build(left, right));
}

fn take_children<W: Semiring>(expr: &mut PathExpr<W>, work: &mut Vec<PathExpr<W>>) {
    let take = |child: &mut Box<PathExpr<W>>| *std::mem::replace(child, Box::new(PathExpr::Zero));
    match expr {
        PathExpr::Seq(left, right) | PathExpr::Alt(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        PathExpr::Star(body) => work.push(take(body)),
        PathExpr::Atom(_) | PathExpr::Zero | PathExpr::One => {},
    }
}

impl<W: Semiring> Drop for PathExpr<W> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut expr) = work.pop() {
            take_children(&mut expr, &mut work);
        }
    }
}

enum DebugTask<'expr, W: Semiring> {
    Visit(&'expr PathExpr<W>),
    Text(&'static str),
}

impl<W: Semiring> fmt::Debug for PathExpr<W> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(PathExpr::Atom(weight)) => write!(formatter, "Atom({weight:?})")?,
                DebugTask::Visit(PathExpr::Zero) => formatter.write_str("Zero")?,
                DebugTask::Visit(PathExpr::One) => formatter.write_str("One")?,
                DebugTask::Visit(PathExpr::Seq(left, right)) => {
                    push_debug_binary(&mut tasks, "Seq(", left, right)
                },
                DebugTask::Visit(PathExpr::Alt(left, right)) => {
                    push_debug_binary(&mut tasks, "Alt(", left, right)
                },
                DebugTask::Visit(PathExpr::Star(body)) => {
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(body));
                    tasks.push(DebugTask::Text("Star("));
                },
            }
        }
        Ok(())
    }
}

fn push_debug_binary<'expr, W: Semiring>(
    tasks: &mut Vec<DebugTask<'expr, W>>,
    open: &'static str,
    left: &'expr PathExpr<W>,
    right: &'expr PathExpr<W>,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Visit(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Visit(left));
    tasks.push(DebugTask::Text(open));
}
