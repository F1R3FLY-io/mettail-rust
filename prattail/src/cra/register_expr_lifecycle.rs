//! Heap-backed lifecycle and formatting PDAs for CRA register expressions.

use super::RegisterExpr;
use std::fmt;

enum CloneTask<'expr> {
    Visit(&'expr RegisterExpr),
    Plus(usize),
    Times(usize),
}

impl Clone for RegisterExpr {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(RegisterExpr::Reg(register)) => {
                    values.push(RegisterExpr::Reg(*register))
                },
                CloneTask::Visit(RegisterExpr::InputCost) => values.push(RegisterExpr::InputCost),
                CloneTask::Visit(RegisterExpr::Zero) => values.push(RegisterExpr::Zero),
                CloneTask::Visit(RegisterExpr::One) => values.push(RegisterExpr::One),
                CloneTask::Visit(RegisterExpr::Plus(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::Plus, left, right)
                },
                CloneTask::Visit(RegisterExpr::Times(left, right)) => {
                    push_binary(&mut tasks, values.len(), CloneTask::Times, left, right)
                },
                CloneTask::Plus(base) => finish_binary(&mut values, base, |left, right| {
                    RegisterExpr::Plus(Box::new(left), Box::new(right))
                }),
                CloneTask::Times(base) => finish_binary(&mut values, base, |left, right| {
                    RegisterExpr::Times(Box::new(left), Box::new(right))
                }),
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("register-expression clone PDA produced no expression")
    }
}

fn push_binary<'expr>(
    tasks: &mut Vec<CloneTask<'expr>>,
    base: usize,
    finish: impl FnOnce(usize) -> CloneTask<'expr>,
    left: &'expr RegisterExpr,
    right: &'expr RegisterExpr,
) {
    tasks.push(finish(base));
    tasks.push(CloneTask::Visit(right));
    tasks.push(CloneTask::Visit(left));
}

fn finish_binary(
    values: &mut Vec<RegisterExpr>,
    base: usize,
    build: impl FnOnce(RegisterExpr, RegisterExpr) -> RegisterExpr,
) {
    let right = values
        .pop()
        .expect("register-expression clone PDA lost a right operand");
    let left = values
        .pop()
        .expect("register-expression clone PDA lost a left operand");
    values.truncate(base);
    values.push(build(left, right));
}

impl PartialEq for RegisterExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (RegisterExpr::Reg(a), RegisterExpr::Reg(b)) if a == b => {},
                (RegisterExpr::InputCost, RegisterExpr::InputCost)
                | (RegisterExpr::Zero, RegisterExpr::Zero)
                | (RegisterExpr::One, RegisterExpr::One) => {},
                (RegisterExpr::Plus(al, ar), RegisterExpr::Plus(bl, br))
                | (RegisterExpr::Times(al, ar), RegisterExpr::Times(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for RegisterExpr {}

fn take_children(expr: &mut RegisterExpr, work: &mut Vec<RegisterExpr>) {
    let take =
        |child: &mut Box<RegisterExpr>| *std::mem::replace(child, Box::new(RegisterExpr::Zero));
    match expr {
        RegisterExpr::Plus(left, right) | RegisterExpr::Times(left, right) => {
            work.push(take(left));
            work.push(take(right));
        },
        RegisterExpr::Reg(_) | RegisterExpr::InputCost | RegisterExpr::Zero | RegisterExpr::One => {
        },
    }
}

impl Drop for RegisterExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut expr) = work.pop() {
            take_children(&mut expr, &mut work);
        }
    }
}

enum FormatTask<'expr> {
    Visit(&'expr RegisterExpr),
    Text(&'static str),
}

impl fmt::Debug for RegisterExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Visit(RegisterExpr::Reg(register)) => {
                    write!(formatter, "Reg({register:?})")?
                },
                FormatTask::Visit(RegisterExpr::InputCost) => formatter.write_str("InputCost")?,
                FormatTask::Visit(RegisterExpr::Zero) => formatter.write_str("Zero")?,
                FormatTask::Visit(RegisterExpr::One) => formatter.write_str("One")?,
                FormatTask::Visit(RegisterExpr::Plus(left, right)) => {
                    push_binary_format(&mut tasks, "Plus(", left, right)
                },
                FormatTask::Visit(RegisterExpr::Times(left, right)) => {
                    push_binary_format(&mut tasks, "Times(", left, right)
                },
            }
        }
        Ok(())
    }
}

impl fmt::Display for RegisterExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Visit(RegisterExpr::Reg(register)) => write!(formatter, "{register}")?,
                FormatTask::Visit(RegisterExpr::InputCost) => formatter.write_str("cost")?,
                FormatTask::Visit(RegisterExpr::Zero) => formatter.write_str("0")?,
                FormatTask::Visit(RegisterExpr::One) => formatter.write_str("1")?,
                FormatTask::Visit(RegisterExpr::Plus(left, right)) => {
                    push_binary_display(&mut tasks, " + ", left, right)
                },
                FormatTask::Visit(RegisterExpr::Times(left, right)) => {
                    push_binary_display(&mut tasks, " * ", left, right)
                },
            }
        }
        Ok(())
    }
}

fn push_binary_format<'expr>(
    tasks: &mut Vec<FormatTask<'expr>>,
    open: &'static str,
    left: &'expr RegisterExpr,
    right: &'expr RegisterExpr,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(", "));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text(open));
}

fn push_binary_display<'expr>(
    tasks: &mut Vec<FormatTask<'expr>>,
    separator: &'static str,
    left: &'expr RegisterExpr,
    right: &'expr RegisterExpr,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Visit(right));
    tasks.push(FormatTask::Text(separator));
    tasks.push(FormatTask::Visit(left));
    tasks.push(FormatTask::Text("("));
}
