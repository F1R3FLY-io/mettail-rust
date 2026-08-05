//! Stack-safe lifecycle traits for free-semiring expression trees.

use super::FreeExpr;
use std::fmt;
use std::hash::{Hash, Hasher};

enum BuildTask<'expr> {
    Visit(&'expr FreeExpr),
    Plus,
    Times,
}

impl Clone for FreeExpr {
    fn clone(&self) -> Self {
        let mut tasks = vec![BuildTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                BuildTask::Visit(FreeExpr::Zero) => values.push(FreeExpr::Zero),
                BuildTask::Visit(FreeExpr::One) => values.push(FreeExpr::One),
                BuildTask::Visit(FreeExpr::Gen(name)) => {
                    values.push(FreeExpr::Gen(name.clone()));
                },
                BuildTask::Visit(FreeExpr::Plus(left, right)) => {
                    tasks.push(BuildTask::Plus);
                    tasks.push(BuildTask::Visit(right));
                    tasks.push(BuildTask::Visit(left));
                },
                BuildTask::Visit(FreeExpr::Times(left, right)) => {
                    tasks.push(BuildTask::Times);
                    tasks.push(BuildTask::Visit(right));
                    tasks.push(BuildTask::Visit(left));
                },
                BuildTask::Plus => finish_binary(&mut values, FreeExpr::Plus),
                BuildTask::Times => finish_binary(&mut values, FreeExpr::Times),
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("free-expression clone PDA produced no value")
    }
}

fn finish_binary(
    values: &mut Vec<FreeExpr>,
    build: impl FnOnce(Box<FreeExpr>, Box<FreeExpr>) -> FreeExpr,
) {
    let right = values
        .pop()
        .expect("free-expression PDA lost its right operand");
    let left = values
        .pop()
        .expect("free-expression PDA lost its left operand");
    values.push(build(Box::new(left), Box::new(right)));
}

fn take_children(expr: &mut FreeExpr, work: &mut Vec<FreeExpr>) {
    if let FreeExpr::Plus(left, right) | FreeExpr::Times(left, right) = expr {
        work.push(*std::mem::replace(left, Box::new(FreeExpr::Zero)));
        work.push(*std::mem::replace(right, Box::new(FreeExpr::Zero)));
    }
}

impl Drop for FreeExpr {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut expr) = work.pop() {
            take_children(&mut expr, &mut work);
        }
    }
}

impl PartialEq for FreeExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (FreeExpr::Zero, FreeExpr::Zero) | (FreeExpr::One, FreeExpr::One) => {},
                (FreeExpr::Gen(a), FreeExpr::Gen(b)) if a == b => {},
                (FreeExpr::Plus(al, ar), FreeExpr::Plus(bl, br))
                | (FreeExpr::Times(al, ar), FreeExpr::Times(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for FreeExpr {}

enum HashTask<'expr> {
    Visit(&'expr FreeExpr),
    Name(&'expr String),
}

impl Hash for FreeExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut tasks = vec![HashTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                HashTask::Visit(expr) => {
                    std::mem::discriminant(expr).hash(state);
                    match expr {
                        FreeExpr::Zero | FreeExpr::One => {},
                        FreeExpr::Gen(name) => tasks.push(HashTask::Name(name)),
                        FreeExpr::Plus(left, right) | FreeExpr::Times(left, right) => {
                            tasks.push(HashTask::Visit(right));
                            tasks.push(HashTask::Visit(left));
                        },
                    }
                },
                HashTask::Name(name) => name.hash(state),
            }
        }
    }
}

enum FormatTask<'expr> {
    Debug(&'expr FreeExpr),
    Display(&'expr FreeExpr),
    Text(&'static str),
}

impl fmt::Debug for FreeExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Debug(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Display(_) => unreachable!("display task reached Debug formatter"),
                FormatTask::Debug(FreeExpr::Zero) => formatter.write_str("Zero")?,
                FormatTask::Debug(FreeExpr::One) => formatter.write_str("One")?,
                FormatTask::Debug(FreeExpr::Gen(name)) => {
                    write!(formatter, "Gen({name:?})")?;
                },
                FormatTask::Debug(FreeExpr::Plus(left, right)) => {
                    formatter.write_str("Plus(")?;
                    push_debug_binary(&mut tasks, left, right);
                },
                FormatTask::Debug(FreeExpr::Times(left, right)) => {
                    formatter.write_str("Times(")?;
                    push_debug_binary(&mut tasks, left, right);
                },
            }
        }
        Ok(())
    }
}

fn push_debug_binary<'expr>(
    tasks: &mut Vec<FormatTask<'expr>>,
    left: &'expr FreeExpr,
    right: &'expr FreeExpr,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Debug(right));
    tasks.push(FormatTask::Text(", "));
    tasks.push(FormatTask::Debug(left));
}

impl fmt::Display for FreeExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Display(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Debug(_) => unreachable!("debug task reached Display formatter"),
                FormatTask::Display(FreeExpr::Zero) => formatter.write_str("0")?,
                FormatTask::Display(FreeExpr::One) => formatter.write_str("1")?,
                FormatTask::Display(FreeExpr::Gen(name)) => formatter.write_str(name)?,
                FormatTask::Display(FreeExpr::Plus(left, right)) => {
                    push_display_binary(&mut tasks, left, right, " + ");
                },
                FormatTask::Display(FreeExpr::Times(left, right)) => {
                    push_display_binary(&mut tasks, left, right, " * ");
                },
            }
        }
        Ok(())
    }
}

fn push_display_binary<'expr>(
    tasks: &mut Vec<FormatTask<'expr>>,
    left: &'expr FreeExpr,
    right: &'expr FreeExpr,
    separator: &'static str,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Display(right));
    tasks.push(FormatTask::Text(separator));
    tasks.push(FormatTask::Display(left));
    tasks.push(FormatTask::Text("("));
}
