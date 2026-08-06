use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::TermExpr;

impl Clone for TermExpr {
    fn clone(&self) -> Self {
        enum Task<'term> {
            Visit(&'term TermExpr),
            App { head: String, child_count: usize },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TermExpr::Var(index)) => values.push(TermExpr::Var(*index)),
                Task::Visit(TermExpr::Const(name)) => {
                    values.push(TermExpr::Const(name.clone()));
                },
                Task::Visit(TermExpr::App { head, args }) => {
                    tasks.push(Task::App {
                        head: head.clone(),
                        child_count: args.len(),
                    });
                    for child in args.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::App { head, child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("term clone PDA lost child results");
                    let args = values.split_off(first);
                    values.push(TermExpr::App { head, args });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("term clone PDA produced no value")
    }
}

impl PartialEq for TermExpr {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TermExpr::Var(a), TermExpr::Var(b)) if a == b => {},
                (TermExpr::Const(a), TermExpr::Const(b)) if a == b => {},
                (TermExpr::App { head: ah, args: aa }, TermExpr::App { head: bh, args: ba })
                    if ah == bh && aa.len() == ba.len() =>
                {
                    for pair in aa.iter().zip(ba).rev() {
                        work.push(pair);
                    }
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for TermExpr {}

impl Hash for TermExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                TermExpr::Var(index) => index.hash(state),
                TermExpr::Const(name) => name.hash(state),
                TermExpr::App { head, args } => {
                    head.hash(state);
                    args.len().hash(state);
                    for child in args.iter().rev() {
                        work.push(child);
                    }
                },
            }
        }
    }
}

impl fmt::Debug for TermExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Node(&'term TermExpr),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(TermExpr::Var(index)) => write!(f, "Var({index:?})")?,
                Task::Node(TermExpr::Const(name)) => write!(f, "Const({name:?})")?,
                Task::Node(TermExpr::App { head, args }) => {
                    tasks.push(Task::Text("] }"));
                    for (index, child) in args.iter().enumerate().rev() {
                        tasks.push(Task::Node(child));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text("["));
                    write!(f, "App {{ head: {head:?}, args: ")?;
                },
            }
        }
        Ok(())
    }
}

impl fmt::Display for TermExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Node(&'term TermExpr),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(TermExpr::Var(index)) => write!(f, "x{index}")?,
                Task::Node(TermExpr::Const(name)) => f.write_str(name)?,
                Task::Node(TermExpr::App { head, args }) => {
                    tasks.push(Task::Text(")"));
                    for (index, child) in args.iter().enumerate().rev() {
                        tasks.push(Task::Node(child));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                    tasks.push(Task::Text("("));
                    f.write_str(head)?;
                },
            }
        }
        Ok(())
    }
}

impl Drop for TermExpr {
    fn drop(&mut self) {
        let root = mem::replace(self, TermExpr::Var(0));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    TermExpr::Var(_) => {},
                    TermExpr::Const(name) => drop(ptr::read(name)),
                    TermExpr::App { head, args } => {
                        drop(ptr::read(head));
                        let args = ptr::read(args);
                        work.extend(args);
                    },
                }
            }
        }
    }
}
