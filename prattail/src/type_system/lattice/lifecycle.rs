use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::LatticeTerm;

impl Clone for LatticeTerm {
    fn clone(&self) -> Self {
        enum Task<'term> {
            Visit(&'term LatticeTerm),
            App { head: String, child_count: usize },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(LatticeTerm::Var(name)) => {
                    values.push(LatticeTerm::Var(name.clone()));
                },
                Task::Visit(LatticeTerm::Const { name, ty }) => {
                    values.push(LatticeTerm::Const { name: name.clone(), ty: *ty });
                },
                Task::Visit(LatticeTerm::App { head, args }) => {
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
                        .expect("lattice term clone lost child results");
                    let args = values.split_off(first);
                    values.push(LatticeTerm::App { head, args });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("lattice term clone produced no value")
    }
}

impl PartialEq for LatticeTerm {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (LatticeTerm::Var(a), LatticeTerm::Var(b)) if a == b => {},
                (
                    LatticeTerm::Const { name: an, ty: at },
                    LatticeTerm::Const { name: bn, ty: bt },
                ) if an == bn && at == bt => {},
                (
                    LatticeTerm::App { head: ah, args: aa },
                    LatticeTerm::App { head: bh, args: ba },
                ) if ah == bh && aa.len() == ba.len() => {
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

impl Eq for LatticeTerm {}

impl Hash for LatticeTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                LatticeTerm::Var(name) => name.hash(state),
                LatticeTerm::Const { name, ty } => {
                    name.hash(state);
                    ty.hash(state);
                },
                LatticeTerm::App { head, args } => {
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

impl fmt::Debug for LatticeTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Node(&'term LatticeTerm),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(LatticeTerm::Var(name)) => write!(f, "Var({name:?})")?,
                Task::Node(LatticeTerm::Const { name, ty }) => {
                    write!(f, "Const {{ name: {name:?}, ty: {ty:?} }}")?;
                },
                Task::Node(LatticeTerm::App { head, args }) => {
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

impl Drop for LatticeTerm {
    fn drop(&mut self) {
        let root = mem::replace(self, LatticeTerm::Var(String::new()));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    LatticeTerm::Var(name) => drop(ptr::read(name)),
                    LatticeTerm::Const { name, .. } => drop(ptr::read(name)),
                    LatticeTerm::App { head, args } => {
                        drop(ptr::read(head));
                        let args = ptr::read(args);
                        work.extend(args);
                    },
                }
            }
        }
    }
}
