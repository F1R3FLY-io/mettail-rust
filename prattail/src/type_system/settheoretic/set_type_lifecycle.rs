use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::SetType;

impl Clone for SetType {
    fn clone(&self) -> Self {
        enum Task<'ty> {
            Visit(&'ty SetType),
            Union,
            Intersection,
            Negation,
            Arrow,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SetType::Atom(name)) => values.push(SetType::Atom(name.clone())),
                Task::Visit(SetType::Union(left, right)) => {
                    tasks.push(Task::Union);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SetType::Intersection(left, right)) => {
                    tasks.push(Task::Intersection);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SetType::Negation(inner)) => {
                    tasks.push(Task::Negation);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(SetType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Arrow);
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(SetType::Top) => values.push(SetType::Top),
                Task::Visit(SetType::Bottom) => values.push(SetType::Bottom),
                Task::Union | Task::Intersection | Task::Arrow => {
                    let right = values
                        .pop()
                        .expect("set-type clone PDA lost its right child");
                    let left = values
                        .pop()
                        .expect("set-type clone PDA lost its left child");
                    values.push(match task {
                        Task::Union => SetType::Union(Box::new(left), Box::new(right)),
                        Task::Intersection => {
                            SetType::Intersection(Box::new(left), Box::new(right))
                        },
                        Task::Arrow => SetType::Arrow(Box::new(left), Box::new(right)),
                        Task::Visit(_) | Task::Negation => unreachable!(),
                    });
                },
                Task::Negation => {
                    let inner = values
                        .pop()
                        .expect("set-type clone PDA lost its negated child");
                    values.push(SetType::Negation(Box::new(inner)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("set-type clone PDA produced no value")
    }
}

impl PartialEq for SetType {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (SetType::Atom(a), SetType::Atom(b)) if a == b => {},
                (SetType::Union(al, ar), SetType::Union(bl, br))
                | (SetType::Intersection(al, ar), SetType::Intersection(bl, br))
                | (SetType::Arrow(al, ar), SetType::Arrow(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (SetType::Negation(a), SetType::Negation(b)) => work.push((a, b)),
                (SetType::Top, SetType::Top) | (SetType::Bottom, SetType::Bottom) => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SetType {}

impl Hash for SetType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                SetType::Atom(name) => name.hash(state),
                SetType::Union(left, right)
                | SetType::Intersection(left, right)
                | SetType::Arrow(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                SetType::Negation(inner) => work.push(inner),
                SetType::Top | SetType::Bottom => {},
            }
        }
    }
}

impl fmt::Debug for SetType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => f.write_str(text)?,
                DebugTask::Node(SetType::Atom(name)) => write!(f, "Atom({name:?})")?,
                DebugTask::Node(SetType::Union(left, right)) => {
                    push_binary_debug(&mut tasks, "Union(", left, right);
                },
                DebugTask::Node(SetType::Intersection(left, right)) => {
                    push_binary_debug(&mut tasks, "Intersection(", left, right);
                },
                DebugTask::Node(SetType::Negation(inner)) => {
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Node(inner));
                    tasks.push(DebugTask::Text("Negation("));
                },
                DebugTask::Node(SetType::Arrow(domain, codomain)) => {
                    push_binary_debug(&mut tasks, "Arrow(", domain, codomain);
                },
                DebugTask::Node(SetType::Top) => f.write_str("Top")?,
                DebugTask::Node(SetType::Bottom) => f.write_str("Bottom")?,
            }
        }
        Ok(())
    }
}

fn push_binary_debug<'ty>(
    tasks: &mut Vec<DebugTask<'ty>>,
    open: &'static str,
    left: &'ty SetType,
    right: &'ty SetType,
) {
    tasks.push(DebugTask::Text(")"));
    tasks.push(DebugTask::Node(right));
    tasks.push(DebugTask::Text(", "));
    tasks.push(DebugTask::Node(left));
    tasks.push(DebugTask::Text(open));
}

enum DebugTask<'ty> {
    Node(&'ty SetType),
    Text(&'static str),
}

impl fmt::Display for SetType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'ty> {
            Node(&'ty SetType),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(SetType::Atom(name)) => f.write_str(name)?,
                Task::Node(SetType::Union(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(" | "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("("));
                },
                Task::Node(SetType::Intersection(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(" & "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("("));
                },
                Task::Node(SetType::Negation(inner)) => {
                    tasks.push(Task::Node(inner));
                    tasks.push(Task::Text("~"));
                },
                Task::Node(SetType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(codomain));
                    tasks.push(Task::Text(" -> "));
                    tasks.push(Task::Node(domain));
                    tasks.push(Task::Text("("));
                },
                Task::Node(SetType::Top) => f.write_str("Top")?,
                Task::Node(SetType::Bottom) => f.write_str("Bottom")?,
            }
        }
        Ok(())
    }
}

impl Drop for SetType {
    fn drop(&mut self) {
        let root = mem::replace(self, SetType::Top);
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    SetType::Atom(name) => drop(ptr::read(name)),
                    SetType::Union(left, right)
                    | SetType::Intersection(left, right)
                    | SetType::Arrow(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    SetType::Negation(inner) => work.push(*ptr::read(inner)),
                    SetType::Top | SetType::Bottom => {},
                }
            }
        }
    }
}
