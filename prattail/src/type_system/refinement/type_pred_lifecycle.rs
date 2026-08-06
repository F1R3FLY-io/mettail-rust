use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::{TypePred, TypeSystem};

impl<S: TypeSystem> Clone for TypePred<S> {
    fn clone(&self) -> Self {
        enum Task<'pred, S: TypeSystem> {
            Visit(&'pred TypePred<S>),
            And,
            Or,
            Not,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TypePred::True) => values.push(TypePred::True),
                Task::Visit(TypePred::False) => values.push(TypePred::False),
                Task::Visit(TypePred::HasType(ty)) => {
                    values.push(TypePred::HasType(ty.clone()));
                },
                Task::Visit(TypePred::Subtype { sub, sup }) => {
                    values.push(TypePred::Subtype { sub: sub.clone(), sup: sup.clone() });
                },
                Task::Visit(TypePred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TypePred::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::And | Task::Or => {
                    let right = values
                        .pop()
                        .expect("type-predicate clone PDA lost its right child");
                    let left = values
                        .pop()
                        .expect("type-predicate clone PDA lost its left child");
                    values.push(match task {
                        Task::And => TypePred::And(Box::new(left), Box::new(right)),
                        Task::Or => TypePred::Or(Box::new(left), Box::new(right)),
                        Task::Visit(_) | Task::Not => unreachable!(),
                    });
                },
                Task::Not => {
                    let inner = values
                        .pop()
                        .expect("type-predicate clone PDA lost its negated child");
                    values.push(TypePred::Not(Box::new(inner)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("type-predicate clone PDA produced no value")
    }
}

impl<S: TypeSystem> PartialEq for TypePred<S> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TypePred::True, TypePred::True) | (TypePred::False, TypePred::False) => {},
                (TypePred::HasType(a), TypePred::HasType(b)) if a == b => {},
                (
                    TypePred::Subtype { sub: asub, sup: asup },
                    TypePred::Subtype { sub: bsub, sup: bsup },
                ) if asub == bsub && asup == bsup => {},
                (TypePred::And(al, ar), TypePred::And(bl, br))
                | (TypePred::Or(al, ar), TypePred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (TypePred::Not(a), TypePred::Not(b)) => work.push((a, b)),
                _ => return false,
            }
        }
        true
    }
}

impl<S: TypeSystem> Eq for TypePred<S> {}

impl<S: TypeSystem> Hash for TypePred<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                TypePred::True | TypePred::False => {},
                TypePred::HasType(ty) => ty.hash(state),
                TypePred::Subtype { sub, sup } => {
                    sub.hash(state);
                    sup.hash(state);
                },
                TypePred::And(left, right) | TypePred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                TypePred::Not(inner) => work.push(inner),
            }
        }
    }
}

impl<S: TypeSystem> fmt::Debug for TypePred<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'pred, S: TypeSystem> {
            Node(&'pred TypePred<S>),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(TypePred::True) => f.write_str("True")?,
                Task::Node(TypePred::False) => f.write_str("False")?,
                Task::Node(TypePred::HasType(ty)) => write!(f, "HasType({ty:?})")?,
                Task::Node(TypePred::Subtype { sub, sup }) => {
                    write!(f, "Subtype {{ sub: {sub:?}, sup: {sup:?} }}")?;
                },
                Task::Node(TypePred::And(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("And("));
                },
                Task::Node(TypePred::Or(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("Or("));
                },
                Task::Node(TypePred::Not(inner)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(inner));
                    tasks.push(Task::Text("Not("));
                },
            }
        }
        Ok(())
    }
}

impl<S: TypeSystem> Drop for TypePred<S> {
    fn drop(&mut self) {
        let root = mem::replace(self, TypePred::True);
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    TypePred::True | TypePred::False => {},
                    TypePred::HasType(ty) => drop(ptr::read(ty)),
                    TypePred::Subtype { sub, sup } => {
                        drop(ptr::read(sub));
                        drop(ptr::read(sup));
                    },
                    TypePred::And(left, right) | TypePred::Or(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    TypePred::Not(inner) => work.push(*ptr::read(inner)),
                }
            }
        }
    }
}
