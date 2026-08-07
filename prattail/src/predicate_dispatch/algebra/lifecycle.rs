use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::SignaturePred;

impl Clone for SignaturePred {
    fn clone(&self) -> Self {
        enum Task<'pred> {
            Visit(&'pred SignaturePred),
            Binary(Binary),
            Not,
        }

        enum Binary {
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SignaturePred::True) => values.push(SignaturePred::True),
                Task::Visit(SignaturePred::False) => values.push(SignaturePred::False),
                Task::Visit(SignaturePred::HasBit(bit)) => {
                    values.push(SignaturePred::HasBit(*bit));
                },
                Task::Visit(SignaturePred::And(left, right)) => {
                    tasks.push(Task::Binary(Binary::And));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SignaturePred::Or(left, right)) => {
                    tasks.push(Task::Binary(Binary::Or));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SignaturePred::Not(body)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(body));
                },
                Task::Binary(binary) => {
                    let right = values
                        .pop()
                        .expect("signature predicate clone lost its right child");
                    let left = values
                        .pop()
                        .expect("signature predicate clone lost its left child");
                    values.push(match binary {
                        Binary::And => SignaturePred::And(Box::new(left), Box::new(right)),
                        Binary::Or => SignaturePred::Or(Box::new(left), Box::new(right)),
                    });
                },
                Task::Not => {
                    let body = values
                        .pop()
                        .expect("signature predicate clone lost its negated child");
                    values.push(SignaturePred::Not(Box::new(body)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("signature predicate clone produced no value")
    }
}

impl PartialEq for SignaturePred {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (SignaturePred::True, SignaturePred::True)
                | (SignaturePred::False, SignaturePred::False) => {},
                (SignaturePred::HasBit(a), SignaturePred::HasBit(b)) if a == b => {},
                (SignaturePred::And(al, ar), SignaturePred::And(bl, br))
                | (SignaturePred::Or(al, ar), SignaturePred::Or(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (SignaturePred::Not(a), SignaturePred::Not(b)) => work.push((a, b)),
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SignaturePred {}

impl Hash for SignaturePred {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                SignaturePred::HasBit(bit) => bit.hash(state),
                SignaturePred::And(left, right) | SignaturePred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                SignaturePred::Not(body) => work.push(body),
                SignaturePred::True | SignaturePred::False => {},
            }
        }
    }
}

impl fmt::Debug for SignaturePred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'pred> {
            Node(&'pred SignaturePred),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(SignaturePred::True) => f.write_str("True")?,
                Task::Node(SignaturePred::False) => f.write_str("False")?,
                Task::Node(SignaturePred::HasBit(bit)) => {
                    write!(f, "HasBit({bit:?})")?;
                },
                Task::Node(SignaturePred::And(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("And("));
                },
                Task::Node(SignaturePred::Or(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Node(left));
                    tasks.push(Task::Text("Or("));
                },
                Task::Node(SignaturePred::Not(body)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(body));
                    tasks.push(Task::Text("Not("));
                },
            }
        }
        Ok(())
    }
}

impl Drop for SignaturePred {
    fn drop(&mut self) {
        let root = mem::replace(self, SignaturePred::True);
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    SignaturePred::And(left, right) | SignaturePred::Or(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    SignaturePred::Not(body) => work.push(*ptr::read(body)),
                    SignaturePred::True | SignaturePred::False | SignaturePred::HasBit(_) => {},
                }
            }
        }
    }
}
