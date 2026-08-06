use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::{SmtConstraint, SmtTerm};

impl Clone for SmtTerm {
    fn clone(&self) -> Self {
        enum Task<'term> {
            Visit(&'term SmtTerm),
            Add,
            Sub,
            Scale(i64),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SmtTerm::IntLit(value)) => values.push(SmtTerm::IntLit(*value)),
                Task::Visit(SmtTerm::IntVar(name)) => values.push(SmtTerm::IntVar(name.clone())),
                Task::Visit(SmtTerm::BvLit(value, width)) => {
                    values.push(SmtTerm::BvLit(*value, *width));
                },
                Task::Visit(SmtTerm::BvVar(name, width)) => {
                    values.push(SmtTerm::BvVar(name.clone(), *width));
                },
                Task::Visit(SmtTerm::Add(left, right)) => {
                    tasks.push(Task::Add);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtTerm::Sub(left, right)) => {
                    tasks.push(Task::Sub);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtTerm::Scale(coefficient, term)) => {
                    tasks.push(Task::Scale(*coefficient));
                    tasks.push(Task::Visit(term));
                },
                Task::Add | Task::Sub => {
                    let right = values.pop().expect("SMT term clone PDA lost binary RHS");
                    let left = values.pop().expect("SMT term clone PDA lost binary LHS");
                    values.push(match task {
                        Task::Add => SmtTerm::Add(Box::new(left), Box::new(right)),
                        Task::Sub => SmtTerm::Sub(Box::new(left), Box::new(right)),
                        _ => unreachable!("binary reducer receives only Add or Sub"),
                    });
                },
                Task::Scale(coefficient) => {
                    let term = values.pop().expect("SMT term clone PDA lost scale operand");
                    values.push(SmtTerm::Scale(coefficient, Box::new(term)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("SMT term clone PDA produced no value")
    }
}

impl fmt::Debug for SmtTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Visit(&'term SmtTerm),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Visit(SmtTerm::IntLit(value)) => write!(f, "IntLit({value:?})")?,
                Task::Visit(SmtTerm::IntVar(name)) => write!(f, "IntVar({name:?})")?,
                Task::Visit(SmtTerm::BvLit(value, width)) => {
                    write!(f, "BvLit({value:?}, {width:?})")?;
                },
                Task::Visit(SmtTerm::BvVar(name, width)) => {
                    write!(f, "BvVar({name:?}, {width:?})")?;
                },
                Task::Visit(SmtTerm::Add(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("Add(")?;
                },
                Task::Visit(SmtTerm::Sub(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("Sub(")?;
                },
                Task::Visit(SmtTerm::Scale(coefficient, term)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(term));
                    write!(f, "Scale({coefficient:?}, ")?;
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for SmtTerm {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (SmtTerm::IntLit(a), SmtTerm::IntLit(b)) if a == b => {},
                (SmtTerm::IntVar(a), SmtTerm::IntVar(b)) if a == b => {},
                (SmtTerm::BvLit(a_value, a_width), SmtTerm::BvLit(b_value, b_width))
                    if a_value == b_value && a_width == b_width => {},
                (SmtTerm::BvVar(a_name, a_width), SmtTerm::BvVar(b_name, b_width))
                    if a_name == b_name && a_width == b_width => {},
                (SmtTerm::Add(a_left, a_right), SmtTerm::Add(b_left, b_right))
                | (SmtTerm::Sub(a_left, a_right), SmtTerm::Sub(b_left, b_right)) => {
                    work.push((a_right, b_right));
                    work.push((a_left, b_left));
                },
                (SmtTerm::Scale(a_coefficient, a_term), SmtTerm::Scale(b_coefficient, b_term)) => {
                    if a_coefficient != b_coefficient {
                        return false;
                    }
                    work.push((a_term, b_term));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SmtTerm {}

impl Hash for SmtTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(term) = work.pop() {
            mem::discriminant(term).hash(state);
            match term {
                SmtTerm::IntLit(value) => value.hash(state),
                SmtTerm::IntVar(name) => name.hash(state),
                SmtTerm::BvLit(value, width) => {
                    value.hash(state);
                    width.hash(state);
                },
                SmtTerm::BvVar(name, width) => {
                    name.hash(state);
                    width.hash(state);
                },
                SmtTerm::Add(left, right) | SmtTerm::Sub(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                SmtTerm::Scale(coefficient, term) => {
                    coefficient.hash(state);
                    work.push(term);
                },
            }
        }
    }
}

impl Drop for SmtTerm {
    fn drop(&mut self) {
        let root = mem::replace(self, SmtTerm::IntLit(0));
        let mut work = vec![root];
        while let Some(term) = work.pop() {
            let mut term = ManuallyDrop::new(term);
            unsafe {
                match &mut *term {
                    SmtTerm::IntLit(_) | SmtTerm::BvLit(_, _) => {},
                    SmtTerm::IntVar(name) => drop(ptr::read(name)),
                    SmtTerm::BvVar(name, _) => drop(ptr::read(name)),
                    SmtTerm::Add(left, right) | SmtTerm::Sub(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    SmtTerm::Scale(_, inner) => work.push(*ptr::read(inner)),
                }
            }
        }
    }
}

impl Clone for SmtConstraint {
    fn clone(&self) -> Self {
        enum Task<'constraint> {
            Visit(&'constraint SmtConstraint),
            Not,
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SmtConstraint::True) => values.push(SmtConstraint::True),
                Task::Visit(SmtConstraint::False) => values.push(SmtConstraint::False),
                Task::Visit(SmtConstraint::BoolVar(name)) => {
                    values.push(SmtConstraint::BoolVar(name.clone()));
                },
                Task::Visit(SmtConstraint::Eq(left, right)) => {
                    values.push(SmtConstraint::Eq(left.clone(), right.clone()));
                },
                Task::Visit(SmtConstraint::Le(left, right)) => {
                    values.push(SmtConstraint::Le(left.clone(), right.clone()));
                },
                Task::Visit(SmtConstraint::Lt(left, right)) => {
                    values.push(SmtConstraint::Lt(left.clone(), right.clone()));
                },
                Task::Visit(SmtConstraint::Ge(left, right)) => {
                    values.push(SmtConstraint::Ge(left.clone(), right.clone()));
                },
                Task::Visit(SmtConstraint::Gt(left, right)) => {
                    values.push(SmtConstraint::Gt(left.clone(), right.clone()));
                },
                Task::Visit(SmtConstraint::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(SmtConstraint::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SmtConstraint::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Not => {
                    let inner = values.pop().expect("SMT constraint clone PDA lost negand");
                    values.push(SmtConstraint::Not(Box::new(inner)));
                },
                Task::And | Task::Or => {
                    let right = values
                        .pop()
                        .expect("SMT constraint clone PDA lost binary RHS");
                    let left = values
                        .pop()
                        .expect("SMT constraint clone PDA lost binary LHS");
                    values.push(match task {
                        Task::And => SmtConstraint::And(Box::new(left), Box::new(right)),
                        Task::Or => SmtConstraint::Or(Box::new(left), Box::new(right)),
                        _ => unreachable!("binary reducer receives only And or Or"),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("SMT constraint clone PDA produced no value")
    }
}

impl fmt::Debug for SmtConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'constraint> {
            Visit(&'constraint SmtConstraint),
            Term(&'constraint SmtTerm),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Term(term) => term.fmt(f)?,
                Task::Visit(SmtConstraint::True) => f.write_str("True")?,
                Task::Visit(SmtConstraint::False) => f.write_str("False")?,
                Task::Visit(SmtConstraint::BoolVar(name)) => write!(f, "BoolVar({name:?})")?,
                Task::Visit(
                    constraint @ (SmtConstraint::Eq(left, right)
                    | SmtConstraint::Le(left, right)
                    | SmtConstraint::Lt(left, right)
                    | SmtConstraint::Ge(left, right)
                    | SmtConstraint::Gt(left, right)),
                ) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Term(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Term(left));
                    f.write_str(match constraint {
                        SmtConstraint::Eq(..) => "Eq(",
                        SmtConstraint::Le(..) => "Le(",
                        SmtConstraint::Lt(..) => "Lt(",
                        SmtConstraint::Ge(..) => "Ge(",
                        SmtConstraint::Gt(..) => "Gt(",
                        _ => unreachable!("comparison pattern contains only comparisons"),
                    })?;
                },
                Task::Visit(SmtConstraint::Not(inner)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(inner));
                    f.write_str("Not(")?;
                },
                Task::Visit(SmtConstraint::And(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("And(")?;
                },
                Task::Visit(SmtConstraint::Or(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("Or(")?;
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for SmtConstraint {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (SmtConstraint::True, SmtConstraint::True)
                | (SmtConstraint::False, SmtConstraint::False) => {},
                (SmtConstraint::BoolVar(a), SmtConstraint::BoolVar(b)) if a == b => {},
                (SmtConstraint::Eq(a1, b1), SmtConstraint::Eq(a2, b2))
                | (SmtConstraint::Le(a1, b1), SmtConstraint::Le(a2, b2))
                | (SmtConstraint::Lt(a1, b1), SmtConstraint::Lt(a2, b2))
                | (SmtConstraint::Ge(a1, b1), SmtConstraint::Ge(a2, b2))
                | (SmtConstraint::Gt(a1, b1), SmtConstraint::Gt(a2, b2))
                    if a1 == a2 && b1 == b2 => {},
                (SmtConstraint::Not(a), SmtConstraint::Not(b)) => work.push((a, b)),
                (SmtConstraint::And(a1, b1), SmtConstraint::And(a2, b2))
                | (SmtConstraint::Or(a1, b1), SmtConstraint::Or(a2, b2)) => {
                    work.push((b1, b2));
                    work.push((a1, a2));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for SmtConstraint {}

impl Hash for SmtConstraint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(constraint) = work.pop() {
            mem::discriminant(constraint).hash(state);
            match constraint {
                SmtConstraint::True | SmtConstraint::False => {},
                SmtConstraint::BoolVar(name) => name.hash(state),
                SmtConstraint::Eq(left, right)
                | SmtConstraint::Le(left, right)
                | SmtConstraint::Lt(left, right)
                | SmtConstraint::Ge(left, right)
                | SmtConstraint::Gt(left, right) => {
                    left.hash(state);
                    right.hash(state);
                },
                SmtConstraint::Not(inner) => work.push(inner),
                SmtConstraint::And(left, right) | SmtConstraint::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
            }
        }
    }
}

impl Drop for SmtConstraint {
    fn drop(&mut self) {
        let root = mem::replace(self, SmtConstraint::False);
        let mut work = vec![root];
        while let Some(constraint) = work.pop() {
            let mut constraint = ManuallyDrop::new(constraint);
            unsafe {
                match &mut *constraint {
                    SmtConstraint::True | SmtConstraint::False => {},
                    SmtConstraint::BoolVar(name) => drop(ptr::read(name)),
                    SmtConstraint::Eq(left, right)
                    | SmtConstraint::Le(left, right)
                    | SmtConstraint::Lt(left, right)
                    | SmtConstraint::Ge(left, right)
                    | SmtConstraint::Gt(left, right) => {
                        drop(ptr::read(left));
                        drop(ptr::read(right));
                    },
                    SmtConstraint::Not(inner) => work.push(*ptr::read(inner)),
                    SmtConstraint::And(left, right) | SmtConstraint::Or(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                }
            }
        }
    }
}
