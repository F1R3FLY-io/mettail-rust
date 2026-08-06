use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::{ConstraintTheory, QuantifiedFormula, TheoryPred};

#[derive(Clone, Copy)]
enum FormulaBinary {
    And,
    Or,
    Implies,
}

#[derive(Clone, Copy)]
enum FormulaQuantifier {
    ForAll,
    Exists,
}

impl Clone for QuantifiedFormula {
    fn clone(&self) -> Self {
        enum Task<'formula> {
            Visit(&'formula QuantifiedFormula),
            Binary(FormulaBinary),
            Not,
            Quantifier {
                quantifier: FormulaQuantifier,
                var: String,
                domain: super::QuantifiedDomain,
            },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(QuantifiedFormula::Atom { relation, args }) => {
                    values.push(QuantifiedFormula::Atom {
                        relation: relation.clone(),
                        args: args.clone(),
                    });
                },
                Task::Visit(QuantifiedFormula::And(left, right)) => {
                    tasks.push(Task::Binary(FormulaBinary::And));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(QuantifiedFormula::Or(left, right)) => {
                    tasks.push(Task::Binary(FormulaBinary::Or));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(QuantifiedFormula::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::Visit(QuantifiedFormula::Implies(left, right)) => {
                    tasks.push(Task::Binary(FormulaBinary::Implies));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(QuantifiedFormula::ForAll { var, domain, body }) => {
                    tasks.push(Task::Quantifier {
                        quantifier: FormulaQuantifier::ForAll,
                        var: var.clone(),
                        domain: domain.clone(),
                    });
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(QuantifiedFormula::Exists { var, domain, body }) => {
                    tasks.push(Task::Quantifier {
                        quantifier: FormulaQuantifier::Exists,
                        var: var.clone(),
                        domain: domain.clone(),
                    });
                    tasks.push(Task::Visit(body));
                },
                Task::Binary(binary) => {
                    let right = values
                        .pop()
                        .expect("quantified formula clone PDA lost binary RHS");
                    let left = values
                        .pop()
                        .expect("quantified formula clone PDA lost binary LHS");
                    values.push(match binary {
                        FormulaBinary::And => {
                            QuantifiedFormula::And(Box::new(left), Box::new(right))
                        },
                        FormulaBinary::Or => QuantifiedFormula::Or(Box::new(left), Box::new(right)),
                        FormulaBinary::Implies => {
                            QuantifiedFormula::Implies(Box::new(left), Box::new(right))
                        },
                    });
                },
                Task::Not => {
                    let inner = values
                        .pop()
                        .expect("quantified formula clone PDA lost negand");
                    values.push(QuantifiedFormula::Not(Box::new(inner)));
                },
                Task::Quantifier { quantifier, var, domain } => {
                    let body = values
                        .pop()
                        .expect("quantified formula clone PDA lost quantified body");
                    values.push(match quantifier {
                        FormulaQuantifier::ForAll => {
                            QuantifiedFormula::ForAll { var, domain, body: Box::new(body) }
                        },
                        FormulaQuantifier::Exists => {
                            QuantifiedFormula::Exists { var, domain, body: Box::new(body) }
                        },
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("quantified formula clone PDA produced no value")
    }
}

impl fmt::Debug for QuantifiedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'formula> {
            Visit(&'formula QuantifiedFormula),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Visit(QuantifiedFormula::Atom { relation, args }) => {
                    write!(f, "Atom {{ relation: {relation:?}, args: {args:?} }}")?;
                },
                Task::Visit(
                    formula @ (QuantifiedFormula::And(left, right)
                    | QuantifiedFormula::Or(left, right)
                    | QuantifiedFormula::Implies(left, right)),
                ) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str(match formula {
                        QuantifiedFormula::And(..) => "And(",
                        QuantifiedFormula::Or(..) => "Or(",
                        QuantifiedFormula::Implies(..) => "Implies(",
                        _ => unreachable!("binary pattern contains only binary formulae"),
                    })?;
                },
                Task::Visit(QuantifiedFormula::Not(inner)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(inner));
                    f.write_str("Not(")?;
                },
                Task::Visit(
                    formula @ (QuantifiedFormula::ForAll { var, domain, body }
                    | QuantifiedFormula::Exists { var, domain, body }),
                ) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Visit(body));
                    write!(
                        f,
                        "{} {{ var: {var:?}, domain: {domain:?}, body: ",
                        match formula {
                            QuantifiedFormula::ForAll { .. } => "ForAll",
                            QuantifiedFormula::Exists { .. } => "Exists",
                            _ => unreachable!("quantifier pattern contains only quantifiers"),
                        }
                    )?;
                },
            }
        }
        Ok(())
    }
}

impl fmt::Display for QuantifiedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'formula> {
            Visit(&'formula QuantifiedFormula),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Visit(QuantifiedFormula::Atom { relation, args }) => {
                    write!(f, "{relation}(")?;
                    for (index, arg) in args.iter().enumerate() {
                        if index != 0 {
                            f.write_str(", ")?;
                        }
                        arg.fmt(f)?;
                    }
                    f.write_str(")")?;
                },
                Task::Visit(QuantifiedFormula::And(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(" ∧ "));
                    tasks.push(Task::Visit(left));
                    f.write_str("(")?;
                },
                Task::Visit(QuantifiedFormula::Or(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(" ∨ "));
                    tasks.push(Task::Visit(left));
                    f.write_str("(")?;
                },
                Task::Visit(QuantifiedFormula::Not(inner)) => {
                    tasks.push(Task::Visit(inner));
                    f.write_str("¬")?;
                },
                Task::Visit(QuantifiedFormula::Implies(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(" ⇒ "));
                    tasks.push(Task::Visit(left));
                    f.write_str("(")?;
                },
                Task::Visit(QuantifiedFormula::ForAll { var, domain, body }) => {
                    tasks.push(Task::Visit(body));
                    write!(f, "∀{var} ∈ {domain}. ")?;
                },
                Task::Visit(QuantifiedFormula::Exists { var, domain, body }) => {
                    tasks.push(Task::Visit(body));
                    write!(f, "∃{var} ∈ {domain}. ")?;
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for QuantifiedFormula {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (
                    QuantifiedFormula::Atom { relation: left_relation, args: left_args },
                    QuantifiedFormula::Atom {
                        relation: right_relation,
                        args: right_args,
                    },
                ) if left_relation == right_relation && left_args == right_args => {},
                (QuantifiedFormula::And(a1, b1), QuantifiedFormula::And(a2, b2))
                | (QuantifiedFormula::Or(a1, b1), QuantifiedFormula::Or(a2, b2))
                | (QuantifiedFormula::Implies(a1, b1), QuantifiedFormula::Implies(a2, b2)) => {
                    work.push((b1, b2));
                    work.push((a1, a2));
                },
                (QuantifiedFormula::Not(a), QuantifiedFormula::Not(b)) => work.push((a, b)),
                (
                    QuantifiedFormula::ForAll {
                        var: left_var,
                        domain: left_domain,
                        body: left_body,
                    },
                    QuantifiedFormula::ForAll {
                        var: right_var,
                        domain: right_domain,
                        body: right_body,
                    },
                )
                | (
                    QuantifiedFormula::Exists {
                        var: left_var,
                        domain: left_domain,
                        body: left_body,
                    },
                    QuantifiedFormula::Exists {
                        var: right_var,
                        domain: right_domain,
                        body: right_body,
                    },
                ) => {
                    if left_var != right_var || left_domain != right_domain {
                        return false;
                    }
                    work.push((left_body, right_body));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for QuantifiedFormula {}

impl Drop for QuantifiedFormula {
    fn drop(&mut self) {
        let root = mem::replace(
            self,
            QuantifiedFormula::Atom {
                relation: String::new(),
                args: Vec::new(),
            },
        );
        let mut work = vec![root];
        while let Some(formula) = work.pop() {
            let mut formula = ManuallyDrop::new(formula);
            unsafe {
                match &mut *formula {
                    QuantifiedFormula::Atom { relation, args } => {
                        std::mem::drop(ptr::read(relation));
                        std::mem::drop(ptr::read(args));
                    },
                    QuantifiedFormula::And(left, right)
                    | QuantifiedFormula::Or(left, right)
                    | QuantifiedFormula::Implies(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    QuantifiedFormula::Not(inner) => work.push(*ptr::read(inner)),
                    QuantifiedFormula::ForAll { var, domain, body }
                    | QuantifiedFormula::Exists { var, domain, body } => {
                        std::mem::drop(ptr::read(var));
                        std::mem::drop(ptr::read(domain));
                        work.push(*ptr::read(body));
                    },
                }
            }
        }
    }
}

impl<T: ConstraintTheory> Clone for TheoryPred<T> {
    fn clone(&self) -> Self {
        enum Task<'predicate, T: ConstraintTheory> {
            Visit(&'predicate TheoryPred<T>),
            And,
            Or,
            Not,
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(TheoryPred::True) => values.push(TheoryPred::True),
                Task::Visit(TheoryPred::False) => values.push(TheoryPred::False),
                Task::Visit(TheoryPred::Atom(constraint)) => {
                    values.push(TheoryPred::Atom(constraint.clone()));
                },
                Task::Visit(TheoryPred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(TheoryPred::Not(inner)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(inner));
                },
                Task::And | Task::Or => {
                    let right = values
                        .pop()
                        .expect("theory predicate clone PDA lost binary RHS");
                    let left = values
                        .pop()
                        .expect("theory predicate clone PDA lost binary LHS");
                    values.push(match task {
                        Task::And => TheoryPred::And(Box::new(left), Box::new(right)),
                        Task::Or => TheoryPred::Or(Box::new(left), Box::new(right)),
                        _ => unreachable!("binary reducer receives only And or Or"),
                    });
                },
                Task::Not => {
                    let inner = values
                        .pop()
                        .expect("theory predicate clone PDA lost negand");
                    values.push(TheoryPred::Not(Box::new(inner)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("theory predicate clone PDA produced no value")
    }
}

impl<T: ConstraintTheory> fmt::Debug for TheoryPred<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'predicate, T: ConstraintTheory> {
            Visit(&'predicate TheoryPred<T>),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Visit(TheoryPred::True) => f.write_str("True")?,
                Task::Visit(TheoryPred::False) => f.write_str("False")?,
                Task::Visit(TheoryPred::Atom(constraint)) => {
                    f.write_str("Atom(")?;
                    constraint.fmt(f)?;
                    f.write_str(")")?;
                },
                Task::Visit(TheoryPred::And(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("And(")?;
                },
                Task::Visit(TheoryPred::Or(left, right)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Visit(left));
                    f.write_str("Or(")?;
                },
                Task::Visit(TheoryPred::Not(inner)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Visit(inner));
                    f.write_str("Not(")?;
                },
            }
        }
        Ok(())
    }
}

impl<T: ConstraintTheory> PartialEq for TheoryPred<T> {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TheoryPred::True, TheoryPred::True) | (TheoryPred::False, TheoryPred::False) => {},
                (TheoryPred::Atom(a), TheoryPred::Atom(b)) if a == b => {},
                (TheoryPred::And(a1, b1), TheoryPred::And(a2, b2))
                | (TheoryPred::Or(a1, b1), TheoryPred::Or(a2, b2)) => {
                    work.push((b1, b2));
                    work.push((a1, a2));
                },
                (TheoryPred::Not(a), TheoryPred::Not(b)) => work.push((a, b)),
                _ => return false,
            }
        }
        true
    }
}

impl<T: ConstraintTheory> Eq for TheoryPred<T> {}

impl<T: ConstraintTheory> Hash for TheoryPred<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(predicate) = work.pop() {
            mem::discriminant(predicate).hash(state);
            match predicate {
                TheoryPred::True | TheoryPred::False => {},
                TheoryPred::Atom(constraint) => constraint.hash(state),
                TheoryPred::And(left, right) | TheoryPred::Or(left, right) => {
                    work.push(right);
                    work.push(left);
                },
                TheoryPred::Not(inner) => work.push(inner),
            }
        }
    }
}

impl<T: ConstraintTheory> Drop for TheoryPred<T> {
    fn drop(&mut self) {
        let root = mem::replace(self, TheoryPred::False);
        let mut work = vec![root];
        while let Some(predicate) = work.pop() {
            let mut predicate = ManuallyDrop::new(predicate);
            unsafe {
                match &mut *predicate {
                    TheoryPred::True | TheoryPred::False => {},
                    TheoryPred::Atom(constraint) => std::mem::drop(ptr::read(constraint)),
                    TheoryPred::And(left, right) | TheoryPred::Or(left, right) => {
                        work.push(*ptr::read(left));
                        work.push(*ptr::read(right));
                    },
                    TheoryPred::Not(inner) => work.push(*ptr::read(inner)),
                }
            }
        }
    }
}
