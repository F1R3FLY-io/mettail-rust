use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::{HmTerm, HmType};

impl Clone for HmType {
    fn clone(&self) -> Self {
        enum Task<'ty> {
            Visit(&'ty HmType),
            Arrow,
            Forall(Vec<String>),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(HmType::Var(name)) => values.push(HmType::Var(name.clone())),
                Task::Visit(HmType::Mono(name)) => values.push(HmType::Mono(name.clone())),
                Task::Visit(HmType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Arrow);
                    tasks.push(Task::Visit(codomain));
                    tasks.push(Task::Visit(domain));
                },
                Task::Visit(HmType::Forall(vars, body)) => {
                    tasks.push(Task::Forall(vars.clone()));
                    tasks.push(Task::Visit(body));
                },
                Task::Arrow => {
                    let codomain = values.pop().expect("HM type clone PDA lost arrow codomain");
                    let domain = values.pop().expect("HM type clone PDA lost arrow domain");
                    values.push(HmType::Arrow(Box::new(domain), Box::new(codomain)));
                },
                Task::Forall(vars) => {
                    let body = values.pop().expect("HM type clone PDA lost forall body");
                    values.push(HmType::Forall(vars, Box::new(body)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("HM type clone PDA produced no value")
    }
}

impl fmt::Debug for HmType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'ty> {
            Node(&'ty HmType),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(HmType::Var(name)) => write!(f, "Var({name:?})")?,
                Task::Node(HmType::Mono(name)) => write!(f, "Mono({name:?})")?,
                Task::Node(HmType::Arrow(domain, codomain)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(codomain));
                    tasks.push(Task::Text(", "));
                    tasks.push(Task::Node(domain));
                    f.write_str("Arrow(")?;
                },
                Task::Node(HmType::Forall(vars, body)) => {
                    tasks.push(Task::Text(")"));
                    tasks.push(Task::Node(body));
                    write!(f, "Forall({vars:?}, ")?;
                },
            }
        }
        Ok(())
    }
}

impl fmt::Display for HmType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'ty> {
            Node(&'ty HmType, bool),
            Text(&'static str),
            Vars(&'ty [String]),
        }

        let mut tasks = vec![Task::Node(self, false)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Vars(vars) => f.write_str(&vars.join(" "))?,
                Task::Node(HmType::Var(name) | HmType::Mono(name), _) => f.write_str(name)?,
                Task::Node(HmType::Arrow(domain, codomain), parenthesize) => {
                    if parenthesize {
                        tasks.push(Task::Text(")"));
                    }
                    tasks.push(Task::Node(codomain, false));
                    tasks.push(Task::Text(" → "));
                    tasks.push(Task::Node(domain, matches!(domain.as_ref(), HmType::Arrow(..))));
                    if parenthesize {
                        f.write_str("(")?;
                    }
                },
                Task::Node(HmType::Forall(vars, body), _) => {
                    tasks.push(Task::Node(body, false));
                    tasks.push(Task::Text(". "));
                    tasks.push(Task::Vars(vars));
                    f.write_str("∀")?;
                },
            }
        }
        Ok(())
    }
}

impl PartialEq for HmType {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (HmType::Var(a), HmType::Var(b)) | (HmType::Mono(a), HmType::Mono(b)) => {
                    if a != b {
                        return false;
                    }
                },
                (HmType::Arrow(a1, b1), HmType::Arrow(a2, b2)) => {
                    work.push((b1, b2));
                    work.push((a1, a2));
                },
                (HmType::Forall(vars1, body1), HmType::Forall(vars2, body2)) => {
                    if vars1 != vars2 {
                        return false;
                    }
                    work.push((body1, body2));
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for HmType {}

impl Hash for HmType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut work = vec![self];
        while let Some(node) = work.pop() {
            mem::discriminant(node).hash(state);
            match node {
                HmType::Var(name) | HmType::Mono(name) => name.hash(state),
                HmType::Arrow(domain, codomain) => {
                    work.push(codomain);
                    work.push(domain);
                },
                HmType::Forall(vars, body) => {
                    vars.hash(state);
                    work.push(body);
                },
            }
        }
    }
}

impl Drop for HmType {
    fn drop(&mut self) {
        let root = mem::replace(self, HmType::Mono(String::new()));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    HmType::Var(name) | HmType::Mono(name) => drop(ptr::read(name)),
                    HmType::Arrow(domain, codomain) => {
                        work.push(*ptr::read(domain));
                        work.push(*ptr::read(codomain));
                    },
                    HmType::Forall(vars, body) => {
                        drop(ptr::read(vars));
                        work.push(*ptr::read(body));
                    },
                }
            }
        }
    }
}

impl Clone for HmTerm {
    fn clone(&self) -> Self {
        enum Task<'term> {
            Visit(&'term HmTerm),
            Abs(String),
            App,
            Let(String),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(HmTerm::Var(name)) => values.push(HmTerm::Var(name.clone())),
                Task::Visit(HmTerm::Abs { param, body }) => {
                    tasks.push(Task::Abs(param.clone()));
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(HmTerm::App { f, arg }) => {
                    tasks.push(Task::App);
                    tasks.push(Task::Visit(arg));
                    tasks.push(Task::Visit(f));
                },
                Task::Visit(HmTerm::Let { name, value, body }) => {
                    tasks.push(Task::Let(name.clone()));
                    tasks.push(Task::Visit(body));
                    tasks.push(Task::Visit(value));
                },
                Task::Visit(HmTerm::LitInt(value)) => values.push(HmTerm::LitInt(*value)),
                Task::Visit(HmTerm::LitBool(value)) => values.push(HmTerm::LitBool(*value)),
                Task::Visit(HmTerm::LitStr(value)) => values.push(HmTerm::LitStr(value.clone())),
                Task::Abs(param) => {
                    let body = values
                        .pop()
                        .expect("HM term clone PDA lost abstraction body");
                    values.push(HmTerm::Abs { param, body: Box::new(body) });
                },
                Task::App => {
                    let arg = values
                        .pop()
                        .expect("HM term clone PDA lost application argument");
                    let function = values
                        .pop()
                        .expect("HM term clone PDA lost application function");
                    values.push(HmTerm::App {
                        f: Box::new(function),
                        arg: Box::new(arg),
                    });
                },
                Task::Let(name) => {
                    let body = values.pop().expect("HM term clone PDA lost let body");
                    let value = values.pop().expect("HM term clone PDA lost let value");
                    values.push(HmTerm::Let {
                        name,
                        value: Box::new(value),
                        body: Box::new(body),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("HM term clone PDA produced no value")
    }
}

impl fmt::Debug for HmTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'term> {
            Node(&'term HmTerm),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::Node(HmTerm::Var(name)) => write!(f, "Var({name:?})")?,
                Task::Node(HmTerm::Abs { param, body }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Node(body));
                    write!(f, "Abs {{ param: {param:?}, body: ")?;
                },
                Task::Node(HmTerm::App { f: function, arg }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Node(arg));
                    tasks.push(Task::Text(", arg: "));
                    tasks.push(Task::Node(function));
                    f.write_str("App { f: ")?;
                },
                Task::Node(HmTerm::Let { name, value, body }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Node(body));
                    tasks.push(Task::Text(", body: "));
                    tasks.push(Task::Node(value));
                    write!(f, "Let {{ name: {name:?}, value: ")?;
                },
                Task::Node(HmTerm::LitInt(value)) => write!(f, "LitInt({value:?})")?,
                Task::Node(HmTerm::LitBool(value)) => write!(f, "LitBool({value:?})")?,
                Task::Node(HmTerm::LitStr(value)) => write!(f, "LitStr({value:?})")?,
            }
        }
        Ok(())
    }
}

impl PartialEq for HmTerm {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (HmTerm::Var(a), HmTerm::Var(b)) | (HmTerm::LitStr(a), HmTerm::LitStr(b)) => {
                    if a != b {
                        return false;
                    }
                },
                (
                    HmTerm::Abs { param: param1, body: body1 },
                    HmTerm::Abs { param: param2, body: body2 },
                ) => {
                    if param1 != param2 {
                        return false;
                    }
                    work.push((body1, body2));
                },
                (HmTerm::App { f: f1, arg: arg1 }, HmTerm::App { f: f2, arg: arg2 }) => {
                    work.push((arg1, arg2));
                    work.push((f1, f2));
                },
                (
                    HmTerm::Let { name: name1, value: value1, body: body1 },
                    HmTerm::Let { name: name2, value: value2, body: body2 },
                ) => {
                    if name1 != name2 {
                        return false;
                    }
                    work.push((body1, body2));
                    work.push((value1, value2));
                },
                (HmTerm::LitInt(a), HmTerm::LitInt(b)) if a == b => {},
                (HmTerm::LitBool(a), HmTerm::LitBool(b)) if a == b => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for HmTerm {}

impl Drop for HmTerm {
    fn drop(&mut self) {
        let root = mem::replace(self, HmTerm::LitBool(false));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    HmTerm::Var(name) | HmTerm::LitStr(name) => drop(ptr::read(name)),
                    HmTerm::Abs { param, body } => {
                        drop(ptr::read(param));
                        work.push(*ptr::read(body));
                    },
                    HmTerm::App { f: function, arg } => {
                        work.push(*ptr::read(function));
                        work.push(*ptr::read(arg));
                    },
                    HmTerm::Let { name, value, body } => {
                        drop(ptr::read(name));
                        work.push(*ptr::read(value));
                        work.push(*ptr::read(body));
                    },
                    HmTerm::LitInt(_) | HmTerm::LitBool(_) => {},
                }
            }
        }
    }
}
