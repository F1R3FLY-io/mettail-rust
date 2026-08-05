//! Stack-safe lifecycle and rendering for recursive inferred term types.

use super::TermType;
use std::fmt;

enum CloneTask<'ty> {
    Visit(&'ty TermType),
    Arrow(usize),
    MultiArrow(usize),
    Ambiguous { base: usize, len: usize },
}

impl Clone for TermType {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(TermType::Base(name)) => {
                    values.push(TermType::Base(name.clone()));
                },
                CloneTask::Visit(TermType::Unknown) => values.push(TermType::Unknown),
                CloneTask::Visit(TermType::Arrow(domain, codomain)) => {
                    let base = values.len();
                    tasks.push(CloneTask::Arrow(base));
                    tasks.push(CloneTask::Visit(codomain));
                    tasks.push(CloneTask::Visit(domain));
                },
                CloneTask::Visit(TermType::MultiArrow(domain, codomain)) => {
                    let base = values.len();
                    tasks.push(CloneTask::MultiArrow(base));
                    tasks.push(CloneTask::Visit(codomain));
                    tasks.push(CloneTask::Visit(domain));
                },
                CloneTask::Visit(TermType::Ambiguous(types)) => {
                    let base = values.len();
                    tasks.push(CloneTask::Ambiguous { base, len: types.len() });
                    for ty in types.iter().rev() {
                        tasks.push(CloneTask::Visit(ty));
                    }
                },
                CloneTask::Arrow(base) => finish_binary(&mut values, base, TermType::Arrow),
                CloneTask::MultiArrow(base) => {
                    finish_binary(&mut values, base, TermType::MultiArrow);
                },
                CloneTask::Ambiguous { base, len } => {
                    let types = values.split_off(base);
                    debug_assert_eq!(types.len(), len);
                    values.push(TermType::Ambiguous(types));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("term-type clone PDA produced no result")
    }
}

fn finish_binary(
    values: &mut Vec<TermType>,
    base: usize,
    build: impl FnOnce(Box<TermType>, Box<TermType>) -> TermType,
) {
    let codomain = values.pop().expect("term-type clone PDA lost its codomain");
    let domain = values.pop().expect("term-type clone PDA lost its domain");
    values.truncate(base);
    values.push(build(Box::new(domain), Box::new(codomain)));
}

fn take_children(ty: &mut TermType, work: &mut Vec<TermType>) {
    let take = |child: &mut Box<TermType>| *std::mem::replace(child, Box::new(TermType::Unknown));
    match ty {
        TermType::Arrow(domain, codomain) | TermType::MultiArrow(domain, codomain) => {
            work.push(take(domain));
            work.push(take(codomain));
        },
        TermType::Ambiguous(types) => work.append(types),
        TermType::Base(_) | TermType::Unknown => {},
    }
}

impl Drop for TermType {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut ty) = work.pop() {
            take_children(&mut ty, &mut work);
        }
    }
}

pub(super) fn into_ambiguous(mut ty: TermType) -> Vec<TermType> {
    match &mut ty {
        TermType::Ambiguous(types) => std::mem::take(types),
        _ => vec![ty],
    }
}

impl PartialEq for TermType {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (TermType::Base(a), TermType::Base(b)) if a == b => {},
                (TermType::Unknown, TermType::Unknown) => {},
                (TermType::Arrow(ad, ac), TermType::Arrow(bd, bc))
                | (TermType::MultiArrow(ad, ac), TermType::MultiArrow(bd, bc)) => {
                    work.push((ac, bc));
                    work.push((ad, bd));
                },
                (TermType::Ambiguous(a), TermType::Ambiguous(b)) if a.len() == b.len() => {
                    work.extend(a.iter().zip(b).rev());
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for TermType {}

enum FormatTask<'ty> {
    Debug(&'ty TermType),
    Display(&'ty TermType),
    Text(&'static str),
}

impl fmt::Debug for TermType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Debug(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Display(_) => unreachable!("display task reached Debug formatter"),
                FormatTask::Debug(TermType::Base(name)) => write!(formatter, "Base({name:?})")?,
                FormatTask::Debug(TermType::Unknown) => formatter.write_str("Unknown")?,
                FormatTask::Debug(TermType::Arrow(domain, codomain)) => {
                    formatter.write_str("Arrow(")?;
                    push_debug_binary(&mut tasks, domain, codomain);
                },
                FormatTask::Debug(TermType::MultiArrow(domain, codomain)) => {
                    formatter.write_str("MultiArrow(")?;
                    push_debug_binary(&mut tasks, domain, codomain);
                },
                FormatTask::Debug(TermType::Ambiguous(types)) => {
                    formatter.write_str("Ambiguous([")?;
                    tasks.push(FormatTask::Text("])"));
                    for (index, ty) in types.iter().enumerate().rev() {
                        tasks.push(FormatTask::Debug(ty));
                        if index != 0 {
                            tasks.push(FormatTask::Text(", "));
                        }
                    }
                },
            }
        }
        Ok(())
    }
}

fn push_debug_binary<'ty>(
    tasks: &mut Vec<FormatTask<'ty>>,
    domain: &'ty TermType,
    codomain: &'ty TermType,
) {
    tasks.push(FormatTask::Text(")"));
    tasks.push(FormatTask::Debug(codomain));
    tasks.push(FormatTask::Text(", "));
    tasks.push(FormatTask::Debug(domain));
}

impl fmt::Display for TermType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![FormatTask::Display(self)];
        while let Some(task) = tasks.pop() {
            match task {
                FormatTask::Text(text) => formatter.write_str(text)?,
                FormatTask::Debug(_) => unreachable!("debug task reached Display formatter"),
                FormatTask::Display(TermType::Base(name)) => formatter.write_str(name)?,
                FormatTask::Display(TermType::Unknown) => formatter.write_str("?")?,
                FormatTask::Display(TermType::Arrow(domain, codomain)) => {
                    formatter.write_str("[")?;
                    push_display_binary(&mut tasks, domain, codomain, " -> ");
                },
                FormatTask::Display(TermType::MultiArrow(domain, codomain)) => {
                    formatter.write_str("[")?;
                    push_display_binary(&mut tasks, domain, codomain, "* -> ");
                },
                FormatTask::Display(TermType::Ambiguous(types)) => {
                    for (index, ty) in types.iter().enumerate().rev() {
                        tasks.push(FormatTask::Display(ty));
                        if index != 0 {
                            tasks.push(FormatTask::Text(" | "));
                        }
                    }
                },
            }
        }
        Ok(())
    }
}

fn push_display_binary<'ty>(
    tasks: &mut Vec<FormatTask<'ty>>,
    domain: &'ty TermType,
    codomain: &'ty TermType,
    separator: &'static str,
) {
    tasks.push(FormatTask::Text("]"));
    tasks.push(FormatTask::Display(codomain));
    tasks.push(FormatTask::Text(separator));
    tasks.push(FormatTask::Display(domain));
}
