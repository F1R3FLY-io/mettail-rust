//! Heap-backed lifecycle and structural transforms for analyzable SFT outputs.

use super::OutputTerm;
use crate::symbolic::BooleanAlgebra;
use std::fmt;

enum CloneTask<'term, A: BooleanAlgebra, B: BooleanAlgebra> {
    Visit(&'term OutputTerm<A, B>),
    Concat(usize),
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Clone for OutputTerm<A, B> {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(OutputTerm::Eps) => values.push(OutputTerm::Eps),
                CloneTask::Visit(OutputTerm::Id) => values.push(OutputTerm::Id),
                CloneTask::Visit(OutputTerm::Const(outputs)) => {
                    values.push(OutputTerm::Const(outputs.clone()))
                },
                CloneTask::Visit(OutputTerm::Concat(left, right)) => {
                    tasks.push(CloneTask::Concat(values.len()));
                    tasks.push(CloneTask::Visit(right));
                    tasks.push(CloneTask::Visit(left));
                },
                CloneTask::Visit(OutputTerm::_Input(never, _)) => match *never {},
                CloneTask::Concat(base) => {
                    let right = values.pop().expect("output-term clone lost a right term");
                    let left = values.pop().expect("output-term clone lost a left term");
                    values.truncate(base);
                    values.push(OutputTerm::Concat(Box::new(left), Box::new(right)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("output-term clone produced no term")
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> PartialEq for OutputTerm<A, B>
where
    B::Domain: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (OutputTerm::Eps, OutputTerm::Eps) | (OutputTerm::Id, OutputTerm::Id) => {},
                (OutputTerm::Const(a), OutputTerm::Const(b)) if a == b => {},
                (OutputTerm::Concat(al, ar), OutputTerm::Concat(bl, br)) => {
                    work.push((ar, br));
                    work.push((al, bl));
                },
                (OutputTerm::_Input(never, _), _) | (_, OutputTerm::_Input(never, _)) => {
                    match *never {}
                },
                _ => return false,
            }
        }
        true
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Eq for OutputTerm<A, B> where B::Domain: Eq {}

fn take_children<A: BooleanAlgebra, B: BooleanAlgebra>(
    term: &mut OutputTerm<A, B>,
    work: &mut Vec<OutputTerm<A, B>>,
) {
    match term {
        OutputTerm::Concat(left, right) => {
            work.push(*std::mem::replace(left, Box::new(OutputTerm::Eps)));
            work.push(*std::mem::replace(right, Box::new(OutputTerm::Eps)));
        },
        OutputTerm::Eps | OutputTerm::Id | OutputTerm::Const(_) => {},
        OutputTerm::_Input(never, _) => match *never {},
    }
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> Drop for OutputTerm<A, B> {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut term) = work.pop() {
            take_children(&mut term, &mut work);
        }
    }
}

enum DebugTask<'term, A: BooleanAlgebra, B: BooleanAlgebra> {
    Visit(&'term OutputTerm<A, B>),
    Text(&'static str),
}

impl<A: BooleanAlgebra, B: BooleanAlgebra> fmt::Debug for OutputTerm<A, B> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Visit(OutputTerm::Eps) => formatter.write_str("Eps")?,
                DebugTask::Visit(OutputTerm::Id) => formatter.write_str("Id")?,
                DebugTask::Visit(OutputTerm::Const(outputs)) => {
                    write!(formatter, "Const({outputs:?})")?
                },
                DebugTask::Visit(OutputTerm::Concat(left, right)) => {
                    tasks.push(DebugTask::Text(")"));
                    tasks.push(DebugTask::Visit(right));
                    tasks.push(DebugTask::Text(", "));
                    tasks.push(DebugTask::Visit(left));
                    tasks.push(DebugTask::Text("Concat("));
                },
                DebugTask::Visit(OutputTerm::_Input(never, _)) => match *never {},
            }
        }
        Ok(())
    }
}

pub(super) fn retype_input<A: BooleanAlgebra, A2: BooleanAlgebra, B: BooleanAlgebra>(
    term: &OutputTerm<A, B>,
) -> OutputTerm<A2, B> {
    enum Task<'term, A: BooleanAlgebra, B: BooleanAlgebra> {
        Visit(&'term OutputTerm<A, B>),
        Concat(usize),
    }

    let mut tasks = vec![Task::Visit(term)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(OutputTerm::Eps) => values.push(OutputTerm::Eps),
            Task::Visit(OutputTerm::Id) => values.push(OutputTerm::Id),
            Task::Visit(OutputTerm::Const(outputs)) => {
                values.push(OutputTerm::Const(outputs.clone()))
            },
            Task::Visit(OutputTerm::Concat(left, right)) => {
                tasks.push(Task::Concat(values.len()));
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(OutputTerm::_Input(never, _)) => match *never {},
            Task::Concat(base) => {
                let right = values
                    .pop()
                    .expect("output-term retyping lost a right term");
                let left = values.pop().expect("output-term retyping lost a left term");
                values.truncate(base);
                values.push(OutputTerm::Concat(Box::new(left), Box::new(right)));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("output-term retyping produced no term")
}
