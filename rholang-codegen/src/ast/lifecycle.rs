//! Stack-safe lifecycle traits for normalized Rholang literal trees.

use super::RhoAstLiteral;
use std::fmt;

enum CloneTask<'literal> {
    Visit(&'literal RhoAstLiteral),
    Sequence {
        kind: SequenceKind,
        base: usize,
    },
    Map {
        source: &'literal [(RhoAstLiteral, RhoAstLiteral)],
        base: usize,
    },
    Bag {
        source: &'literal [(RhoAstLiteral, usize)],
        base: usize,
    },
}

#[derive(Clone, Copy)]
enum SequenceKind {
    List,
    Tuple,
    Set,
}

impl Clone for RhoAstLiteral {
    fn clone(&self) -> Self {
        let mut tasks = vec![CloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                CloneTask::Visit(literal) => match literal {
                    RhoAstLiteral::Int(value) => values.push(RhoAstLiteral::Int(*value)),
                    RhoAstLiteral::Bool(value) => values.push(RhoAstLiteral::Bool(*value)),
                    RhoAstLiteral::String(value) => {
                        values.push(RhoAstLiteral::String(value.clone()));
                    },
                    RhoAstLiteral::Uri(value) => values.push(RhoAstLiteral::Uri(value.clone())),
                    RhoAstLiteral::Bytes(value) => {
                        values.push(RhoAstLiteral::Bytes(value.clone()));
                    },
                    RhoAstLiteral::DoubleBits(value) => {
                        values.push(RhoAstLiteral::DoubleBits(*value));
                    },
                    RhoAstLiteral::BigIntBytes(value) => {
                        values.push(RhoAstLiteral::BigIntBytes(value.clone()));
                    },
                    RhoAstLiteral::BigRationalBytes { numerator, denominator } => {
                        values.push(RhoAstLiteral::BigRationalBytes {
                            numerator: numerator.clone(),
                            denominator: denominator.clone(),
                        });
                    },
                    RhoAstLiteral::FixedPointBytes { unscaled, scale } => {
                        values.push(RhoAstLiteral::FixedPointBytes {
                            unscaled: unscaled.clone(),
                            scale: *scale,
                        });
                    },
                    RhoAstLiteral::PrivateName(value) => {
                        values.push(RhoAstLiteral::PrivateName(value.clone()));
                    },
                    RhoAstLiteral::DeployId(value) => {
                        values.push(RhoAstLiteral::DeployId(value.clone()));
                    },
                    RhoAstLiteral::DeployerId(value) => {
                        values.push(RhoAstLiteral::DeployerId(value.clone()));
                    },
                    RhoAstLiteral::SysAuthToken => values.push(RhoAstLiteral::SysAuthToken),
                    RhoAstLiteral::List(children) => {
                        push_sequence(&mut tasks, &values, children, SequenceKind::List);
                    },
                    RhoAstLiteral::Tuple(children) => {
                        push_sequence(&mut tasks, &values, children, SequenceKind::Tuple);
                    },
                    RhoAstLiteral::Set(children) => {
                        push_sequence(&mut tasks, &values, children, SequenceKind::Set);
                    },
                    RhoAstLiteral::Map(entries) => {
                        let base = values.len();
                        tasks.push(CloneTask::Map { source: entries, base });
                        for (key, value) in entries.iter().rev() {
                            tasks.push(CloneTask::Visit(value));
                            tasks.push(CloneTask::Visit(key));
                        }
                    },
                    RhoAstLiteral::Bag(entries) => {
                        let base = values.len();
                        tasks.push(CloneTask::Bag { source: entries, base });
                        for (value, _) in entries.iter().rev() {
                            tasks.push(CloneTask::Visit(value));
                        }
                    },
                    RhoAstLiteral::QuotedChannel(value) => {
                        values.push(RhoAstLiteral::QuotedChannel(value.clone()));
                    },
                },
                CloneTask::Sequence { kind, base } => {
                    let children = values.split_off(base);
                    values.push(match kind {
                        SequenceKind::List => RhoAstLiteral::List(children),
                        SequenceKind::Tuple => RhoAstLiteral::Tuple(children),
                        SequenceKind::Set => RhoAstLiteral::Set(children),
                    });
                },
                CloneTask::Map { source, base } => {
                    let children = values.split_off(base);
                    debug_assert_eq!(children.len(), source.len() * 2);
                    let mut children = children.into_iter();
                    let entries = (0..source.len())
                        .map(|_| {
                            (
                                children.next().expect("literal clone PDA lost a map key"),
                                children.next().expect("literal clone PDA lost a map value"),
                            )
                        })
                        .collect();
                    values.push(RhoAstLiteral::Map(entries));
                },
                CloneTask::Bag { source, base } => {
                    let children = values.split_off(base);
                    debug_assert_eq!(children.len(), source.len());
                    values.push(RhoAstLiteral::Bag(
                        children
                            .into_iter()
                            .zip(source.iter().map(|(_, count)| *count))
                            .collect(),
                    ));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("literal clone PDA produced no value")
    }
}

fn push_sequence<'literal>(
    tasks: &mut Vec<CloneTask<'literal>>,
    values: &[RhoAstLiteral],
    children: &'literal [RhoAstLiteral],
    kind: SequenceKind,
) {
    tasks.push(CloneTask::Sequence { kind, base: values.len() });
    for child in children.iter().rev() {
        tasks.push(CloneTask::Visit(child));
    }
}

fn take_children(literal: &mut RhoAstLiteral, work: &mut Vec<RhoAstLiteral>) {
    match literal {
        RhoAstLiteral::List(children)
        | RhoAstLiteral::Tuple(children)
        | RhoAstLiteral::Set(children) => work.append(children),
        RhoAstLiteral::Map(entries) => {
            for (key, value) in std::mem::take(entries) {
                work.push(key);
                work.push(value);
            }
        },
        RhoAstLiteral::Bag(entries) => {
            for (value, _) in std::mem::take(entries) {
                work.push(value);
            }
        },
        RhoAstLiteral::Int(_)
        | RhoAstLiteral::Bool(_)
        | RhoAstLiteral::String(_)
        | RhoAstLiteral::Uri(_)
        | RhoAstLiteral::Bytes(_)
        | RhoAstLiteral::DoubleBits(_)
        | RhoAstLiteral::BigIntBytes(_)
        | RhoAstLiteral::BigRationalBytes { .. }
        | RhoAstLiteral::FixedPointBytes { .. }
        | RhoAstLiteral::PrivateName(_)
        | RhoAstLiteral::DeployId(_)
        | RhoAstLiteral::DeployerId(_)
        | RhoAstLiteral::SysAuthToken
        | RhoAstLiteral::QuotedChannel(_) => {},
    }
}

impl Drop for RhoAstLiteral {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_children(self, &mut work);
        while let Some(mut literal) = work.pop() {
            take_children(&mut literal, &mut work);
        }
    }
}

impl PartialEq for RhoAstLiteral {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (RhoAstLiteral::Int(a), RhoAstLiteral::Int(b)) if a == b => {},
                (RhoAstLiteral::Bool(a), RhoAstLiteral::Bool(b)) if a == b => {},
                (RhoAstLiteral::String(a), RhoAstLiteral::String(b)) if a == b => {},
                (RhoAstLiteral::Uri(a), RhoAstLiteral::Uri(b)) if a == b => {},
                (RhoAstLiteral::Bytes(a), RhoAstLiteral::Bytes(b)) if a == b => {},
                (RhoAstLiteral::DoubleBits(a), RhoAstLiteral::DoubleBits(b)) if a == b => {},
                (RhoAstLiteral::BigIntBytes(a), RhoAstLiteral::BigIntBytes(b)) if a == b => {},
                (
                    RhoAstLiteral::BigRationalBytes { numerator: an, denominator: ad },
                    RhoAstLiteral::BigRationalBytes { numerator: bn, denominator: bd },
                ) if an == bn && ad == bd => {},
                (
                    RhoAstLiteral::FixedPointBytes { unscaled: au, scale: ascale },
                    RhoAstLiteral::FixedPointBytes { unscaled: bu, scale: bscale },
                ) if au == bu && ascale == bscale => {},
                (RhoAstLiteral::PrivateName(a), RhoAstLiteral::PrivateName(b)) if a == b => {},
                (RhoAstLiteral::DeployId(a), RhoAstLiteral::DeployId(b)) if a == b => {},
                (RhoAstLiteral::DeployerId(a), RhoAstLiteral::DeployerId(b)) if a == b => {},
                (RhoAstLiteral::SysAuthToken, RhoAstLiteral::SysAuthToken) => {},
                (RhoAstLiteral::QuotedChannel(a), RhoAstLiteral::QuotedChannel(b)) if a == b => {},
                (RhoAstLiteral::List(a), RhoAstLiteral::List(b))
                | (RhoAstLiteral::Tuple(a), RhoAstLiteral::Tuple(b))
                | (RhoAstLiteral::Set(a), RhoAstLiteral::Set(b))
                    if a.len() == b.len() =>
                {
                    work.extend(a.iter().zip(b).rev());
                },
                (RhoAstLiteral::Map(a), RhoAstLiteral::Map(b)) if a.len() == b.len() => {
                    for ((ak, av), (bk, bv)) in a.iter().zip(b).rev() {
                        work.push((av, bv));
                        work.push((ak, bk));
                    }
                },
                (RhoAstLiteral::Bag(a), RhoAstLiteral::Bag(b)) if a.len() == b.len() => {
                    for ((av, ac), (bv, bc)) in a.iter().zip(b).rev() {
                        if ac != bc {
                            return false;
                        }
                        work.push((av, bv));
                    }
                },
                _ => return false,
            }
        }
        true
    }
}

impl Eq for RhoAstLiteral {}

enum DebugTask<'literal> {
    Visit(&'literal RhoAstLiteral),
    Text(&'static str),
    Count(usize),
}

impl fmt::Debug for RhoAstLiteral {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugTask::Text(text) => formatter.write_str(text)?,
                DebugTask::Count(count) => write!(formatter, "{count:?}")?,
                DebugTask::Visit(literal) => match literal {
                    RhoAstLiteral::Int(value) => write!(formatter, "Int({value:?})")?,
                    RhoAstLiteral::Bool(value) => write!(formatter, "Bool({value:?})")?,
                    RhoAstLiteral::String(value) => write!(formatter, "String({value:?})")?,
                    RhoAstLiteral::Uri(value) => write!(formatter, "Uri({value:?})")?,
                    RhoAstLiteral::Bytes(value) => write!(formatter, "Bytes({value:?})")?,
                    RhoAstLiteral::DoubleBits(value) => {
                        write!(formatter, "DoubleBits({value:?})")?;
                    },
                    RhoAstLiteral::BigIntBytes(value) => {
                        write!(formatter, "BigIntBytes({value:?})")?;
                    },
                    RhoAstLiteral::BigRationalBytes { numerator, denominator } => write!(
                        formatter,
                        "BigRationalBytes {{ numerator: {numerator:?}, denominator: {denominator:?} }}"
                    )?,
                    RhoAstLiteral::FixedPointBytes { unscaled, scale } => write!(
                        formatter,
                        "FixedPointBytes {{ unscaled: {unscaled:?}, scale: {scale:?} }}"
                    )?,
                    RhoAstLiteral::PrivateName(value) => {
                        write!(formatter, "PrivateName({value:?})")?;
                    },
                    RhoAstLiteral::DeployId(value) => write!(formatter, "DeployId({value:?})")?,
                    RhoAstLiteral::DeployerId(value) => {
                        write!(formatter, "DeployerId({value:?})")?;
                    },
                    RhoAstLiteral::SysAuthToken => formatter.write_str("SysAuthToken")?,
                    RhoAstLiteral::List(children) => {
                        formatter.write_str("List(")?;
                        push_sequence_debug(&mut tasks, children);
                    },
                    RhoAstLiteral::Tuple(children) => {
                        formatter.write_str("Tuple(")?;
                        push_sequence_debug(&mut tasks, children);
                    },
                    RhoAstLiteral::Set(children) => {
                        formatter.write_str("Set(")?;
                        push_sequence_debug(&mut tasks, children);
                    },
                    RhoAstLiteral::Map(entries) => {
                        formatter.write_str("Map([")?;
                        tasks.push(DebugTask::Text("])"));
                        for (index, (key, value)) in entries.iter().enumerate().rev() {
                            tasks.push(DebugTask::Text(")"));
                            tasks.push(DebugTask::Visit(value));
                            tasks.push(DebugTask::Text(", "));
                            tasks.push(DebugTask::Visit(key));
                            tasks.push(DebugTask::Text("("));
                            if index != 0 {
                                tasks.push(DebugTask::Text(", "));
                            }
                        }
                    },
                    RhoAstLiteral::Bag(entries) => {
                        formatter.write_str("Bag([")?;
                        tasks.push(DebugTask::Text("])"));
                        for (index, (value, count)) in entries.iter().enumerate().rev() {
                            tasks.push(DebugTask::Text(")"));
                            tasks.push(DebugTask::Count(*count));
                            tasks.push(DebugTask::Text(", "));
                            tasks.push(DebugTask::Visit(value));
                            tasks.push(DebugTask::Text("("));
                            if index != 0 {
                                tasks.push(DebugTask::Text(", "));
                            }
                        }
                    },
                    RhoAstLiteral::QuotedChannel(value) => {
                        write!(formatter, "QuotedChannel({value:?})")?;
                    },
                },
            }
        }
        Ok(())
    }
}

fn push_sequence_debug<'literal>(
    tasks: &mut Vec<DebugTask<'literal>>,
    children: &'literal [RhoAstLiteral],
) {
    tasks.push(DebugTask::Text("])"));
    for (index, child) in children.iter().enumerate().rev() {
        tasks.push(DebugTask::Visit(child));
        if index != 0 {
            tasks.push(DebugTask::Text(", "));
        }
    }
    tasks.push(DebugTask::Text("["));
}
