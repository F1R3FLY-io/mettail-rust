//! Stack-safe lifecycle operations for recursive constructor-tooling models.

use super::{DebugNode, FieldSpec};
use std::fmt;

impl Clone for FieldSpec {
    fn clone(&self) -> Self {
        let mut depth = 0usize;
        let mut cursor = self;
        while let FieldSpec::Opt(inner) = cursor {
            depth += 1;
            cursor = inner;
        }
        let mut cloned = clone_field_leaf(cursor);
        for _ in 0..depth {
            cloned = FieldSpec::Opt(Box::new(cloned));
        }
        cloned
    }
}

fn clone_field_leaf(spec: &FieldSpec) -> FieldSpec {
    match spec {
        FieldSpec::Cat(value) => FieldSpec::Cat(value.clone()),
        FieldSpec::Var => FieldSpec::Var,
        FieldSpec::Native(value) => FieldSpec::Native(value.clone()),
        FieldSpec::Coll { kind, elem } => {
            FieldSpec::Coll { kind: kind.clone(), elem: elem.clone() }
        },
        FieldSpec::CollLit { kind, elem } => {
            FieldSpec::CollLit { kind: kind.clone(), elem: elem.clone() }
        },
        FieldSpec::NativeZipper { storage, access, key, value } => FieldSpec::NativeZipper {
            storage: *storage,
            access: *access,
            key: key.clone(),
            value: value.clone(),
        },
        FieldSpec::Scope1 { binder, body } => FieldSpec::Scope1 {
            binder: binder.clone(),
            body: body.clone(),
        },
        FieldSpec::ScopeN { binder, body } => FieldSpec::ScopeN {
            binder: binder.clone(),
            body: body.clone(),
        },
        FieldSpec::Pred => FieldSpec::Pred,
        FieldSpec::OpaqueToken => FieldSpec::OpaqueToken,
        FieldSpec::OpaqueGuest => FieldSpec::OpaqueGuest,
        FieldSpec::Opt(_) => unreachable!("field-spec leaf clone stopped on an option"),
    }
}

impl Drop for FieldSpec {
    fn drop(&mut self) {
        let mut next = take_optional_child(self);
        while let Some(mut child) = next {
            next = take_optional_child(&mut child);
        }
    }
}

fn take_optional_child(spec: &mut FieldSpec) -> Option<FieldSpec> {
    match spec {
        FieldSpec::Opt(inner) => Some(*std::mem::replace(inner, Box::new(FieldSpec::Var))),
        _ => None,
    }
}

impl PartialEq for FieldSpec {
    fn eq(&self, other: &Self) -> bool {
        let mut left = self;
        let mut right = other;
        loop {
            match (left, right) {
                (FieldSpec::Opt(a), FieldSpec::Opt(b)) => {
                    left = a;
                    right = b;
                },
                (FieldSpec::Cat(a), FieldSpec::Cat(b))
                | (FieldSpec::Native(a), FieldSpec::Native(b)) => return a == b,
                (
                    FieldSpec::Coll { kind: ak, elem: ae },
                    FieldSpec::Coll { kind: bk, elem: be },
                )
                | (
                    FieldSpec::CollLit { kind: ak, elem: ae },
                    FieldSpec::CollLit { kind: bk, elem: be },
                ) => return ak == bk && ae == be,
                (
                    FieldSpec::NativeZipper {
                        storage: as_,
                        access: aa,
                        key: ak,
                        value: av,
                    },
                    FieldSpec::NativeZipper {
                        storage: bs,
                        access: ba,
                        key: bk,
                        value: bv,
                    },
                ) => return as_ == bs && aa == ba && ak == bk && av == bv,
                (
                    FieldSpec::Scope1 { binder: ab, body: ad },
                    FieldSpec::Scope1 { binder: bb, body: bd },
                )
                | (
                    FieldSpec::ScopeN { binder: ab, body: ad },
                    FieldSpec::ScopeN { binder: bb, body: bd },
                ) => return ab == bb && ad == bd,
                (FieldSpec::Var, FieldSpec::Var)
                | (FieldSpec::Pred, FieldSpec::Pred)
                | (FieldSpec::OpaqueToken, FieldSpec::OpaqueToken)
                | (FieldSpec::OpaqueGuest, FieldSpec::OpaqueGuest) => return true,
                _ => return false,
            }
        }
    }
}

impl Eq for FieldSpec {}

impl fmt::Debug for FieldSpec {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut depth = 0usize;
        let mut cursor = self;
        while let FieldSpec::Opt(inner) = cursor {
            formatter.write_str("Opt(")?;
            depth += 1;
            cursor = inner;
        }
        match cursor {
            FieldSpec::Cat(value) => write!(formatter, "Cat({value:?})")?,
            FieldSpec::Var => formatter.write_str("Var")?,
            FieldSpec::Native(value) => write!(formatter, "Native({value:?})")?,
            FieldSpec::Coll { kind, elem } => {
                write!(formatter, "Coll {{ kind: {kind:?}, elem: {elem:?} }}")?;
            },
            FieldSpec::CollLit { kind, elem } => {
                write!(formatter, "CollLit {{ kind: {kind:?}, elem: {elem:?} }}")?;
            },
            FieldSpec::NativeZipper { storage, access, key, value } => {
                write!(
                    formatter,
                    "NativeZipper {{ storage: {storage:?}, access: {access:?}, key: {key:?}, value: {value:?} }}",
                )?;
            },
            FieldSpec::Scope1 { binder, body } => {
                write!(formatter, "Scope1 {{ binder: {binder:?}, body: {body:?} }}")?;
            },
            FieldSpec::ScopeN { binder, body } => {
                write!(formatter, "ScopeN {{ binder: {binder:?}, body: {body:?} }}")?;
            },
            FieldSpec::Pred => formatter.write_str("Pred")?,
            FieldSpec::OpaqueToken => formatter.write_str("OpaqueToken")?,
            FieldSpec::OpaqueGuest => formatter.write_str("OpaqueGuest")?,
            FieldSpec::Opt(_) => unreachable!("field-spec debug stopped on an option"),
        }
        for _ in 0..depth {
            formatter.write_str(")")?;
        }
        Ok(())
    }
}

enum DebugCloneTask<'node> {
    Visit(&'node DebugNode),
    Sequence {
        kind: DebugSequenceKind,
        base: usize,
    },
    Call {
        head: &'node str,
        base: usize,
    },
    Struct {
        head: &'node str,
        fields: &'node [(String, DebugNode)],
        base: usize,
    },
    Map {
        len: usize,
        base: usize,
    },
    Named {
        name: &'node str,
        base: usize,
    },
}

#[derive(Clone, Copy)]
enum DebugSequenceKind {
    List,
    Set,
    Tuple,
}

impl Clone for DebugNode {
    fn clone(&self) -> Self {
        clone_debug_node(self, false)
    }
}

pub(super) fn clone_with_sorted_braces(root: &DebugNode) -> DebugNode {
    clone_debug_node(root, true)
}

fn clone_debug_node(root: &DebugNode, sort_braces: bool) -> DebugNode {
    let mut tasks = vec![DebugCloneTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            DebugCloneTask::Visit(node) => match node {
                DebugNode::Call { head, args } => {
                    let base = values.len();
                    tasks.push(DebugCloneTask::Call { head, base });
                    push_debug_children(&mut tasks, args);
                },
                DebugNode::Struct { head, fields } => {
                    let base = values.len();
                    tasks.push(DebugCloneTask::Struct { head, fields, base });
                    for (_, value) in fields.iter().rev() {
                        tasks.push(DebugCloneTask::Visit(value));
                    }
                },
                DebugNode::Ident(value) => values.push(DebugNode::Ident(value.clone())),
                DebugNode::Str(value) => values.push(DebugNode::Str(value.clone())),
                DebugNode::Int(value) => values.push(DebugNode::Int(*value)),
                DebugNode::Float(value) => values.push(DebugNode::Float(*value)),
                DebugNode::Ratio(numerator, denominator) => {
                    values.push(DebugNode::Ratio(*numerator, *denominator));
                },
                DebugNode::List(children) => {
                    push_debug_sequence(&mut tasks, &values, children, DebugSequenceKind::List);
                },
                DebugNode::Set(children) => {
                    push_debug_sequence(&mut tasks, &values, children, DebugSequenceKind::Set);
                },
                DebugNode::Map(entries) => {
                    let base = values.len();
                    tasks.push(DebugCloneTask::Map { len: entries.len(), base });
                    for (key, value) in entries.iter().rev() {
                        tasks.push(DebugCloneTask::Visit(value));
                        tasks.push(DebugCloneTask::Visit(key));
                    }
                },
                DebugNode::Tuple(children) => {
                    push_debug_sequence(&mut tasks, &values, children, DebugSequenceKind::Tuple);
                },
                DebugNode::Named { name, value } => {
                    let base = values.len();
                    tasks.push(DebugCloneTask::Named { name, base });
                    tasks.push(DebugCloneTask::Visit(value));
                },
                DebugNode::Range(low, high) => values.push(DebugNode::Range(*low, *high)),
            },
            DebugCloneTask::Sequence { kind, base } => {
                let mut children = values.split_off(base);
                if sort_braces && matches!(kind, DebugSequenceKind::Set) {
                    children.sort_by_key(super::render_debug);
                }
                values.push(match kind {
                    DebugSequenceKind::List => DebugNode::List(children),
                    DebugSequenceKind::Set => DebugNode::Set(children),
                    DebugSequenceKind::Tuple => DebugNode::Tuple(children),
                });
            },
            DebugCloneTask::Call { head, base } => {
                let args = values.split_off(base);
                values.push(DebugNode::Call { head: head.to_string(), args });
            },
            DebugCloneTask::Struct { head, fields, base } => {
                let children = values.split_off(base);
                debug_assert_eq!(children.len(), fields.len());
                values.push(DebugNode::Struct {
                    head: head.to_string(),
                    fields: fields
                        .iter()
                        .map(|(name, _)| name.clone())
                        .zip(children)
                        .collect(),
                });
            },
            DebugCloneTask::Map { len, base } => {
                let children = values.split_off(base);
                debug_assert_eq!(children.len(), len * 2);
                let mut children = children.into_iter();
                let mut entries = (0..len)
                    .map(|_| {
                        (
                            children.next().expect("debug-node clone lost a map key"),
                            children.next().expect("debug-node clone lost a map value"),
                        )
                    })
                    .collect::<Vec<_>>();
                if sort_braces {
                    entries.sort_by_key(|(key, value)| {
                        (super::render_debug(key), super::render_debug(value))
                    });
                }
                values.push(DebugNode::Map(entries));
            },
            DebugCloneTask::Named { name, base } => {
                debug_assert_eq!(values.len(), base + 1);
                let value = values.pop().expect("debug-node clone lost a named value");
                values.push(DebugNode::Named {
                    name: name.to_string(),
                    value: Box::new(value),
                });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("debug-node clone PDA produced no value")
}

fn push_debug_children<'node>(
    tasks: &mut Vec<DebugCloneTask<'node>>,
    children: &'node [DebugNode],
) {
    for child in children.iter().rev() {
        tasks.push(DebugCloneTask::Visit(child));
    }
}

fn push_debug_sequence<'node>(
    tasks: &mut Vec<DebugCloneTask<'node>>,
    values: &[DebugNode],
    children: &'node [DebugNode],
    kind: DebugSequenceKind,
) {
    tasks.push(DebugCloneTask::Sequence { kind, base: values.len() });
    push_debug_children(tasks, children);
}

fn take_debug_children(node: &mut DebugNode, work: &mut Vec<DebugNode>) {
    match node {
        DebugNode::Call { args, .. }
        | DebugNode::List(args)
        | DebugNode::Set(args)
        | DebugNode::Tuple(args) => work.append(args),
        DebugNode::Struct { fields, .. } => {
            for (_, value) in std::mem::take(fields) {
                work.push(value);
            }
        },
        DebugNode::Map(entries) => {
            for (key, value) in std::mem::take(entries) {
                work.push(key);
                work.push(value);
            }
        },
        DebugNode::Named { value, .. } => {
            work.push(*std::mem::replace(value, Box::new(DebugNode::Int(0))));
        },
        DebugNode::Ident(_)
        | DebugNode::Str(_)
        | DebugNode::Int(_)
        | DebugNode::Float(_)
        | DebugNode::Ratio(_, _)
        | DebugNode::Range(_, _) => {},
    }
}

impl Drop for DebugNode {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_debug_children(self, &mut work);
        while let Some(mut node) = work.pop() {
            take_debug_children(&mut node, &mut work);
        }
    }
}

impl PartialEq for DebugNode {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (
                    DebugNode::Call { head: ah, args: aa },
                    DebugNode::Call { head: bh, args: ba },
                ) if ah == bh && aa.len() == ba.len() => work.extend(aa.iter().zip(ba).rev()),
                (
                    DebugNode::Struct { head: ah, fields: af },
                    DebugNode::Struct { head: bh, fields: bf },
                ) if ah == bh && af.len() == bf.len() => {
                    for ((an, av), (bn, bv)) in af.iter().zip(bf).rev() {
                        if an != bn {
                            return false;
                        }
                        work.push((av, bv));
                    }
                },
                (DebugNode::Ident(a), DebugNode::Ident(b))
                | (DebugNode::Str(a), DebugNode::Str(b))
                    if a == b => {},
                (DebugNode::Int(a), DebugNode::Int(b)) if a == b => {},
                (DebugNode::Float(a), DebugNode::Float(b)) if a == b => {},
                (DebugNode::Ratio(an, ad), DebugNode::Ratio(bn, bd)) if an == bn && ad == bd => {},
                (DebugNode::List(a), DebugNode::List(b))
                | (DebugNode::Set(a), DebugNode::Set(b))
                | (DebugNode::Tuple(a), DebugNode::Tuple(b))
                    if a.len() == b.len() =>
                {
                    work.extend(a.iter().zip(b).rev());
                },
                (DebugNode::Map(a), DebugNode::Map(b)) if a.len() == b.len() => {
                    for ((ak, av), (bk, bv)) in a.iter().zip(b).rev() {
                        work.push((av, bv));
                        work.push((ak, bk));
                    }
                },
                (
                    DebugNode::Named { name: an, value: av },
                    DebugNode::Named { name: bn, value: bv },
                ) if an == bn => work.push((av, bv)),
                (DebugNode::Range(al, ah), DebugNode::Range(bl, bh)) if al == bl && ah == bh => {},
                _ => return false,
            }
        }
        true
    }
}

enum DebugFormatTask<'node> {
    Visit(&'node DebugNode),
    Text(&'static str),
    FieldName(&'node str),
}

impl fmt::Debug for DebugNode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![DebugFormatTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                DebugFormatTask::Text(text) => formatter.write_str(text)?,
                DebugFormatTask::FieldName(name) => write!(formatter, "{name:?}")?,
                DebugFormatTask::Visit(node) => match node {
                    DebugNode::Call { head, args } => {
                        formatter.write_str("Call { head: ")?;
                        write!(formatter, "{head:?}")?;
                        formatter.write_str(", args: ")?;
                        push_debug_vec_format(&mut tasks, args, "] }");
                    },
                    DebugNode::Struct { head, fields } => {
                        formatter.write_str("Struct { head: ")?;
                        write!(formatter, "{head:?}")?;
                        formatter.write_str(", fields: [")?;
                        tasks.push(DebugFormatTask::Text("] }"));
                        for (index, (name, value)) in fields.iter().enumerate().rev() {
                            tasks.push(DebugFormatTask::Text(")"));
                            tasks.push(DebugFormatTask::Visit(value));
                            tasks.push(DebugFormatTask::Text(", "));
                            tasks.push(DebugFormatTask::FieldName(name));
                            tasks.push(DebugFormatTask::Text("("));
                            if index != 0 {
                                tasks.push(DebugFormatTask::Text(", "));
                            }
                        }
                    },
                    DebugNode::Ident(value) => write!(formatter, "Ident({value:?})")?,
                    DebugNode::Str(value) => write!(formatter, "Str({value:?})")?,
                    DebugNode::Int(value) => write!(formatter, "Int({value:?})")?,
                    DebugNode::Float(value) => write!(formatter, "Float({value:?})")?,
                    DebugNode::Ratio(numerator, denominator) => {
                        write!(formatter, "Ratio({numerator:?}, {denominator:?})")?;
                    },
                    DebugNode::List(children) => {
                        formatter.write_str("List(")?;
                        push_debug_vec_format(&mut tasks, children, "])");
                    },
                    DebugNode::Set(children) => {
                        formatter.write_str("Set(")?;
                        push_debug_vec_format(&mut tasks, children, "])");
                    },
                    DebugNode::Map(entries) => {
                        formatter.write_str("Map([")?;
                        tasks.push(DebugFormatTask::Text("])"));
                        for (index, (key, value)) in entries.iter().enumerate().rev() {
                            tasks.push(DebugFormatTask::Text(")"));
                            tasks.push(DebugFormatTask::Visit(value));
                            tasks.push(DebugFormatTask::Text(", "));
                            tasks.push(DebugFormatTask::Visit(key));
                            tasks.push(DebugFormatTask::Text("("));
                            if index != 0 {
                                tasks.push(DebugFormatTask::Text(", "));
                            }
                        }
                    },
                    DebugNode::Tuple(children) => {
                        formatter.write_str("Tuple(")?;
                        push_debug_vec_format(&mut tasks, children, "])");
                    },
                    DebugNode::Named { name, value } => {
                        formatter.write_str("Named { name: ")?;
                        write!(formatter, "{name:?}")?;
                        formatter.write_str(", value: ")?;
                        tasks.push(DebugFormatTask::Text(" }"));
                        tasks.push(DebugFormatTask::Visit(value));
                    },
                    DebugNode::Range(low, high) => write!(formatter, "Range({low:?}, {high:?})")?,
                },
            }
        }
        Ok(())
    }
}

fn push_debug_vec_format<'node>(
    tasks: &mut Vec<DebugFormatTask<'node>>,
    children: &'node [DebugNode],
    close: &'static str,
) {
    tasks.push(DebugFormatTask::Text(close));
    for (index, child) in children.iter().enumerate().rev() {
        tasks.push(DebugFormatTask::Visit(child));
        if index != 0 {
            tasks.push(DebugFormatTask::Text(", "));
        }
    }
    tasks.push(DebugFormatTask::Text("["));
}
