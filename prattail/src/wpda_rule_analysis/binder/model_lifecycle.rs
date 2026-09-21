//! Heap-backed lifecycle operations for recursive parser-codegen models.

use super::{ActionArgKind, BinderPosition};
use std::fmt;

enum BinderCloneTask<'position> {
    Visit(&'position BinderPosition),
    BinderListLoop {
        separator: &'position str,
        close: &'position str,
        collection_param_cat: &'position Option<String>,
        allow_empty: bool,
        allow_multi: bool,
        slot_idx: u8,
        base: usize,
        len: usize,
    },
    OptionalGroup {
        group_idx: u32,
        first_token_set: &'position [String],
        base: usize,
        len: usize,
    },
}

impl Clone for BinderPosition {
    fn clone(&self) -> Self {
        let mut tasks = vec![BinderCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                BinderCloneTask::Visit(BinderPosition::Literal(text)) => {
                    values.push(BinderPosition::Literal(text.clone()));
                },
                BinderCloneTask::Visit(BinderPosition::TokenKindCapture {
                    kind_name,
                    param_name,
                }) => values.push(BinderPosition::TokenKindCapture {
                    kind_name: kind_name.clone(),
                    param_name: param_name.clone(),
                }),
                BinderCloneTask::Visit(BinderPosition::IdentTextCapture { param_name }) => {
                    values
                        .push(BinderPosition::IdentTextCapture { param_name: param_name.clone() });
                },
                BinderCloneTask::Visit(BinderPosition::GuestBodyCapture {
                    open_kind,
                    nested_open_kinds,
                    close_kind,
                    param_name,
                }) => values.push(BinderPosition::GuestBodyCapture {
                    open_kind: open_kind.clone(),
                    nested_open_kinds: nested_open_kinds.clone(),
                    close_kind: close_kind.clone(),
                    param_name: param_name.clone(),
                }),
                BinderCloneTask::Visit(BinderPosition::BinderIdent) => {
                    values.push(BinderPosition::BinderIdent);
                },
                BinderCloneTask::Visit(BinderPosition::BinderListLoop {
                    separator,
                    close,
                    inner_positions,
                    collection_param_cat,
                    allow_empty,
                    allow_multi,
                    slot_idx,
                }) => {
                    tasks.push(BinderCloneTask::BinderListLoop {
                        separator,
                        close,
                        collection_param_cat,
                        allow_empty: *allow_empty,
                        allow_multi: *allow_multi,
                        slot_idx: *slot_idx,
                        base: values.len(),
                        len: inner_positions.len(),
                    });
                    tasks.extend(inner_positions.iter().rev().map(BinderCloneTask::Visit));
                },
                BinderCloneTask::Visit(BinderPosition::ParamParse { cat, collection }) => {
                    values.push(BinderPosition::ParamParse {
                        cat: cat.clone(),
                        collection: collection.clone(),
                    });
                },
                BinderCloneTask::Visit(BinderPosition::GuardSlot) => {
                    values.push(BinderPosition::GuardSlot);
                },
                BinderCloneTask::Visit(BinderPosition::OptionalGroup {
                    positions,
                    group_idx,
                    first_token_set,
                }) => {
                    tasks.push(BinderCloneTask::OptionalGroup {
                        group_idx: *group_idx,
                        first_token_set,
                        base: values.len(),
                        len: positions.len(),
                    });
                    tasks.extend(positions.iter().rev().map(BinderCloneTask::Visit));
                },
                BinderCloneTask::BinderListLoop {
                    separator,
                    close,
                    collection_param_cat,
                    allow_empty,
                    allow_multi,
                    slot_idx,
                    base,
                    len,
                } => {
                    debug_assert_eq!(values.len(), base + len);
                    let inner_positions = values.drain(base..).collect();
                    values.push(BinderPosition::BinderListLoop {
                        separator: separator.to_string(),
                        close: close.to_string(),
                        inner_positions,
                        collection_param_cat: collection_param_cat.clone(),
                        allow_empty,
                        allow_multi,
                        slot_idx,
                    });
                },
                BinderCloneTask::OptionalGroup { group_idx, first_token_set, base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let positions = values.drain(base..).collect();
                    values.push(BinderPosition::OptionalGroup {
                        positions,
                        group_idx,
                        first_token_set: first_token_set.to_vec(),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("binder-position clone produced no value")
    }
}

enum ActionCloneTask<'kind> {
    Visit(&'kind ActionArgKind),
    Optional { base: usize, len: usize },
}

impl Clone for ActionArgKind {
    fn clone(&self) -> Self {
        let mut tasks = vec![ActionCloneTask::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                ActionCloneTask::Visit(ActionArgKind::BinderName) => {
                    values.push(ActionArgKind::BinderName);
                },
                ActionCloneTask::Visit(ActionArgKind::TokenText { param_name }) => {
                    values.push(ActionArgKind::TokenText { param_name: param_name.clone() });
                },
                ActionCloneTask::Visit(ActionArgKind::IdentText { param_name }) => {
                    values.push(ActionArgKind::IdentText { param_name: param_name.clone() });
                },
                ActionCloneTask::Visit(ActionArgKind::GuestBody { param_name, kind }) => {
                    values.push(ActionArgKind::GuestBody {
                        param_name: param_name.clone(),
                        kind: *kind,
                    });
                },
                ActionCloneTask::Visit(ActionArgKind::Term(category)) => {
                    values.push(ActionArgKind::Term(category.clone()));
                },
                ActionCloneTask::Visit(ActionArgKind::Predicate) => {
                    values.push(ActionArgKind::Predicate);
                },
                ActionCloneTask::Visit(ActionArgKind::BinderList) => {
                    values.push(ActionArgKind::BinderList);
                },
                ActionCloneTask::Visit(ActionArgKind::Optional(inner)) => {
                    tasks.push(ActionCloneTask::Optional { base: values.len(), len: inner.len() });
                    tasks.extend(inner.iter().rev().map(ActionCloneTask::Visit));
                },
                ActionCloneTask::Visit(ActionArgKind::CollectionDrain { elem_cat, coll_kind }) => {
                    values.push(ActionArgKind::CollectionDrain {
                        elem_cat: elem_cat.clone(),
                        coll_kind: coll_kind.clone(),
                    });
                },
                ActionCloneTask::Optional { base, len } => {
                    debug_assert_eq!(values.len(), base + len);
                    let inner = values.drain(base..).collect();
                    values.push(ActionArgKind::Optional(inner));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("action-argument kind clone produced no value")
    }
}

fn take_binder_children(position: &mut BinderPosition, work: &mut Vec<BinderPosition>) {
    match position {
        BinderPosition::BinderListLoop { inner_positions, .. } => {
            work.extend(std::mem::take(inner_positions));
        },
        BinderPosition::OptionalGroup { positions, .. } => {
            work.extend(std::mem::take(positions));
        },
        _ => {},
    }
}

impl Drop for BinderPosition {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_binder_children(self, &mut work);
        while let Some(mut position) = work.pop() {
            take_binder_children(&mut position, &mut work);
        }
    }
}

fn take_action_children(kind: &mut ActionArgKind, work: &mut Vec<ActionArgKind>) {
    if let ActionArgKind::Optional(inner) = kind {
        work.extend(std::mem::take(inner));
    }
}

impl Drop for ActionArgKind {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_action_children(self, &mut work);
        while let Some(mut kind) = work.pop() {
            take_action_children(&mut kind, &mut work);
        }
    }
}

enum BinderDebugTask<'position> {
    Visit(&'position BinderPosition),
    Text(&'static str),
    BinderListSuffix {
        collection_param_cat: &'position Option<String>,
        allow_empty: bool,
        allow_multi: bool,
        slot_idx: u8,
    },
    OptionalSuffix {
        group_idx: u32,
        first_token_set: &'position [String],
    },
}

fn push_binder_list<'position>(
    tasks: &mut Vec<BinderDebugTask<'position>>,
    positions: &'position [BinderPosition],
) {
    tasks.push(BinderDebugTask::Text("]"));
    for (index, position) in positions.iter().enumerate().rev() {
        tasks.push(BinderDebugTask::Visit(position));
        if index > 0 {
            tasks.push(BinderDebugTask::Text(", "));
        }
    }
}

impl fmt::Debug for BinderPosition {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![BinderDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                BinderDebugTask::Text(text) => formatter.write_str(text)?,
                BinderDebugTask::BinderListSuffix {
                    collection_param_cat,
                    allow_empty,
                    allow_multi,
                    slot_idx,
                } => write!(
                    formatter,
                    ", collection_param_cat: {collection_param_cat:?}, allow_empty: {allow_empty:?}, allow_multi: {allow_multi:?}, slot_idx: {slot_idx:?} }}"
                )?,
                BinderDebugTask::OptionalSuffix {
                    group_idx,
                    first_token_set,
                } => write!(
                    formatter,
                    ", group_idx: {group_idx:?}, first_token_set: {first_token_set:?} }}"
                )?,
                BinderDebugTask::Visit(BinderPosition::Literal(text)) => {
                    write!(formatter, "Literal({text:?})")?;
                },
                BinderDebugTask::Visit(BinderPosition::TokenKindCapture {
                    kind_name,
                    param_name,
                }) => write!(
                    formatter,
                    "TokenKindCapture {{ kind_name: {kind_name:?}, param_name: {param_name:?} }}"
                )?,
                BinderDebugTask::Visit(BinderPosition::IdentTextCapture { param_name }) => {
                    write!(formatter, "IdentTextCapture {{ param_name: {param_name:?} }}")?;
                },
                BinderDebugTask::Visit(BinderPosition::GuestBodyCapture {
                    open_kind,
                    nested_open_kinds,
                    close_kind,
                    param_name,
                }) => write!(
                    formatter,
                    "GuestBodyCapture {{ open_kind: {open_kind:?}, nested_open_kinds: {nested_open_kinds:?}, close_kind: {close_kind:?}, param_name: {param_name:?} }}"
                )?,
                BinderDebugTask::Visit(BinderPosition::BinderIdent) => {
                    formatter.write_str("BinderIdent")?;
                },
                BinderDebugTask::Visit(BinderPosition::BinderListLoop {
                    separator,
                    close,
                    inner_positions,
                    collection_param_cat,
                    allow_empty,
                    allow_multi,
                    slot_idx,
                }) => {
                    tasks.push(BinderDebugTask::BinderListSuffix {
                        collection_param_cat,
                        allow_empty: *allow_empty,
                        allow_multi: *allow_multi,
                        slot_idx: *slot_idx,
                    });
                    push_binder_list(&mut tasks, inner_positions);
                    write!(
                        formatter,
                        "BinderListLoop {{ separator: {separator:?}, close: {close:?}, inner_positions: ["
                    )?;
                },
                BinderDebugTask::Visit(BinderPosition::ParamParse { cat, collection }) => {
                    write!(formatter, "ParamParse {{ cat: {cat:?}, collection: {collection:?} }}")?;
                },
                BinderDebugTask::Visit(BinderPosition::GuardSlot) => {
                    formatter.write_str("GuardSlot")?;
                },
                BinderDebugTask::Visit(BinderPosition::OptionalGroup {
                    positions,
                    group_idx,
                    first_token_set,
                }) => {
                    tasks.push(BinderDebugTask::OptionalSuffix {
                        group_idx: *group_idx,
                        first_token_set,
                    });
                    push_binder_list(&mut tasks, positions);
                    formatter.write_str("OptionalGroup { positions: [")?;
                },
            }
        }
        Ok(())
    }
}

enum ActionDebugTask<'kind> {
    Visit(&'kind ActionArgKind),
    Text(&'static str),
}

impl fmt::Debug for ActionArgKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tasks = vec![ActionDebugTask::Visit(self)];
        while let Some(task) = tasks.pop() {
            match task {
                ActionDebugTask::Text(text) => formatter.write_str(text)?,
                ActionDebugTask::Visit(ActionArgKind::BinderName) => {
                    formatter.write_str("BinderName")?;
                },
                ActionDebugTask::Visit(ActionArgKind::TokenText { param_name }) => {
                    write!(formatter, "TokenText {{ param_name: {param_name:?} }}")?;
                },
                ActionDebugTask::Visit(ActionArgKind::IdentText { param_name }) => {
                    write!(formatter, "IdentText {{ param_name: {param_name:?} }}")?;
                },
                ActionDebugTask::Visit(ActionArgKind::GuestBody { param_name, kind }) => {
                    write!(
                        formatter,
                        "GuestBody {{ param_name: {param_name:?}, kind: {kind:?} }}",
                    )?;
                },
                ActionDebugTask::Visit(ActionArgKind::Term(category)) => {
                    write!(formatter, "Term({category:?})")?;
                },
                ActionDebugTask::Visit(ActionArgKind::Predicate) => {
                    formatter.write_str("Predicate")?;
                },
                ActionDebugTask::Visit(ActionArgKind::BinderList) => {
                    formatter.write_str("BinderList")?;
                },
                ActionDebugTask::Visit(ActionArgKind::Optional(inner)) => {
                    tasks.push(ActionDebugTask::Text("])"));
                    for (index, kind) in inner.iter().enumerate().rev() {
                        tasks.push(ActionDebugTask::Visit(kind));
                        if index > 0 {
                            tasks.push(ActionDebugTask::Text(", "));
                        }
                    }
                    formatter.write_str("Optional([")?;
                },
                ActionDebugTask::Visit(ActionArgKind::CollectionDrain { elem_cat, coll_kind }) => {
                    write!(
                        formatter,
                        "CollectionDrain {{ elem_cat: {elem_cat:?}, coll_kind: {coll_kind:?} }}"
                    )?;
                },
            }
        }
        Ok(())
    }
}
