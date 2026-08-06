use std::fmt;
use std::mem::{self, ManuallyDrop};
use std::ptr;

use super::RDSyntaxItem;

impl Clone for RDSyntaxItem {
    fn clone(&self) -> Self {
        enum Task<'item> {
            Visit(&'item RDSyntaxItem),
            Sep {
                separator: String,
                kind: super::CollectionKind,
            },
            Map {
                child_count: usize,
            },
            Zip {
                left_name: String,
                right_name: String,
                left_category: String,
                right_category: String,
            },
            Optional {
                child_count: usize,
            },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(RDSyntaxItem::Terminal(text)) => {
                    values.push(RDSyntaxItem::Terminal(text.clone()));
                },
                Task::Visit(RDSyntaxItem::NonTerminal { category, param_name }) => {
                    values.push(RDSyntaxItem::NonTerminal {
                        category: category.clone(),
                        param_name: param_name.clone(),
                    });
                },
                Task::Visit(RDSyntaxItem::IdentCapture { param_name }) => {
                    values.push(RDSyntaxItem::IdentCapture { param_name: param_name.clone() });
                },
                Task::Visit(RDSyntaxItem::TokenKindCapture { param_name, kind_name }) => {
                    values.push(RDSyntaxItem::TokenKindCapture {
                        param_name: param_name.clone(),
                        kind_name: kind_name.clone(),
                    });
                },
                Task::Visit(RDSyntaxItem::Binder { param_name, binder_category }) => {
                    values.push(RDSyntaxItem::Binder {
                        param_name: param_name.clone(),
                        binder_category: binder_category.clone(),
                    });
                },
                Task::Visit(RDSyntaxItem::Collection {
                    param_name,
                    element_category,
                    separator,
                    kind,
                    key_val_separator,
                }) => values.push(RDSyntaxItem::Collection {
                    param_name: param_name.clone(),
                    element_category: element_category.clone(),
                    separator: separator.clone(),
                    kind: *kind,
                    key_val_separator: key_val_separator.clone(),
                }),
                Task::Visit(RDSyntaxItem::SepList {
                    collection_name,
                    element_category,
                    separator,
                    kind,
                }) => values.push(RDSyntaxItem::SepList {
                    collection_name: collection_name.clone(),
                    element_category: element_category.clone(),
                    separator: separator.clone(),
                    kind: *kind,
                }),
                Task::Visit(RDSyntaxItem::Sep { body, separator, kind }) => {
                    tasks.push(Task::Sep {
                        separator: separator.clone(),
                        kind: *kind,
                    });
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(RDSyntaxItem::Map { body_items }) => {
                    tasks.push(Task::Map { child_count: body_items.len() });
                    for child in body_items.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::Visit(RDSyntaxItem::Zip {
                    left_name,
                    right_name,
                    left_category,
                    right_category,
                    body,
                }) => {
                    tasks.push(Task::Zip {
                        left_name: left_name.clone(),
                        right_name: right_name.clone(),
                        left_category: left_category.clone(),
                        right_category: right_category.clone(),
                    });
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(RDSyntaxItem::BinderCollection { param_name, separator }) => {
                    values.push(RDSyntaxItem::BinderCollection {
                        param_name: param_name.clone(),
                        separator: separator.clone(),
                    });
                },
                Task::Visit(RDSyntaxItem::Optional { inner }) => {
                    tasks.push(Task::Optional { child_count: inner.len() });
                    for child in inner.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::Visit(RDSyntaxItem::GuardExpression { param_name }) => {
                    values.push(RDSyntaxItem::GuardExpression { param_name: param_name.clone() });
                },
                Task::Sep { separator, kind } => {
                    let body = values
                        .pop()
                        .expect("RD syntax-item clone PDA lost its separated body");
                    values.push(RDSyntaxItem::Sep { body: Box::new(body), separator, kind });
                },
                Task::Map { child_count } | Task::Optional { child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("RD syntax-item clone PDA lost sequence children");
                    let children = values.split_off(first);
                    values.push(match task {
                        Task::Map { .. } => RDSyntaxItem::Map { body_items: children },
                        Task::Optional { .. } => RDSyntaxItem::Optional { inner: children },
                        _ => unreachable!(),
                    });
                },
                Task::Zip {
                    left_name,
                    right_name,
                    left_category,
                    right_category,
                } => {
                    let body = values
                        .pop()
                        .expect("RD syntax-item clone PDA lost its zip body");
                    values.push(RDSyntaxItem::Zip {
                        left_name,
                        right_name,
                        left_category,
                        right_category,
                        body: Box::new(body),
                    });
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("RD syntax-item clone PDA produced no value")
    }
}

impl fmt::Debug for RDSyntaxItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'item> {
            Node(&'item RDSyntaxItem),
            Text(&'static str),
            SepTail(&'item str, super::CollectionKind),
        }

        fn push_list<'item>(
            tasks: &mut Vec<Task<'item>>,
            close: &'static str,
            items: &'item [RDSyntaxItem],
        ) {
            tasks.push(Task::Text(close));
            for (index, item) in items.iter().enumerate().rev() {
                tasks.push(Task::Node(item));
                if index > 0 {
                    tasks.push(Task::Text(", "));
                }
            }
            tasks.push(Task::Text("["));
        }

        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => f.write_str(text)?,
                Task::SepTail(separator, kind) => {
                    write!(f, ", separator: {separator:?}, kind: {kind:?}")?;
                },
                Task::Node(RDSyntaxItem::Terminal(text)) => write!(f, "Terminal({text:?})")?,
                Task::Node(RDSyntaxItem::NonTerminal { category, param_name }) => {
                    write!(
                        f,
                        "NonTerminal {{ category: {category:?}, param_name: {param_name:?} }}"
                    )?;
                },
                Task::Node(RDSyntaxItem::IdentCapture { param_name }) => {
                    write!(f, "IdentCapture {{ param_name: {param_name:?} }}")?;
                },
                Task::Node(RDSyntaxItem::TokenKindCapture { param_name, kind_name }) => {
                    write!(
                        f,
                        "TokenKindCapture {{ param_name: {param_name:?}, kind_name: {kind_name:?} }}"
                    )?;
                },
                Task::Node(RDSyntaxItem::Binder { param_name, binder_category }) => {
                    write!(
                        f,
                        "Binder {{ param_name: {param_name:?}, binder_category: {binder_category:?} }}"
                    )?;
                },
                Task::Node(RDSyntaxItem::Collection {
                    param_name,
                    element_category,
                    separator,
                    kind,
                    key_val_separator,
                }) => write!(
                    f,
                    "Collection {{ param_name: {param_name:?}, element_category: {element_category:?}, separator: {separator:?}, kind: {kind:?}, key_val_separator: {key_val_separator:?} }}"
                )?,
                Task::Node(RDSyntaxItem::SepList {
                    collection_name,
                    element_category,
                    separator,
                    kind,
                }) => write!(
                    f,
                    "SepList {{ collection_name: {collection_name:?}, element_category: {element_category:?}, separator: {separator:?}, kind: {kind:?} }}"
                )?,
                Task::Node(RDSyntaxItem::Sep { body, separator, kind }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::SepTail(separator, *kind));
                    tasks.push(Task::Node(body));
                    write!(f, "Sep {{ body: ")?;
                },
                Task::Node(RDSyntaxItem::Map { body_items }) => {
                    tasks.push(Task::Text(" }"));
                    push_list(&mut tasks, "]", body_items);
                    tasks.push(Task::Text("Map { body_items: "));
                },
                Task::Node(RDSyntaxItem::Zip {
                    left_name,
                    right_name,
                    left_category,
                    right_category,
                    body,
                }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::Node(body));
                    write!(
                        f,
                        "Zip {{ left_name: {left_name:?}, right_name: {right_name:?}, left_category: {left_category:?}, right_category: {right_category:?}, body: "
                    )?;
                },
                Task::Node(RDSyntaxItem::BinderCollection { param_name, separator }) => {
                    write!(
                        f,
                        "BinderCollection {{ param_name: {param_name:?}, separator: {separator:?} }}"
                    )?;
                },
                Task::Node(RDSyntaxItem::Optional { inner }) => {
                    tasks.push(Task::Text(" }"));
                    push_list(&mut tasks, "]", inner);
                    tasks.push(Task::Text("Optional { inner: "));
                },
                Task::Node(RDSyntaxItem::GuardExpression { param_name }) => {
                    write!(f, "GuardExpression {{ param_name: {param_name:?} }}")?;
                },
            }
        }
        Ok(())
    }
}

impl Drop for RDSyntaxItem {
    fn drop(&mut self) {
        let root = mem::replace(self, RDSyntaxItem::Terminal(String::new()));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    RDSyntaxItem::Terminal(text) => std::mem::drop(ptr::read(text)),
                    RDSyntaxItem::NonTerminal { category, param_name } => {
                        std::mem::drop(ptr::read(category));
                        std::mem::drop(ptr::read(param_name));
                    },
                    RDSyntaxItem::IdentCapture { param_name }
                    | RDSyntaxItem::GuardExpression { param_name } => {
                        std::mem::drop(ptr::read(param_name));
                    },
                    RDSyntaxItem::TokenKindCapture { param_name, kind_name } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(kind_name));
                    },
                    RDSyntaxItem::Binder { param_name, binder_category } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(binder_category));
                    },
                    RDSyntaxItem::Collection {
                        param_name,
                        element_category,
                        separator,
                        key_val_separator,
                        ..
                    } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(element_category));
                        std::mem::drop(ptr::read(separator));
                        std::mem::drop(ptr::read(key_val_separator));
                    },
                    RDSyntaxItem::SepList {
                        collection_name,
                        element_category,
                        separator,
                        ..
                    } => {
                        std::mem::drop(ptr::read(collection_name));
                        std::mem::drop(ptr::read(element_category));
                        std::mem::drop(ptr::read(separator));
                    },
                    RDSyntaxItem::Sep { body, separator, .. } => {
                        work.push(*ptr::read(body));
                        std::mem::drop(ptr::read(separator));
                    },
                    RDSyntaxItem::Map { body_items } => work.extend(ptr::read(body_items)),
                    RDSyntaxItem::Zip {
                        left_name,
                        right_name,
                        left_category,
                        right_category,
                        body,
                    } => {
                        std::mem::drop(ptr::read(left_name));
                        std::mem::drop(ptr::read(right_name));
                        std::mem::drop(ptr::read(left_category));
                        std::mem::drop(ptr::read(right_category));
                        work.push(*ptr::read(body));
                    },
                    RDSyntaxItem::BinderCollection { param_name, separator } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(separator));
                    },
                    RDSyntaxItem::Optional { inner } => work.extend(ptr::read(inner)),
                }
            }
        }
    }
}
