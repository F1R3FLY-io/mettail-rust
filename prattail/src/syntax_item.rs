//! Iterative lifecycle and traversal machinery for [`SyntaxItemSpec`].
//!
//! Grammar syntax is a tree, not an arbitrarily shallow list: `Sep`, `Map`,
//! `Zip`, and `Optional` recursively own more syntax items.  Keeping the
//! traversal kernel here gives every analysis and lowering pass the same
//! stack-safe depth-first order instead of duplicating recursive walkers.

use std::fmt;
use std::mem::{self, ManuallyDrop};
use std::ptr;

use crate::grammar::ir::RDSyntaxItem;
use crate::SyntaxItemSpec;

/// Stack-safe, left-to-right preorder traversal over one or more syntax roots.
pub(crate) struct SyntaxItemPreorder<'item> {
    work: Vec<&'item SyntaxItemSpec>,
}

impl<'item> SyntaxItemPreorder<'item> {
    pub(crate) fn new(items: &'item [SyntaxItemSpec]) -> Self {
        Self { work: items.iter().rev().collect() }
    }
}

impl<'item> Iterator for SyntaxItemPreorder<'item> {
    type Item = &'item SyntaxItemSpec;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.work.pop()?;
        match item {
            SyntaxItemSpec::Sep { body, .. } | SyntaxItemSpec::Zip { body, .. } => {
                self.work.push(body);
            },
            SyntaxItemSpec::Map { body_items } => {
                self.work.extend(body_items.iter().rev());
            },
            SyntaxItemSpec::Optional { inner } => {
                self.work.extend(inner.iter().rev());
            },
            _ => {},
        }
        Some(item)
    }
}

/// Stack-safe, left-to-right postorder traversal over one or more syntax roots.
pub(crate) struct SyntaxItemPostorder<'item> {
    work: Vec<(&'item SyntaxItemSpec, bool)>,
}

impl<'item> SyntaxItemPostorder<'item> {
    pub(crate) fn new(items: &'item [SyntaxItemSpec]) -> Self {
        Self {
            work: items.iter().rev().map(|item| (item, false)).collect(),
        }
    }
}

impl<'item> Iterator for SyntaxItemPostorder<'item> {
    type Item = &'item SyntaxItemSpec;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((item, visited)) = self.work.pop() {
            if visited {
                return Some(item);
            }
            self.work.push((item, true));
            match item {
                SyntaxItemSpec::Sep { body, .. } | SyntaxItemSpec::Zip { body, .. } => {
                    self.work.push((body, false));
                },
                SyntaxItemSpec::Map { body_items } => {
                    self.work
                        .extend(body_items.iter().rev().map(|child| (child, false)));
                },
                SyntaxItemSpec::Optional { inner } => {
                    self.work
                        .extend(inner.iter().rev().map(|child| (child, false)));
                },
                _ => {},
            }
        }
        None
    }
}

pub(crate) fn preorder(items: &[SyntaxItemSpec]) -> SyntaxItemPreorder<'_> {
    SyntaxItemPreorder::new(items)
}

pub(crate) fn postorder(items: &[SyntaxItemSpec]) -> SyntaxItemPostorder<'_> {
    SyntaxItemPostorder::new(items)
}

fn take_children<T>(values: &mut Vec<T>, count: usize, invariant: &'static str) -> Vec<T> {
    let first = values.len().checked_sub(count).expect(invariant);
    values.split_off(first)
}

/// Lower a syntax tree to recursive-descent IR without using the call stack.
fn to_rd(root: &SyntaxItemSpec) -> RDSyntaxItem {
    let mut values = Vec::new();
    for item in postorder(std::slice::from_ref(root)) {
        let lowered = match item {
            SyntaxItemSpec::Terminal(text) => RDSyntaxItem::Terminal(text.clone()),
            SyntaxItemSpec::NonTerminal { category, param_name } => RDSyntaxItem::NonTerminal {
                category: category.clone(),
                param_name: param_name.clone(),
            },
            SyntaxItemSpec::IdentCapture { param_name } => {
                RDSyntaxItem::IdentCapture { param_name: param_name.clone() }
            },
            SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
                RDSyntaxItem::TokenKindCapture {
                    param_name: param_name.clone(),
                    kind_name: kind_name.clone(),
                }
            },
            SyntaxItemSpec::Binder { param_name, category, .. } => RDSyntaxItem::Binder {
                param_name: param_name.clone(),
                binder_category: category.clone(),
            },
            SyntaxItemSpec::Collection {
                param_name,
                element_category,
                separator,
                kind,
                key_val_separator,
            } => RDSyntaxItem::Collection {
                param_name: param_name.clone(),
                element_category: element_category.clone(),
                separator: separator.clone(),
                kind: *kind,
                key_val_separator: key_val_separator.clone(),
            },
            SyntaxItemSpec::Sep { separator, kind, .. } => {
                let body = values.pop().expect("syntax lowering PDA lost its Sep body");
                RDSyntaxItem::Sep {
                    body: Box::new(body),
                    separator: separator.clone(),
                    kind: *kind,
                }
            },
            SyntaxItemSpec::Map { body_items } => RDSyntaxItem::Map {
                body_items: take_children(
                    &mut values,
                    body_items.len(),
                    "syntax lowering PDA lost Map children",
                ),
            },
            SyntaxItemSpec::Zip {
                left_name,
                right_name,
                left_category,
                right_category,
                ..
            } => {
                let body = values.pop().expect("syntax lowering PDA lost its Zip body");
                RDSyntaxItem::Zip {
                    left_name: left_name.clone(),
                    right_name: right_name.clone(),
                    left_category: left_category.clone(),
                    right_category: right_category.clone(),
                    body: Box::new(body),
                }
            },
            SyntaxItemSpec::BinderCollection { param_name, separator } => {
                RDSyntaxItem::BinderCollection {
                    param_name: param_name.clone(),
                    separator: separator.clone(),
                }
            },
            SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
                inner: take_children(
                    &mut values,
                    inner.len(),
                    "syntax lowering PDA lost Optional children",
                ),
            },
            SyntaxItemSpec::GuardExpression { param_name } => {
                RDSyntaxItem::GuardExpression { param_name: param_name.clone() }
            },
        };
        values.push(lowered);
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("syntax lowering PDA produced no value")
}

impl SyntaxItemSpec {
    /// Lower this syntax tree to recursive-descent IR using an iterative
    /// postorder automaton.
    pub fn to_recursive_descent_item(&self) -> RDSyntaxItem {
        to_rd(self)
    }
}

impl Clone for SyntaxItemSpec {
    fn clone(&self) -> Self {
        let mut values = Vec::new();
        for item in postorder(std::slice::from_ref(self)) {
            let cloned = match item {
                SyntaxItemSpec::Terminal(text) => SyntaxItemSpec::Terminal(text.clone()),
                SyntaxItemSpec::NonTerminal { category, param_name } => {
                    SyntaxItemSpec::NonTerminal {
                        category: category.clone(),
                        param_name: param_name.clone(),
                    }
                },
                SyntaxItemSpec::IdentCapture { param_name } => {
                    SyntaxItemSpec::IdentCapture { param_name: param_name.clone() }
                },
                SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
                    SyntaxItemSpec::TokenKindCapture {
                        param_name: param_name.clone(),
                        kind_name: kind_name.clone(),
                    }
                },
                SyntaxItemSpec::Binder { param_name, category, is_multi } => {
                    SyntaxItemSpec::Binder {
                        param_name: param_name.clone(),
                        category: category.clone(),
                        is_multi: *is_multi,
                    }
                },
                SyntaxItemSpec::Collection {
                    param_name,
                    element_category,
                    separator,
                    kind,
                    key_val_separator,
                } => SyntaxItemSpec::Collection {
                    param_name: param_name.clone(),
                    element_category: element_category.clone(),
                    separator: separator.clone(),
                    kind: *kind,
                    key_val_separator: key_val_separator.clone(),
                },
                SyntaxItemSpec::Sep { separator, kind, .. } => {
                    let body = values
                        .pop()
                        .expect("syntax-item clone PDA lost its Sep body");
                    SyntaxItemSpec::Sep {
                        body: Box::new(body),
                        separator: separator.clone(),
                        kind: *kind,
                    }
                },
                SyntaxItemSpec::Map { body_items } => SyntaxItemSpec::Map {
                    body_items: take_children(
                        &mut values,
                        body_items.len(),
                        "syntax-item clone PDA lost Map children",
                    ),
                },
                SyntaxItemSpec::Zip {
                    left_name,
                    right_name,
                    left_category,
                    right_category,
                    ..
                } => {
                    let body = values
                        .pop()
                        .expect("syntax-item clone PDA lost its Zip body");
                    SyntaxItemSpec::Zip {
                        left_name: left_name.clone(),
                        right_name: right_name.clone(),
                        left_category: left_category.clone(),
                        right_category: right_category.clone(),
                        body: Box::new(body),
                    }
                },
                SyntaxItemSpec::BinderCollection { param_name, separator } => {
                    SyntaxItemSpec::BinderCollection {
                        param_name: param_name.clone(),
                        separator: separator.clone(),
                    }
                },
                SyntaxItemSpec::Optional { inner } => SyntaxItemSpec::Optional {
                    inner: take_children(
                        &mut values,
                        inner.len(),
                        "syntax-item clone PDA lost Optional children",
                    ),
                },
                SyntaxItemSpec::GuardExpression { param_name } => {
                    SyntaxItemSpec::GuardExpression { param_name: param_name.clone() }
                },
            };
            values.push(cloned);
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("syntax-item clone PDA produced no value")
    }
}

impl fmt::Debug for SyntaxItemSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'item> {
            Node(&'item SyntaxItemSpec),
            Text(&'static str),
            SepTail(&'item str, crate::grammar::ir::CollectionKind),
        }

        fn push_list<'item>(tasks: &mut Vec<Task<'item>>, items: &'item [SyntaxItemSpec]) {
            tasks.push(Task::Text("]"));
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
                Task::Node(SyntaxItemSpec::Terminal(text)) => write!(f, "Terminal({text:?})")?,
                Task::Node(SyntaxItemSpec::NonTerminal { category, param_name }) => write!(
                    f,
                    "NonTerminal {{ category: {category:?}, param_name: {param_name:?} }}"
                )?,
                Task::Node(SyntaxItemSpec::IdentCapture { param_name }) => {
                    write!(f, "IdentCapture {{ param_name: {param_name:?} }}")?;
                },
                Task::Node(SyntaxItemSpec::TokenKindCapture { param_name, kind_name }) => write!(
                    f,
                    "TokenKindCapture {{ param_name: {param_name:?}, kind_name: {kind_name:?} }}"
                )?,
                Task::Node(SyntaxItemSpec::Binder { param_name, category, is_multi }) => write!(
                    f,
                    "Binder {{ param_name: {param_name:?}, category: {category:?}, is_multi: {is_multi:?} }}"
                )?,
                Task::Node(SyntaxItemSpec::Collection {
                    param_name,
                    element_category,
                    separator,
                    kind,
                    key_val_separator,
                }) => write!(
                    f,
                    "Collection {{ param_name: {param_name:?}, element_category: {element_category:?}, separator: {separator:?}, kind: {kind:?}, key_val_separator: {key_val_separator:?} }}"
                )?,
                Task::Node(SyntaxItemSpec::Sep { body, separator, kind }) => {
                    tasks.push(Task::Text(" }"));
                    tasks.push(Task::SepTail(separator, *kind));
                    tasks.push(Task::Node(body));
                    f.write_str("Sep { body: ")?;
                },
                Task::Node(SyntaxItemSpec::Map { body_items }) => {
                    tasks.push(Task::Text(" }"));
                    push_list(&mut tasks, body_items);
                    tasks.push(Task::Text("Map { body_items: "));
                },
                Task::Node(SyntaxItemSpec::Zip {
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
                Task::Node(SyntaxItemSpec::BinderCollection { param_name, separator }) => write!(
                    f,
                    "BinderCollection {{ param_name: {param_name:?}, separator: {separator:?} }}"
                )?,
                Task::Node(SyntaxItemSpec::Optional { inner }) => {
                    tasks.push(Task::Text(" }"));
                    push_list(&mut tasks, inner);
                    tasks.push(Task::Text("Optional { inner: "));
                },
                Task::Node(SyntaxItemSpec::GuardExpression { param_name }) => {
                    write!(f, "GuardExpression {{ param_name: {param_name:?} }}")?;
                },
            }
        }
        Ok(())
    }
}

impl Drop for SyntaxItemSpec {
    fn drop(&mut self) {
        let root = mem::replace(self, SyntaxItemSpec::Terminal(String::new()));
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    SyntaxItemSpec::Terminal(text) => std::mem::drop(ptr::read(text)),
                    SyntaxItemSpec::NonTerminal { category, param_name } => {
                        std::mem::drop(ptr::read(category));
                        std::mem::drop(ptr::read(param_name));
                    },
                    SyntaxItemSpec::IdentCapture { param_name }
                    | SyntaxItemSpec::GuardExpression { param_name } => {
                        std::mem::drop(ptr::read(param_name));
                    },
                    SyntaxItemSpec::TokenKindCapture { param_name, kind_name } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(kind_name));
                    },
                    SyntaxItemSpec::Binder { param_name, category, .. } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(category));
                    },
                    SyntaxItemSpec::Collection {
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
                    SyntaxItemSpec::Sep { body, separator, .. } => {
                        work.push(*ptr::read(body));
                        std::mem::drop(ptr::read(separator));
                    },
                    SyntaxItemSpec::Map { body_items } => work.extend(ptr::read(body_items)),
                    SyntaxItemSpec::Zip {
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
                    SyntaxItemSpec::BinderCollection { param_name, separator } => {
                        std::mem::drop(ptr::read(param_name));
                        std::mem::drop(ptr::read(separator));
                    },
                    SyntaxItemSpec::Optional { inner } => work.extend(ptr::read(inner)),
                }
            }
        }
    }
}
