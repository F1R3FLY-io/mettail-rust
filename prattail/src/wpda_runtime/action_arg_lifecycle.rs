use std::any::Any;
use std::mem::{self, ManuallyDrop};
use std::ptr;
use std::sync::Arc;

use super::ActionArg;

impl Clone for ActionArg {
    fn clone(&self) -> Self {
        enum Task<'arg> {
            Visit(&'arg ActionArg),
            Optional { child_count: usize },
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(ActionArg::Token { kind, text, pos }) => {
                    values.push(ActionArg::Token {
                        kind: kind.clone(),
                        text: text.clone(),
                        pos: *pos,
                    });
                },
                Task::Visit(ActionArg::Ident { name, pos }) => {
                    values.push(ActionArg::Ident { name: name.clone(), pos: *pos });
                },
                Task::Visit(ActionArg::Term { value, type_name }) => {
                    values.push(ActionArg::Term { value: Arc::clone(value), type_name });
                },
                Task::Visit(ActionArg::BinderScope(handle)) => {
                    values.push(ActionArg::BinderScope(handle.clone()));
                },
                Task::Visit(ActionArg::Collection { value, type_name }) => {
                    values.push(ActionArg::Collection { value: Arc::clone(value), type_name });
                },
                Task::Visit(ActionArg::CollectionId(id)) => {
                    values.push(ActionArg::CollectionId(*id));
                },
                Task::Visit(ActionArg::Predicate(value)) => {
                    values.push(ActionArg::Predicate(Arc::clone(value)));
                },
                Task::Visit(ActionArg::Optional(Some(args))) => {
                    tasks.push(Task::Optional { child_count: args.len() });
                    for child in args.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::Visit(ActionArg::Optional(None)) => {
                    values.push(ActionArg::Optional(None));
                },
                Task::Visit(ActionArg::GuestBody(body)) => {
                    values.push(ActionArg::GuestBody(Arc::clone(body)));
                },
                Task::Visit(ActionArg::UnsetCollectionValue) => {
                    values.push(ActionArg::UnsetCollectionValue);
                },
                Task::Optional { child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("action-argument clone PDA lost optional children");
                    let args = values.split_off(first);
                    values.push(ActionArg::Optional(Some(args)));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("action-argument clone PDA produced no value")
    }
}

impl ActionArg {
    pub(super) fn into_term_parts(
        self,
    ) -> Result<(Arc<dyn Any + Send + Sync>, &'static str), Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::Term { value, type_name } = &mut *this {
                return Ok((ptr::read(value), *type_name));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }

    pub(super) fn into_collection_parts(self) -> Result<Arc<dyn Any + Send + Sync>, Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::Collection { value, .. } = &mut *this {
                return Ok(ptr::read(value));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }

    pub(super) fn into_predicate_value(self) -> Result<Arc<dyn Any + Send + Sync>, Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::Predicate(value) = &mut *this {
                return Ok(ptr::read(value));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }

    pub(super) fn into_optional_value(self) -> Result<Option<Vec<ActionArg>>, Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::Optional(value) = &mut *this {
                return Ok(ptr::read(value));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }

    pub(super) fn into_binder_scope_value(self) -> Result<super::BinderHandle, Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::BinderScope(handle) = &mut *this {
                return Ok(ptr::read(handle));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }

    pub(super) fn into_ident_name_value(self) -> Result<String, Self> {
        let mut this = ManuallyDrop::new(self);
        unsafe {
            if let ActionArg::Ident { name, .. } = &mut *this {
                return Ok(ptr::read(name));
            }
            Err(ManuallyDrop::into_inner(this))
        }
    }
}

impl Drop for ActionArg {
    fn drop(&mut self) {
        let root = mem::replace(self, ActionArg::UnsetCollectionValue);
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            let mut node = ManuallyDrop::new(node);
            unsafe {
                match &mut *node {
                    ActionArg::Token { kind, text, .. } => {
                        std::mem::drop(ptr::read(kind));
                        std::mem::drop(ptr::read(text));
                    },
                    ActionArg::Ident { name, .. } => std::mem::drop(ptr::read(name)),
                    ActionArg::Term { value, .. }
                    | ActionArg::Collection { value, .. }
                    | ActionArg::Predicate(value) => std::mem::drop(ptr::read(value)),
                    ActionArg::BinderScope(handle) => std::mem::drop(ptr::read(handle)),
                    ActionArg::CollectionId(_) | ActionArg::UnsetCollectionValue => {},
                    ActionArg::Optional(value) => {
                        if let Some(args) = ptr::read(value) {
                            work.extend(args);
                        }
                    },
                    ActionArg::GuestBody(body) => std::mem::drop(ptr::read(body)),
                }
            }
        }
    }
}
