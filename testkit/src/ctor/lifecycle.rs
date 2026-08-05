//! Stack-safe lifecycle operations for recursive constructor-tooling models.

use super::FieldSpec;
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
