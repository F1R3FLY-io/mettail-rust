//! Original declaration-preorder worklist over borrowed parameter observations.
//!
//! Optional groups change the inherited flag without yielding a leaf. Children
//! are reverse-pushed onto the same explicit stack used by the macro iterator;
//! no recursive projection, type traversal, or declaration reordering is needed.

pub use mettail_grammar_core::{TermParamObservation, TermParamReader};

/// A non-grouping term parameter, with the variant-specific fields exposed by type.
#[derive(Clone, Copy)]
pub enum TermParamLeafKind<P, N, T> {
    Simple { param: P, name: N, ty: T },
    GuardBody { param: P, name: N },
    Abstraction { param: P, binder: N, body: N, ty: T },
    MultiAbstraction { param: P, binder: N, body: N, ty: T },
}

impl<P, N, T> TermParamLeafKind<P, N, T> {
    /// Return the original authored parameter handle, not a reconstructed node.
    pub fn param(self) -> P {
        match self {
            Self::Simple { param, .. }
            | Self::GuardBody { param, .. }
            | Self::Abstraction { param, .. }
            | Self::MultiAbstraction { param, .. } => param,
        }
    }
}

/// One non-grouping term parameter encountered in declaration preorder.
#[derive(Clone, Copy)]
pub struct TermParamLeaf<P, N, T> {
    pub kind: TermParamLeafKind<P, N, T>,
    /// True once the path to this leaf has entered an `Optional` group.
    pub is_optional: bool,
}

/// Stack-safe declaration-order traversal over the leaves of nested term
/// parameters. `Optional` is structural and therefore does not itself yield an
/// item; each enclosed leaf is yielded with `is_optional = true`.
pub struct TermParamLeaves<'syntax, R: TermParamReader<'syntax>> {
    reader: &'syntax R,
    work: Vec<(R::Param, bool)>,
}

impl<'syntax, R: TermParamReader<'syntax>> TermParamLeaves<'syntax, R> {
    pub fn new(reader: &'syntax R, params: R::Parameters, is_optional: bool) -> Self {
        Self {
            reader,
            work: (0..reader.params_len(params))
                .rev()
                .map(|index| {
                    (
                        reader
                            .param_at(params, index)
                            .expect("parameter index is in bounds"),
                        is_optional,
                    )
                })
                .collect(),
        }
    }
}

impl<'syntax, R: TermParamReader<'syntax>> Iterator for TermParamLeaves<'syntax, R> {
    type Item = TermParamLeaf<R::Param, R::Name, R::Type>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((param, is_optional)) = self.work.pop() {
            if let TermParamObservation::Optional { params } = self.reader.param(param) {
                self.work
                    .extend((0..self.reader.params_len(params)).rev().map(|index| {
                        (
                            self.reader
                                .param_at(params, index)
                                .expect("parameter index is in bounds"),
                            true,
                        )
                    }));
                continue;
            }
            let kind = match self.reader.param(param) {
                TermParamObservation::Simple { name, ty } => {
                    TermParamLeafKind::Simple { param, name, ty }
                },
                TermParamObservation::GuardBody { name } => {
                    TermParamLeafKind::GuardBody { param, name }
                },
                TermParamObservation::Abstraction { binder, body, ty } => {
                    TermParamLeafKind::Abstraction { param, binder, body, ty }
                },
                TermParamObservation::MultiAbstraction { binder, body, ty } => {
                    TermParamLeafKind::MultiAbstraction { param, binder, body, ty }
                },
                TermParamObservation::Optional { .. } => continue,
            };
            return Some(TermParamLeaf { kind, is_optional });
        }
        None
    }
}
