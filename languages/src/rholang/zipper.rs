//! Testable literal carriers for Rholang read/write zippers.
//!
//! Executable zipper semantics live in f1r3node's native `EPathMap` method table. These compact
//! carriers remain because the generated AST and structural receive matcher can represent zipper
//! literals without duplicating PathMap operations in the language crate.

use std::fmt;

use mettail_runtime::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

use super::pathmap::ProcPathMap;
use super::Proc;

/// Immutable read-zipper literal: underlying trie literal plus encoded focus path.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ReadZipperLit(pub ProcPathMap, pub Vec<u8>);

/// Immutable write-zipper literal: underlying trie literal plus encoded focus path.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct WriteZipperLit(pub ProcPathMap, pub Vec<u8>);

macro_rules! impl_zipper_bound_term {
    ($carrier:ty) => {
        impl<N> BoundTerm<N> for $carrier
        where
            N: Clone + PartialEq,
            Proc: BoundTerm<N>,
        {
            fn term_eq(&self, other: &Self) -> bool {
                self.0.term_eq(&other.0)
            }

            fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
                self.0.close_term(state, on_free);
            }

            fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
                self.0.open_term(state, on_bound);
            }

            fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
                self.0.visit_vars(on_var);
            }

            fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
                self.0.visit_mut_vars(on_var);
            }
        }
    };
}

impl_zipper_bound_term!(ReadZipperLit);
impl_zipper_bound_term!(WriteZipperLit);

impl fmt::Display for ReadZipperLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "readZipper@{}", self.1.len())
    }
}

impl fmt::Display for WriteZipperLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "writeZipper@{}", self.1.len())
    }
}
