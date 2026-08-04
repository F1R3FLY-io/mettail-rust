//! Minimal generated-AST carrier for executable checks of the production formula PDA source.
//!
//! The full generated `languages` crate exceeds the local 4 GiB code-generation envelope. This
//! module supplies every constructor read by the formula classifier while importing the exact
//! production implementation with `#[path]`; neither its traversal nor its reductions are copied.

#![allow(dead_code)]

use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Bool {
    BoolLit(bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parts(Vec<Proc>);

impl Parts {
    pub fn new(parts: impl IntoIterator<Item = Proc>) -> Self {
        Self(parts.into_iter().collect())
    }

    pub fn iter_elements(&self) -> impl Iterator<Item = &Proc> {
        self.0.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proc {
    CastBool(Arc<Bool>),
    And(Arc<Proc>, Arc<Proc>),
    Or(Arc<Proc>, Arc<Proc>),
    Not(Arc<Proc>),
    Implies(Arc<Proc>, Arc<Proc>),
    SpatialPPar(Arc<Proc>, Arc<Proc>),
    PParInfix(Arc<Proc>, Arc<Proc>),
    PPar(Parts),
    PZero,
    Term(i64),
}

impl Proc {
    pub fn match_pattern(&self, pattern: &Self) -> Option<()> {
        (self == pattern).then_some(())
    }
}

pub mod runtime {
    use super::Proc;

    pub fn canon_for_term_equality(term: &Proc) -> Proc {
        term.clone()
    }
}

#[path = "../../../languages/src/rholang/formula.rs"]
pub mod formula;
