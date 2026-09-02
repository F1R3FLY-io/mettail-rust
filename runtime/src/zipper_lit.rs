//! Structural read/write zipper literal carriers.
//!
//! A zipper literal is the product of a homogeneous [`PathMapLit`] context and
//! an exact focus path.  The access mode belongs to the carrier type, while the
//! context and focus remain ordinary closed data.  Keeping this product in the
//! language-neutral runtime lets every generated language describe it by the
//! same carrier algebra instead of teaching generators Rholang-specific names.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use moniker::{BoundTerm, OnBoundFn, OnFreeFn, ScopeState, Var};

use crate::PathMapLit;

/// Immutable read-zipper literal: a structural context plus its encoded focus.
#[derive(Clone, Debug)]
pub struct ReadZipperLit<K, V>(pub PathMapLit<K, V>, pub Vec<u8>);

/// Immutable write-zipper literal: a structural context plus its encoded focus.
#[derive(Clone, Debug)]
pub struct WriteZipperLit<K, V>(pub PathMapLit<K, V>, pub Vec<u8>);

macro_rules! impl_zipper_lit {
    ($carrier:ident, $display_name:literal) => {
        impl<K, V> Default for $carrier<K, V> {
            fn default() -> Self {
                Self(PathMapLit::default(), Vec::new())
            }
        }

        impl<K, V> PartialEq for $carrier<K, V>
        where
            K: Eq + Hash,
            V: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0 && self.1 == other.1
            }
        }

        impl<K, V> Eq for $carrier<K, V>
        where
            K: Eq + Hash,
            V: Eq,
        {
        }

        impl<K, V> PartialOrd for $carrier<K, V>
        where
            K: Ord + Eq + Hash,
            V: Ord,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<K, V> Ord for $carrier<K, V>
        where
            K: Ord + Eq + Hash,
            V: Ord,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                self.0.cmp(&other.0).then_with(|| self.1.cmp(&other.1))
            }
        }

        impl<K, V> Hash for $carrier<K, V>
        where
            K: Hash + Ord,
            V: Hash + Ord,
        {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.0.hash(state);
                self.1.hash(state);
            }
        }

        impl<N, K, V> BoundTerm<N> for $carrier<K, V>
        where
            N: Clone + PartialEq,
            K: Clone + Eq + Hash + BoundTerm<N>,
            V: Clone + BoundTerm<N>,
        {
            fn term_eq(&self, other: &Self) -> bool {
                self.0.term_eq(&other.0) && self.1 == other.1
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

        impl<K, V> fmt::Display for $carrier<K, V> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($display_name, "@{}"), self.1.len())
            }
        }
    };
}

impl_zipper_lit!(ReadZipperLit, "readZipper");
impl_zipper_lit!(WriteZipperLit, "writeZipper");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn focus_is_part_of_structural_term_equality() {
        let left = ReadZipperLit::<String, String>(PathMapLit::Empty, vec![1]);
        let right = ReadZipperLit::<String, String>(PathMapLit::Empty, vec![2]);

        assert!(!BoundTerm::<String>::term_eq(&left, &right));
        assert_ne!(left, right);
    }

    #[test]
    fn access_modes_are_distinct_types_with_the_same_structural_product() {
        let read = ReadZipperLit::<String, String>(PathMapLit::Empty, vec![1, 2]);
        let write = WriteZipperLit::<String, String>(PathMapLit::Empty, vec![1, 2]);

        assert_eq!(read.to_string(), "readZipper@2");
        assert_eq!(write.to_string(), "writeZipper@2");
    }
}
