//! `PathValue` — the value slot of a **value-optional** key/value collection.
//!
//! # Why this type exists
//!
//! A Rholang pathmap literal admits two entry shapes under ONE production:
//!
//! ```text
//! {| k : v |}      the key `k` is bound to the value `v`
//! {| k |}          the key `k` is present and bound to NOTHING
//! ```
//!
//! The second shape is not sugar. Upstream Rholang's pathmap
//! (`pathmap: seq('{|', commaSep($._proc), '|}')`) has *no* value slot at all,
//! so every upstream pathmap entry is of the second shape; MeTTaIL's kv pathmap
//! generalises it. The all-unset case must therefore be expressible, and it must
//! be **distinguishable** from an entry whose value happens to be `Nil`.
//!
//! ## The defect this type retires (#74)
//!
//! Before this type existed, the value slot of a pathmap was simply the key's own
//! type, and a bare entry was materialised by *duplicating the key into the value
//! slot* — `{| k |}` became `{| k : k |}`. That is not a representation of
//! absence; it is a fabricated presence. Concretely it made `{| 1 |}` and
//! `{| 1 : 1 |}` the same term, and it made `Display` print `{|1:1|}` for an
//! input the user wrote as `{|1|}` — so the surface was not even a fixpoint of
//! `parse ∘ display`.
//!
//! Two other encodings were considered and rejected for the same reason:
//!
//! | candidate encoding | why it fails |
//! |---|---|
//! | value := `Nil` | `Nil` is a legitimate user-written value. `{\|k\|}` and `{\|k:Nil\|}` would collide, and `Display` would print `{\|k:Nil\|}`, breaking the fixpoint. |
//! | value := a reserved sentinel term | a sentinel is an inhabitant of the value category, so a program can write it; the collision returns. |
//! | value := the key (the shipped defect) | fabricates a binding the user never wrote. |
//!
//! Every alternative reuses an inhabitant of the value type. Absence is not an
//! inhabitant of the value type — it is a property of the *slot*. `PathValue`
//! makes the slot's optionality part of the type, so the distinction is carried
//! by construction rather than by convention.
//!
//! ## Why it is not `Option<V>`
//!
//! `Option<V>` is structurally identical, and that is exactly the problem: the
//! codebase already uses `Option<V>` throughout for "this field may be absent
//! from the AST", "this lookup may miss", and "this decode may fail". Naming the
//! *language-level* notion separately means a `PathValue::Unset` can never be
//! silently produced by an unrelated `None`, and it gives the term-ops emitters
//! (`semantic_hash`, `Display`, `is_ground`, `term_depth`, `subst`,
//! `match_pattern`) a type to dispatch on that means one thing only.
//!
//! ## The spec already knew
//!
//! `CollectionType::PathMap` has carried `kv_value_optional = true` as a
//! compile-time property of the container kind since 2026-06-27
//! (`macros/src/gen/runtime/wpda_codegen/collection.rs`, `let kv_value_optional =
//! matches!(shape.coll_kind, CollectionType::PathMap)`). The parser has always
//! known that a pathmap's value slot is optional; only the *type* disagreed.
//! `PathValue` is the type catching up to the spec — no DSL change, no
//! `TypeExpr` change, and no `unit` inhabitant added to any grammar.
//!
//! # Semantics
//!
//! | operation | `Unset` | `Set(v)` |
//! |---|---|---|
//! | `Display` | the entry prints as the bare key `k` | the entry prints as `k : v` |
//! | `semantic_hash` | writes tag byte `0` | writes tag byte `1`, then `v` |
//! | `is_ground` | `true` (binds nothing) | `v.is_ground()` |
//! | `term_depth` | `0` | `v.term_depth()` |
//! | `subst` | identity | substitutes into `v` |
//! | pattern match | matches only `Unset` | matches only a `Set` whose payload matches |
//!
//! The `semantic_hash` tag is what makes the three-way distinction *enforceable*
//! rather than merely conventional: `{|k|}`, `{|k:Nil|}` and `{|k:5|}` produce
//! three distinct write streams, so no downstream fingerprint can merge them.
//!
//! # Ordering
//!
//! `Unset < Set(_)` for every `V` — the derived `Ord` on the declaration order
//! below. This is a total order whenever `V: Ord`, which the deterministic
//! containers (`HashMapLit`, `PathMapLit`) require for their `Ord` impls.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::{BoundTerm, Var};
use moniker::{OnBoundFn, OnFreeFn, ScopeState};

/// The value slot of a value-optional key/value collection entry.
///
/// `Unset` means *the key is present and bound to nothing* — the shape written
/// `{| k |}`. It is **not** `Nil`, not a sentinel term, and not the key. See the
/// module documentation for why every such encoding is unsound.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum PathValue<V> {
    /// The key is present; no value was written for it.
    #[default]
    Unset,
    /// The key is present and bound to `V`.
    Set(V),
}

impl<V> PathValue<V> {
    /// The `semantic_hash` discriminator byte. Exposed as a named constant pair
    /// so the generated emitters and any hand-written hasher agree by
    /// construction rather than by both happening to write `0`/`1`.
    pub const TAG_UNSET: u8 = 0;
    /// See [`PathValue::TAG_UNSET`].
    pub const TAG_SET: u8 = 1;

    /// The tag byte for this value, for `semantic_hash` write streams.
    #[inline]
    pub fn semantic_tag(&self) -> u8 {
        match self {
            PathValue::Unset => Self::TAG_UNSET,
            PathValue::Set(_) => Self::TAG_SET,
        }
    }

    /// `true` when no value was written for the key.
    #[inline]
    pub fn is_unset(&self) -> bool {
        matches!(self, PathValue::Unset)
    }

    /// `true` when a value was written for the key.
    #[inline]
    pub fn is_set(&self) -> bool {
        matches!(self, PathValue::Set(_))
    }

    /// Borrow the written value, if any.
    #[inline]
    pub fn as_ref(&self) -> Option<&V> {
        match self {
            PathValue::Unset => None,
            PathValue::Set(v) => Some(v),
        }
    }

    /// Mutably borrow the written value, if any.
    #[inline]
    pub fn as_mut(&mut self) -> Option<&mut V> {
        match self {
            PathValue::Unset => None,
            PathValue::Set(v) => Some(v),
        }
    }

    /// Consume into the written value, if any.
    ///
    /// ⚠ This is a *projection*, not a decode: callers that need to preserve the
    /// unset/`Nil` distinction must match on the variant instead. In particular
    /// no caller may substitute `Nil` for `Unset` — see the module docs.
    #[inline]
    pub fn into_inner(self) -> Option<V> {
        match self {
            PathValue::Unset => None,
            PathValue::Set(v) => Some(v),
        }
    }

    /// Map the written value, preserving `Unset`.
    #[inline]
    pub fn map<W, F: FnOnce(V) -> W>(self, f: F) -> PathValue<W> {
        match self {
            PathValue::Unset => PathValue::Unset,
            PathValue::Set(v) => PathValue::Set(f(v)),
        }
    }

    /// Borrowing counterpart of [`PathValue::map`].
    #[inline]
    pub fn as_ref_map<W, F: FnOnce(&V) -> W>(&self, f: F) -> PathValue<W> {
        match self {
            PathValue::Unset => PathValue::Unset,
            PathValue::Set(v) => PathValue::Set(f(v)),
        }
    }
}

impl<V> From<Option<V>> for PathValue<V> {
    #[inline]
    fn from(opt: Option<V>) -> Self {
        match opt {
            None => PathValue::Unset,
            Some(v) => PathValue::Set(v),
        }
    }
}

impl<V> From<PathValue<V>> for Option<V> {
    #[inline]
    fn from(pv: PathValue<V>) -> Self {
        pv.into_inner()
    }
}

/// `Display` renders ONLY the value part; the enclosing collection's `Display`
/// decides whether to emit the `:` separator (it must not, for `Unset`). An
/// `Unset` therefore renders as the empty string, so a caller that mistakenly
/// concatenates `k`, `":"` and this value produces `k:` — a syntax error the
/// round-trip test catches — rather than the *silently wrong* `k:Nil`.
impl<V: fmt::Display> fmt::Display for PathValue<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathValue::Unset => Ok(()),
            PathValue::Set(v) => v.fmt(f),
        }
    }
}

impl<N, V> BoundTerm<N> for PathValue<V>
where
    N: Clone + PartialEq,
    V: Clone + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PathValue::Unset, PathValue::Unset) => true,
            (PathValue::Set(a), PathValue::Set(b)) => a.term_eq(b),
            // ⚠ `Unset` is α-equivalent to nothing but `Unset`. In particular it
            // is NOT equal to `Set(Nil)` — that collapse is exactly #74.
            _ => false,
        }
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        if let PathValue::Set(v) = self {
            v.close_term(state, on_free);
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        if let PathValue::Set(v) = self {
            v.open_term(state, on_bound);
        }
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        if let PathValue::Set(v) = self {
            v.visit_vars(on_var);
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        if let PathValue::Set(v) = self {
            v.visit_mut_vars(on_var);
        }
    }
}

/// Explicit total order, spelled out rather than derived, so the `Unset < Set`
/// convention is documented at the point that fixes it. (The `#[derive(Ord)]`
/// above would already produce this order from the variant declaration order;
/// this impl is intentionally NOT written — see the derive. The function below
/// exists only as a named, testable statement of the same fact.)
#[inline]
pub fn path_value_order<V: Ord>(a: &PathValue<V>, b: &PathValue<V>) -> Ordering {
    match (a, b) {
        (PathValue::Unset, PathValue::Unset) => Ordering::Equal,
        (PathValue::Unset, PathValue::Set(_)) => Ordering::Less,
        (PathValue::Set(_), PathValue::Unset) => Ordering::Greater,
        (PathValue::Set(x), PathValue::Set(y)) => x.cmp(y),
    }
}

/// Write the `semantic_hash` discriminator for a `PathValue` into `state`.
///
/// The generated collection-literal emitters call this before hashing the
/// payload, so `{|k|}`, `{|k:Nil|}` and `{|k:5|}` are three distinct write
/// streams. Kept here (rather than inlined into codegen) so the tag bytes have
/// exactly one definition.
#[inline]
pub fn write_path_value_tag<V, H: Hasher>(value: &PathValue<V>, state: &mut H) {
    state.write_u8(value.semantic_tag());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unset_is_not_set_of_anything() {
        let unset: PathValue<i32> = PathValue::Unset;
        assert_ne!(unset, PathValue::Set(0));
        assert_ne!(unset, PathValue::Set(i32::MIN));
        assert!(unset.is_unset());
        assert!(!unset.is_set());
    }

    #[test]
    fn tags_are_distinct_and_stable() {
        assert_eq!(PathValue::<i32>::Unset.semantic_tag(), PathValue::<i32>::TAG_UNSET);
        assert_eq!(PathValue::Set(7).semantic_tag(), PathValue::<i32>::TAG_SET);
        assert_ne!(PathValue::<i32>::TAG_UNSET, PathValue::<i32>::TAG_SET);
    }

    #[test]
    fn unset_orders_before_every_set() {
        let unset: PathValue<i32> = PathValue::Unset;
        assert_eq!(path_value_order(&unset, &PathValue::Set(i32::MIN)), Ordering::Less);
        assert_eq!(unset.cmp(&PathValue::Set(i32::MIN)), Ordering::Less);
        assert_eq!(unset.cmp(&PathValue::Unset), Ordering::Equal);
        assert_eq!(PathValue::Set(2).cmp(&PathValue::Set(1)), Ordering::Greater);
    }

    #[test]
    fn display_of_unset_is_empty_not_a_value() {
        assert_eq!(PathValue::<i32>::Unset.to_string(), "");
        assert_eq!(PathValue::Set(42).to_string(), "42");
    }

    #[test]
    fn option_round_trips() {
        let a: PathValue<i32> = None.into();
        assert_eq!(a, PathValue::Unset);
        let b: PathValue<i32> = Some(3).into();
        assert_eq!(b, PathValue::Set(3));
        assert_eq!(Option::<i32>::from(PathValue::Unset), None);
        assert_eq!(Option::<i32>::from(PathValue::Set(3)), Some(3));
    }

    #[test]
    fn map_preserves_unset() {
        assert_eq!(PathValue::<i32>::Unset.map(|v| v + 1), PathValue::Unset);
        assert_eq!(PathValue::Set(1).map(|v| v + 1), PathValue::Set(2));
    }
}
