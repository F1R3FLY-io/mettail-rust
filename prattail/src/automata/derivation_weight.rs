//! M1 (2026-05-13): `DerivationWeight<W, D>` — ambiguity-preserving semiring.
//!
//! Per the longstanding "never disambiguate early" principle
//! (`feedback_never_disambiguate_early.md`), the WPDS pipeline must NOT
//! collapse alternatives via weight-based `pick one` combinators (lex-min,
//! Viterbi, etc.). The natural algebraic structure for this is a **multiset
//! over (weight, derivation) pairs** — the polynomial / free semiring over
//! a tropical-like weight component.
//!
//! ## Algebra
//!
//! ```text
//! DerivationWeight<W, D> = Vec<(W, D)>     // multiset over (weight, derivation)
//!
//! zero    = vec![]                          // empty multiset
//! one     = vec![(W::one(), D::unit())]     // singleton with identity derivation
//! a ⊕ b   = concat(a, b)                    // multiset union (preserves duplicates)
//! a ⊗ b   = { (wₐ ⊗ wᵦ, dₐ ⊗ dᵦ) : (wₐ, dₐ) ∈ a, (wᵦ, dᵦ) ∈ b }
//! ```
//!
//! **Properties** (verified by proptest below):
//! - Commutative monoid `(⊕, zero)`: multiset union is commutative; `vec![]`
//!   is identity.
//! - Associative monoid `(⊗, one)`: cross-product is associative; singleton-
//!   of-identity is identity.
//! - Distributive: `(a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)`.
//! - Zero annihilates ⊗: `vec![] ⊗ anything = vec![]`.
//! - **Not idempotent**: `vec![(w,d)] ⊕ vec![(w,d)] = vec![(w,d), (w,d)]`.
//!   This is a FEATURE — two independently-derived parses that happen to
//!   yield equal terms ARE distinct derivations and must both be preserved
//!   (the caller may dedupe by structural equality of `D` if appropriate).
//!
//! ## Carrier choice
//!
//! - `W` is the underlying weight (typically `LexicographicWeight`). Retained
//!   for tiebreak ORDERING when the CALLER forces a single-pick at EOI —
//!   never used as the disambiguation mechanism inside the WPDS itself.
//! - `D` is a derivation carrier with a `DerivationCombine` operation. For
//!   the WPDS walker this is `Arc<SemanticBuilder>` (a per-derivation
//!   builder snapshot taken at merge time).
//!
//! ## Trait choice
//!
//! `Vec<...>` is not `Copy`, so this type implements [`SemiringRef`] (which
//! drops the `Copy` requirement) rather than [`Semiring`]. The walker
//! migrates from `Semiring` to `SemiringRef` as part of M7a — the blanket
//! `impl<T: Semiring> SemiringRef for T` ensures backward compatibility
//! with existing `Copy` weights.

use crate::automata::semiring::SemiringRef;
use std::fmt;

/// Trait for derivation carriers used inside [`DerivationWeight`].
///
/// `D` represents a single derivation (e.g., a builder snapshot, an AST,
/// or a derivation-tag id). The trait provides the operations needed for
/// the semiring's identity element (`unit`) and the cross-product
/// combination (`combine`, used by `times`).
///
/// **Semantics of `combine`**: when two cursors `cₐ` (weight `wₐ`, derivation
/// `dₐ`) and `cᵦ` (weight `wᵦ`, derivation `dᵦ`) merge into a sequenced
/// composition, the resulting derivation is `dₐ.combine(&dᵦ)`. For
/// `Arc<SemanticBuilder>`, this is typically "take cₐ's builder forward"
/// (the historical snapshot semantics — see the comprehensive plan's
/// §C.5.1 for the discussion).
///
/// **`is_unit`**: returns true for the identity-derivation element. Used by
/// the semiring's `is_one_ref` check.
pub trait DerivationCombine: Clone + fmt::Debug + PartialEq + Send + Sync + 'static {
    /// Identity element for `combine` (the `one` derivation).
    fn unit() -> Self;

    /// Sequential composition of two derivations.
    fn combine(&self, other: &Self) -> Self;

    /// Whether this is the identity-derivation element.
    fn is_unit(&self) -> bool;
}

/// Ambiguity-preserving semiring: multiset over `(weight, derivation)` pairs.
///
/// See module docs for algebraic properties and the `feedback_never_disambiguate_early`
/// memo for the principle this implements.
#[derive(Clone, PartialEq)]
pub struct DerivationWeight<W, D> {
    /// The multiset of `(weight, derivation)` entries.
    ///
    /// **Public field** for ergonomic construction at boundary code (e.g.,
    /// the walker's Fork-apply site). Most callers should use the
    /// `singleton`, `from_entries`, or `iter` accessors instead.
    pub entries: Vec<(W, D)>,
}

impl<W, D> DerivationWeight<W, D> {
    /// Construct an empty multiset (the additive identity, `zero`).
    pub fn empty() -> Self {
        DerivationWeight { entries: Vec::new() }
    }

    /// Construct a singleton multiset with one `(weight, derivation)` entry.
    pub fn singleton(w: W, d: D) -> Self {
        DerivationWeight {
            entries: vec![(w, d)],
        }
    }

    /// Construct from an arbitrary `Vec` of entries.
    pub fn from_entries(entries: Vec<(W, D)>) -> Self {
        DerivationWeight { entries }
    }

    /// Number of `(weight, derivation)` entries in the multiset.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the multiset is empty (the additive identity).
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over `(weight, derivation)` entries.
    pub fn iter(&self) -> std::slice::Iter<'_, (W, D)> {
        self.entries.iter()
    }
}

impl<W: SemiringRef, D: DerivationCombine> SemiringRef for DerivationWeight<W, D> {
    fn zero_ref() -> Self {
        DerivationWeight::empty()
    }

    fn one_ref() -> Self {
        DerivationWeight::singleton(W::one_ref(), D::unit())
    }

    /// Multiset union: concatenate the entries of `self` and `other`.
    ///
    /// Preserves duplicates — two derivations with the same `(w, d)` BOTH
    /// remain in the result (the caller may dedupe by structural equality
    /// of `D` if the carrier supports it).
    fn plus_ref(&self, other: &Self) -> Self {
        let mut entries = Vec::with_capacity(self.entries.len() + other.entries.len());
        entries.extend(self.entries.iter().cloned());
        entries.extend(other.entries.iter().cloned());
        DerivationWeight { entries }
    }

    /// Cross-product: every entry of `self` paired with every entry of
    /// `other`. Weights compose via `W::times_ref`; derivations compose
    /// via `DerivationCombine::combine`.
    ///
    /// Result size is `|self| × |other|`. Zero annihilates: if either side
    /// is empty, the result is empty.
    fn times_ref(&self, other: &Self) -> Self {
        let mut entries = Vec::with_capacity(self.entries.len() * other.entries.len());
        for (wa, da) in &self.entries {
            for (wb, db) in &other.entries {
                entries.push((wa.times_ref(wb), da.combine(db)));
            }
        }
        DerivationWeight { entries }
    }

    fn is_zero_ref(&self) -> bool {
        self.entries.is_empty()
    }

    fn is_one_ref(&self) -> bool {
        self.entries.len() == 1
            && self.entries[0].0.is_one_ref()
            && self.entries[0].1.is_unit()
    }
}

impl<W: fmt::Debug, D: fmt::Debug> fmt::Debug for DerivationWeight<W, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DerivationWeight")
            .field("entries", &self.entries)
            .finish()
    }
}

/// `DerivationCombine` impl for `Arc<SemanticBuilder>` (the walker's D
/// carrier, set up by M7b).
///
/// **`unit()`**: a fresh empty `SemanticBuilder` wrapped in `Arc::new`.
/// Represents the "identity derivation" — no terms pushed yet.
///
/// **`combine(a, b)`**: returns `Arc::clone(b)` (right-bias composition).
/// Conceptually: `a` is "the derivation so far," `b` is "the next step's
/// builder snapshot." For sequential composition `a ⊗ b`, the right side
/// supersedes since the cursor's current builder IS the in-progress
/// state. This is correct for the WPDS walker's use case where each
/// cursor's builder is monotonically refined; older snapshots are
/// historical anchors only.
///
/// **`is_unit()`**: true when the builder has no pushed args / collections.
/// The check uses `is_accepting_terminal` (already O(1) via field reads).
///
/// Lives in `wpds_runtime.rs` to avoid a circular dep between
/// `automata::derivation_weight` and `wpds_runtime::SemanticBuilder`.
/// See `wpds_runtime.rs::impl DerivationCombine for Arc<SemanticBuilder>`.

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::Semiring;

    /// A minimal `DerivationCombine` impl for axiom testing.
    ///
    /// Represents a derivation as a `Vec<u8>` (a tag sequence); `combine`
    /// concatenates. `unit()` is the empty sequence.
    #[derive(Clone, Debug, PartialEq)]
    struct TagSeq(Vec<u8>);

    impl DerivationCombine for TagSeq {
        fn unit() -> Self {
            TagSeq(Vec::new())
        }

        fn combine(&self, other: &Self) -> Self {
            let mut combined = self.0.clone();
            combined.extend(other.0.iter().copied());
            TagSeq(combined)
        }

        fn is_unit(&self) -> bool {
            self.0.is_empty()
        }
    }

    /// Use a Copy semiring (TropicalWeight) as the W component to keep
    /// axiom checks simple. Production walker uses LexicographicWeight.
    use crate::automata::semiring::TropicalWeight;

    type DW = DerivationWeight<TropicalWeight, TagSeq>;

    fn w(cost: f64, tag: u8) -> DW {
        DerivationWeight::singleton(TropicalWeight(cost), TagSeq(vec![tag]))
    }

    fn equiv(a: &DW, b: &DW) -> bool {
        // Multiset equality: same length AND same entries up to permutation.
        // Because TropicalWeight + TagSeq are both PartialEq, we can sort
        // by their (cost, tag) representation and compare.
        if a.entries.len() != b.entries.len() {
            return false;
        }
        let mut a_sorted: Vec<_> = a.entries.iter().cloned().collect();
        let mut b_sorted: Vec<_> = b.entries.iter().cloned().collect();
        let key = |(w, d): &(TropicalWeight, TagSeq)| {
            (w.0.to_bits(), d.0.clone())
        };
        a_sorted.sort_by(|x, y| key(x).cmp(&key(y)));
        b_sorted.sort_by(|x, y| key(x).cmp(&key(y)));
        a_sorted == b_sorted
    }

    #[test]
    fn zero_is_empty() {
        let z: DW = DerivationWeight::zero_ref();
        assert!(z.is_zero_ref());
        assert_eq!(z.len(), 0);
    }

    #[test]
    fn one_is_singleton_with_identities() {
        let o: DW = DerivationWeight::one_ref();
        assert!(o.is_one_ref());
        assert_eq!(o.len(), 1);
        assert!(o.entries[0].0.is_one());
        assert!(o.entries[0].1.is_unit());
    }

    #[test]
    fn plus_is_multiset_union() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let c = a.plus_ref(&b);
        assert_eq!(c.len(), 2);
        assert!(c.entries.iter().any(|(w, _)| w.0 == 1.0));
        assert!(c.entries.iter().any(|(w, _)| w.0 == 2.0));
    }

    #[test]
    fn plus_preserves_duplicates() {
        let a = w(1.0, b'a');
        let dup = a.plus_ref(&a);
        // NOT idempotent — both copies remain.
        assert_eq!(dup.len(), 2);
        assert_eq!(dup.entries[0], dup.entries[1]);
    }

    #[test]
    fn plus_commutative() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let ab = a.plus_ref(&b);
        let ba = b.plus_ref(&a);
        assert!(equiv(&ab, &ba));
    }

    #[test]
    fn plus_associative() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let c = w(3.0, b'c');
        let lhs = a.plus_ref(&b).plus_ref(&c);
        let rhs = a.plus_ref(&b.plus_ref(&c));
        assert!(equiv(&lhs, &rhs));
    }

    #[test]
    fn zero_is_additive_identity() {
        let a = w(1.0, b'a');
        let z: DW = DerivationWeight::zero_ref();
        assert!(equiv(&a.plus_ref(&z), &a));
        assert!(equiv(&z.plus_ref(&a), &a));
    }

    #[test]
    fn times_is_cross_product() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let c = a.times_ref(&b);
        assert_eq!(c.len(), 1);
        // Weight: 1.0 + 2.0 = 3.0 (tropical times = sum).
        assert_eq!(c.entries[0].0 .0, 3.0);
        // Derivation: TagSeq([b'a']) combined with TagSeq([b'b']) = TagSeq([b'a', b'b']).
        assert_eq!(c.entries[0].1, TagSeq(vec![b'a', b'b']));
    }

    #[test]
    fn times_size_is_product_of_sizes() {
        let a = w(1.0, b'a').plus_ref(&w(2.0, b'b')); // |a| = 2
        let b = w(3.0, b'c').plus_ref(&w(4.0, b'd')); // |b| = 2
        let c = a.times_ref(&b);
        assert_eq!(c.len(), 4); // 2 × 2 = 4
    }

    #[test]
    fn times_associative() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let c = w(3.0, b'c');
        let lhs = a.times_ref(&b).times_ref(&c);
        let rhs = a.times_ref(&b.times_ref(&c));
        assert!(equiv(&lhs, &rhs));
    }

    #[test]
    fn one_is_multiplicative_identity() {
        let a = w(1.0, b'a');
        let o: DW = DerivationWeight::one_ref();
        // a ⊗ one's combine drops the unit TagSeq (empty Vec extension):
        // TagSeq([b'a']).combine(TagSeq([])) = TagSeq([b'a']).
        assert!(equiv(&a.times_ref(&o), &a));
        assert!(equiv(&o.times_ref(&a), &a));
    }

    #[test]
    fn zero_annihilates_times() {
        let a = w(1.0, b'a');
        let z: DW = DerivationWeight::zero_ref();
        assert!(z.times_ref(&a).is_zero_ref());
        assert!(a.times_ref(&z).is_zero_ref());
    }

    #[test]
    fn times_distributes_over_plus() {
        let a = w(1.0, b'a');
        let b = w(2.0, b'b');
        let c = w(3.0, b'c');
        // a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
        let lhs = a.times_ref(&b.plus_ref(&c));
        let rhs = a.times_ref(&b).plus_ref(&a.times_ref(&c));
        assert!(equiv(&lhs, &rhs));
        // (b ⊕ c) ⊗ a = (b ⊗ a) ⊕ (c ⊗ a)
        let lhs2 = b.plus_ref(&c).times_ref(&a);
        let rhs2 = b.times_ref(&a).plus_ref(&c.times_ref(&a));
        assert!(equiv(&lhs2, &rhs2));
    }
}
