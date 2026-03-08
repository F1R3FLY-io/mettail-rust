//! Tensor product of semirings.
//!
//! The tensor product `S1 ⊗ S2` of two semirings combines two independent
//! analyses into a single pass. Unlike [`ProductWeight<S1, S2>`] (which applies
//! both analyses component-wise and independently), the tensor product allows
//! *interaction* between the two analyses via a bilinear map.
//!
//! # Algebraic Definition
//!
//! Given semirings `(S1, ⊕₁, ⊗₁, 0₁, 1₁)` and `(S2, ⊕₂, ⊗₂, 0₂, 1₂)`,
//! the tensor product semiring `S1 ⊗ S2` has elements that are formal sums of
//! elementary tensors:
//!
//! ```text
//!   Σᵢ  a_i ⊗ b_i     where a_i ∈ S1, b_i ∈ S2
//! ```
//!
//! with operations:
//!
//! - **Plus** (⊕): concatenation of term lists, then simplification
//! - **Times** (⊗): all pairwise products via bilinearity:
//!   `(Σᵢ aᵢ ⊗ bᵢ) ⊗ (Σⱼ cⱼ ⊗ dⱼ) = Σᵢⱼ (aᵢ ⊗₁ cⱼ) ⊗ (bᵢ ⊗₂ dⱼ)`
//! - **Zero**: empty sum (no terms)
//! - **One**: `1₁ ⊗ 1₂` (single elementary tensor of identities)
//!
//! # Difference from `ProductWeight`
//!
//! | Property            | `ProductWeight<S1, S2>`     | `TensorWeight<S1, S2>`          |
//! |---------------------|-----------------------------|---------------------------------|
//! | Representation      | Single pair `(s1, s2)`      | Sum of pairs `Σ (s1_i, s2_i)`  |
//! | Plus                | Component-wise              | Union of term lists + merge     |
//! | Times               | Component-wise              | Bilinear (all pairwise)         |
//! | Interaction         | None (independent)          | Cross-analysis correlation      |
//! | Projections         | Trivial (`left`/`right`)    | Marginalizes: `Σ s1_i` or `Σ s2_i` |
//!
//! # Capacity
//!
//! To satisfy the `Copy` bound required by the [`Semiring`] trait, terms are
//! stored in a fixed-capacity inline array of up to [`MAX_TENSOR_TERMS`] (8)
//! elementary tensors. Simplification (merging terms with equal first
//! components) keeps the term count manageable. If capacity is exceeded during
//! an operation, the result is truncated to the first `MAX_TENSOR_TERMS` terms
//! after simplification — a sound over-approximation for analysis purposes.
//!
//! # Applications
//!
//! - **Cost + provenance**: `TropicalWeight ⊗ CountingWeight` tracks which
//!   cost levels contribute how many derivations (richer than ProductWeight's
//!   independent `(best_cost, total_count)`).
//! - **Reachability + cost**: `BooleanWeight ⊗ TropicalWeight` correlates
//!   reachability with cost structure.
//! - **Multi-pass fusion**: Combine two WFST analyses (e.g., disambiguation +
//!   error recovery scoring) into a single automaton traversal.

use std::fmt;

use crate::automata::semiring::{Semiring, StarSemiring};

// ══════════════════════════════════════════════════════════════════════════════
// Constants
// ══════════════════════════════════════════════════════════════════════════════

/// Maximum number of elementary tensor terms in a `TensorWeight`.
///
/// This bound exists to satisfy the `Copy` requirement of the `Semiring` trait.
/// Eight terms suffice for most practical analyses; after simplification
/// (merging terms with equal first components), the effective capacity is
/// often much larger than the raw limit suggests.
pub const MAX_TENSOR_TERMS: usize = 8;

/// Maximum iteration count for the `StarSemiring::star()` approximation.
///
/// `star(x) = Σ_{k=0}^{STAR_ITERATION_LIMIT} x^k`. The limit prevents
/// divergence while providing a reasonable approximation for most analyses.
const STAR_ITERATION_LIMIT: usize = 32;

// ══════════════════════════════════════════════════════════════════════════════
// TensorWeight
// ══════════════════════════════════════════════════════════════════════════════

/// Tensor product semiring element: a formal sum of elementary tensors.
///
/// Represents `Σᵢ w1_i ⊗ w2_i` as a fixed-capacity inline array of pairs.
/// See the [module-level documentation](self) for algebraic details.
#[derive(Clone, Copy)]
pub struct TensorWeight<W1: Semiring, W2: Semiring> {
    /// Elementary tensor terms stored inline. Only the first `len` entries
    /// are meaningful; the rest are padding filled with `(W1::zero(), W2::zero())`.
    terms: [(W1, W2); MAX_TENSOR_TERMS],
    /// Number of active terms. Invariant: `len <= MAX_TENSOR_TERMS`.
    len: usize,
}

// ── Constructors ─────────────────────────────────────────────────────────────

impl<W1: Semiring, W2: Semiring> TensorWeight<W1, W2> {
    /// Create a single elementary tensor `w1 ⊗ w2`.
    #[inline]
    pub fn elementary(w1: W1, w2: W2) -> Self {
        let mut terms = [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS];
        terms[0] = (w1, w2);
        TensorWeight { terms, len: 1 }
    }

    /// Create a tensor weight from a slice of elementary tensor pairs.
    ///
    /// If `pairs.len() > MAX_TENSOR_TERMS`, the result is simplified first,
    /// and if it still exceeds capacity, it is truncated.
    pub fn from_pairs(pairs: &[(W1, W2)]) -> Self {
        let mut tw = TensorWeight {
            terms: [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS],
            len: 0,
        };
        let limit = pairs.len().min(MAX_TENSOR_TERMS);
        for i in 0..limit {
            tw.terms[i] = pairs[i];
        }
        tw.len = limit;
        // If the input was oversized, simplify to try to fit; if still over,
        // the truncation already happened above.
        if pairs.len() > MAX_TENSOR_TERMS {
            tw.simplify_in_place();
        }
        tw
    }

    /// Number of active elementary tensor terms.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether this tensor weight has zero terms.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Iterate over the active elementary tensor terms.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &(W1, W2)> {
        self.terms[..self.len].iter()
    }

    /// Get the active terms as a slice.
    #[inline]
    pub fn as_slice(&self) -> &[(W1, W2)] {
        &self.terms[..self.len]
    }
}

// ── Simplification ───────────────────────────────────────────────────────────

impl<W1: Semiring, W2: Semiring> TensorWeight<W1, W2> {
    /// Simplify by merging terms with equal first components.
    ///
    /// For each group of terms `(w1, w2_i)` sharing the same `w1`, replace
    /// them with a single term `(w1, Σ w2_i)`. This reduces the term count
    /// while preserving the algebraic value.
    ///
    /// Runs in O(n^2) where n = `self.len`, which is bounded by
    /// `MAX_TENSOR_TERMS` (8), so this is effectively O(1).
    pub fn simplify(mut self) -> Self {
        self.simplify_in_place();
        self
    }

    /// In-place simplification. See [`simplify`](Self::simplify).
    fn simplify_in_place(&mut self) {
        if self.len == 0 {
            return;
        }

        // First pass: remove zero terms. A term (w1, w2) contributes nothing
        // if either component is zero, since by bilinearity:
        //   w1 ⊗ 0₂ = 0  and  0₁ ⊗ w2 = 0
        let mut write = 0;
        for read in 0..self.len {
            if !self.terms[read].0.is_zero() && !self.terms[read].1.is_zero() {
                if write != read {
                    self.terms[write] = self.terms[read];
                }
                write += 1;
            }
        }
        self.len = write;

        if self.len <= 1 {
            return;
        }

        // Second pass: merge terms with equal first components.
        // For each position i, scan forward for matching first components.
        // merged[j] tracks whether term j has already been folded into an
        // earlier term.
        let mut merged = [false; MAX_TENSOR_TERMS];
        let mut out = [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS];
        let mut out_len = 0;

        for i in 0..self.len {
            if merged[i] {
                continue;
            }
            let mut combined_w2 = self.terms[i].1;
            for j in (i + 1)..self.len {
                if !merged[j] && self.terms[i].0 == self.terms[j].0 {
                    combined_w2 = combined_w2.plus(&self.terms[j].1);
                    merged[j] = true;
                }
            }
            if !combined_w2.is_zero() && out_len < MAX_TENSOR_TERMS {
                out[out_len] = (self.terms[i].0, combined_w2);
                out_len += 1;
            }
        }

        self.terms = out;
        self.len = out_len;
    }
}

// ── Projections ──────────────────────────────────────────────────────────────

impl<W1: Semiring, W2: Semiring> TensorWeight<W1, W2> {
    /// Project onto the left (first) component: marginalize out W2.
    ///
    /// Returns `Σᵢ w1_i` (summing all first components via W1's plus).
    pub fn project_left(&self) -> W1 {
        let mut result = W1::zero();
        for i in 0..self.len {
            result = result.plus(&self.terms[i].0);
        }
        result
    }

    /// Project onto the right (second) component: marginalize out W1.
    ///
    /// Returns `Σᵢ w2_i` (summing all second components via W2's plus).
    pub fn project_right(&self) -> W2 {
        let mut result = W2::zero();
        for i in 0..self.len {
            result = result.plus(&self.terms[i].1);
        }
        result
    }

    /// Conditional projection: sum of left components where the right
    /// component equals the given value.
    ///
    /// Returns `Σ { w1_i | w2_i == w2 }`.
    pub fn left_given_right(&self, w2: &W2) -> W1 {
        let mut result = W1::zero();
        for i in 0..self.len {
            if self.terms[i].1 == *w2 {
                result = result.plus(&self.terms[i].0);
            }
        }
        result
    }

    /// Conditional projection: sum of right components where the left
    /// component equals the given value.
    ///
    /// Returns `Σ { w2_i | w1_i == w1 }`.
    pub fn right_given_left(&self, w1: &W1) -> W2 {
        let mut result = W2::zero();
        for i in 0..self.len {
            if self.terms[i].0 == *w1 {
                result = result.plus(&self.terms[i].1);
            }
        }
        result
    }
}

// ── Semiring implementation ──────────────────────────────────────────────────

impl<W1: Semiring, W2: Semiring> Semiring for TensorWeight<W1, W2> {
    /// Additive identity: empty sum (no terms).
    #[inline]
    fn zero() -> Self {
        TensorWeight {
            terms: [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS],
            len: 0,
        }
    }

    /// Multiplicative identity: `1₁ ⊗ 1₂`.
    #[inline]
    fn one() -> Self {
        Self::elementary(W1::one(), W2::one())
    }

    /// Semiring addition: union of term lists, then simplification.
    ///
    /// `(Σ aᵢ ⊗ bᵢ) ⊕ (Σ cⱼ ⊗ dⱼ) = Σ aᵢ ⊗ bᵢ  ⊕  Σ cⱼ ⊗ dⱼ`
    ///
    /// After concatenation, [`simplify`](Self::simplify) merges terms with
    /// equal first components.
    fn plus(&self, other: &Self) -> Self {
        let total = self.len + other.len;
        let mut result = TensorWeight {
            terms: [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS],
            len: 0,
        };

        // Copy terms from self.
        let self_count = self.len.min(MAX_TENSOR_TERMS);
        for i in 0..self_count {
            result.terms[i] = self.terms[i];
        }
        result.len = self_count;

        // Copy terms from other (as many as fit).
        let remaining_capacity = MAX_TENSOR_TERMS - result.len;
        let other_count = other.len.min(remaining_capacity);
        for i in 0..other_count {
            result.terms[result.len + i] = other.terms[i];
        }
        result.len += other_count;

        // Simplification is essential: it merges terms with equal first
        // components, freeing capacity. If the raw concatenation exceeded
        // capacity, simplification may recover space. If total > capacity
        // and simplification doesn't reduce enough, we lose precision
        // (truncation) — this is a documented limitation.
        if total > MAX_TENSOR_TERMS || result.len > 1 {
            result.simplify_in_place();
        }

        result
    }

    /// Semiring multiplication: bilinear expansion.
    ///
    /// `(Σ aᵢ ⊗ bᵢ) ⊗ (Σ cⱼ ⊗ dⱼ) = Σᵢⱼ (aᵢ ⊗₁ cⱼ) ⊗ (bᵢ ⊗₂ dⱼ)`
    ///
    /// Generates up to `m * n` terms, then simplifies.
    fn times(&self, other: &Self) -> Self {
        // Zero optimization: if either operand is zero, result is zero.
        if self.len == 0 || other.len == 0 {
            return Self::zero();
        }

        let mut result = TensorWeight {
            terms: [(W1::zero(), W2::zero()); MAX_TENSOR_TERMS],
            len: 0,
        };

        // Generate all pairwise products.
        for i in 0..self.len {
            for j in 0..other.len {
                let w1 = self.terms[i].0.times(&other.terms[j].0);
                let w2 = self.terms[i].1.times(&other.terms[j].1);

                // Skip zero terms early to save capacity. Either component
                // being zero makes the elementary tensor zero by bilinearity.
                if w1.is_zero() || w2.is_zero() {
                    continue;
                }

                if result.len < MAX_TENSOR_TERMS {
                    result.terms[result.len] = (w1, w2);
                    result.len += 1;
                } else {
                    // Capacity full — try simplification to free slots.
                    result.simplify_in_place();
                    if result.len < MAX_TENSOR_TERMS {
                        result.terms[result.len] = (w1, w2);
                        result.len += 1;
                    }
                    // If still full after simplification, this term is lost
                    // (truncation). Documented limitation.
                }
            }
        }

        result.simplify_in_place();
        result
    }

    /// A tensor weight is zero iff it has no non-zero active terms.
    ///
    /// A term is zero if either component is zero (by bilinearity:
    /// `0₁ ⊗ w2 = 0` and `w1 ⊗ 0₂ = 0`).
    #[inline]
    fn is_zero(&self) -> bool {
        if self.len == 0 {
            return true;
        }
        for i in 0..self.len {
            if !self.terms[i].0.is_zero() && !self.terms[i].1.is_zero() {
                return false;
            }
        }
        true
    }

    /// A tensor weight is one iff it is exactly `1₁ ⊗ 1₂`.
    fn is_one(&self) -> bool {
        if self.len != 1 {
            return false;
        }
        self.terms[0].0.is_one() && self.terms[0].1.is_one()
    }

    /// Approximate equality: check that term counts match and all
    /// corresponding terms are approximately equal (after simplification).
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        let a = self.simplify();
        let b = other.simplify();

        if a.len != b.len {
            return false;
        }

        // For each term in a, find a matching term in b.
        let mut matched = [false; MAX_TENSOR_TERMS];
        for i in 0..a.len {
            let mut found = false;
            for j in 0..b.len {
                if !matched[j]
                    && a.terms[i].0.approx_eq(&b.terms[j].0, epsilon)
                    && a.terms[i].1.approx_eq(&b.terms[j].1, epsilon)
                {
                    matched[j] = true;
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        true
    }
}

// ── StarSemiring implementation ──────────────────────────────────────────────

impl<W1: StarSemiring, W2: StarSemiring> StarSemiring for TensorWeight<W1, W2> {
    /// Approximate Kleene star via bounded iteration.
    ///
    /// `star(x) = Σ_{k=0}^{STAR_ITERATION_LIMIT} x^k`
    ///
    /// Iterates until convergence (via `approx_eq`) or the iteration limit
    /// is reached. Each iteration adds `x^k` to the running sum, where
    /// `x^k = x^{k-1} ⊗ x`.
    fn star(&self) -> Self {
        // star(0) = 1 (the empty path always exists).
        if self.is_zero() {
            return Self::one();
        }

        // Accumulator starts at 1 (the x^0 term).
        let mut sum = Self::one();
        // x_power tracks x^k, starting at x^1 = x.
        let mut x_power = *self;

        for _ in 0..STAR_ITERATION_LIMIT {
            let next_sum = sum.plus(&x_power);
            // Convergence check: if adding x^k didn't change the sum,
            // the series has stabilized.
            if next_sum.approx_eq(&sum, 1e-10) {
                return next_sum;
            }
            sum = next_sum;
            x_power = x_power.times(self);
        }

        sum
    }

    /// Kleene plus: `x⁺ = x ⊗ x*`.
    fn plus_star(&self) -> Self {
        self.times(&self.star())
    }
}

// ── Trait implementations ────────────────────────────────────────────────────

impl<W1: Semiring, W2: Semiring> PartialEq for TensorWeight<W1, W2> {
    fn eq(&self, other: &Self) -> bool {
        // Compare simplified forms for canonical equality.
        let a = self.simplify();
        let b = other.simplify();

        if a.len != b.len {
            return false;
        }

        // Order-independent comparison: each term in a must have a match in b.
        let mut matched = [false; MAX_TENSOR_TERMS];
        for i in 0..a.len {
            let mut found = false;
            for j in 0..b.len {
                if !matched[j] && a.terms[i].0 == b.terms[j].0 && a.terms[i].1 == b.terms[j].1 {
                    matched[j] = true;
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        true
    }
}

impl<W1: Semiring, W2: Semiring> fmt::Debug for TensorWeight<W1, W2> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len == 0 {
            return write!(f, "TensorWeight(0)");
        }
        write!(f, "TensorWeight(")?;
        for i in 0..self.len {
            if i > 0 {
                write!(f, " + ")?;
            }
            write!(f, "{:?} \u{2297} {:?}", self.terms[i].0, self.terms[i].1)?;
        }
        write!(f, ")")
    }
}

impl<W1: Semiring + fmt::Display, W2: Semiring + fmt::Display> fmt::Display
    for TensorWeight<W1, W2>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len == 0 {
            return write!(f, "0");
        }
        for i in 0..self.len {
            if i > 0 {
                write!(f, " + ")?;
            }
            write!(f, "{}\u{2297}{}", self.terms[i].0, self.terms[i].1)?;
        }
        Ok(())
    }
}

impl<W1: Semiring, W2: Semiring> Default for TensorWeight<W1, W2> {
    fn default() -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::semiring::{
        BooleanWeight, CountingWeight, ProductWeight, TropicalWeight,
    };

    // Convenience aliases for test readability.
    type TW = TropicalWeight;
    type CW = CountingWeight;
    type BW = BooleanWeight;
    type TensorTC = TensorWeight<TW, CW>;
    type TensorTT = TensorWeight<TW, TW>;
    type TensorBB = TensorWeight<BW, BW>;
    type TensorBC = TensorWeight<BW, CW>;

    // ═════════════════════════════════════════════════════════════════════════
    // Construction tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn elementary_tensor_construction() {
        let t = TensorTC::elementary(TW::new(3.0), CW::new(5));
        assert_eq!(t.len(), 1);
        assert_eq!(t.as_slice()[0], (TW::new(3.0), CW::new(5)));
    }

    #[test]
    fn from_pairs_construction() {
        let pairs = [(TW::new(1.0), CW::new(2)), (TW::new(3.0), CW::new(4))];
        let t = TensorTC::from_pairs(&pairs);
        assert_eq!(t.len(), 2);
        assert_eq!(t.as_slice()[0], (TW::new(1.0), CW::new(2)));
        assert_eq!(t.as_slice()[1], (TW::new(3.0), CW::new(4)));
    }

    #[test]
    fn from_pairs_oversized_truncates() {
        // More than MAX_TENSOR_TERMS pairs — should truncate to capacity.
        let pairs: Vec<(TW, CW)> = (0..16)
            .map(|i| (TW::new(i as f64), CW::new(i + 1)))
            .collect();
        let t = TensorTC::from_pairs(&pairs);
        assert!(t.len() <= MAX_TENSOR_TERMS);
    }

    #[test]
    fn zero_is_empty() {
        let z = TensorTC::zero();
        assert!(z.is_zero());
        assert!(z.is_empty());
        assert_eq!(z.len(), 0);
    }

    #[test]
    fn one_is_single_identity_tensor() {
        let one = TensorTC::one();
        assert!(one.is_one());
        assert_eq!(one.len(), 1);
        assert!(one.as_slice()[0].0.is_one()); // TW::one() = 0.0
        assert!(one.as_slice()[0].1.is_one()); // CW::one() = 1
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Associativity of plus
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn plus_associativity() {
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = TensorTC::elementary(TW::new(3.0), CW::new(4));
        let c = TensorTC::elementary(TW::new(5.0), CW::new(6));

        let lhs = a.plus(&b).plus(&c);
        let rhs = a.plus(&b.plus(&c));
        assert_eq!(lhs, rhs);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Commutativity of plus
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn plus_commutativity() {
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = TensorTC::elementary(TW::new(3.0), CW::new(4));

        assert_eq!(a.plus(&b), b.plus(&a));
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Associativity of times
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn times_associativity() {
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = TensorTC::elementary(TW::new(3.0), CW::new(3));
        let c = TensorTC::elementary(TW::new(2.0), CW::new(4));

        let lhs = a.times(&b).times(&c);
        let rhs = a.times(&b.times(&c));
        assert_eq!(lhs, rhs);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Zero identity for plus
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn zero_is_additive_identity() {
        let a = TensorTC::elementary(TW::new(3.0), CW::new(5));
        let z = TensorTC::zero();

        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: One identity for times
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn one_is_multiplicative_identity() {
        let a = TensorTC::elementary(TW::new(3.0), CW::new(5));
        let one = TensorTC::one();

        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Zero annihilation
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn zero_annihilates_times() {
        let a = TensorTC::elementary(TW::new(3.0), CW::new(5));
        let z = TensorTC::zero();

        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests: Distributivity
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn left_distributivity() {
        // a * (b + c) = a*b + a*c
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = TensorTC::elementary(TW::new(3.0), CW::new(3));
        let c = TensorTC::elementary(TW::new(2.0), CW::new(4));

        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn right_distributivity() {
        // (a + b) * c = a*c + b*c
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = TensorTC::elementary(TW::new(3.0), CW::new(3));
        let c = TensorTC::elementary(TW::new(2.0), CW::new(4));

        let lhs = a.plus(&b).times(&c);
        let rhs = a.times(&c).plus(&b.times(&c));
        assert_eq!(lhs, rhs);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Times distributes correctly over tensor pairs
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn times_bilinear_expansion() {
        // (a1 ⊗ b1 + a2 ⊗ b2) * (c1 ⊗ d1)
        // = (a1*c1) ⊗ (b1*d1) + (a2*c1) ⊗ (b2*d1)
        let lhs = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(3.0), CW::new(4)),
        ]);
        let rhs = TensorTC::elementary(TW::new(0.5), CW::new(3));

        let result = lhs.times(&rhs);

        // Expected:
        // (1.0+0.5) ⊗ (2*3) + (3.0+0.5) ⊗ (4*3) = 1.5 ⊗ 6 + 3.5 ⊗ 12
        let expected = TensorTC::from_pairs(&[
            (TW::new(1.5), CW::new(6)),
            (TW::new(3.5), CW::new(12)),
        ]);
        assert_eq!(result, expected);
    }

    #[test]
    fn times_two_multi_term_tensors() {
        // (a1 ⊗ b1 + a2 ⊗ b2) * (c1 ⊗ d1 + c2 ⊗ d2)
        // = (a1*c1) ⊗ (b1*d1) + (a1*c2) ⊗ (b1*d2)
        //   + (a2*c1) ⊗ (b2*d1) + (a2*c2) ⊗ (b2*d2)
        let x = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(2.0), CW::new(3)),
        ]);
        let y = TensorTC::from_pairs(&[
            (TW::new(0.0), CW::new(1)), // TW::one() = 0.0
            (TW::new(1.0), CW::new(2)),
        ]);

        let result = x.times(&y);
        // Term 1: (1.0+0.0, 2*1) = (1.0, 2)
        // Term 2: (1.0+1.0, 2*2) = (2.0, 4)
        // Term 3: (2.0+0.0, 3*1) = (2.0, 3)
        // Term 4: (2.0+1.0, 3*2) = (3.0, 6)
        // After simplification, terms 2 and 3 both have w1=2.0:
        // merge to (2.0, 4+3) = (2.0, 7)
        // Result: (1.0, 2) + (2.0, 7) + (3.0, 6)
        let expected = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(2.0), CW::new(7)),
            (TW::new(3.0), CW::new(6)),
        ]);
        assert_eq!(result, expected);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Projection tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn project_left_marginalizes_right() {
        let t = TensorTC::from_pairs(&[
            (TW::new(2.0), CW::new(3)),
            (TW::new(5.0), CW::new(7)),
        ]);
        // project_left: TW::plus(2.0, 5.0) = min(2.0, 5.0) = 2.0
        assert_eq!(t.project_left(), TW::new(2.0));
    }

    #[test]
    fn project_right_marginalizes_left() {
        let t = TensorTC::from_pairs(&[
            (TW::new(2.0), CW::new(3)),
            (TW::new(5.0), CW::new(7)),
        ]);
        // project_right: CW::plus(3, 7) = 3 + 7 = 10
        assert_eq!(t.project_right(), CW::new(10));
    }

    #[test]
    fn project_left_of_zero_is_zero() {
        let z = TensorTC::zero();
        assert!(z.project_left().is_zero());
    }

    #[test]
    fn project_right_of_zero_is_zero() {
        let z = TensorTC::zero();
        assert!(z.project_right().is_zero());
    }

    #[test]
    fn project_left_of_one() {
        let one = TensorTC::one();
        assert!(one.project_left().is_one());
    }

    #[test]
    fn project_right_of_one() {
        let one = TensorTC::one();
        assert!(one.project_right().is_one());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Conditional projection tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn left_given_right_filters_correctly() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(5)),
            (TW::new(2.0), CW::new(5)),
            (TW::new(3.0), CW::new(7)),
        ]);
        // Left components where right == 5: TW::plus(1.0, 2.0) = min(1.0, 2.0) = 1.0
        assert_eq!(t.left_given_right(&CW::new(5)), TW::new(1.0));
        // Left components where right == 7: TW(3.0)
        assert_eq!(t.left_given_right(&CW::new(7)), TW::new(3.0));
        // No match: zero
        assert!(t.left_given_right(&CW::new(99)).is_zero());
    }

    #[test]
    fn right_given_left_filters_correctly() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(5)),
            (TW::new(1.0), CW::new(3)),
            (TW::new(2.0), CW::new(7)),
        ]);
        // Right components where left == 1.0: CW::plus(5, 3) = 8
        assert_eq!(t.right_given_left(&TW::new(1.0)), CW::new(8));
        // Right components where left == 2.0: CW(7)
        assert_eq!(t.right_given_left(&TW::new(2.0)), CW::new(7));
        // No match
        assert!(t.right_given_left(&TW::new(99.0)).is_zero());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Simplification tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn simplify_merges_equal_first_components() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(3)),
            (TW::new(1.0), CW::new(5)),
            (TW::new(2.0), CW::new(7)),
        ]);
        let s = t.simplify();
        // Two terms with TW(1.0) merge: CW::plus(3, 5) = 8
        assert_eq!(s.len(), 2);

        // Verify merged value.
        assert_eq!(s.right_given_left(&TW::new(1.0)), CW::new(8));
        assert_eq!(s.right_given_left(&TW::new(2.0)), CW::new(7));
    }

    #[test]
    fn simplify_removes_zero_second_components() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::zero()),
            (TW::new(2.0), CW::new(5)),
        ]);
        let s = t.simplify();
        assert_eq!(s.len(), 1);
        assert_eq!(s.as_slice()[0], (TW::new(2.0), CW::new(5)));
    }

    #[test]
    fn simplify_removes_zero_first_components() {
        // TW::zero() = +inf (tropical zero). A term (0₁, w2) is zero
        // by bilinearity, so it should be stripped.
        let t = TensorTC::from_pairs(&[
            (TW::zero(), CW::new(3)),
            (TW::new(2.0), CW::new(5)),
        ]);
        let s = t.simplify();
        assert_eq!(s.len(), 1);
        assert_eq!(s.as_slice()[0], (TW::new(2.0), CW::new(5)));
    }

    #[test]
    fn simplify_all_zeros_yields_zero() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::zero()),
            (TW::new(2.0), CW::zero()),
        ]);
        let s = t.simplify();
        assert!(s.is_zero());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Comparison with ProductWeight for independent analyses
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn elementary_tensor_times_matches_product_weight_times() {
        // For single elementary tensors, times should match ProductWeight behavior.
        let a1 = TW::new(2.0);
        let b1 = CW::new(3);
        let a2 = TW::new(5.0);
        let b2 = CW::new(4);

        let tensor_result = TensorTC::elementary(a1, b1).times(&TensorTC::elementary(a2, b2));
        let product_result = ProductWeight::new(a1, b1).times(&ProductWeight::new(a2, b2));

        // Tensor: single term (a1*a2, b1*b2) = (7.0, 12)
        assert_eq!(tensor_result.len(), 1);
        assert_eq!(tensor_result.as_slice()[0].0, product_result.left);
        assert_eq!(tensor_result.as_slice()[0].1, product_result.right);
    }

    #[test]
    fn elementary_tensor_plus_differs_from_product_weight_plus() {
        // For plus, tensor keeps both terms while product does component-wise plus.
        let a1 = TW::new(2.0);
        let b1 = CW::new(3);
        let a2 = TW::new(5.0);
        let b2 = CW::new(4);

        let tensor_result = TensorTC::elementary(a1, b1).plus(&TensorTC::elementary(a2, b2));
        let product_result = ProductWeight::new(a1, b1).plus(&ProductWeight::new(a2, b2));

        // Tensor: two terms (2.0, 3) and (5.0, 4) — distinct first components.
        assert_eq!(tensor_result.len(), 2);

        // Product: (min(2,5), 3+4) = (2.0, 7) — single component-wise value.
        assert_eq!(product_result.left, TW::new(2.0));
        assert_eq!(product_result.right, CW::new(7));

        // Tensor projections differ:
        // project_left: min(2.0, 5.0) = 2.0 — same as product left.
        assert_eq!(tensor_result.project_left(), product_result.left);
        // project_right: 3 + 4 = 7 — same as product right.
        assert_eq!(tensor_result.project_right(), product_result.right);

        // But the tensor retains the correlation: "cost 2.0 had count 3,
        // cost 5.0 had count 4" — information lost in ProductWeight.
    }

    #[test]
    fn tensor_retains_correlation_lost_by_product() {
        // Demonstrate that tensor product preserves cross-analysis correlation.
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(10)), // cost 1.0 → 10 derivations
            (TW::new(5.0), CW::new(2)),  // cost 5.0 → 2 derivations
        ]);

        // Query: "how many derivations have cost 1.0?"
        assert_eq!(t.right_given_left(&TW::new(1.0)), CW::new(10));
        // Query: "how many derivations have cost 5.0?"
        assert_eq!(t.right_given_left(&TW::new(5.0)), CW::new(2));

        // ProductWeight loses this: it would give (min(1,5), 10+2) = (1.0, 12).
        // Cannot ask "how many derivations at cost 5.0?" from a ProductWeight.
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Boolean semiring tensor tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn boolean_tensor_semiring_laws() {
        let t = BW::new(true);

        // Use non-trivial elements: (true ⊗ true) is not zero and not one
        // since it equals one in the boolean case. Use counting as second
        // component for a richer test.
        let a = TensorBB::elementary(t, t);
        let z = TensorBB::zero();
        let one = TensorBB::one();

        // Zero identity
        assert_eq!(z.plus(&a), a);
        assert_eq!(a.plus(&z), a);

        // One identity
        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);

        // Zero annihilates
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Plus commutativity with a different element
        let b = TensorBB::elementary(t, t);
        assert_eq!(a.plus(&b), b.plus(&a));
    }

    #[test]
    fn boolean_tensor_zero_second_component_is_zero() {
        let t = BW::new(true);
        let f = BW::new(false);

        // (true ⊗ false) is algebraically zero: w1 ⊗ 0₂ = 0
        let a = TensorBB::elementary(t, f);
        assert!(a.is_zero(), "true ⊗ false should be zero (0₂ annihilates)");

        // (false ⊗ true) is also algebraically zero since false = 0₁
        // but we only strip zero *second* components in simplification.
        // However, is_zero checks all terms for zero second component.
        // Here the second component is true (not zero), so this is NOT
        // the zero element by our simplification rule. But algebraically
        // it should be zero since 0₁ ⊗ w2 = 0 too.
        // For correctness, also strip terms with zero first component.
        let b = TensorBB::elementary(f, t);
        assert!(b.is_zero(), "false ⊗ true should be zero (0₁ annihilates)");
    }

    #[test]
    fn boolean_tensor_times_is_conjunction() {
        let t = BW::new(true);
        let f = BW::new(false);

        // (true ⊗ true) * (true ⊗ true) = (true∧true) ⊗ (true∧true) = true ⊗ true
        let tt = TensorBB::elementary(t, t);
        assert_eq!(tt.times(&tt), tt);

        // (true ⊗ false) * (true ⊗ true) = (true∧true) ⊗ (false∧true) = true ⊗ false
        let tf = TensorBB::elementary(t, f);
        let result = tf.times(&tt);
        // (true, false∧true) = (true, false) — zero second component → zero after simplify
        assert!(result.is_zero());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // BooleanWeight ⊗ CountingWeight tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn boolean_counting_tensor() {
        let t = BW::new(true);

        let a = TensorBC::elementary(t, CW::new(3));
        let b = TensorBC::elementary(t, CW::new(5));

        // Plus: both have first component = true (non-zero), so after
        // simplification they merge: (true, 3+5) = (true, 8)
        let sum = a.plus(&b);
        assert_eq!(sum.len(), 1);
        assert_eq!(sum.project_left(), t);
        assert_eq!(sum.project_right(), CW::new(8));

        // Times: (true∧true, 3*5) = (true, 15)
        let product = a.times(&b);
        assert_eq!(product.len(), 1);
        assert_eq!(product.as_slice()[0], (t, CW::new(15)));
    }

    #[test]
    fn boolean_counting_tensor_zero_first_component() {
        let t = BW::new(true);
        let f = BW::new(false);

        // (false ⊗ CW(5)) is algebraically zero since false = 0₁
        let b = TensorBC::elementary(f, CW::new(5));
        assert!(b.is_zero());

        // (true ⊗ CW(3)) + (false ⊗ CW(5)):
        // The second term is zero, so the sum is just (true, 3)
        let a = TensorBC::elementary(t, CW::new(3));
        let sum = a.plus(&b);
        assert_eq!(sum.project_left(), t);
        assert_eq!(sum.project_right(), CW::new(3));
    }

    // ═════════════════════════════════════════════════════════════════════════
    // TropicalWeight ⊗ TropicalWeight tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn tropical_tropical_tensor_times() {
        // Two cost dimensions: (latency_cost ⊗ space_cost)
        let a = TensorTT::elementary(TW::new(2.0), TW::new(3.0));
        let b = TensorTT::elementary(TW::new(1.0), TW::new(4.0));

        let result = a.times(&b);
        // (2.0+1.0, 3.0+4.0) = (3.0, 7.0)
        assert_eq!(result.len(), 1);
        assert_eq!(result.as_slice()[0], (TW::new(3.0), TW::new(7.0)));
    }

    #[test]
    fn tropical_tropical_tensor_plus() {
        let a = TensorTT::elementary(TW::new(2.0), TW::new(3.0));
        let b = TensorTT::elementary(TW::new(1.0), TW::new(4.0));

        let result = a.plus(&b);
        // Two distinct terms, since first components differ.
        assert_eq!(result.len(), 2);
        // project_left: min(2.0, 1.0) = 1.0
        assert_eq!(result.project_left(), TW::new(1.0));
        // project_right: min(3.0, 4.0) = 3.0
        assert_eq!(result.project_right(), TW::new(3.0));
    }

    #[test]
    fn tropical_tropical_tensor_plus_same_first_merges() {
        // Same first component → merge second components.
        let a = TensorTT::elementary(TW::new(2.0), TW::new(3.0));
        let b = TensorTT::elementary(TW::new(2.0), TW::new(5.0));

        let result = a.plus(&b);
        // After simplification: (2.0, min(3.0, 5.0)) = (2.0, 3.0)
        assert_eq!(result.len(), 1);
        assert_eq!(result.as_slice()[0], (TW::new(2.0), TW::new(3.0)));
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Display / Debug tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn debug_zero_tensor() {
        let z = TensorTC::zero();
        assert_eq!(format!("{:?}", z), "TensorWeight(0)");
    }

    #[test]
    fn debug_elementary_tensor() {
        let t = TensorBB::elementary(BW::new(true), BW::new(false));
        let dbg = format!("{:?}", t);
        assert!(dbg.contains("TensorWeight("));
        assert!(dbg.contains("\u{2297}")); // ⊗ symbol
    }

    #[test]
    fn display_zero_tensor() {
        let z: TensorWeight<BooleanWeight, BooleanWeight> = TensorWeight::zero();
        assert_eq!(format!("{}", z), "0");
    }

    // ═════════════════════════════════════════════════════════════════════════
    // StarSemiring tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn star_of_zero_is_one() {
        let z = TensorBB::zero();
        let s = z.star();
        assert!(s.is_one());
    }

    #[test]
    fn star_of_boolean_tensor() {
        // Boolean star: star(a) = true for all a.
        // For tensor of booleans, star should converge.
        let t = TensorBB::elementary(BW::new(true), BW::new(true));
        let s = t.star();
        // star(true ⊗ true) converges: 1 + (T⊗T) + (T⊗T)^2 + ...
        // = (T⊗T) since boolean is idempotent and T∧T=T, T∨T=T.
        assert!(s.is_one() || s.len() >= 1);
        // The result should project to true on both sides.
        assert_eq!(s.project_left(), BW::new(true));
        assert_eq!(s.project_right(), BW::new(true));
    }

    #[test]
    fn plus_star_of_zero_is_zero() {
        let z = TensorBB::zero();
        let ps = z.plus_star();
        // plus_star(0) = 0 * star(0) = 0 * 1 = 0
        assert!(ps.is_zero());
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Semiring law tests with multi-term tensors
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn distributivity_multi_term() {
        // a * (b + c) = a*b + a*c with multi-term tensors.
        let a = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(2.0), CW::new(1)),
        ]);
        let b = TensorTC::elementary(TW::new(0.5), CW::new(3));
        let c = TensorTC::elementary(TW::new(1.0), CW::new(2));

        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn zero_annihilation_multi_term() {
        let a = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(3.0), CW::new(4)),
        ]);
        let z = TensorTC::zero();

        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn one_identity_multi_term() {
        let a = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(3.0), CW::new(4)),
        ]);
        let one = TensorTC::one();

        assert_eq!(one.times(&a), a);
        assert_eq!(a.times(&one), a);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Copy semantics test
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn tensor_weight_is_copy() {
        let a = TensorTC::elementary(TW::new(1.0), CW::new(2));
        let b = a; // Copy
        let c = a; // Still valid because Copy
        assert_eq!(b, c);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // PartialEq tests (order-independent after simplification)
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn equality_is_order_independent() {
        let a = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(3.0), CW::new(4)),
        ]);
        let b = TensorTC::from_pairs(&[
            (TW::new(3.0), CW::new(4)),
            (TW::new(1.0), CW::new(2)),
        ]);
        assert_eq!(a, b);
    }

    #[test]
    fn equality_after_simplification() {
        // (1.0, 2) + (1.0, 3) simplifies to (1.0, 5)
        let a = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(1.0), CW::new(3)),
        ]);
        let b = TensorTC::elementary(TW::new(1.0), CW::new(5));
        assert_eq!(a, b);
    }

    // ═════════════════════════════════════════════════════════════════════════
    // approx_eq tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn approx_eq_matching_terms() {
        let a = TensorTT::elementary(TW::new(1.0), TW::new(2.0));
        let b = TensorTT::elementary(TW::new(1.0 + 1e-12), TW::new(2.0 + 1e-12));
        assert!(a.approx_eq(&b, 1e-10));
    }

    #[test]
    fn approx_eq_different_counts_false() {
        let a = TensorTT::elementary(TW::new(1.0), TW::new(2.0));
        let b = TensorTT::from_pairs(&[
            (TW::new(1.0), TW::new(2.0)),
            (TW::new(3.0), TW::new(4.0)),
        ]);
        assert!(!a.approx_eq(&b, 1e-10));
    }

    // ═════════════════════════════════════════════════════════════════════════
    // Iterator / as_slice tests
    // ═════════════════════════════════════════════════════════════════════════

    #[test]
    fn iter_yields_active_terms_only() {
        let t = TensorTC::from_pairs(&[
            (TW::new(1.0), CW::new(2)),
            (TW::new(3.0), CW::new(4)),
        ]);
        let collected: Vec<_> = t.iter().cloned().collect();
        assert_eq!(collected.len(), 2);
        assert_eq!(collected[0], (TW::new(1.0), CW::new(2)));
        assert_eq!(collected[1], (TW::new(3.0), CW::new(4)));
    }

    #[test]
    fn iter_zero_tensor_yields_nothing() {
        let z = TensorTC::zero();
        assert_eq!(z.iter().count(), 0);
    }
}
