//! Decimal fixed-point values for use in category enums and Ascent relations.
//!
//! A value is `(unscaled, places)` representing `unscaled / 10^places`.
//! Uses [`CanonicalBigInt`] for the unscaled payload so the pair is `Copy`.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Rem, Sub};

use moniker::{BoundTerm, Var};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::Zero;

use crate::CanonicalBigInt;

/// Decimal fixed-point: exact value `unscaled / 10^places`.
#[derive(Clone, Copy)]
pub struct CanonicalFixedPoint {
    unscaled: CanonicalBigInt,
    places: u32,
}

fn pow10(p: u32) -> BigInt {
    BigInt::from(10u32).pow(p)
}

impl CanonicalFixedPoint {
    /// Constructs from unscaled integer and decimal place count, then normalizes.
    pub fn new(unscaled: BigInt, places: u32) -> Self {
        Self::from_raw(CanonicalBigInt::from(unscaled), places)
    }

    fn from_raw(unscaled: CanonicalBigInt, places: u32) -> Self {
        let mut s = Self { unscaled, places };
        s.normalize_in_place();
        s
    }

    /// Only collapse true zero to `0p0`. Do not strip trailing decimal zeros: `100p1` (ten with
    /// scale 1) must stay distinct from `10p0` for literal-backed scale, while `+`/`-`/`*`/`/`
    /// still align operands by `max(places)`.
    fn normalize_in_place(&mut self) {
        if self.unscaled.get().is_zero() {
            self.places = 0;
        }
    }

    pub(crate) fn value_ratio(&self) -> Ratio<BigInt> {
        Ratio::new(self.unscaled.get().clone(), pow10(self.places))
    }

    #[inline]
    pub fn unscaled(&self) -> &BigInt {
        self.unscaled.get()
    }

    #[inline]
    pub fn places(&self) -> u32 {
        self.places
    }

    /// Deterministic canonical byte serialization that agrees with [`Eq`]: two
    /// `CanonicalFixedPoint`s are equal iff their canonical bytes are equal. **Critically,
    /// this keys on [`value_ratio`](Self::value_ratio) — the reduced rational
    /// `unscaled / 10^places` — exactly as `PartialEq`/`Hash` do, NOT on the raw
    /// `(unscaled, places)` pair.** Using the raw pair (or `Debug`, which renders the raw
    /// pair) would give two `Eq`-equal values (e.g. `15p1` and `150p2`, both `3/2`) distinct
    /// bytes and break the `SemanticHash`↔`Eq` agreement that the Dovetail e-graph relies on
    /// to dedup. Used to give a generated typed op-enum a sound `SemanticHash` content key.
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let r = self.value_ratio();
        let n = r.numer().to_signed_bytes_le();
        let d = r.denom().to_signed_bytes_le();
        let mut out = Vec::with_capacity(n.len() + d.len() + 16);
        out.extend_from_slice(&(n.len() as u64).to_le_bytes());
        out.extend_from_slice(&n);
        out.extend_from_slice(&(d.len() as u64).to_le_bytes());
        out.extend_from_slice(&d);
        out
    }
}

impl Default for CanonicalFixedPoint {
    /// Zero fixed-point (`0p0`).
    fn default() -> Self {
        Self::from_raw(CanonicalBigInt::default(), 0)
    }
}

impl CanonicalFixedPoint {
    /// Align both operands to `P = max(places_a, places_b)`; returns scaled unscaled values.
    fn align_pair(a: Self, b: Self) -> (BigInt, BigInt, u32) {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ua = a.unscaled.get() * scale_a;
        let ub = b.unscaled.get() * scale_b;
        (ua, ub, p)
    }

    /// Shifted integer division: `(ua * 10^P) / ub` at common scale `P`.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let numer = ua * pow10(p);
        let q = numer / ub;
        Some(Self::from_raw(CanonicalBigInt::from(q), p))
    }

    /// Remainder on the aligned unscaled integers, at the shared scale `P`: `ua % ub`, truncated
    /// toward zero so the sign follows the DIVIDEND (as `BigInt`'s and Rust's `i64`'s `%` do).
    ///
    /// # Upstream is the definition
    ///
    /// This matches upstream Rholang's `combine_mod` `GFixedPoint` arm exactly —
    /// `f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs:3460-3470`:
    ///
    /// ```text
    /// let ua = bytes_to_bigint(&fp1.unscaled);
    /// let ub = bytes_to_bigint(&fp2.unscaled);
    /// let remainder = &ua % &ub;
    /// make_fixedpoint_expr(GFixedPoint { unscaled: …, scale: fp1.scale }, "%")
    /// ```
    ///
    /// ⇒ remainder on the unscaled integers, scale preserved. ★ Note the exact remainder ALWAYS
    /// fits this type: `/` must approximate (`10.0/3.0` is not representable at any finite scale),
    /// but `%` never must, because `ua % ub` is an integer no wider than `ua`.
    ///
    /// # ⚠ WHAT THIS USED TO COMPUTE, AND WHY IT WAS WRONG
    ///
    /// Until 2026-07-30 the body was:
    ///
    /// ```text
    /// let q = (ua.clone() * pow10(p)) / &ub;     // ← scaled quotient
    /// let rem = ua - (q * &ub) / pow10(p);       // ← then divided back down
    /// ```
    ///
    /// That is `a − trunc_p(a/b)·b`, which expands to `(a/b − trunc_p(a/b))·b = ε·b` with
    /// `0 ≤ ε < 10⁻ᵖ` — **the truncation error of the division, scaled by the divisor.** A
    /// residual, not a remainder. Its magnitude is bounded by `|b|·10⁻ᵖ`, so it tends to ZERO as
    /// precision grows, which no remainder does. Measured consequences:
    ///
    /// | input | superseded | correct (= upstream) |
    /// |---|---|---|
    /// | `7.00p2 % 3.00p2` | `0.01p2` | `1.00p2` |
    /// | `10.0p1 % 3.0p1`  | `0.1p1`  | `1.0p1`  |
    /// | `7.50p2 % 2.00p2` | `0p0`    | `1.50p2` |
    ///
    /// The `7.50 % 2.00` row shows the mechanism plainly: `7.50/2.00 = 3.75` is EXACT at two
    /// places, so `ε = 0` and the old code returned zero for a division that leaves remainder
    /// `1.50`.
    ///
    /// ## Why "copy+paste" is the diagnosis
    ///
    /// Compare [`checked_div`](Self::checked_div) directly above: there `let numer = ua * pow10(p)`
    /// is **essential**, because a quotient must be computed at scale to have fractional digits at
    /// all. `checked_rem` copied that line and then bolted on a compensating `/ pow10(p)` to make
    /// the units balance. The round trip exists ONLY to undo a factor that should never have been
    /// introduced — deleting both is the whole fix.
    ///
    /// The copy is recorded upstream of the code, in the design note
    /// `docs/design/exploring/ieee754-fixed-point.md` §4.4(5), which derived `%` by substituting
    /// item (4)'s SHIFTED quotient into the C99 identity `(a/b)·b + a%b == a`. That identity is
    /// C99 §6.5.5's, and it is stated for INTEGER division; item (4)'s `q` is a `p`-places
    /// fixed-point number, not an integer, so the substitution is invalid. The note has been
    /// corrected alongside this function, because it would otherwise regenerate the defect.
    ///
    /// ## ★★ The decisive defect: `%` was not a function on this type's own equality
    ///
    /// [`PartialEq`], [`Hash`] and [`to_canonical_bytes`](Self::to_canonical_bytes) all key on
    /// [`value_ratio`](Self::value_ratio) — the reduced rational — because keying on the raw
    /// `(unscaled, places)` pair would break the `SemanticHash`↔`Eq` agreement the Dovetail
    /// e-graph relies on to dedup. So `places` is NOT part of a value's identity, and
    /// `7.00p2 == 7.0p1`. But the superseded `%` READ `places`: it answered `0.01` for the first
    /// spelling and `0.1` for the second. **Equal inputs, unequal outputs.** Whatever else it was,
    /// it was not a function on the equivalence classes this type declares. Pinned by
    /// `tests::remainder_is_invariant_under_the_places_spelling`.
    ///
    /// # The identity that no longer holds — and why that is correct, not a loss
    ///
    /// `checked_div(a,b)·b + checked_rem(a,b) == a` is now FALSE (`3.3·3.0 + 1.0 = 10.9 ≠ 10.0`),
    /// and it was true before. That is not a regression: the division identity
    /// `q·b + r == a` is a theorem about the **integer** (truncated) quotient, and
    /// [`checked_div`](Self::checked_div) does not return that — it returns the quotient carried to
    /// `p` fractional places, which is a different (and deliberately approximating) operation. The
    /// old pairing satisfied the identity only because the old `%` was defined as "whatever makes
    /// `checked_div` exact", i.e. as the division's own error term. The identity that holds now is
    /// `trunc(a/b)·b + (a % b) == a`, asserted in `tests::div_mod_example` and
    /// `tests::div_mod_with_negatives`. ★ Upstream claims no such identity between its `/` and `%`
    /// either, which is why it has no such test.
    ///
    /// `/` is deliberately NOT changed here; only `%` moved.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let rem = ua % ub;
        Some(Self::from_raw(CanonicalBigInt::from(rem), p))
    }

    fn bitwise_aligned<F>(a: Self, b: Self, op: F) -> Self
    where
        F: FnOnce(BigInt, BigInt) -> BigInt,
    {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ia = a.unscaled.get() * scale_a;
        let ib = b.unscaled.get() * scale_b;
        let r = op(ia, ib);
        Self::from_raw(CanonicalBigInt::from(r), p)
    }
}

impl PartialEq for CanonicalFixedPoint {
    fn eq(&self, other: &Self) -> bool {
        self.value_ratio() == other.value_ratio()
    }
}

impl Eq for CanonicalFixedPoint {}

impl PartialOrd for CanonicalFixedPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CanonicalFixedPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value_ratio().cmp(&other.value_ratio())
    }
}

impl Hash for CanonicalFixedPoint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let r = self.value_ratio();
        r.numer().hash(state);
        r.denom().hash(state);
    }
}

impl fmt::Debug for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fixed({}/{})", self.unscaled.get(), pow10(self.places))
    }
}

impl fmt::Display for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let u = self.unscaled.get();
        let p = self.places as usize;
        if p == 0 {
            return write!(f, "{}p0", u);
        }
        let us = u.to_string();
        let neg = us.starts_with('-');
        let digits = if neg { &us[1..] } else { &us[..] };
        if digits.len() <= p {
            let pad = p - digits.len();
            let frac: String = std::iter::repeat_n('0', pad)
                .chain(digits.chars())
                .collect();
            if neg {
                write!(f, "-0.{frac}p{}", self.places)
            } else {
                write!(f, "0.{frac}p{}", self.places)
            }
        } else {
            let split = digits.len() - p;
            let (int_part, frac_part) = digits.split_at(split);
            if neg {
                write!(f, "-{int_part}.{frac_part}p{}", self.places)
            } else {
                write!(f, "{int_part}.{frac_part}p{}", self.places)
            }
        }
    }
}

impl BoundTerm<String> for CanonicalFixedPoint {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_free: &impl moniker::OnFreeFn<String>,
    ) {
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&Var<String>)) {}

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut Var<String>)) {}
}

impl Add for CanonicalFixedPoint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua + ub), p)
    }
}

impl Sub for CanonicalFixedPoint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua - ub), p)
    }
}

impl Mul for CanonicalFixedPoint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let numer = self.unscaled.get() * rhs.unscaled.get();
        let places = self.places + rhs.places;
        Self::from_raw(CanonicalBigInt::from(numer), places)
    }
}

impl Div for CanonicalFixedPoint {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self.checked_div(rhs)
            .expect("fixed-point division by zero or overflow path")
    }
}

impl Rem for CanonicalFixedPoint {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        self.checked_rem(rhs)
            .expect("fixed-point remainder: division by zero")
    }
}

impl Neg for CanonicalFixedPoint {
    type Output = Self;
    fn neg(self) -> Self {
        Self::from_raw(CanonicalBigInt::from(-self.unscaled.get().clone()), self.places)
    }
}

impl BitAnd for CanonicalFixedPoint {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a & b)
    }
}

impl BitOr for CanonicalFixedPoint {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a | b)
    }
}

impl BitXor for CanonicalFixedPoint {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a ^ b)
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    use super::*;

    fn fp(s_int: i64, s_frac: i64, places: u32) -> CanonicalFixedPoint {
        // helper: value (s_int * 10^p + s_frac) / 10^p for small tests (s_frac < 10^p)
        let ten_p = 10i64.pow(places);
        let u = BigInt::from(s_int) * BigInt::from(ten_p) + BigInt::from(s_frac);
        CanonicalFixedPoint::new(u, places)
    }

    fn hash_val(x: &CanonicalFixedPoint) -> u64 {
        let mut h = DefaultHasher::new();
        x.hash(&mut h);
        h.finish()
    }

    /// The TRUNCATED INTEGER quotient `trunc(a/b)`, as an integer-valued fixed point
    /// (`places = 0`).
    ///
    /// ★ This is the quotient `checked_rem`'s remainder pairs with, and it is NOT what
    /// [`CanonicalFixedPoint::checked_div`] returns. `checked_div` carries the quotient to `p`
    /// fractional places (`10.0p1 / 3.0p1 == 3.3p1`); the division identity
    /// `q·b + r == a` holds for the INTEGER quotient only. Written out here so the two tests
    /// below can name the distinction instead of implying it.
    fn integer_quotient(
        a: CanonicalFixedPoint,
        b: CanonicalFixedPoint,
    ) -> CanonicalFixedPoint {
        let (ua, ub, _p) = CanonicalFixedPoint::align_pair(a, b);
        CanonicalFixedPoint::new(ua / ub, 0)
    }

    /// ★ RE-DERIVED 2026-07-30 — NOT re-blessed. `%` is the remainder on the ALIGNED UNSCALED
    /// INTEGERS (upstream's definition, `reduce.rs:3460-3470`), so `10.0p1 % 3.0p1` aligns to
    /// `ua = 100`, `ub = 30` and answers `100 % 30 = 10` at `places = 1` — the value **1.0**.
    ///
    /// **The identity that HOLDS** is against the TRUNCATED INTEGER quotient:
    ///   `trunc(a/b)·b + (a % b) == a`, i.e. `3·3.0 + 1.0 == 10.0`. ✓
    ///
    /// **The identity that NO LONGER HOLDS** is against `checked_div`'s quotient:
    ///   `(a/b)·b + (a % b) == a`, i.e. `3.3·3.0 + 1.0 == 10.9 ≠ 10.0`. ✗
    ///
    /// The second is asserted as an INEQUALITY deliberately. It is exactly the identity the
    /// superseded `checked_rem` satisfied (it returned `0.1p1`, and `3.3·3.0 + 0.1 == 10.0`), so
    /// reverting the `checked_rem` fix turns THIS row red rather than letting the residual-valued
    /// `%` back in as a "restored invariant". `/` is unchanged and its pin below is untouched.
    #[test]
    fn div_mod_example() {
        let a = fp(10, 0, 1);
        let b = fp(3, 0, 1);
        let q = a.checked_div(b).expect("div");
        let r = a.checked_rem(b).expect("rem");

        // `/` is NOT changed: the quotient is still carried to `p` places.
        assert_eq!(q.unscaled(), &BigInt::from(33));
        assert_eq!(q.places(), 1);

        // `%` is the remainder on the aligned unscaled integers, at the shared scale.
        assert_eq!(
            r.unscaled(),
            &BigInt::from(10),
            "`10.0p1 % 3.0p1` aligns to `100 % 30 = 10`; unscaled `1` would be `0.1p1`, the \
             truncation residual of the division, not a remainder",
        );
        assert_eq!(r.places(), 1, "upstream preserves the operand scale");
        assert_eq!(r.to_string(), "1.0p1");

        // THE IDENTITY THAT HOLDS: against the truncated integer quotient.
        let q_int = integer_quotient(a, b);
        assert_eq!(q_int.unscaled(), &BigInt::from(3), "trunc(10/3) == 3");
        assert_eq!(
            q_int * b + r,
            a,
            "`trunc(a/b)·b + (a % b) == a` — the division identity the exact remainder satisfies",
        );

        // THE IDENTITY THAT DOES NOT: against the p-places quotient. `3.3·3.0 + 1.0 == 10.9`.
        assert_ne!(
            q * b + r,
            a,
            "`(a/b)·b + (a % b) == a` holds only for the p-PLACES quotient paired with the \
             p-places truncation RESIDUAL — the superseded behaviour. If this row passes, \
             `checked_rem` has been reverted to computing `ε·b`.",
        );
        assert_eq!(
            (q * b + r).to_string(),
            "10.90p2",
            "the pairing is off by exactly the residual the old `%` returned (0.1·3.0 = 0.30… \
             precisely: 9.90 + 1.0 = 10.90 versus a = 10.0)",
        );
    }

    /// ★ RE-DERIVED 2026-07-30 — NOT re-blessed. `BigInt`'s `%` truncates toward zero, so the
    /// sign of the remainder follows the DIVIDEND, matching Rust's `i64 %` and therefore matching
    /// upstream's `GInt` row (`lhs % rhs`) and its `GFixedPoint` row (`&ua % &ub`) alike.
    ///
    /// The identity asserted for every row is `trunc(a/b)·b + (a % b) == a` — the same one
    /// [`div_mod_example`] establishes, now over all four sign combinations. ⚠ The originally
    /// pinned operand pair (`-1.00p2 % 0.25p2`) is kept as the first row but measures NO sign
    /// behaviour: `25` divides `100` exactly, so its remainder is identically zero. That is why
    /// the four `±7 % ±3` rows were added — the old pin could not have caught a sign error.
    #[test]
    fn div_mod_with_negatives() {
        // Row 0: the originally pinned pair. Exact division ⇒ remainder is EXACTLY ZERO, which
        // normalizes to `0p0`. Retained for continuity, not for coverage.
        let a = CanonicalFixedPoint::new(BigInt::from(-100), 2);
        let b = CanonicalFixedPoint::new(BigInt::from(25), 2);
        let r = a.checked_rem(b).expect("r");
        assert!(
            r.unscaled().is_zero(),
            "-1.00p2 / 0.25p2 is exact (-4), so the remainder is 0 and this row cannot detect a \
             sign defect",
        );
        assert_eq!(r.places(), 0, "true zero normalizes to `0p0`");
        let q_int = integer_quotient(a, b);
        assert_eq!(q_int.unscaled(), &BigInt::from(-4));
        assert_eq!(q_int * b + r, a, "`trunc(a/b)·b + (a % b) == a`");

        // Rows 1-4: every sign combination, checked against `i64 %` — the carrier upstream's
        // `GInt` row uses, so agreement here is agreement with upstream on sign.
        for (ai, bi) in [(7i64, 3i64), (-7, 3), (7, -3), (-7, -3)] {
            let a = CanonicalFixedPoint::new(BigInt::from(ai) * 100, 2);
            let b = CanonicalFixedPoint::new(BigInt::from(bi) * 100, 2);
            let r = a.checked_rem(b).expect("rem");
            let want = CanonicalFixedPoint::new(BigInt::from(ai % bi) * 100, 2);
            assert_eq!(
                r, want,
                "`{ai}.00p2 % {bi}.00p2` must equal `{}` — the value of `{ai}i64 % {bi}i64`, \
                 truncated toward zero with the sign of the dividend",
                ai % bi,
            );
            let q_int = integer_quotient(a, b);
            assert_eq!(
                q_int * b + r,
                a,
                "`trunc(a/b)·b + (a % b) == a` must hold at signs ({ai}, {bi})",
            );
        }
    }

    /// ★ SCALE INVARIANCE — THE LAW THE SUPERSEDED `checked_rem` BROKE, and which nothing checked.
    ///
    /// `PartialEq`, `Hash` and `to_canonical_bytes` all key on `value_ratio()` (see the doc comment
    /// on [`CanonicalFixedPoint::to_canonical_bytes`], which explains that keying on the raw
    /// `(unscaled, places)` pair would break the `SemanticHash`↔`Eq` agreement the Dovetail e-graph
    /// relies on). `places` is therefore NOT part of a value's identity: `7.00p2 == 7.0p1 == 7p0`.
    ///
    /// An operation on this type must consequently be a function on those equivalence classes —
    /// **equal inputs, equal outputs.** `%` was not. It read `places`, and the three spellings of
    /// the same two values gave three different answers:
    ///
    /// | spelling | superseded `%` | correct `%` |
    /// |---|---|---|
    /// | `7.00p2 % 3.00p2` | `0.01` | `1` |
    /// | `7.0p1 % 3.0p1`   | `0.1`  | `1` |
    /// | `7p0 % 3p0`       | `1`    | `1` |
    ///
    /// This is the decisive defect, and no other test in the suite could see it: each spelling was
    /// internally consistent, and the carrier matrix pinned only the `p2` row.
    #[test]
    fn remainder_is_invariant_under_the_places_spelling() {
        let spellings = [
            ("7.00p2 % 3.00p2", 700, 300, 2u32),
            ("7.0p1 % 3.0p1", 70, 30, 1),
            ("7p0 % 3p0", 7, 3, 0),
        ];
        let one = CanonicalFixedPoint::new(BigInt::from(1), 0);

        // PREMISE, asserted rather than assumed: the operands really are pairwise equal.
        let seven = CanonicalFixedPoint::new(BigInt::from(7), 0);
        let three = CanonicalFixedPoint::new(BigInt::from(3), 0);
        for (label, ua, ub, p) in spellings {
            let a = CanonicalFixedPoint::new(BigInt::from(ua), p);
            let b = CanonicalFixedPoint::new(BigInt::from(ub), p);
            assert_eq!(a, seven, "the dividend of `{label}` is the value 7");
            assert_eq!(b, three, "the divisor of `{label}` is the value 3");
        }

        let mut results = Vec::with_capacity(spellings.len());
        for (label, ua, ub, p) in spellings {
            let a = CanonicalFixedPoint::new(BigInt::from(ua), p);
            let b = CanonicalFixedPoint::new(BigInt::from(ub), p);
            let r = a.checked_rem(b).expect("rem");
            assert_eq!(
                r, one,
                "`{label}` must be the value 1: `%` reads `places`, but `places` is not part of \
                 this type's identity, so a `places`-dependent answer makes `%` not a function \
                 on its own equivalence classes",
            );
            assert_eq!(r.places(), p, "`{label}` preserves the operand scale, as upstream does");
            results.push((label, r));
        }

        // The consequence spelled out: equal values ⇒ equal hashes ⇒ equal canonical bytes. This
        // is the e-graph's dedup key, so a `places`-dependent `%` would have produced two e-nodes
        // that must be one.
        let (first_label, first) = results[0];
        for &(label, r) in &results[1..] {
            assert_eq!(
                hash_val(&r),
                hash_val(&first),
                "`{label}` and `{first_label}` must hash alike",
            );
            assert_eq!(
                r.to_canonical_bytes(),
                first.to_canonical_bytes(),
                "`{label}` and `{first_label}` must have identical canonical bytes",
            );
        }
    }

    #[test]
    fn checked_div_rem_by_zero() {
        let a = fp(1, 0, 0);
        let z = fp(0, 0, 0);
        assert!(a.checked_div(z).is_none());
        assert!(a.checked_rem(z).is_none());
    }

    #[test]
    fn normalize_zero() {
        let z = CanonicalFixedPoint::new(BigInt::from(0), 5);
        assert!(z.unscaled.get().is_zero());
        assert_eq!(z.places(), 0);
    }

    #[test]
    fn display_zero_and_integer_p0() {
        let z = CanonicalFixedPoint::new(BigInt::from(0), 0);
        assert_eq!(z.to_string(), "0p0");
        let n = CanonicalFixedPoint::new(BigInt::from(-42), 0);
        assert_eq!(n.to_string(), "-42p0");
    }

    #[test]
    fn display_padding_frac_only() {
        // unscaled 5, places 2 → 0.05p2
        let x = CanonicalFixedPoint::new(BigInt::from(5), 2);
        assert_eq!(x.to_string(), "0.05p2");
        let y = CanonicalFixedPoint::new(BigInt::from(-3), 3);
        assert_eq!(y.to_string(), "-0.003p3");
    }

    #[test]
    fn display_int_and_frac_parts() {
        let x = CanonicalFixedPoint::new(BigInt::from(12345), 3);
        assert_eq!(x.to_string(), "12.345p3");
    }

    #[test]
    fn eq_same_rational_different_places() {
        let a = CanonicalFixedPoint::new(BigInt::from(100), 1);
        let b = CanonicalFixedPoint::new(BigInt::from(10), 0);
        assert_eq!(a, b);
        assert_ne!(a.to_string(), b.to_string());
    }

    #[test]
    fn ord_and_partial_ord() {
        let a = fp(1, 0, 0);
        let b = fp(2, 0, 0);
        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(b.cmp(&a), Ordering::Greater);
        assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
    }

    #[test]
    fn hash_matches_eq() {
        let x = CanonicalFixedPoint::new(BigInt::from(100), 1);
        let y = CanonicalFixedPoint::new(BigInt::from(10), 0);
        assert_eq!(hash_val(&x), hash_val(&y));
        let z = fp(1, 0, 0);
        assert_ne!(hash_val(&x), hash_val(&z));
    }

    #[test]
    fn add_sub_misaligned_places() {
        let one = fp(1, 0, 0);
        let half = fp(0, 5, 1);
        let s = one + half;
        let expected = fp(1, 5, 1);
        assert_eq!(s, expected);
        assert_eq!(s - half, one);
    }

    #[test]
    fn mul_sums_places() {
        let a = fp(2, 0, 1);
        let b = fp(3, 0, 1);
        let p = a * b;
        assert_eq!(p.places(), 2);
        assert_eq!(p, fp(6, 0, 2));
    }

    #[test]
    fn neg_flips_unscaled_keeps_places() {
        let x = fp(3, 3, 1);
        let n = -x;
        assert_eq!(n.unscaled.get(), &BigInt::from(-33));
        assert_eq!(n.places(), 1);
        assert_eq!(-(-x), x);
    }

    #[test]
    fn bitwise_and_aligned() {
        let a = CanonicalFixedPoint::new(BigInt::from(12), 1);
        let b = CanonicalFixedPoint::new(BigInt::from(10), 1);
        let c = a & b;
        assert_eq!(c.unscaled.get(), &BigInt::from(8));
        assert_eq!(c.places(), 1);
    }

    #[test]
    fn bitwise_misaligned_places() {
        let a = CanonicalFixedPoint::new(BigInt::from(15), 0);
        let b = CanonicalFixedPoint::new(BigInt::from(14), 1);
        let c = a & b;
        // 15p0 → 150p1 aligned; 150 & 14 = 6
        assert_eq!(c.unscaled.get(), &BigInt::from(6));
        assert_eq!(c.places(), 1);
    }

    #[test]
    fn bitwise_or_xor() {
        let a = fp(5, 0, 0);
        let b = fp(3, 0, 0);
        assert_eq!(a | b, fp(7, 0, 0));
        assert_eq!(a ^ b, fp(6, 0, 0));
    }

    #[test]
    fn bitwise_negative_unscaled() {
        let a = CanonicalFixedPoint::new(BigInt::from(-4), 0);
        let b = CanonicalFixedPoint::new(BigInt::from(2), 0);
        let c = a & b;
        assert_eq!(c.unscaled.get(), &(BigInt::from(-4) & BigInt::from(2)));
    }
}
