//! Step A of the Dovetail native-fold reduction work (Increment 2 prerequisite).
//!
//! The typed Dovetail op-enum `L` generated per fold-bearing language carries the canonical
//! numeric payload types by value in its literal-leaf variants. The generated
//! `unsafe impl SemanticHash for L` (emitted in the `languages` crate, which sees both
//! `dovetail` and `mettail-runtime`; `mettail-runtime` itself does not depend on `dovetail`)
//! frames `payload.to_canonical_bytes()` into the e-graph content key. For that key to be
//! SOUND, `to_canonical_bytes` must be:
//!   * deterministic (same value → same bytes across calls), and
//!   * in exact agreement with `Eq` — `a == b  ⇔  a.to_canonical_bytes() == b.to_canonical_bytes()`
//! otherwise two `Eq`-equal terms could receive distinct content keys and fail to dedup
//! (a silent `SemanticHash` unsoundness, since the trait is `unsafe`).

use mettail_runtime::{
    CanonicalBigInt, CanonicalBigRat, CanonicalFixedPoint, CanonicalFloat32, CanonicalFloat64,
};
use num_bigint::BigInt;

#[test]
fn bigint_bytes_deterministic_and_eq_agreeing() {
    let a = CanonicalBigInt::new(BigInt::from(123_456_789i64));
    let b = CanonicalBigInt::new(BigInt::from(123_456_789i64));
    let neg = CanonicalBigInt::new(BigInt::from(-123_456_789i64));

    assert_eq!(a.to_canonical_bytes(), a.to_canonical_bytes(), "deterministic");
    assert_eq!(a, b);
    assert_eq!(a.to_canonical_bytes(), b.to_canonical_bytes(), "Eq ⇒ equal bytes");
    assert_ne!(a, neg);
    assert_ne!(a.to_canonical_bytes(), neg.to_canonical_bytes(), "distinct ⇒ distinct bytes");
}

#[test]
fn bigrat_reduced_form_eq_agreeing_and_framed() {
    // 1/2 and 2/4 reduce to the same Ratio ⇒ Eq ⇒ equal bytes.
    let half = CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(2)).expect("nonzero d");
    let two_quarters =
        CanonicalBigRat::try_from_nd(BigInt::from(2), BigInt::from(4)).expect("nonzero d");
    assert_eq!(half, two_quarters);
    assert_eq!(half.to_canonical_bytes(), two_quarters.to_canonical_bytes());

    let third = CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(3)).expect("nonzero d");
    assert_ne!(half, third);
    assert_ne!(half.to_canonical_bytes(), third.to_canonical_bytes());

    // Length-framing of numer/denom prevents 1/23 and 12/3 from aliasing into the same bytes.
    let a = CanonicalBigRat::try_from_nd(BigInt::from(1), BigInt::from(23)).expect("nonzero d");
    let b = CanonicalBigRat::try_from_nd(BigInt::from(12), BigInt::from(3)).expect("nonzero d");
    assert_ne!(a.to_canonical_bytes(), b.to_canonical_bytes());
}

#[test]
fn fixed_point_keys_on_value_ratio_not_raw_pair() {
    // 15 @ 1 place = 1.5 = 150 @ 2 places: distinct raw (unscaled, places) pairs, SAME value.
    // `Eq`/`Hash`/`to_canonical_bytes` all key on value_ratio() ⇒ they must compare EQUAL.
    let a = CanonicalFixedPoint::new(BigInt::from(15), 1);
    let b = CanonicalFixedPoint::new(BigInt::from(150), 2);
    assert_eq!(a, b, "Eq keys on value_ratio()");
    assert_eq!(
        a.to_canonical_bytes(),
        b.to_canonical_bytes(),
        "to_canonical_bytes must agree with Eq (value_ratio, not the raw pair)"
    );

    let c = CanonicalFixedPoint::new(BigInt::from(16), 1); // 1.6
    assert_ne!(a, c);
    assert_ne!(a.to_canonical_bytes(), c.to_canonical_bytes());
}

#[test]
fn float64_canonicalizes_nan_and_signed_zero() {
    let pos0 = CanonicalFloat64::from(0.0_f64);
    let neg0 = CanonicalFloat64::from(-0.0_f64);
    assert_eq!(pos0, neg0);
    assert_eq!(pos0.to_canonical_bytes(), neg0.to_canonical_bytes(), "-0.0 == +0.0");

    // Two distinct NaN bit patterns both canonicalize to one quiet NaN ⇒ equal bytes.
    let nan_a = CanonicalFloat64::from(f64::NAN);
    let nan_b = CanonicalFloat64::from(f64::from_bits(0x7ff8_0000_0000_0001));
    assert_eq!(nan_a, nan_b);
    assert_eq!(nan_a.to_canonical_bytes(), nan_b.to_canonical_bytes(), "all NaN equal");

    let one = CanonicalFloat64::from(1.0_f64);
    assert_ne!(pos0.to_canonical_bytes(), one.to_canonical_bytes());
    assert_eq!(one.to_canonical_bytes().len(), 8, "f64 ⇒ 8 bytes");
}

#[test]
fn float32_canonicalizes_nan_and_signed_zero() {
    let pos0 = CanonicalFloat32::from(0.0_f32);
    let neg0 = CanonicalFloat32::from(-0.0_f32);
    assert_eq!(pos0.to_canonical_bytes(), neg0.to_canonical_bytes());

    let nan_a = CanonicalFloat32::from(f32::NAN);
    let nan_b = CanonicalFloat32::from(f32::from_bits(0x7fc0_0001));
    assert_eq!(nan_a.to_canonical_bytes(), nan_b.to_canonical_bytes());

    let one = CanonicalFloat32::from(1.0_f32);
    assert_ne!(pos0.to_canonical_bytes(), one.to_canonical_bytes());
    assert_eq!(one.to_canonical_bytes().len(), 4, "f32 ⇒ 4 bytes");
}
