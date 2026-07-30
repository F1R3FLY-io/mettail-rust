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
//!
//! ★ **`CanonicalFixedPoint` carries TWO canonical-bytes methods since work item #200
//! (2026-07-30), because it has two consumers with contradictory requirements:**
//!
//! | method | keys on | consumer | requirement |
//! |---|---|---|---|
//! | `to_canonical_bytes` | raw `(unscaled, places)` | op-enum content key, `dovetail_report/op_enum.rs:141-146` | agree with `Eq`, which the owner ruled onto the raw pair |
//! | `to_rational_canonical_bytes` | `value_ratio()` | realize-frontier fingerprint, `term_ops/semantic_hash.rs` | unify a `Fixed` with an equal `BigRat`, or the frontier fans out `m^k` |
//!
//! No single method can satisfy both, and the `Eq`-agreement contract above attaches to the
//! FIRST. Both are pinned below, in both directions.

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

/// ★ INVERTED AND RENAMED 2026-07-30 (work item #200). It was
/// `fixed_point_keys_on_value_ratio_not_raw_pair` and read, verbatim:
///
/// ```text
/// // 15 @ 1 place = 1.5 = 150 @ 2 places: distinct raw (unscaled, places) pairs, SAME value.
/// // `Eq`/`Hash`/`to_canonical_bytes` all key on value_ratio() ⇒ they must compare EQUAL.
/// assert_eq!(a, b, "Eq keys on value_ratio()");
/// assert_eq!(a.to_canonical_bytes(), b.to_canonical_bytes(), …);
/// ```
///
/// The owner ruled `Eq`/`Hash`/`Ord` onto `(unscaled, places)` because keying on the value made
/// the Dovetail e-graph's hashcons collapse two differently-scaled spellings of one number, so
/// `/`, `&`, `|` and `bitnot` computed from whichever spelling appeared first in the source
/// text. `to_canonical_bytes` is bound to `Eq` by `dovetail/src/key.rs:96-104` — a
/// BICONDITIONAL over an exact `Vec<u8>`, not a hash — so it had to move with it.
#[test]
fn fixed_point_keys_on_the_raw_pair_not_value_ratio() {
    // 15 @ 1 place = 1.5 = 150 @ 2 places: SAME number, distinct raw `(unscaled, places)`
    // pairs ⇒ distinct VALUES, and therefore distinct bytes.
    let a = CanonicalFixedPoint::new(BigInt::from(15), 1);
    let b = CanonicalFixedPoint::new(BigInt::from(150), 2);
    assert_ne!(a, b, "Eq keys on the raw (unscaled, places) pair");
    assert_ne!(
        a.to_canonical_bytes(),
        b.to_canonical_bytes(),
        "to_canonical_bytes must agree with Eq (the raw pair, not value_ratio)"
    );

    // Distinct NUMBERS are of course still distinct.
    let c = CanonicalFixedPoint::new(BigInt::from(16), 1); // 1.6
    assert_ne!(a, c);
    assert_ne!(a.to_canonical_bytes(), c.to_canonical_bytes());

    // The other half of the biconditional: EQUAL values ⇒ EQUAL bytes.
    let a_again = CanonicalFixedPoint::new(BigInt::from(15), 1);
    assert_eq!(a, a_again);
    assert_eq!(a.to_canonical_bytes(), a_again.to_canonical_bytes(), "Eq ⇒ equal bytes");

    // The layout is `framed(unscaled LE) ++ places LE(4)`: 8 length bytes + 1 mantissa byte
    // (`15` fits in one signed LE byte) + 4 places bytes = 13.
    assert_eq!(
        a.to_canonical_bytes().len(),
        13,
        "8-byte length frame + minimal two's-complement mantissa + fixed 4-byte `places`",
    );
}

/// ★ NEW 2026-07-30 (work item #200) — **this unification was load-bearing and pinned by
/// NOTHING.** Splitting `to_canonical_bytes` could have silently broken it.
///
/// A numeric literal read from ONE source token can reach a category through several
/// transparent lossless promotion casts, `Fixed → BigRat` among them
/// (`ast/src/language/model.rs::lossless_targets`). The realize-frontier dedup fingerprints
/// each alternative (`macros/src/gen/term_ops/semantic_hash.rs`), and if the two readings of
/// one token fingerprint differently the frontier fans out: `k` literals with `m` transparent
/// reps each give `m^k` alternatives — the measured `3^4 = 81` for `Map().set(1,10).set(2,20)`,
/// with a memcg-OOM at 20k-ternary attributed to the class. The arm therefore requires that a
/// `CanonicalFixedPoint` and a `CanonicalBigRat` of EQUAL VALUE write byte-identical canonical
/// bytes.
///
/// Since #200 that requirement is carried by `to_rational_canonical_bytes` on the fixed-point
/// side (its `to_canonical_bytes` now keys on identity, which would break the unification), so
/// this test pins BOTH directions: the value-keyed pair agrees, and the identity-keyed one
/// deliberately does not.
#[test]
fn fixed_and_bigrat_of_equal_value_share_value_keyed_bytes() {
    // 1.5 spelled three ways: two fixed-point scales and a rational.
    let fixed_p1 = CanonicalFixedPoint::new(BigInt::from(15), 1);
    let fixed_p2 = CanonicalFixedPoint::new(BigInt::from(150), 2);
    let rat = CanonicalBigRat::try_from_nd(BigInt::from(3), BigInt::from(2)).expect("nonzero d");

    assert_eq!(
        fixed_p1.to_rational_canonical_bytes(),
        rat.to_canonical_bytes(),
        "THE UNIFICATION: `1.5p1` and `3/2` must write identical value-keyed bytes, or the \
         realize frontier fans out m^k over the transparent Fixed → BigRat promotion",
    );
    assert_eq!(
        fixed_p2.to_rational_canonical_bytes(),
        rat.to_canonical_bytes(),
        "…and it must not depend on the fixed-point SCALE — `150 @ p2` is the same number",
    );
    assert_eq!(
        fixed_p1.to_rational_canonical_bytes(),
        fixed_p2.to_rational_canonical_bytes(),
        "…hence the two scales agree with each other too",
    );

    // The deliberate counterpart: the IDENTITY-keyed form separates the two scales. If this
    // ever starts agreeing, `to_canonical_bytes` has drifted back onto the value and the
    // e-graph hashcons collapse is back.
    assert_ne!(
        fixed_p1.to_canonical_bytes(),
        fixed_p2.to_canonical_bytes(),
        "the identity-keyed form must SEPARATE what the value-keyed form unifies",
    );

    // A different number must not unify under either key.
    let two_thirds =
        CanonicalBigRat::try_from_nd(BigInt::from(2), BigInt::from(3)).expect("nonzero d");
    assert_ne!(fixed_p1.to_rational_canonical_bytes(), two_thirds.to_canonical_bytes());
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
