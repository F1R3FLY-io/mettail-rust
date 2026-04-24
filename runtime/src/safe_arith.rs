//! Overflow-safe and NaN-safe arithmetic for native-type category evaluation.
//!
//! The `language!` macro lets users write arbitrary Rust inside `![...]` blocks
//! (e.g., `![a + b]`, `![{ (1..=a).product::<i32>() }]`). At runtime, these
//! expressions execute inside the evaluator and inside Ascent datalog rewrite
//! rules. Panicking arithmetic (integer overflow in debug mode) propagates as
//! a panic, which is at best swallowed by `catch_unwind` and at worst causes a
//! double-panic SIGABRT under proptest/nextest.
//!
//! This module defines a trait `SafeArith` that returns `Option<T>` on overflow
//! or NaN, letting callers treat "this rule can't fire on this input" as a
//! value rather than a control-flow event. Each call to a `safe_*` method is a
//! self-contained step — a trampoline-friendly shape that composes cleanly with
//! the PDA-based tree walker in `eval.rs`.
//!
//! ## Policy
//!
//! - **Integers** — delegate to `checked_*` from the stdlib. Overflow → `None`.
//! - **Floats** — compute the IEEE result; return `None` iff the result is
//!   `NaN`. `±Inf` is preserved as `Some(±Inf)` because it is a legitimate
//!   extended-real value (used by log-domain / tropical semirings). The
//!   `language!` macro's rewrite pass wraps the outer closure with an additional
//!   `is_finite` filter so that rewrite rules do not fire on `Inf`; code that
//!   wants `Inf` in a fold (e.g., tropical min) calls the trait directly.
//! - **`-0.0`** — normalised to `+0.0` in `safe_neg`, matching
//!   `CanonicalFloat64`'s existing canonicalisation.
//!
//! ## Why a trait, not free functions
//!
//! `safe_product` / `safe_sum` need to fold over iterators of unknown element
//! type. Dispatch through `Self` keeps the generated code monomorphic per
//! category without forcing callers to specify the type twice.
//!
//! This module provides integer impls. Float impls live alongside in a separate
//! block (added incrementally — see `impl SafeArith for f64` below).

/// Overflow-safe arithmetic. Every method returns `Option<Self>`; `None`
/// indicates the operation's result is not representable (integer overflow,
/// `NaN`, division by zero in integer contexts) and the caller should treat the
/// whole enclosing computation as unevaluable.
pub trait SafeArith: Sized {
    /// Result type for checked operations. Defaults to `Self` for owned-value
    /// impls (e.g. `i32`, `CanonicalBigInt`, `f64`). Reference impls like
    /// `&num_bigint::BigInt` set `Output` to the owned type so that
    /// `a.get() - b.get()` (which produces a new owned `BigInt`) still
    /// type-checks against the trait method signature.
    type Output;

    fn safe_add(self, rhs: Self) -> Option<Self::Output>;
    fn safe_sub(self, rhs: Self) -> Option<Self::Output>;
    fn safe_mul(self, rhs: Self) -> Option<Self::Output>;
    fn safe_div(self, rhs: Self) -> Option<Self::Output>;
    fn safe_rem(self, rhs: Self) -> Option<Self::Output>;
    fn safe_neg(self) -> Option<Self::Output>;

    /// Bitwise NOT. Used by the rewriter to handle user code like `!v`
    /// where `v` is an integer. For floats this is meaningless — returns
    /// `None`. Integer impls return `Some(!self)` unconditionally (bitwise
    /// NOT never overflows; `!T::MIN` for signed is `T::MAX` etc.).
    fn safe_not(self) -> Option<Self::Output>;

    /// `self` raised to an integer power. Used by the rewriter to rewrite
    /// `.pow(n)` and `.powi(n)`. For floats, `safe_powf` handles the
    /// floating-point exponent case.
    fn safe_pow(self, exp: i32) -> Option<Self::Output>;

    /// Fold-based product with short-circuit on `None`. Each iteration is one
    /// checked multiplication; a single overflow or `NaN` aborts the fold.
    fn safe_product<I: IntoIterator<Item = Self>>(iter: I) -> Option<Self::Output>
    where
        Self: From<u8> + SafeArith<Output = Self>,
    {
        let mut acc = Self::from(1u8);
        for x in iter {
            acc = acc.safe_mul(x)?;
        }
        Some(acc)
    }

    /// Fold-based sum with short-circuit on `None`. Each iteration is one
    /// checked addition; a single overflow or `NaN` aborts the fold.
    fn safe_sum<I: IntoIterator<Item = Self>>(iter: I) -> Option<Self::Output>
    where
        Self: From<u8> + SafeArith<Output = Self>,
    {
        let mut acc = Self::from(0u8);
        for x in iter {
            acc = acc.safe_add(x)?;
        }
        Some(acc)
    }
}

// ─── Integer impls ──────────────────────────────────────────────────────────
//
// Each impl delegates to the stdlib's `checked_*` family. Division and
// remainder by zero return `None`; signed `i::MIN` divided / remaindered by
// `-1` overflows and also returns `None`. `safe_pow` takes an `i32` exponent
// uniformly; for signed integers a negative exponent is `None` (integer
// reciprocal is not representable in the same type). For unsigned integers
// the exponent is clamped at 0.

macro_rules! impl_safe_arith_signed {
    ($t:ty) => {
        impl SafeArith for $t {
            type Output = Self;
            #[inline]
            fn safe_add(self, rhs: Self) -> Option<Self> { self.checked_add(rhs) }
            #[inline]
            fn safe_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }
            #[inline]
            fn safe_mul(self, rhs: Self) -> Option<Self> { self.checked_mul(rhs) }
            #[inline]
            fn safe_div(self, rhs: Self) -> Option<Self> { self.checked_div(rhs) }
            #[inline]
            fn safe_rem(self, rhs: Self) -> Option<Self> { self.checked_rem(rhs) }
            #[inline]
            fn safe_neg(self) -> Option<Self> { self.checked_neg() }
            #[inline]
            fn safe_not(self) -> Option<Self> { Some(!self) }
            #[inline]
            fn safe_pow(self, exp: i32) -> Option<Self> {
                // Negative exponent on integer: result is not integral (e.g. 2^-1 = 1/2).
                if exp < 0 { return None; }
                self.checked_pow(exp as u32)
            }
        }
    };
}

macro_rules! impl_safe_arith_unsigned {
    ($t:ty) => {
        impl SafeArith for $t {
            type Output = Self;
            #[inline]
            fn safe_add(self, rhs: Self) -> Option<Self> { self.checked_add(rhs) }
            #[inline]
            fn safe_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }
            #[inline]
            fn safe_mul(self, rhs: Self) -> Option<Self> { self.checked_mul(rhs) }
            #[inline]
            fn safe_div(self, rhs: Self) -> Option<Self> { self.checked_div(rhs) }
            #[inline]
            fn safe_rem(self, rhs: Self) -> Option<Self> { self.checked_rem(rhs) }
            #[inline]
            fn safe_neg(self) -> Option<Self> {
                // 0_u* has a trivially representable negation (itself); all others overflow.
                if self == 0 { Some(self) } else { None }
            }
            #[inline]
            fn safe_not(self) -> Option<Self> { Some(!self) }
            #[inline]
            fn safe_pow(self, exp: i32) -> Option<Self> {
                if exp < 0 { return None; }
                self.checked_pow(exp as u32)
            }
        }
    };
}

impl_safe_arith_signed!(i8);
impl_safe_arith_signed!(i16);
impl_safe_arith_signed!(i32);
impl_safe_arith_signed!(i64);
impl_safe_arith_signed!(i128);
impl_safe_arith_signed!(isize);

impl_safe_arith_unsigned!(u8);
impl_safe_arith_unsigned!(u16);
impl_safe_arith_unsigned!(u32);
impl_safe_arith_unsigned!(u64);
impl_safe_arith_unsigned!(u128);
impl_safe_arith_unsigned!(usize);

// ─── Reference impls for primitive Copy types ───────────────────────────────
//
// Enables `safeify` to rewrite `x + y` → `SafeArith::safe_add(x, y)?` for
// reference forms (user code in `![...]` blocks often pattern-matches
// `(Cat::Lit(x), Cat::Lit(y))` where `x, y: &T`). A blanket
// `impl<T: SafeArith + Copy> SafeArith for &T` would be cleaner, but Rust's
// coherence rules conflict with the specific `impl SafeArith for &BigInt`
// below (BigInt is !Copy but Rust can't prove negative bounds). So we emit
// one macro-driven impl per primitive type instead.
macro_rules! impl_safe_arith_ref {
    ($t:ty) => {
        impl SafeArith for &$t {
            type Output = <$t as SafeArith>::Output;
            #[inline] fn safe_add(self, rhs: Self) -> Option<Self::Output> { (*self).safe_add(*rhs) }
            #[inline] fn safe_sub(self, rhs: Self) -> Option<Self::Output> { (*self).safe_sub(*rhs) }
            #[inline] fn safe_mul(self, rhs: Self) -> Option<Self::Output> { (*self).safe_mul(*rhs) }
            #[inline] fn safe_div(self, rhs: Self) -> Option<Self::Output> { (*self).safe_div(*rhs) }
            #[inline] fn safe_rem(self, rhs: Self) -> Option<Self::Output> { (*self).safe_rem(*rhs) }
            #[inline] fn safe_neg(self) -> Option<Self::Output> { (*self).safe_neg() }
            #[inline] fn safe_not(self) -> Option<Self::Output> { (*self).safe_not() }
            #[inline] fn safe_pow(self, exp: i32) -> Option<Self::Output> { (*self).safe_pow(exp) }
        }
    };
}

impl_safe_arith_ref!(i8);
impl_safe_arith_ref!(i16);
impl_safe_arith_ref!(i32);
impl_safe_arith_ref!(i64);
impl_safe_arith_ref!(i128);
impl_safe_arith_ref!(isize);
impl_safe_arith_ref!(u8);
impl_safe_arith_ref!(u16);
impl_safe_arith_ref!(u32);
impl_safe_arith_ref!(u64);
impl_safe_arith_ref!(u128);
impl_safe_arith_ref!(usize);
impl_safe_arith_ref!(f32);
impl_safe_arith_ref!(f64);
impl_safe_arith_ref!(bool);

// ─── Bool impl ──────────────────────────────────────────────────────────────
//
// Booleans form a semiring under `(||, false)` addition and `(&&, true)`
// multiplication. `safe_*` methods follow that convention so `safe_sum` on a
// `Vec<bool>` is a logical OR and `safe_product` is a logical AND. Subtract,
// divide, remainder, and negation-as-Additive-inverse are meaningless for
// booleans and return `None`; `safe_neg` maps to logical `!` so that
// `safe_neg(false) == Some(true)` — this matches the `Not` trait.

impl SafeArith for bool {
    type Output = Self;
    #[inline]
    fn safe_add(self, rhs: Self) -> Option<Self> { Some(self || rhs) }
    #[inline]
    fn safe_sub(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_mul(self, rhs: Self) -> Option<Self> { Some(self && rhs) }
    #[inline]
    fn safe_div(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_rem(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_neg(self) -> Option<Self> { Some(!self) }
    #[inline]
    fn safe_not(self) -> Option<Self> { Some(!self) }
    #[inline]
    fn safe_pow(self, _exp: i32) -> Option<Self> { None }
}

// ─── String impl ────────────────────────────────────────────────────────────
//
// Strings form a monoid under concatenation. `safe_add` is concat; the rest
// return `None`. Useful for rules that sum/concat a vector of strings.

impl SafeArith for String {
    type Output = Self;
    #[inline]
    fn safe_add(self, rhs: Self) -> Option<Self> {
        let mut out = self;
        out.push_str(&rhs);
        Some(out)
    }
    #[inline]
    fn safe_sub(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_mul(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_div(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_rem(self, _rhs: Self) -> Option<Self> { None }
    #[inline]
    fn safe_neg(self) -> Option<Self> { None }
    #[inline]
    fn safe_not(self) -> Option<Self> { None }
    #[inline]
    fn safe_pow(self, _exp: i32) -> Option<Self> { None }
}

// ─── Float impls ────────────────────────────────────────────────────────────
//
// Float arithmetic never panics in Rust (IEEE semantics: overflow → ±Inf,
// undefined → NaN). `SafeArith` for floats rejects `NaN` results (`None`) but
// preserves `±Inf` as `Some(±Inf)`. Rationale:
//   - `NaN` is the indeterminate form; propagating it through rewrites would
//     produce unstable / meaningless results that poison hash keys.
//   - `±Inf` is a valid element of the extended reals, ordered, hashable,
//     and used by log-domain / tropical semirings. Codegen that wants to
//     *reject* `Inf` (e.g., in a rewrite rule) adds an outer `.is_finite()`
//     filter; callers that want to *preserve* `Inf` (e.g., the tropical
//     semiring) call the trait directly.
//   - `-0.0` is normalised to `+0.0` in `safe_neg` to match
//     `CanonicalFloat64::canonicalize` — otherwise the rewritten eval would
//     disagree with the wrapper's canonical equality.

use crate::canonical_float::{CanonicalFloat32, CanonicalFloat64};

/// Convert a raw float to `Some(value)` unless it is `NaN`.
///
/// Used by every `SafeArith` impl for `f32`/`f64` so the policy lives in one
/// place.
#[inline]
fn finite_or_inf_f64(x: f64) -> Option<f64> {
    if x.is_nan() { None } else { Some(x) }
}

#[inline]
fn finite_or_inf_f32(x: f32) -> Option<f32> {
    if x.is_nan() { None } else { Some(x) }
}

/// Float-only extension trait for transcendental functions.
///
/// These wrap `f64::sqrt`, `f64::ln`, etc., in the same NaN-rejecting policy as
/// `SafeArith`. Not part of `SafeArith` itself because integers can't sensibly
/// have `sqrt` / `ln`, and we want the trait to be implementable uniformly.
pub trait SafeFloat: SafeArith {
    fn safe_sqrt(self) -> Option<Self>;
    fn safe_ln(self) -> Option<Self>;
    fn safe_log2(self) -> Option<Self>;
    fn safe_log10(self) -> Option<Self>;
    fn safe_exp(self) -> Option<Self>;
    fn safe_sin(self) -> Option<Self>;
    fn safe_cos(self) -> Option<Self>;
    fn safe_tan(self) -> Option<Self>;
    fn safe_asin(self) -> Option<Self>;
    fn safe_acos(self) -> Option<Self>;
    fn safe_atan(self) -> Option<Self>;
    /// Floating-point exponent (distinct from `SafeArith::safe_pow`'s integer
    /// exponent). Used by the rewriter for `.powf(...)` method calls.
    fn safe_powf(self, exp: Self) -> Option<Self>;
}

impl SafeArith for f64 {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { finite_or_inf_f64(self + r) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { finite_or_inf_f64(self - r) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { finite_or_inf_f64(self * r) }
    #[inline] fn safe_div(self, r: Self) -> Option<Self> { finite_or_inf_f64(self / r) }
    #[inline] fn safe_rem(self, r: Self) -> Option<Self> { finite_or_inf_f64(self % r) }
    #[inline] fn safe_neg(self) -> Option<Self> {
        // Normalise `-0.0` to `+0.0` (matches CanonicalFloat64 canonicalisation).
        let r = -self;
        let r = if r == 0.0 { 0.0_f64 } else { r };
        finite_or_inf_f64(r)
    }
    #[inline] fn safe_not(self) -> Option<Self> { None }
    #[inline] fn safe_pow(self, exp: i32) -> Option<Self> { finite_or_inf_f64(self.powi(exp)) }
}

impl SafeFloat for f64 {
    #[inline] fn safe_sqrt(self)  -> Option<Self> { finite_or_inf_f64(self.sqrt()) }
    #[inline] fn safe_ln(self)    -> Option<Self> { finite_or_inf_f64(self.ln()) }
    #[inline] fn safe_log2(self)  -> Option<Self> { finite_or_inf_f64(self.log2()) }
    #[inline] fn safe_log10(self) -> Option<Self> { finite_or_inf_f64(self.log10()) }
    #[inline] fn safe_exp(self)   -> Option<Self> { finite_or_inf_f64(self.exp()) }
    #[inline] fn safe_sin(self)   -> Option<Self> { finite_or_inf_f64(self.sin()) }
    #[inline] fn safe_cos(self)   -> Option<Self> { finite_or_inf_f64(self.cos()) }
    #[inline] fn safe_tan(self)   -> Option<Self> { finite_or_inf_f64(self.tan()) }
    #[inline] fn safe_asin(self)  -> Option<Self> { finite_or_inf_f64(self.asin()) }
    #[inline] fn safe_acos(self)  -> Option<Self> { finite_or_inf_f64(self.acos()) }
    #[inline] fn safe_atan(self)  -> Option<Self> { finite_or_inf_f64(self.atan()) }
    #[inline] fn safe_powf(self, exp: Self) -> Option<Self> { finite_or_inf_f64(self.powf(exp)) }
}

impl SafeArith for f32 {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { finite_or_inf_f32(self + r) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { finite_or_inf_f32(self - r) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { finite_or_inf_f32(self * r) }
    #[inline] fn safe_div(self, r: Self) -> Option<Self> { finite_or_inf_f32(self / r) }
    #[inline] fn safe_rem(self, r: Self) -> Option<Self> { finite_or_inf_f32(self % r) }
    #[inline] fn safe_neg(self) -> Option<Self> {
        let r = -self;
        let r = if r == 0.0_f32 { 0.0_f32 } else { r };
        finite_or_inf_f32(r)
    }
    #[inline] fn safe_not(self) -> Option<Self> { None }
    #[inline] fn safe_pow(self, exp: i32) -> Option<Self> { finite_or_inf_f32(self.powi(exp)) }
}

impl SafeFloat for f32 {
    #[inline] fn safe_sqrt(self)  -> Option<Self> { finite_or_inf_f32(self.sqrt()) }
    #[inline] fn safe_ln(self)    -> Option<Self> { finite_or_inf_f32(self.ln()) }
    #[inline] fn safe_log2(self)  -> Option<Self> { finite_or_inf_f32(self.log2()) }
    #[inline] fn safe_log10(self) -> Option<Self> { finite_or_inf_f32(self.log10()) }
    #[inline] fn safe_exp(self)   -> Option<Self> { finite_or_inf_f32(self.exp()) }
    #[inline] fn safe_sin(self)   -> Option<Self> { finite_or_inf_f32(self.sin()) }
    #[inline] fn safe_cos(self)   -> Option<Self> { finite_or_inf_f32(self.cos()) }
    #[inline] fn safe_tan(self)   -> Option<Self> { finite_or_inf_f32(self.tan()) }
    #[inline] fn safe_asin(self)  -> Option<Self> { finite_or_inf_f32(self.asin()) }
    #[inline] fn safe_acos(self)  -> Option<Self> { finite_or_inf_f32(self.acos()) }
    #[inline] fn safe_atan(self)  -> Option<Self> { finite_or_inf_f32(self.atan()) }
    #[inline] fn safe_powf(self, exp: Self) -> Option<Self> { finite_or_inf_f32(self.powf(exp)) }
}

// Wrapper-type impls: delegate to the raw float impl, then re-canonicalise via
// `From<f64>` / `From<f32>` (which maps `-0.0` → `+0.0` and all NaNs to one
// canonical NaN — but `SafeArith` already rejects NaN before `.from` runs, so
// canonicalisation is a defence-in-depth measure).

impl SafeArith for CanonicalFloat64 {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { self.get().safe_add(r.get()).map(Self::from) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { self.get().safe_sub(r.get()).map(Self::from) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { self.get().safe_mul(r.get()).map(Self::from) }
    #[inline] fn safe_div(self, r: Self) -> Option<Self> { self.get().safe_div(r.get()).map(Self::from) }
    #[inline] fn safe_rem(self, r: Self) -> Option<Self> { self.get().safe_rem(r.get()).map(Self::from) }
    #[inline] fn safe_neg(self) -> Option<Self> { self.get().safe_neg().map(Self::from) }
    #[inline] fn safe_not(self) -> Option<Self> { None }
    #[inline] fn safe_pow(self, exp: i32) -> Option<Self> { self.get().safe_pow(exp).map(Self::from) }
}

impl SafeFloat for CanonicalFloat64 {
    #[inline] fn safe_sqrt(self)  -> Option<Self> { self.get().safe_sqrt().map(Self::from) }
    #[inline] fn safe_ln(self)    -> Option<Self> { self.get().safe_ln().map(Self::from) }
    #[inline] fn safe_log2(self)  -> Option<Self> { self.get().safe_log2().map(Self::from) }
    #[inline] fn safe_log10(self) -> Option<Self> { self.get().safe_log10().map(Self::from) }
    #[inline] fn safe_exp(self)   -> Option<Self> { self.get().safe_exp().map(Self::from) }
    #[inline] fn safe_sin(self)   -> Option<Self> { self.get().safe_sin().map(Self::from) }
    #[inline] fn safe_cos(self)   -> Option<Self> { self.get().safe_cos().map(Self::from) }
    #[inline] fn safe_tan(self)   -> Option<Self> { self.get().safe_tan().map(Self::from) }
    #[inline] fn safe_asin(self)  -> Option<Self> { self.get().safe_asin().map(Self::from) }
    #[inline] fn safe_acos(self)  -> Option<Self> { self.get().safe_acos().map(Self::from) }
    #[inline] fn safe_atan(self)  -> Option<Self> { self.get().safe_atan().map(Self::from) }
    #[inline] fn safe_powf(self, exp: Self) -> Option<Self> { self.get().safe_powf(exp.get()).map(Self::from) }
}

impl SafeArith for CanonicalFloat32 {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { self.get().safe_add(r.get()).map(Self::from) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { self.get().safe_sub(r.get()).map(Self::from) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { self.get().safe_mul(r.get()).map(Self::from) }
    #[inline] fn safe_div(self, r: Self) -> Option<Self> { self.get().safe_div(r.get()).map(Self::from) }
    #[inline] fn safe_rem(self, r: Self) -> Option<Self> { self.get().safe_rem(r.get()).map(Self::from) }
    #[inline] fn safe_neg(self) -> Option<Self> { self.get().safe_neg().map(Self::from) }
    #[inline] fn safe_not(self) -> Option<Self> { None }
    #[inline] fn safe_pow(self, exp: i32) -> Option<Self> { self.get().safe_pow(exp).map(Self::from) }
}

impl SafeFloat for CanonicalFloat32 {
    #[inline] fn safe_sqrt(self)  -> Option<Self> { self.get().safe_sqrt().map(Self::from) }
    #[inline] fn safe_ln(self)    -> Option<Self> { self.get().safe_ln().map(Self::from) }
    #[inline] fn safe_log2(self)  -> Option<Self> { self.get().safe_log2().map(Self::from) }
    #[inline] fn safe_log10(self) -> Option<Self> { self.get().safe_log10().map(Self::from) }
    #[inline] fn safe_exp(self)   -> Option<Self> { self.get().safe_exp().map(Self::from) }
    #[inline] fn safe_sin(self)   -> Option<Self> { self.get().safe_sin().map(Self::from) }
    #[inline] fn safe_cos(self)   -> Option<Self> { self.get().safe_cos().map(Self::from) }
    #[inline] fn safe_tan(self)   -> Option<Self> { self.get().safe_tan().map(Self::from) }
    #[inline] fn safe_asin(self)  -> Option<Self> { self.get().safe_asin().map(Self::from) }
    #[inline] fn safe_acos(self)  -> Option<Self> { self.get().safe_acos().map(Self::from) }
    #[inline] fn safe_atan(self)  -> Option<Self> { self.get().safe_atan().map(Self::from) }
    #[inline] fn safe_powf(self, exp: Self) -> Option<Self> { self.get().safe_powf(exp.get()).map(Self::from) }
}

// ─── Arbitrary-precision impls ──────────────────────────────────────────────
//
// `CanonicalBigInt`/`CanonicalBigRat`/`CanonicalFixedPoint` cannot overflow the
// way bounded integers do, so most operations always succeed. Division/remainder
// by zero return `None`. Power with negative exponent on `CanonicalBigInt` is
// `None` (not representable in the same type); `CanonicalBigRat` supports
// negative powers via reciprocation; `CanonicalFixedPoint` clamps to non-negative.

// `&num_bigint::BigInt` impl: the safeify pass rewrites `a.get() - b.get()`
// inside user `![…]` bodies to `SafeArith::safe_sub(a.get(), b.get())?`.
// `CanonicalBigInt::get()` returns `&BigInt`, so the rewrite receives
// references. The arithmetic produces an owned `BigInt`, which the caller
// wraps back into `CanonicalBigInt::from(result)` via its original body.
// Arbitrary precision cannot overflow, so only division / remainder by zero
// yield `None`; negative exponents also yield `None`.
impl SafeArith for &num_bigint::BigInt {
    type Output = num_bigint::BigInt;
    #[inline] fn safe_add(self, r: Self) -> Option<Self::Output> { Some(self + r) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self::Output> { Some(self - r) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self::Output> { Some(self * r) }
    #[inline]
    fn safe_div(self, r: Self) -> Option<Self::Output> {
        use num_traits::Zero;
        if r.is_zero() { None } else { Some(self / r) }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Option<Self::Output> {
        use num_traits::Zero;
        if r.is_zero() { None } else { Some(self % r) }
    }
    #[inline] fn safe_neg(self) -> Option<Self::Output> { Some(-self) }
    #[inline] fn safe_not(self) -> Option<Self::Output> { Some(!self.clone()) }
    #[inline]
    fn safe_pow(self, exp: i32) -> Option<Self::Output> {
        if exp < 0 { return None; }
        Some(num_traits::pow::pow(self.clone(), exp as usize))
    }
}

// Owned `num_bigint::BigInt` impl: needed when user code produces an owned
// BigInt via `a.get().clone()` or similar. Arbitrary precision, no overflow;
// same semantics as the `&BigInt` impl but takes Self by value.
impl SafeArith for num_bigint::BigInt {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { Some(self + r) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { Some(self - r) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { Some(self * r) }
    #[inline]
    fn safe_div(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.is_zero() { None } else { Some(self / r) }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.is_zero() { None } else { Some(self % r) }
    }
    #[inline] fn safe_neg(self) -> Option<Self> { Some(-self) }
    #[inline] fn safe_not(self) -> Option<Self> { Some(!self) }
    #[inline]
    fn safe_pow(self, exp: i32) -> Option<Self> {
        if exp < 0 { return None; }
        Some(num_traits::pow::pow(self, exp as usize))
    }
}

impl SafeArith for crate::CanonicalBigInt {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { Some(Self::from(self.get() + r.get())) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { Some(Self::from(self.get() - r.get())) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { Some(Self::from(self.get() * r.get())) }
    #[inline]
    fn safe_div(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.get().is_zero() { None } else { Some(Self::from(self.get() / r.get())) }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.get().is_zero() { None } else { Some(Self::from(self.get() % r.get())) }
    }
    #[inline] fn safe_neg(self) -> Option<Self> { Some(Self::from(-self.get())) }
    #[inline] fn safe_not(self) -> Option<Self> { Some(Self::from(!self.get().clone())) }
    #[inline]
    fn safe_pow(self, exp: i32) -> Option<Self> {
        if exp < 0 { return None; } // negative exponent: reciprocal not in BigInt
        Some(Self::from(num_traits::pow::pow(self.get().clone(), exp as usize)))
    }
}

impl SafeArith for crate::CanonicalBigRat {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { Some(Self::from(self.get() + r.get())) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { Some(Self::from(self.get() - r.get())) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { Some(Self::from(self.get() * r.get())) }
    #[inline]
    fn safe_div(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.get().is_zero() { None } else { Some(Self::from(self.get() / r.get())) }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.get().is_zero() { None } else { Some(Self::from(self.get() % r.get())) }
    }
    #[inline] fn safe_neg(self) -> Option<Self> { Some(Self::from(-self.get())) }
    #[inline]
    fn safe_not(self) -> Option<Self> {
        // Bitwise NOT on a rational: flip the numerator bits, keep denominator.
        // Matches the user-level `bitnot_aligned` semantics; since Ratio
        // doesn't define `!`, delegate to BigInt.
        let (n, d) = (self.get().numer().clone(), self.get().denom().clone());
        Some(Self::from(num_rational::Ratio::new(!n, d)))
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Option<Self> {
        Some(Self::from(num_traits::pow::Pow::pow(self.get().clone(), exp)))
    }
}

impl SafeArith for crate::CanonicalFixedPoint {
    type Output = Self;
    #[inline] fn safe_add(self, r: Self) -> Option<Self> { Some(self + r) }
    #[inline] fn safe_sub(self, r: Self) -> Option<Self> { Some(self - r) }
    #[inline] fn safe_mul(self, r: Self) -> Option<Self> { Some(self * r) }
    #[inline]
    fn safe_div(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.unscaled().is_zero() { None } else { Some(self / r) }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Option<Self> {
        use num_traits::Zero;
        if r.unscaled().is_zero() { None } else { Some(self % r) }
    }
    #[inline] fn safe_neg(self) -> Option<Self> { Some(-self) }
    #[inline]
    fn safe_not(self) -> Option<Self> {
        // Bitwise NOT on a fixed-point: flip the scaled integer bits,
        // keep the places. Matches user-level `bitnot_aligned` semantics.
        Some(Self::new(!self.unscaled().clone(), self.places()))
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Option<Self> {
        if exp < 0 { return None; }
        let mut acc = Self::new(num_bigint::BigInt::from(1), 0);
        for _ in 0..exp {
            acc = acc * self.clone();
        }
        Some(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ─── i32 ─────────────────────────────────────────────────────────────
    #[test]
    fn i32_add_normal() {
        assert_eq!(1_i32.safe_add(2), Some(3));
    }

    #[test]
    fn i32_add_overflow() {
        assert_eq!(i32::MAX.safe_add(1), None);
    }

    #[test]
    fn i32_sub_underflow() {
        assert_eq!(i32::MIN.safe_sub(1), None);
    }

    #[test]
    fn i32_mul_overflow() {
        assert_eq!(i32::MAX.safe_mul(2), None);
    }

    #[test]
    fn i32_div_by_zero() {
        assert_eq!(1_i32.safe_div(0), None);
    }

    #[test]
    fn i32_rem_by_zero() {
        assert_eq!(1_i32.safe_rem(0), None);
    }

    #[test]
    fn i32_div_min_by_neg_one_overflows() {
        assert_eq!(i32::MIN.safe_div(-1), None);
    }

    #[test]
    fn i32_neg_min_overflows() {
        // i32::MIN has no positive counterpart.
        assert_eq!(i32::MIN.safe_neg(), None);
    }

    #[test]
    fn i32_pow_normal() {
        assert_eq!(2_i32.safe_pow(10), Some(1024));
    }

    #[test]
    fn i32_pow_overflow() {
        assert_eq!(2_i32.safe_pow(31), None);
    }

    #[test]
    fn i32_pow_negative_exponent_is_none() {
        assert_eq!(2_i32.safe_pow(-1), None);
    }

    #[test]
    fn i32_product_overflow_short_circuits() {
        let factorial_50 = (1..=50_i32).collect::<Vec<_>>();
        assert_eq!(i32::safe_product(factorial_50), None);
    }

    #[test]
    fn i32_product_finite() {
        let factorial_12 = (1..=12_i32).collect::<Vec<_>>();
        assert_eq!(i32::safe_product(factorial_12), Some(479_001_600));
    }

    #[test]
    fn i32_sum_overflow_short_circuits() {
        let chain = vec![i32::MAX, 1];
        assert_eq!(i32::safe_sum(chain), None);
    }

    #[test]
    fn i32_sum_normal() {
        let xs = vec![1, 2, 3, 4, 5];
        assert_eq!(i32::safe_sum(xs), Some(15));
    }

    // ─── u32 ─────────────────────────────────────────────────────────────
    #[test]
    fn u32_sub_underflow() {
        assert_eq!(0_u32.safe_sub(1), None);
    }

    #[test]
    fn u32_neg_zero_is_zero() {
        assert_eq!(0_u32.safe_neg(), Some(0));
    }

    #[test]
    fn u32_neg_nonzero_is_none() {
        assert_eq!(1_u32.safe_neg(), None);
    }

    // ─── i64 ─────────────────────────────────────────────────────────────
    #[test]
    fn i64_mul_overflow() {
        assert_eq!(i64::MAX.safe_mul(2), None);
    }

    #[test]
    fn i64_factorial_20_fits() {
        // 20! = 2432902008176640000, within i64
        let f = (1..=20_i64).collect::<Vec<_>>();
        assert_eq!(i64::safe_product(f), Some(2_432_902_008_176_640_000));
    }

    #[test]
    fn i64_factorial_21_overflows() {
        let f = (1..=21_i64).collect::<Vec<_>>();
        assert_eq!(i64::safe_product(f), None);
    }

    // ─── bool ────────────────────────────────────────────────────────────
    #[test]
    fn bool_add_is_or() {
        assert_eq!(true.safe_add(false), Some(true));
        assert_eq!(false.safe_add(false), Some(false));
    }

    #[test]
    fn bool_mul_is_and() {
        assert_eq!(true.safe_mul(true), Some(true));
        assert_eq!(true.safe_mul(false), Some(false));
    }

    #[test]
    fn bool_neg_is_not() {
        assert_eq!(true.safe_neg(), Some(false));
        assert_eq!(false.safe_neg(), Some(true));
    }

    #[test]
    fn bool_sub_div_rem_pow_are_none() {
        assert_eq!(true.safe_sub(false), None);
        assert_eq!(true.safe_div(false), None);
        assert_eq!(true.safe_rem(false), None);
        assert_eq!(true.safe_pow(2), None);
    }

    // ─── String ──────────────────────────────────────────────────────────
    #[test]
    fn string_add_concats() {
        let a = "hello".to_string();
        let b = ", world".to_string();
        assert_eq!(a.safe_add(b), Some("hello, world".to_string()));
    }

    #[test]
    fn string_other_ops_none() {
        let a = "x".to_string();
        assert_eq!(a.clone().safe_sub("y".to_string()), None);
        assert_eq!(a.clone().safe_mul("y".to_string()), None);
        assert_eq!(a.safe_neg(), None);
    }

    // ─── f64 ─────────────────────────────────────────────────────────────
    #[test]
    fn f64_add_finite() {
        assert_eq!(1.0_f64.safe_add(2.0), Some(3.0));
    }

    #[test]
    fn f64_add_overflow_to_inf_is_some() {
        // MAX + MAX saturates to +Inf, which SafeArith preserves.
        let r = f64::MAX.safe_add(f64::MAX);
        assert_eq!(r, Some(f64::INFINITY));
    }

    #[test]
    fn f64_add_inf_minus_inf_is_none() {
        // +Inf + -Inf is NaN in IEEE, rejected by SafeArith.
        assert_eq!(f64::INFINITY.safe_add(f64::NEG_INFINITY), None);
    }

    #[test]
    fn f64_add_nan_is_none() {
        assert_eq!(f64::NAN.safe_add(1.0), None);
        assert_eq!(1.0_f64.safe_add(f64::NAN), None);
    }

    #[test]
    fn f64_div_by_zero_positive_is_inf() {
        assert_eq!(1.0_f64.safe_div(0.0), Some(f64::INFINITY));
    }

    #[test]
    fn f64_div_by_zero_negative_is_neg_inf() {
        assert_eq!((-1.0_f64).safe_div(0.0), Some(f64::NEG_INFINITY));
    }

    #[test]
    fn f64_zero_div_zero_is_none() {
        assert_eq!(0.0_f64.safe_div(0.0), None);
    }

    #[test]
    fn f64_rem_by_zero_is_none() {
        assert_eq!(1.0_f64.safe_rem(0.0), None);
    }

    #[test]
    fn f64_neg_zero_normalises_to_positive_zero() {
        let r = 0.0_f64.safe_neg().unwrap();
        assert_eq!(r, 0.0);
        assert!(!r.is_sign_negative(),
                "safe_neg(0.0) must produce +0.0 (found -0.0) to match CanonicalFloat64");
    }

    #[test]
    fn f64_pow_zero_neg_one_is_inf() {
        // 0.powi(-1) = 1/0 = +Inf
        assert_eq!(0.0_f64.safe_pow(-1), Some(f64::INFINITY));
    }

    #[test]
    fn f64_powf_neg_root_is_none() {
        // sqrt(-1) = NaN
        assert_eq!((-1.0_f64).safe_powf(0.5), None);
    }

    #[test]
    fn f64_sqrt_negative_is_none() {
        assert_eq!((-1.0_f64).safe_sqrt(), None);
    }

    #[test]
    fn f64_ln_zero_is_neg_inf() {
        // ln(0) = -Inf
        assert_eq!(0.0_f64.safe_ln(), Some(f64::NEG_INFINITY));
    }

    #[test]
    fn f64_ln_negative_is_none() {
        assert_eq!((-1.0_f64).safe_ln(), None);
    }

    #[test]
    fn f64_product_short_circuits_on_nan() {
        use std::cell::Cell;
        let count = Cell::new(0_usize);
        // Iterator that yields 1.0, 2.0, NaN, 4.0. If short-circuit works, count ≤ 3.
        let iter = (0..4).map(|i| {
            count.set(count.get() + 1);
            match i { 0 => 1.0, 1 => 2.0, 2 => f64::NAN, _ => 4.0 }
        });
        assert_eq!(f64::safe_product(iter), None);
        assert!(count.get() <= 3,
                "safe_product should short-circuit on NaN, consumed {}", count.get());
    }

    #[test]
    fn f64_product_with_inf_is_some() {
        // Product that saturates to +Inf should still be Some(Inf) — the NaN
        // gate only rejects indeterminate results.
        let xs = vec![1e300_f64, 1e300, 1e300];
        let r = f64::safe_product(xs);
        assert_eq!(r, Some(f64::INFINITY));
    }

    #[test]
    fn f64_sum_mixed_inf_is_none() {
        // +Inf + -Inf = NaN.
        let xs = vec![f64::INFINITY, f64::NEG_INFINITY];
        assert_eq!(f64::safe_sum(xs), None);
    }

    #[test]
    fn f64_subnormal_passes_through() {
        // Subnormal numbers are finite and valid; never rejected.
        let small = f64::MIN_POSITIVE / 2.0;
        assert!(small > 0.0 && small.is_finite());
        assert_eq!(small.safe_add(0.0), Some(small));
        assert_eq!(small.safe_mul(1.0), Some(small));
    }

    // ─── CanonicalFloat64 ────────────────────────────────────────────────
    #[test]
    fn canonical_f64_delegates_to_f64() {
        let a = CanonicalFloat64::from(1.0);
        let b = CanonicalFloat64::from(2.0);
        assert_eq!(a.safe_add(b), Some(CanonicalFloat64::from(3.0)));
    }

    #[test]
    fn canonical_f64_inf_round_trips() {
        let a = CanonicalFloat64::from(1.0);
        let z = CanonicalFloat64::from(0.0);
        let r = a.safe_div(z).expect("1.0 / 0.0 should be Some(+Inf)");
        assert!(r.get().is_infinite());
    }

    #[test]
    fn canonical_f64_nan_input_rejected() {
        // Constructing a NaN CanonicalFloat64, then doing an op on it, returns None.
        let nan = CanonicalFloat64::from(f64::NAN);
        assert_eq!(nan.safe_add(CanonicalFloat64::from(1.0)), None);
    }

    #[test]
    fn canonical_f64_try_finite_rejects_nan() {
        assert!(CanonicalFloat64::try_finite(f64::NAN).is_none());
        assert_eq!(CanonicalFloat64::try_finite(1.0), Some(CanonicalFloat64::from(1.0)));
        // Inf is accepted.
        assert!(CanonicalFloat64::try_finite(f64::INFINITY).is_some());
    }

    #[test]
    fn canonical_f64_product_identity() {
        // Empty product is the multiplicative identity (1.0).
        let empty: Vec<CanonicalFloat64> = vec![];
        assert_eq!(CanonicalFloat64::safe_product(empty), Some(CanonicalFloat64::from(1.0)));
    }

    #[test]
    fn canonical_f64_sum_identity() {
        let empty: Vec<CanonicalFloat64> = vec![];
        assert_eq!(CanonicalFloat64::safe_sum(empty), Some(CanonicalFloat64::from(0.0)));
    }

    // ─── f32 (sanity) ────────────────────────────────────────────────────
    #[test]
    fn f32_nan_rejected() {
        assert_eq!(f32::NAN.safe_add(1.0), None);
    }

    #[test]
    fn f32_inf_preserved() {
        assert_eq!(f32::MAX.safe_add(f32::MAX), Some(f32::INFINITY));
    }
}
