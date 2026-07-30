//! Overflow-safe and NaN-safe arithmetic for native-type category evaluation.
//!
//! The `language!` macro lets users write arbitrary Rust inside `![...]` blocks
//! (e.g., `![a + b]`, `![{ (1..=a).product::<i32>() }]`). At runtime, these
//! expressions execute inside the evaluator and inside Ascent datalog rewrite
//! rules. Panicking arithmetic (integer overflow in debug mode) propagates as
//! a panic, which is at best swallowed by `catch_unwind` and at worst causes a
//! double-panic SIGABRT under proptest/nextest.
//!
//! This module defines a trait `SafeArith` whose methods return
//! `Result<T, Partiality>`: on overflow, `NaN`, or an undefined input the caller
//! receives a value that says **which** partiality occurred, letting "this rule
//! can't fire on this input" be a *reported* value rather than a control-flow
//! event. Each call to a `safe_*` method is a self-contained step — a
//! trampoline-friendly shape that composes cleanly with the PDA-based tree
//! walker in `eval.rs`.
//!
//! ## Policy
//!
//! - **Integers** — delegate to `checked_*` from the stdlib. Overflow →
//!   [`Partiality::NotRepresentable`]; a zero divisor/modulus →
//!   [`UndefinedReason::DivisionByZero`] / [`UndefinedReason::RemainderByZero`].
//! - **Floats** — compute the IEEE result; decline iff the result is `NaN`
//!   ([`UndefinedReason::NotANumber`]). `±Inf` is preserved as `Ok(±Inf)`
//!   because it is a legitimate extended-real value (used by log-domain /
//!   tropical semirings). The `language!` macro's rewrite pass wraps the outer
//!   closure with an additional `is_finite` filter so that rewrite rules do not
//!   fire on `Inf`; code that wants `Inf` in a fold (e.g., tropical min) calls
//!   the trait directly.
//! - **`-0.0`** — normalised to `+0.0` in `safe_neg`, matching
//!   `CanonicalFloat64`'s existing canonicalisation.
//!
//! ## Why a trait, not free functions
//!
//! `safe_product` / `safe_sum` need to fold over iterators of unknown element
//! type. Dispatch through `Self` keeps the generated code monomorphic per
//! category without forcing callers to specify the type twice.
//!
//! ## ⚠ Carrier naming for wrapper types
//!
//! `CanonicalFloat32` / `CanonicalFloat64` delegate to the raw `f32` / `f64`
//! impls and therefore report `carrier: "f32"` / `"f64"`. That is deliberate and
//! accurate: the canonical wrappers are newtypes over exactly those IEEE
//! carriers, and the deployer's remedy (widen, or guard the input) is a property
//! of the IEEE carrier, not of the wrapper. The arbitrary-precision types report
//! the grammar-facing carrier names `"BigInt"` / `"BigRat"` / `"FixedPoint"`.

use crate::partiality::{Partiality, UndefinedReason};

/// Overflow-safe arithmetic. Every method returns `Result<Self::Output, Partiality>`.
///
/// ★ The error channel **distinguishes the three partialities** that used to share one `None`:
///
/// | input | disposition | why |
/// |---|---|---|
/// | `1 / 0` | [`Partiality::Undefined`] with [`UndefinedReason::DivisionByZero`] | no carrier supplies a quotient — case **(a)** |
/// | `0.0 / 0.0`, `Inf - Inf` | [`Partiality::Undefined`] with [`UndefinedReason::NotANumber`] | the IEEE indeterminate form — case **(a)** |
/// | `i64::MAX + 1` | [`Partiality::NotRepresentable`] naming `"i64"` | the value exists; THIS carrier is too narrow — case **(b)** |
///
/// The distinction is what lets a run report say *why* a fold declined instead of merely that it
/// did. It is also the (a)/(b) split of the partition rule in [`crate::partiality`]: (a) means no
/// reduction can supply a value, (b) means a lossless-promotion reading may still succeed in a
/// wider carrier and only the declining reading drops out.
///
/// ⚠ Every method is **total** — it never panics. That property is load-bearing and predates the
/// reason channel: a panic raised inside a fold body runs with the e-graph mid-saturation and, in
/// this workspace's cg_clif dev profile, is not containable by `catch_unwind`.
pub trait SafeArith: Sized {
    /// Result type for checked operations. Defaults to `Self` for owned-value
    /// impls (e.g. `i32`, `CanonicalBigInt`, `f64`). Reference impls like
    /// `&num_bigint::BigInt` set `Output` to the owned type so that
    /// `a.get() - b.get()` (which produces a new owned `BigInt`) still
    /// type-checks against the trait method signature.
    type Output;

    fn safe_add(self, rhs: Self) -> Result<Self::Output, Partiality>;
    fn safe_sub(self, rhs: Self) -> Result<Self::Output, Partiality>;
    fn safe_mul(self, rhs: Self) -> Result<Self::Output, Partiality>;
    fn safe_div(self, rhs: Self) -> Result<Self::Output, Partiality>;
    fn safe_rem(self, rhs: Self) -> Result<Self::Output, Partiality>;
    fn safe_neg(self) -> Result<Self::Output, Partiality>;

    /// Bitwise NOT. Used by the rewriter to handle user code like `!v`
    /// where `v` is an integer. For floats this is meaningless — declines with
    /// [`UndefinedReason::NotDefinedForCarrier`]. Integer impls return
    /// `Ok(!self)` unconditionally (bitwise NOT never overflows; `!T::MIN` for
    /// signed is `T::MAX` etc.).
    fn safe_not(self) -> Result<Self::Output, Partiality>;

    /// `self` raised to an integer power. Used by the rewriter to rewrite
    /// `.pow(n)` and `.powi(n)`. For floats, `safe_powf` handles the
    /// floating-point exponent case.
    fn safe_pow(self, exp: i32) -> Result<Self::Output, Partiality>;

    /// Fold-based product with short-circuit on the first decline. Each iteration is one
    /// checked multiplication; a single overflow or `NaN` aborts the fold and its reason is the
    /// reason the whole fold reports.
    fn safe_product<I: IntoIterator<Item = Self>>(iter: I) -> Result<Self::Output, Partiality>
    where
        Self: From<u8> + SafeArith<Output = Self>,
    {
        let mut acc = Self::from(1u8);
        for x in iter {
            acc = acc.safe_mul(x)?;
        }
        Ok(acc)
    }

    /// Fold-based sum with short-circuit on the first decline. Each iteration is one
    /// checked addition; a single overflow or `NaN` aborts the fold and its reason is the
    /// reason the whole fold reports.
    fn safe_sum<I: IntoIterator<Item = Self>>(iter: I) -> Result<Self::Output, Partiality>
    where
        Self: From<u8> + SafeArith<Output = Self>,
    {
        let mut acc = Self::from(0u8);
        for x in iter {
            acc = acc.safe_add(x)?;
        }
        Ok(acc)
    }
}

// ─── Integer impls ──────────────────────────────────────────────────────────
//
// Each impl delegates to the stdlib's `checked_*` family, then NAMES the
// partiality the `None` stood for:
//
//   * a zero divisor / modulus is `Undefined` — case (a), no carrier helps;
//   * every other `checked_*` failure is `NotRepresentable` naming the carrier
//     — case (b), a wider carrier would hold the value. That covers overflow,
//     `i::MIN / -1`, `i::MIN % -1`, and `-i::MIN`.
//
// `safe_pow` takes an `i32` exponent uniformly; a negative exponent is
// `Undefined(NegativeExponent)` for every integer carrier, because the value is
// rational and no wider INTEGER carrier holds it.

macro_rules! impl_safe_arith_signed {
    ($t:ty) => {
        impl SafeArith for $t {
            type Output = Self;
            #[inline]
            fn safe_add(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_add(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "add",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_sub(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_sub(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "sub",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_mul(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_mul(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "mul",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_div(self, rhs: Self) -> Result<Self, Partiality> {
                if rhs == 0 {
                    return Err(Partiality::Undefined {
                        operation: "div",
                        carrier: stringify!($t),
                        reason: UndefinedReason::DivisionByZero,
                    });
                }
                // The only surviving failure is the single overflowing quotient
                // `MIN / -1`, whose value exists one carrier up.
                self.checked_div(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "div",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_rem(self, rhs: Self) -> Result<Self, Partiality> {
                if rhs == 0 {
                    return Err(Partiality::Undefined {
                        operation: "rem",
                        carrier: stringify!($t),
                        reason: UndefinedReason::RemainderByZero,
                    });
                }
                self.checked_rem(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "rem",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_neg(self) -> Result<Self, Partiality> {
                self.checked_neg().ok_or(Partiality::NotRepresentable {
                    operation: "neg",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_not(self) -> Result<Self, Partiality> {
                Ok(!self)
            }
            #[inline]
            fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
                // Negative exponent on integer: result is not integral (e.g. 2^-1 = 1/2), and no
                // wider integer carrier holds it — so this is (a), not (b).
                if exp < 0 {
                    return Err(Partiality::Undefined {
                        operation: "pow",
                        carrier: stringify!($t),
                        reason: UndefinedReason::NegativeExponent,
                    });
                }
                self.checked_pow(exp as u32)
                    .ok_or(Partiality::NotRepresentable {
                        operation: "pow",
                        carrier: stringify!($t),
                    })
            }
        }
    };
}

macro_rules! impl_safe_arith_unsigned {
    ($t:ty) => {
        impl SafeArith for $t {
            type Output = Self;
            #[inline]
            fn safe_add(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_add(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "add",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_sub(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_sub(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "sub",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_mul(self, rhs: Self) -> Result<Self, Partiality> {
                self.checked_mul(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "mul",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_div(self, rhs: Self) -> Result<Self, Partiality> {
                if rhs == 0 {
                    return Err(Partiality::Undefined {
                        operation: "div",
                        carrier: stringify!($t),
                        reason: UndefinedReason::DivisionByZero,
                    });
                }
                self.checked_div(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "div",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_rem(self, rhs: Self) -> Result<Self, Partiality> {
                if rhs == 0 {
                    return Err(Partiality::Undefined {
                        operation: "rem",
                        carrier: stringify!($t),
                        reason: UndefinedReason::RemainderByZero,
                    });
                }
                self.checked_rem(rhs).ok_or(Partiality::NotRepresentable {
                    operation: "rem",
                    carrier: stringify!($t),
                })
            }
            #[inline]
            fn safe_neg(self) -> Result<Self, Partiality> {
                // 0_u* has a trivially representable negation (itself); every other value's
                // negation is a negative number, which exists in a signed carrier but not here.
                if self == 0 {
                    Ok(self)
                } else {
                    Err(Partiality::NotRepresentable {
                        operation: "neg",
                        carrier: stringify!($t),
                    })
                }
            }
            #[inline]
            fn safe_not(self) -> Result<Self, Partiality> {
                Ok(!self)
            }
            #[inline]
            fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
                if exp < 0 {
                    return Err(Partiality::Undefined {
                        operation: "pow",
                        carrier: stringify!($t),
                        reason: UndefinedReason::NegativeExponent,
                    });
                }
                self.checked_pow(exp as u32)
                    .ok_or(Partiality::NotRepresentable {
                        operation: "pow",
                        carrier: stringify!($t),
                    })
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
//
// The reported carrier is the VALUE type's, because each method dereferences
// and delegates: a reference to an `i64` overflows as an `i64`.
macro_rules! impl_safe_arith_ref {
    ($t:ty) => {
        impl SafeArith for &$t {
            type Output = <$t as SafeArith>::Output;
            #[inline]
            fn safe_add(self, rhs: Self) -> Result<Self::Output, Partiality> {
                (*self).safe_add(*rhs)
            }
            #[inline]
            fn safe_sub(self, rhs: Self) -> Result<Self::Output, Partiality> {
                (*self).safe_sub(*rhs)
            }
            #[inline]
            fn safe_mul(self, rhs: Self) -> Result<Self::Output, Partiality> {
                (*self).safe_mul(*rhs)
            }
            #[inline]
            fn safe_div(self, rhs: Self) -> Result<Self::Output, Partiality> {
                (*self).safe_div(*rhs)
            }
            #[inline]
            fn safe_rem(self, rhs: Self) -> Result<Self::Output, Partiality> {
                (*self).safe_rem(*rhs)
            }
            #[inline]
            fn safe_neg(self) -> Result<Self::Output, Partiality> {
                (*self).safe_neg()
            }
            #[inline]
            fn safe_not(self) -> Result<Self::Output, Partiality> {
                (*self).safe_not()
            }
            #[inline]
            fn safe_pow(self, exp: i32) -> Result<Self::Output, Partiality> {
                (*self).safe_pow(exp)
            }
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
// divide, remainder, and exponentiation are meaningless for booleans and
// decline with `NotDefinedForCarrier` — case (a): no wider carrier defines
// them either. `safe_neg` maps to logical `!` so that
// `safe_neg(false) == Ok(true)` — this matches the `Not` trait.

/// `bool` has no arithmetic subtraction / division / remainder / power.
#[inline]
const fn bool_not_defined(operation: &'static str) -> Partiality {
    Partiality::Undefined {
        operation,
        carrier: "bool",
        reason: UndefinedReason::NotDefinedForCarrier,
    }
}

impl SafeArith for bool {
    type Output = Self;
    #[inline]
    fn safe_add(self, rhs: Self) -> Result<Self, Partiality> {
        Ok(self || rhs)
    }
    #[inline]
    fn safe_sub(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(bool_not_defined("sub"))
    }
    #[inline]
    fn safe_mul(self, rhs: Self) -> Result<Self, Partiality> {
        Ok(self && rhs)
    }
    #[inline]
    fn safe_div(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(bool_not_defined("div"))
    }
    #[inline]
    fn safe_rem(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(bool_not_defined("rem"))
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Ok(!self)
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Ok(!self)
    }
    #[inline]
    fn safe_pow(self, _exp: i32) -> Result<Self, Partiality> {
        Err(bool_not_defined("pow"))
    }
}

// ─── String impl ────────────────────────────────────────────────────────────
//
// Strings form a monoid under concatenation. `safe_add` is concat; every other
// operation declines with `NotDefinedForCarrier`. Useful for rules that
// sum/concat a vector of strings.

/// `String` is a concatenation monoid and nothing more.
#[inline]
const fn string_not_defined(operation: &'static str) -> Partiality {
    Partiality::Undefined {
        operation,
        carrier: "String",
        reason: UndefinedReason::NotDefinedForCarrier,
    }
}

impl SafeArith for String {
    type Output = Self;
    #[inline]
    fn safe_add(self, rhs: Self) -> Result<Self, Partiality> {
        let mut out = self;
        out.push_str(&rhs);
        Ok(out)
    }
    #[inline]
    fn safe_sub(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(string_not_defined("sub"))
    }
    #[inline]
    fn safe_mul(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(string_not_defined("mul"))
    }
    #[inline]
    fn safe_div(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(string_not_defined("div"))
    }
    #[inline]
    fn safe_rem(self, _rhs: Self) -> Result<Self, Partiality> {
        Err(string_not_defined("rem"))
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Err(string_not_defined("neg"))
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Err(string_not_defined("not"))
    }
    #[inline]
    fn safe_pow(self, _exp: i32) -> Result<Self, Partiality> {
        Err(string_not_defined("pow"))
    }
}

// ─── Float impls ────────────────────────────────────────────────────────────
//
// Float arithmetic never panics in Rust (IEEE semantics: overflow → ±Inf,
// undefined → NaN). `SafeArith` for floats declines a `NaN` result with
// `Undefined(NotANumber)` but preserves `±Inf` as `Ok(±Inf)`. Rationale:
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
//
// ⚠ NaN is case (a), NOT case (b): no wider float carrier gives `0.0 / 0.0` a
// value. That is why the float path never produces `NotRepresentable`.

use crate::canonical_float::{CanonicalFloat32, CanonicalFloat64};

/// Accept a raw `f64` unless it is `NaN`, naming the operation that produced it.
///
/// Used by every `SafeArith` / `SafeFloat` impl for `f64` so the policy — and the reason it
/// reports — lives in one place.
#[inline]
fn finite_or_inf_f64(x: f64, operation: &'static str) -> Result<f64, Partiality> {
    if x.is_nan() {
        Err(Partiality::Undefined {
            operation,
            carrier: "f64",
            reason: UndefinedReason::NotANumber,
        })
    } else {
        Ok(x)
    }
}

/// Accept a raw `f32` unless it is `NaN`, naming the operation that produced it.
#[inline]
fn finite_or_inf_f32(x: f32, operation: &'static str) -> Result<f32, Partiality> {
    if x.is_nan() {
        Err(Partiality::Undefined {
            operation,
            carrier: "f32",
            reason: UndefinedReason::NotANumber,
        })
    } else {
        Ok(x)
    }
}

/// A carrier that can name IEEE 754's quiet `NaN`. Implemented for exactly the four float
/// carriers, so [`nan_is_a_value`] cannot be applied to an integer result by accident.
pub trait QuietNaN: Sized {
    /// IEEE 754's quiet `NaN` in this carrier.
    fn quiet_nan() -> Self;
}

impl QuietNaN for f64 {
    #[inline]
    fn quiet_nan() -> Self { f64::NAN }
}

impl QuietNaN for f32 {
    #[inline]
    fn quiet_nan() -> Self { f32::NAN }
}

impl QuietNaN for crate::CanonicalFloat64 {
    #[inline]
    fn quiet_nan() -> Self { crate::CanonicalFloat64::from(f64::NAN) }
}

impl QuietNaN for crate::CanonicalFloat32 {
    #[inline]
    fn quiet_nan() -> Self { crate::CanonicalFloat32::from(f32::NAN) }
}

/// ★★ Re-admit IEEE 754's `NaN` as a **VALUE**, for a caller that must reproduce IEEE exactly.
///
/// [`SafeArith`]'s float impls deliver `±Inf` but DECLINE `NaN` — see [`finite_or_inf_f64`] — which
/// is the right default for a language that wants an indeterminate form to stop a computation. It
/// is the WRONG answer for a language whose floor is an upstream evaluator that computes IEEE: for
/// those, `0.0 / 0.0` has an answer (`NaN`) and refusing it rejects a program upstream accepts.
///
/// ⚠ **This does not change `SafeArith`'s policy for anybody.** It is an opt-in adapter applied at
/// a single call site. The tropical and log-domain semirings, and every other consumer that wants
/// the decline, are untouched — they simply do not call this.
///
/// ★ Only [`UndefinedReason::NotANumber`] is converted. Every other decline passes through
/// unchanged, so a caller that wraps a `safe_div` still refuses a `DivisionByZero` on an integer
/// carrier, and a future decline reason this function has never seen surfaces as a failure rather
/// than being silently answered `NaN`.
///
/// ★ The conversion is EXACT, not a fallback. `finite_or_inf_f{32,64}` raise
/// `NotANumber` precisely when the IEEE operation produced a `NaN`, and IEEE 754 §6.2 / §7.2 give
/// `NaN` as the delivered result for every one of those cases (an operation with a `NaN` operand
/// propagates one; the invalid operations `∞ − ∞`, `∞ + (−∞)`, `0 × ∞`, `0/0`, `∞/∞` deliver one).
/// So there is no input for which this returns `NaN` where IEEE returns something else.
///
/// ⚠ It cannot be spelled with an operator. `macros/src/gen/native/rust_code_rewrite.rs`
/// (`binop_to_safe_method`) rewrites every `+`, `-`, `*`, `/`, `%` and unary `-` inside a `![ … ]`
/// grammar block into `<_ as SafeArith>::safe_*(…)?`, **including on raw `f64`**, and the `?`
/// short-circuits the whole fold body — leaving a STUCK TERM rather than a value or an `error`.
/// Wrapping the `safe_*` call in this function is therefore the only way a grammar arm can obtain
/// IEEE semantics.
///
/// ```
/// use mettail_runtime::{nan_is_a_value, CanonicalFloat64, SafeArith};
///
/// // `SafeArith` alone declines the indeterminate form...
/// let zero = CanonicalFloat64::from(0.0);
/// assert!(<CanonicalFloat64 as SafeArith>::safe_div(zero, zero).is_err());
///
/// // ...and with the adapter it is IEEE's answer.
/// let nan = nan_is_a_value(<CanonicalFloat64 as SafeArith>::safe_div(zero, zero))
///     .expect("IEEE delivers a NaN for 0/0");
/// assert!(nan.get().is_nan());
///
/// // `±Inf` was never declined, so it is unaffected.
/// let one = CanonicalFloat64::from(1.0);
/// let inf = nan_is_a_value(<CanonicalFloat64 as SafeArith>::safe_div(one, zero))
///     .expect("IEEE delivers +Inf for 1/0");
/// assert_eq!(inf.get(), f64::INFINITY);
/// ```
#[inline]
pub fn nan_is_a_value<T: QuietNaN>(r: Result<T, Partiality>) -> Result<T, Partiality> {
    match r {
        Err(Partiality::Undefined {
            reason: UndefinedReason::NotANumber,
            ..
        }) => Ok(T::quiet_nan()),
        other => other,
    }
}

/// Float-only extension trait for transcendental functions.
///
/// These wrap `f64::sqrt`, `f64::ln`, etc., in the same NaN-rejecting policy as
/// `SafeArith`. Not part of `SafeArith` itself because integers can't sensibly
/// have `sqrt` / `ln`, and we want the trait to be implementable uniformly.
pub trait SafeFloat: SafeArith {
    fn safe_sqrt(self) -> Result<Self, Partiality>;
    fn safe_ln(self) -> Result<Self, Partiality>;
    fn safe_log2(self) -> Result<Self, Partiality>;
    fn safe_log10(self) -> Result<Self, Partiality>;
    fn safe_exp(self) -> Result<Self, Partiality>;
    fn safe_sin(self) -> Result<Self, Partiality>;
    fn safe_cos(self) -> Result<Self, Partiality>;
    fn safe_tan(self) -> Result<Self, Partiality>;
    fn safe_asin(self) -> Result<Self, Partiality>;
    fn safe_acos(self) -> Result<Self, Partiality>;
    fn safe_atan(self) -> Result<Self, Partiality>;
    /// Floating-point exponent (distinct from `SafeArith::safe_pow`'s integer
    /// exponent). Used by the rewriter for `.powf(...)` method calls.
    fn safe_powf(self, exp: Self) -> Result<Self, Partiality>;
}

impl SafeArith for f64 {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self + r, "add")
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self - r, "sub")
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self * r, "mul")
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self / r, "div")
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self % r, "rem")
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        // Normalise `-0.0` to `+0.0` (matches CanonicalFloat64 canonicalisation).
        let r = -self;
        let r = if r == 0.0 { 0.0_f64 } else { r };
        finite_or_inf_f64(r, "neg")
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Err(Partiality::Undefined {
            operation: "not",
            carrier: "f64",
            reason: UndefinedReason::NotDefinedForCarrier,
        })
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.powi(exp), "pow")
    }
}

impl SafeFloat for f64 {
    #[inline]
    fn safe_sqrt(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.sqrt(), "sqrt")
    }
    #[inline]
    fn safe_ln(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.ln(), "ln")
    }
    #[inline]
    fn safe_log2(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.log2(), "log2")
    }
    #[inline]
    fn safe_log10(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.log10(), "log10")
    }
    #[inline]
    fn safe_exp(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.exp(), "exp")
    }
    #[inline]
    fn safe_sin(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.sin(), "sin")
    }
    #[inline]
    fn safe_cos(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.cos(), "cos")
    }
    #[inline]
    fn safe_tan(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.tan(), "tan")
    }
    #[inline]
    fn safe_asin(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.asin(), "asin")
    }
    #[inline]
    fn safe_acos(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.acos(), "acos")
    }
    #[inline]
    fn safe_atan(self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.atan(), "atan")
    }
    #[inline]
    fn safe_powf(self, exp: Self) -> Result<Self, Partiality> {
        finite_or_inf_f64(self.powf(exp), "powf")
    }
}

impl SafeArith for f32 {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self + r, "add")
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self - r, "sub")
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self * r, "mul")
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self / r, "div")
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self % r, "rem")
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        let r = -self;
        let r = if r == 0.0_f32 { 0.0_f32 } else { r };
        finite_or_inf_f32(r, "neg")
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Err(Partiality::Undefined {
            operation: "not",
            carrier: "f32",
            reason: UndefinedReason::NotDefinedForCarrier,
        })
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.powi(exp), "pow")
    }
}

impl SafeFloat for f32 {
    #[inline]
    fn safe_sqrt(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.sqrt(), "sqrt")
    }
    #[inline]
    fn safe_ln(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.ln(), "ln")
    }
    #[inline]
    fn safe_log2(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.log2(), "log2")
    }
    #[inline]
    fn safe_log10(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.log10(), "log10")
    }
    #[inline]
    fn safe_exp(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.exp(), "exp")
    }
    #[inline]
    fn safe_sin(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.sin(), "sin")
    }
    #[inline]
    fn safe_cos(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.cos(), "cos")
    }
    #[inline]
    fn safe_tan(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.tan(), "tan")
    }
    #[inline]
    fn safe_asin(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.asin(), "asin")
    }
    #[inline]
    fn safe_acos(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.acos(), "acos")
    }
    #[inline]
    fn safe_atan(self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.atan(), "atan")
    }
    #[inline]
    fn safe_powf(self, exp: Self) -> Result<Self, Partiality> {
        finite_or_inf_f32(self.powf(exp), "powf")
    }
}

// Wrapper-type impls: delegate to the raw float impl, then re-canonicalise via
// `From<f64>` / `From<f32>` (which maps `-0.0` → `+0.0` and all NaNs to one
// canonical NaN — but `SafeArith` already declines NaN before `.from` runs, so
// canonicalisation is a defence-in-depth measure). The reported carrier is the
// raw IEEE one (see the module header).

impl SafeArith for CanonicalFloat64 {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_add(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_sub(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_mul(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_div(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_rem(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        self.get().safe_neg().map(Self::from)
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        self.get().safe_not().map(Self::from)
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        self.get().safe_pow(exp).map(Self::from)
    }
}

impl SafeFloat for CanonicalFloat64 {
    #[inline]
    fn safe_sqrt(self) -> Result<Self, Partiality> {
        self.get().safe_sqrt().map(Self::from)
    }
    #[inline]
    fn safe_ln(self) -> Result<Self, Partiality> {
        self.get().safe_ln().map(Self::from)
    }
    #[inline]
    fn safe_log2(self) -> Result<Self, Partiality> {
        self.get().safe_log2().map(Self::from)
    }
    #[inline]
    fn safe_log10(self) -> Result<Self, Partiality> {
        self.get().safe_log10().map(Self::from)
    }
    #[inline]
    fn safe_exp(self) -> Result<Self, Partiality> {
        self.get().safe_exp().map(Self::from)
    }
    #[inline]
    fn safe_sin(self) -> Result<Self, Partiality> {
        self.get().safe_sin().map(Self::from)
    }
    #[inline]
    fn safe_cos(self) -> Result<Self, Partiality> {
        self.get().safe_cos().map(Self::from)
    }
    #[inline]
    fn safe_tan(self) -> Result<Self, Partiality> {
        self.get().safe_tan().map(Self::from)
    }
    #[inline]
    fn safe_asin(self) -> Result<Self, Partiality> {
        self.get().safe_asin().map(Self::from)
    }
    #[inline]
    fn safe_acos(self) -> Result<Self, Partiality> {
        self.get().safe_acos().map(Self::from)
    }
    #[inline]
    fn safe_atan(self) -> Result<Self, Partiality> {
        self.get().safe_atan().map(Self::from)
    }
    #[inline]
    fn safe_powf(self, exp: Self) -> Result<Self, Partiality> {
        self.get().safe_powf(exp.get()).map(Self::from)
    }
}

impl SafeArith for CanonicalFloat32 {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_add(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_sub(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_mul(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_div(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        self.get().safe_rem(r.get()).map(Self::from)
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        self.get().safe_neg().map(Self::from)
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        self.get().safe_not().map(Self::from)
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        self.get().safe_pow(exp).map(Self::from)
    }
}

impl SafeFloat for CanonicalFloat32 {
    #[inline]
    fn safe_sqrt(self) -> Result<Self, Partiality> {
        self.get().safe_sqrt().map(Self::from)
    }
    #[inline]
    fn safe_ln(self) -> Result<Self, Partiality> {
        self.get().safe_ln().map(Self::from)
    }
    #[inline]
    fn safe_log2(self) -> Result<Self, Partiality> {
        self.get().safe_log2().map(Self::from)
    }
    #[inline]
    fn safe_log10(self) -> Result<Self, Partiality> {
        self.get().safe_log10().map(Self::from)
    }
    #[inline]
    fn safe_exp(self) -> Result<Self, Partiality> {
        self.get().safe_exp().map(Self::from)
    }
    #[inline]
    fn safe_sin(self) -> Result<Self, Partiality> {
        self.get().safe_sin().map(Self::from)
    }
    #[inline]
    fn safe_cos(self) -> Result<Self, Partiality> {
        self.get().safe_cos().map(Self::from)
    }
    #[inline]
    fn safe_tan(self) -> Result<Self, Partiality> {
        self.get().safe_tan().map(Self::from)
    }
    #[inline]
    fn safe_asin(self) -> Result<Self, Partiality> {
        self.get().safe_asin().map(Self::from)
    }
    #[inline]
    fn safe_acos(self) -> Result<Self, Partiality> {
        self.get().safe_acos().map(Self::from)
    }
    #[inline]
    fn safe_atan(self) -> Result<Self, Partiality> {
        self.get().safe_atan().map(Self::from)
    }
    #[inline]
    fn safe_powf(self, exp: Self) -> Result<Self, Partiality> {
        self.get().safe_powf(exp.get()).map(Self::from)
    }
}

// ─── Arbitrary-precision impls ──────────────────────────────────────────────
//
// `CanonicalBigInt`/`CanonicalBigRat`/`CanonicalFixedPoint` cannot overflow the
// way bounded integers do, so most operations always succeed and NONE of them
// ever reports `NotRepresentable` — case (b) is empty for an unbounded carrier.
// Division/remainder by zero is `Undefined`. Power with a negative exponent on
// an integral carrier is `Undefined(NegativeExponent)`; `CanonicalBigRat`
// supports negative powers via reciprocation.

/// A zero divisor on an arbitrary-precision carrier.
#[inline]
const fn arbitrary_precision_div_zero(
    operation: &'static str,
    carrier: &'static str,
    reason: UndefinedReason,
) -> Partiality {
    Partiality::Undefined {
        operation,
        carrier,
        reason,
    }
}

// `&num_bigint::BigInt` impl: the safeify pass rewrites `a.get() - b.get()`
// inside user `![…]` bodies to `SafeArith::safe_sub(a.get(), b.get())?`.
// `CanonicalBigInt::get()` returns `&BigInt`, so the rewrite receives
// references. The arithmetic produces an owned `BigInt`, which the caller
// wraps back into `CanonicalBigInt::from(result)` via its original body.
impl SafeArith for &num_bigint::BigInt {
    type Output = num_bigint::BigInt;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self::Output, Partiality> {
        Ok(self + r)
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self::Output, Partiality> {
        Ok(self - r)
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self::Output, Partiality> {
        Ok(self * r)
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self::Output, Partiality> {
        use num_traits::Zero;
        if r.is_zero() {
            Err(arbitrary_precision_div_zero(
                "div",
                "BigInt",
                UndefinedReason::DivisionByZero,
            ))
        } else {
            Ok(self / r)
        }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self::Output, Partiality> {
        use num_traits::Zero;
        if r.is_zero() {
            Err(arbitrary_precision_div_zero(
                "rem",
                "BigInt",
                UndefinedReason::RemainderByZero,
            ))
        } else {
            Ok(self % r)
        }
    }
    #[inline]
    fn safe_neg(self) -> Result<Self::Output, Partiality> {
        Ok(-self)
    }
    #[inline]
    fn safe_not(self) -> Result<Self::Output, Partiality> {
        Ok(!self.clone())
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self::Output, Partiality> {
        if exp < 0 {
            return Err(arbitrary_precision_div_zero(
                "pow",
                "BigInt",
                UndefinedReason::NegativeExponent,
            ));
        }
        Ok(num_traits::pow::pow(self.clone(), exp as usize))
    }
}

// Owned `num_bigint::BigInt` impl: needed when user code produces an owned
// BigInt via `a.get().clone()` or similar. Arbitrary precision, no overflow;
// same semantics as the `&BigInt` impl but takes Self by value.
impl SafeArith for num_bigint::BigInt {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        Ok(self + r)
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        Ok(self - r)
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        Ok(self * r)
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.is_zero() {
            Err(arbitrary_precision_div_zero(
                "div",
                "BigInt",
                UndefinedReason::DivisionByZero,
            ))
        } else {
            Ok(self / r)
        }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.is_zero() {
            Err(arbitrary_precision_div_zero(
                "rem",
                "BigInt",
                UndefinedReason::RemainderByZero,
            ))
        } else {
            Ok(self % r)
        }
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Ok(-self)
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Ok(!self)
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        if exp < 0 {
            return Err(arbitrary_precision_div_zero(
                "pow",
                "BigInt",
                UndefinedReason::NegativeExponent,
            ));
        }
        Ok(num_traits::pow::pow(self, exp as usize))
    }
}

impl SafeArith for crate::CanonicalBigInt {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() + r.get()))
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() - r.get()))
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() * r.get()))
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.get().is_zero() {
            Err(arbitrary_precision_div_zero(
                "div",
                "BigInt",
                UndefinedReason::DivisionByZero,
            ))
        } else {
            Ok(Self::from(self.get() / r.get()))
        }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.get().is_zero() {
            Err(arbitrary_precision_div_zero(
                "rem",
                "BigInt",
                UndefinedReason::RemainderByZero,
            ))
        } else {
            Ok(Self::from(self.get() % r.get()))
        }
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Ok(Self::from(-self.get()))
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        Ok(Self::from(!self.get().clone()))
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        // negative exponent: the reciprocal is rational, not integral
        if exp < 0 {
            return Err(arbitrary_precision_div_zero(
                "pow",
                "BigInt",
                UndefinedReason::NegativeExponent,
            ));
        }
        Ok(Self::from(num_traits::pow::pow(self.get().clone(), exp as usize)))
    }
}

impl SafeArith for crate::CanonicalBigRat {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() + r.get()))
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() - r.get()))
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        Ok(Self::from(self.get() * r.get()))
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.get().is_zero() {
            Err(arbitrary_precision_div_zero(
                "div",
                "BigRat",
                UndefinedReason::DivisionByZero,
            ))
        } else {
            Ok(Self::from(self.get() / r.get()))
        }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.get().is_zero() {
            Err(arbitrary_precision_div_zero(
                "rem",
                "BigRat",
                UndefinedReason::RemainderByZero,
            ))
        } else {
            Ok(Self::from(self.get() % r.get()))
        }
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Ok(Self::from(-self.get()))
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        // Bitwise NOT on a rational: flip the numerator bits, keep denominator.
        // Matches the user-level `bitnot_aligned` semantics; since Ratio
        // doesn't define `!`, delegate to BigInt.
        let (n, d) = (self.get().numer().clone(), self.get().denom().clone());
        Ok(Self::from(num_rational::Ratio::new(!n, d)))
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        Ok(Self::from(num_traits::pow::Pow::pow(self.get().clone(), exp)))
    }
}

impl SafeArith for crate::CanonicalFixedPoint {
    type Output = Self;
    #[inline]
    fn safe_add(self, r: Self) -> Result<Self, Partiality> {
        Ok(self + r)
    }
    #[inline]
    fn safe_sub(self, r: Self) -> Result<Self, Partiality> {
        Ok(self - r)
    }
    #[inline]
    fn safe_mul(self, r: Self) -> Result<Self, Partiality> {
        Ok(self * r)
    }
    #[inline]
    fn safe_div(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.unscaled().is_zero() {
            Err(arbitrary_precision_div_zero(
                "div",
                "FixedPoint",
                UndefinedReason::DivisionByZero,
            ))
        } else {
            Ok(self / r)
        }
    }
    #[inline]
    fn safe_rem(self, r: Self) -> Result<Self, Partiality> {
        use num_traits::Zero;
        if r.unscaled().is_zero() {
            Err(arbitrary_precision_div_zero(
                "rem",
                "FixedPoint",
                UndefinedReason::RemainderByZero,
            ))
        } else {
            Ok(self % r)
        }
    }
    #[inline]
    fn safe_neg(self) -> Result<Self, Partiality> {
        Ok(-self)
    }
    #[inline]
    fn safe_not(self) -> Result<Self, Partiality> {
        // Bitwise NOT on a fixed-point: flip the scaled integer bits,
        // keep the places. Matches user-level `bitnot_aligned` semantics.
        Ok(Self::new(!self.unscaled().clone(), self.places()))
    }
    #[inline]
    fn safe_pow(self, exp: i32) -> Result<Self, Partiality> {
        if exp < 0 {
            return Err(arbitrary_precision_div_zero(
                "pow",
                "FixedPoint",
                UndefinedReason::NegativeExponent,
            ));
        }
        let mut acc = Self::new(num_bigint::BigInt::from(1), 0);
        for _ in 0..exp {
            acc = acc * self.clone();
        }
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The `(a)`-side reason a declining call must carry, spelled once so the cells below read as
    /// assertions about the PARTITION rather than as spellings of an enum literal.
    fn undefined(operation: &'static str, carrier: &'static str, reason: UndefinedReason) -> Partiality {
        Partiality::Undefined {
            operation,
            carrier,
            reason,
        }
    }

    /// The `(b)`-side reason: the value exists, this carrier is too narrow.
    fn overflow(operation: &'static str, carrier: &'static str) -> Partiality {
        Partiality::NotRepresentable { operation, carrier }
    }

    // ─── i32 ─────────────────────────────────────────────────────────────
    #[test]
    fn i32_add_normal() {
        assert_eq!(1_i32.safe_add(2), Ok(3));
    }

    /// ★ (b): the sum exists in `i64`; `i32` cannot hold it. The carrier is NAMED.
    #[test]
    fn i32_add_overflow() {
        assert_eq!(i32::MAX.safe_add(1), Err(overflow("add", "i32")));
    }

    #[test]
    fn i32_sub_underflow() {
        assert_eq!(i32::MIN.safe_sub(1), Err(overflow("sub", "i32")));
    }

    #[test]
    fn i32_mul_overflow() {
        assert_eq!(i32::MAX.safe_mul(2), Err(overflow("mul", "i32")));
    }

    /// ★ (a): no carrier supplies `1 / 0`, so this is `Undefined`, NOT `NotRepresentable`.
    /// The two must never collapse — that collapse is the defect this channel exists to fix.
    #[test]
    fn i32_div_by_zero() {
        assert_eq!(
            1_i32.safe_div(0),
            Err(undefined("div", "i32", UndefinedReason::DivisionByZero)),
        );
        assert_eq!(1_i32.safe_div(0).unwrap_err().reason_token(), "DivisionByZero");
    }

    #[test]
    fn i32_rem_by_zero() {
        assert_eq!(
            1_i32.safe_rem(0),
            Err(undefined("rem", "i32", UndefinedReason::RemainderByZero)),
        );
    }

    /// ★ The discriminating pair: the SAME operation declines for two DIFFERENT reasons.
    #[test]
    fn i32_div_min_by_neg_one_overflows_and_is_not_the_same_reason_as_div_by_zero() {
        assert_eq!(i32::MIN.safe_div(-1), Err(overflow("div", "i32")));
        assert_ne!(
            i32::MIN.safe_div(-1).unwrap_err().reason_token(),
            1_i32.safe_div(0).unwrap_err().reason_token(),
            "`MIN / -1` is (b) — the quotient exists in a wider carrier — while `1 / 0` is (a)",
        );
    }

    #[test]
    fn i32_neg_min_overflows() {
        // i32::MIN has no positive counterpart.
        assert_eq!(i32::MIN.safe_neg(), Err(overflow("neg", "i32")));
    }

    /// ★ `i64::MIN % -1` DECLINES, matching upstream's explicit refusal.
    ///
    /// Upstream's `combine_mod` `GInt` row guards it by hand — `if lhs == i64::MIN && rhs == -1 {
    /// return Err(ReduceError("Arithmetic overflow in modulo")) }`
    /// (`f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs:3416-3420`) — and mettail
    /// reaches the same disposition structurally, because `safe_rem` is `i64::checked_rem`, which
    /// is `None` here (the *quotient* overflows). The mathematical remainder is 0, so this is one
    /// of the few places where "the exact answer exists but is refused"; upstream refuses, and
    /// upstream is the floor on semantics.
    ///
    /// Recorded during the 2026-07-30 `%` sibling sweep: this is the `GInt` row of upstream's
    /// `combine_mod`, and it AGREES.
    #[test]
    fn i64_rem_min_by_neg_one_declines_as_upstream_does() {
        assert_eq!(i64::MIN.safe_rem(-1), Err(overflow("rem", "i64")));
        assert_eq!(
            i64::MIN.safe_rem(-1).unwrap_err().reason_token(),
            "NotRepresentable",
            "the quotient is what does not fit; the remainder itself would be 0",
        );
        // The ordinary rows are plain truncated remainder, sign following the dividend.
        assert_eq!(7_i64.safe_rem(3), Ok(1));
        assert_eq!((-7_i64).safe_rem(3), Ok(-1));
        assert_eq!(7_i64.safe_rem(-3), Ok(1));
    }

    /// ⚠ REPORTED, NOT RULED (2026-07-30 `%` sibling sweep): `CanonicalBigRat::safe_rem` does NOT
    /// agree with upstream's `GBigRat` row, and this test MEASURES the disagreement rather than
    /// asserting either side is right.
    ///
    /// Upstream's `combine_mod` `GBigRat` arm returns the LITERAL RATIONAL ZERO for every non-zero
    /// divisor (`reduce.rs:3437-3448`), which is exact: in the field ℚ every non-zero `b` divides
    /// every `a`, so nothing is left over. `CanonicalBigRat::safe_rem` instead delegates to
    /// `num_rational`'s `Rem`, which is the common-denominator numerator remainder
    /// `a/b % c/d = ((a·l/b) % (c·l/d))/l`, `l = lcm(b,d)` (`num-rational-0.4.2/src/lib.rs:761-791`,
    /// via `arith_impl!(impl Rem, rem)`) — so `7r % 3r` is `1`, not `0`.
    ///
    /// ★ WHY THIS IS NOT CHANGED HERE. It is NOT on the Rholang `%` path: `languages/src/rholang.rs`
    /// answers `BigRat %` with its own arm that builds the rational zero directly, reproducing
    /// upstream (pinned by `rholang_arith_carrier_matrix::bigrat_modulo_is_the_rational_zero`). This
    /// impl is reached only by OTHER generated languages, so changing it would move a computed value
    /// on languages the owner's `%` ruling did not mention, and the ruling was specifically "align
    /// `%` semantics with upstream **Rholang**". Pinned so the divergence is a record, not a
    /// surprise.
    #[test]
    fn bigrat_rem_diverges_from_upstreams_rholang_row_and_is_pinned_not_fixed() {
        let seven = crate::CanonicalBigRat::from(num_rational::Ratio::new(
            num_bigint::BigInt::from(7),
            num_bigint::BigInt::from(1),
        ));
        let three = crate::CanonicalBigRat::from(num_rational::Ratio::new(
            num_bigint::BigInt::from(3),
            num_bigint::BigInt::from(1),
        ));
        let got = seven.safe_rem(three).expect("3r is non-zero, so `%` is defined");
        let one = num_rational::Ratio::new(num_bigint::BigInt::from(1), num_bigint::BigInt::from(1));
        assert_eq!(
            got.get(),
            &one,
            "`num_rational`'s `Rem` gives the integer-style remainder 1 here; upstream's Rholang \
             `GBigRat` row would give 0. If this row moves to 0, the divergence has been SETTLED \
             — record the ruling, and check `rholang.rs`'s own `BigRat %` arm still agrees too.",
        );
        assert_ne!(
            got.get().numer(),
            &num_bigint::BigInt::from(0),
            "stated explicitly: this is NOT upstream's literal zero",
        );
    }

    #[test]
    fn i32_pow_normal() {
        assert_eq!(2_i32.safe_pow(10), Ok(1024));
    }

    #[test]
    fn i32_pow_overflow() {
        assert_eq!(2_i32.safe_pow(31), Err(overflow("pow", "i32")));
    }

    /// A negative integer exponent is (a): `2^-1` is rational, and no wider INTEGER carrier
    /// holds it either.
    #[test]
    fn i32_pow_negative_exponent_is_undefined() {
        assert_eq!(
            2_i32.safe_pow(-1),
            Err(undefined("pow", "i32", UndefinedReason::NegativeExponent)),
        );
    }

    #[test]
    fn i32_product_overflow_short_circuits() {
        let factorial_50 = (1..=50_i32).collect::<Vec<_>>();
        assert_eq!(i32::safe_product(factorial_50), Err(overflow("mul", "i32")));
    }

    #[test]
    fn i32_product_finite() {
        let factorial_12 = (1..=12_i32).collect::<Vec<_>>();
        assert_eq!(i32::safe_product(factorial_12), Ok(479_001_600));
    }

    #[test]
    fn i32_sum_overflow_short_circuits() {
        let chain = vec![i32::MAX, 1];
        assert_eq!(i32::safe_sum(chain), Err(overflow("add", "i32")));
    }

    #[test]
    fn i32_sum_normal() {
        let xs = vec![1, 2, 3, 4, 5];
        assert_eq!(i32::safe_sum(xs), Ok(15));
    }

    // ─── u32 ─────────────────────────────────────────────────────────────
    #[test]
    fn u32_sub_underflow() {
        assert_eq!(0_u32.safe_sub(1), Err(overflow("sub", "u32")));
    }

    #[test]
    fn u32_neg_zero_is_zero() {
        assert_eq!(0_u32.safe_neg(), Ok(0));
    }

    #[test]
    fn u32_neg_nonzero_is_not_representable() {
        assert_eq!(1_u32.safe_neg(), Err(overflow("neg", "u32")));
    }

    // ─── i64 ─────────────────────────────────────────────────────────────
    #[test]
    fn i64_mul_overflow() {
        assert_eq!(i64::MAX.safe_mul(2), Err(overflow("mul", "i64")));
    }

    /// ★ The token pins the RED suite depends on: `i64` overflow is `NotRepresentable` and names
    /// `"i64"` as the carrier that did not fit.
    #[test]
    fn i64_overflow_names_the_carrier_that_did_not_fit() {
        let declined = i64::MAX.safe_add(1).unwrap_err();
        assert_eq!(declined.reason_token(), "NotRepresentable");
        assert_eq!(declined.carrier(), Some("i64"));
        assert_eq!(declined.operation(), Some("add"));
    }

    #[test]
    fn i64_factorial_20_fits() {
        // 20! = 2432902008176640000, within i64
        let f = (1..=20_i64).collect::<Vec<_>>();
        assert_eq!(i64::safe_product(f), Ok(2_432_902_008_176_640_000));
    }

    #[test]
    fn i64_factorial_21_overflows() {
        let f = (1..=21_i64).collect::<Vec<_>>();
        assert_eq!(i64::safe_product(f), Err(overflow("mul", "i64")));
    }

    // ─── bool ────────────────────────────────────────────────────────────
    #[test]
    fn bool_add_is_or() {
        assert_eq!(true.safe_add(false), Ok(true));
        assert_eq!(false.safe_add(false), Ok(false));
    }

    #[test]
    fn bool_mul_is_and() {
        assert_eq!(true.safe_mul(true), Ok(true));
        assert_eq!(true.safe_mul(false), Ok(false));
    }

    #[test]
    fn bool_neg_is_not() {
        assert_eq!(true.safe_neg(), Ok(false));
        assert_eq!(false.safe_neg(), Ok(true));
    }

    #[test]
    fn bool_sub_div_rem_pow_are_not_defined_for_the_carrier() {
        let reason = UndefinedReason::NotDefinedForCarrier;
        assert_eq!(true.safe_sub(false), Err(undefined("sub", "bool", reason)));
        assert_eq!(true.safe_div(false), Err(undefined("div", "bool", reason)));
        assert_eq!(true.safe_rem(false), Err(undefined("rem", "bool", reason)));
        assert_eq!(true.safe_pow(2), Err(undefined("pow", "bool", reason)));
    }

    // ─── String ──────────────────────────────────────────────────────────
    #[test]
    fn string_add_concats() {
        let a = "hello".to_string();
        let b = ", world".to_string();
        assert_eq!(a.safe_add(b), Ok("hello, world".to_string()));
    }

    #[test]
    fn string_other_ops_are_not_defined_for_the_carrier() {
        let reason = UndefinedReason::NotDefinedForCarrier;
        let a = "x".to_string();
        assert_eq!(
            a.clone().safe_sub("y".to_string()),
            Err(undefined("sub", "String", reason)),
        );
        assert_eq!(
            a.clone().safe_mul("y".to_string()),
            Err(undefined("mul", "String", reason)),
        );
        assert_eq!(a.safe_neg(), Err(undefined("neg", "String", reason)));
    }

    // ─── f64 ─────────────────────────────────────────────────────────────
    #[test]
    fn f64_add_finite() {
        assert_eq!(1.0_f64.safe_add(2.0), Ok(3.0));
    }

    #[test]
    fn f64_add_overflow_to_inf_is_ok() {
        // MAX + MAX saturates to +Inf, which SafeArith preserves.
        let r = f64::MAX.safe_add(f64::MAX);
        assert_eq!(r, Ok(f64::INFINITY));
    }

    /// ★ `Inf - Inf` is the IEEE indeterminate form: (a), not (b). No wider float helps.
    #[test]
    fn f64_add_inf_minus_inf_is_not_a_number() {
        assert_eq!(
            f64::INFINITY.safe_add(f64::NEG_INFINITY),
            Err(undefined("add", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_add_nan_is_not_a_number() {
        let expected = Err(undefined("add", "f64", UndefinedReason::NotANumber));
        assert_eq!(f64::NAN.safe_add(1.0), expected);
        assert_eq!(1.0_f64.safe_add(f64::NAN), expected);
    }

    #[test]
    fn f64_div_by_zero_positive_is_inf() {
        assert_eq!(1.0_f64.safe_div(0.0), Ok(f64::INFINITY));
    }

    #[test]
    fn f64_div_by_zero_negative_is_neg_inf() {
        assert_eq!((-1.0_f64).safe_div(0.0), Ok(f64::NEG_INFINITY));
    }

    #[test]
    fn f64_zero_div_zero_is_not_a_number() {
        assert_eq!(
            0.0_f64.safe_div(0.0),
            Err(undefined("div", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_rem_by_zero_is_not_a_number() {
        assert_eq!(
            1.0_f64.safe_rem(0.0),
            Err(undefined("rem", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_neg_zero_normalises_to_positive_zero() {
        let r = 0.0_f64.safe_neg().expect("safe_neg(0.0) is total");
        assert_eq!(r, 0.0);
        assert!(
            !r.is_sign_negative(),
            "safe_neg(0.0) must produce +0.0 (found -0.0) to match CanonicalFloat64"
        );
    }

    #[test]
    fn f64_pow_zero_neg_one_is_inf() {
        // 0.powi(-1) = 1/0 = +Inf
        assert_eq!(0.0_f64.safe_pow(-1), Ok(f64::INFINITY));
    }

    #[test]
    fn f64_powf_neg_root_is_not_a_number() {
        // sqrt(-1) = NaN
        assert_eq!(
            (-1.0_f64).safe_powf(0.5),
            Err(undefined("powf", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_sqrt_negative_is_not_a_number() {
        assert_eq!(
            (-1.0_f64).safe_sqrt(),
            Err(undefined("sqrt", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_ln_zero_is_neg_inf() {
        // ln(0) = -Inf
        assert_eq!(0.0_f64.safe_ln(), Ok(f64::NEG_INFINITY));
    }

    #[test]
    fn f64_ln_negative_is_not_a_number() {
        assert_eq!(
            (-1.0_f64).safe_ln(),
            Err(undefined("ln", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_product_short_circuits_on_nan() {
        use std::cell::Cell;
        let count = Cell::new(0_usize);
        // Iterator that yields 1.0, 2.0, NaN, 4.0. If short-circuit works, count ≤ 3.
        let iter = (0..4).map(|i| {
            count.set(count.get() + 1);
            match i {
                0 => 1.0,
                1 => 2.0,
                2 => f64::NAN,
                _ => 4.0,
            }
        });
        assert_eq!(
            f64::safe_product(iter),
            Err(undefined("mul", "f64", UndefinedReason::NotANumber)),
        );
        assert!(
            count.get() <= 3,
            "safe_product should short-circuit on NaN, consumed {}",
            count.get()
        );
    }

    #[test]
    fn f64_product_with_inf_is_ok() {
        // Product that saturates to +Inf should still be Ok(Inf) — the NaN
        // gate only rejects indeterminate results.
        let xs = vec![1e300_f64, 1e300, 1e300];
        let r = f64::safe_product(xs);
        assert_eq!(r, Ok(f64::INFINITY));
    }

    #[test]
    fn f64_sum_mixed_inf_is_not_a_number() {
        // +Inf + -Inf = NaN.
        let xs = vec![f64::INFINITY, f64::NEG_INFINITY];
        assert_eq!(
            f64::safe_sum(xs),
            Err(undefined("add", "f64", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f64_subnormal_passes_through() {
        // Subnormal numbers are finite and valid; never rejected.
        let small = f64::MIN_POSITIVE / 2.0;
        assert!(small > 0.0 && small.is_finite());
        assert_eq!(small.safe_add(0.0), Ok(small));
        assert_eq!(small.safe_mul(1.0), Ok(small));
    }

    // ─── CanonicalFloat64 ────────────────────────────────────────────────
    #[test]
    fn canonical_f64_delegates_to_f64() {
        let a = CanonicalFloat64::from(1.0);
        let b = CanonicalFloat64::from(2.0);
        assert_eq!(a.safe_add(b), Ok(CanonicalFloat64::from(3.0)));
    }

    #[test]
    fn canonical_f64_inf_round_trips() {
        let a = CanonicalFloat64::from(1.0);
        let z = CanonicalFloat64::from(0.0);
        let r = a.safe_div(z).expect("1.0 / 0.0 should be Ok(+Inf)");
        assert!(r.get().is_infinite());
    }

    /// The wrapper reports the RAW IEEE carrier — see the module header's carrier-naming note.
    #[test]
    fn canonical_f64_nan_input_declines_naming_the_raw_carrier() {
        // Constructing a NaN CanonicalFloat64, then doing an op on it, declines.
        let nan = CanonicalFloat64::from(f64::NAN);
        let declined = nan
            .safe_add(CanonicalFloat64::from(1.0))
            .expect_err("NaN input must decline");
        assert_eq!(declined.reason_token(), "NotANumber");
        assert_eq!(declined.carrier(), Some("f64"));
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
        assert_eq!(CanonicalFloat64::safe_product(empty), Ok(CanonicalFloat64::from(1.0)));
    }

    #[test]
    fn canonical_f64_sum_identity() {
        let empty: Vec<CanonicalFloat64> = vec![];
        assert_eq!(CanonicalFloat64::safe_sum(empty), Ok(CanonicalFloat64::from(0.0)));
    }

    // ─── f32 (sanity) ────────────────────────────────────────────────────
    #[test]
    fn f32_nan_rejected() {
        assert_eq!(
            f32::NAN.safe_add(1.0),
            Err(undefined("add", "f32", UndefinedReason::NotANumber)),
        );
    }

    #[test]
    fn f32_inf_preserved() {
        assert_eq!(f32::MAX.safe_add(f32::MAX), Ok(f32::INFINITY));
    }

    // ─── Arbitrary precision: case (b) is EMPTY ──────────────────────────
    /// ★ An unbounded carrier can never report `NotRepresentable` — there is no width to exceed.
    /// Its only partialities are (a): a zero divisor and a negative integral exponent.
    #[test]
    fn arbitrary_precision_declines_only_for_undefined_never_for_width() {
        use crate::CanonicalBigInt;
        let zero = CanonicalBigInt::from(num_bigint::BigInt::from(0));
        let one = CanonicalBigInt::from(num_bigint::BigInt::from(1));
        assert_eq!(
            one.clone().safe_div(zero.clone()).unwrap_err().reason_token(),
            "DivisionByZero",
        );
        assert_eq!(
            one.clone().safe_rem(zero).unwrap_err().reason_token(),
            "RemainderByZero",
        );
        assert_eq!(one.clone().safe_pow(-1).unwrap_err().reason_token(), "NegativeExponent");
        assert_eq!(one.clone().safe_pow(-1).unwrap_err().carrier(), Some("BigInt"));
        // And the total direction still computes.
        assert_eq!(
            one.clone().safe_add(one).expect("1 + 1 is total"),
            CanonicalBigInt::from(num_bigint::BigInt::from(2)),
        );
    }
}
